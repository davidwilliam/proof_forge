"""ProofForge API: forge jobs (live or replayed), event streams, verification, Passports,
the payout sidecar, and results.

Statuses shown to clients come only from runner records: agent events, judge and
binary-check results, and Passports built by harness/passport.py.

Run: .venv/bin/uvicorn server.app:app --port 8000
Environment:
  PF_MODE=live|replay     replay refuses live model jobs (kill switch); default live
  PF_JUDGE_KEY=<secret>   requests with header X-Judge-Key get the judge quota
  PF_LIVE_QUOTA=2         live jobs per client IP per day without the judge key
  PF_JUDGE_QUOTA=30       live jobs per day with the judge key
  PF_JOB_BUDGET_USD=3     per-job cap at standard-tier list prices
"""
import asyncio, json, os, pathlib, shutil, subprocess, sys, tempfile, threading, time, uuid

from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import StreamingResponse
from pydantic import BaseModel

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import judge, passport, task as taskmod  # noqa: E402

JOBS = ROOT / "runs" / "jobs"
PASSPORTS = ROOT / "runs" / "passports"
BUILDS = ROOT / "runs" / "builds"
RECORDINGS = ROOT / "recordings"
for d in (JOBS, PASSPORTS, BUILDS):
    d.mkdir(parents=True, exist_ok=True)

app = FastAPI(title="ProofForge API", version="0.1")
app.add_middleware(CORSMiddleware, allow_origins=os.environ.get("PF_CORS", "*").split(","),
                   allow_methods=["GET", "POST"], allow_headers=["*"])

_quota, _lock = {}, threading.Lock()


def mode():
    return os.environ.get("PF_MODE", "live")


def take_quota(req: Request):
    key = req.headers.get("x-judge-key")
    judge_ok = bool(os.environ.get("PF_JUDGE_KEY")) and key == os.environ.get("PF_JUDGE_KEY")
    who = "judge" if judge_ok else (req.client.host if req.client else "unknown")
    limit = int(os.environ.get("PF_JUDGE_QUOTA" if judge_ok else "PF_LIVE_QUOTA", "30" if judge_ok else "2"))
    day = time.strftime("%Y-%m-%d")
    with _lock:
        n = _quota.get((who, day), 0)
        if n >= limit:
            raise HTTPException(429, f"live quota reached ({limit} per day); replay mode is available")
        _quota[(who, day)] = n + 1


# Tasks

def task_summary(t, detail=False):
    reqs = []
    for rid, th in t.requirements:
        stmt = passport.statement(t, th)
        reqs.append({"id": rid, "theorem": f"{t.ns}.{th}", "statement": stmt, "text": passport.docstring(t, stmt)})
    out = {"id": t.id, "family": t.family, "split": t.split, "namespace": t.ns, "issue": t.issue,
           "definitions": t.definitions, "requirements": reqs, "manifest_sha256": t.locked()["manifest_sha256"]}
    if detail:
        out["files"] = {p: (t.root / p).read_text() for p in t.readable}
        out["locked"] = t.locked()["files"]
        out["comparator"] = json.loads((t.root / "spec/comparator.json").read_text())
    return out


@app.get("/api/health")
def health():
    return {"ok": True, "mode": mode(), "judge_image": judge.image_id(), "in_image": judge.IN_IMAGE}


@app.get("/api/tasks")
def tasks(split: str | None = None):
    return [task_summary(t) for t in taskmod.all_tasks(split) if (t.root / "spec/locked.json").exists()]


@app.get("/api/tasks/{task_id}")
def task_detail(task_id: str):
    try:
        return task_summary(taskmod.load(task_id), detail=True)
    except FileNotFoundError:
        raise HTTPException(404, "no such task")


# Jobs

class ForgeRequest(BaseModel):
    task: str = "payout-flagship"
    mode: str = "replay"            # live | replay
    arm: str = "A2"                 # A1 (no planner) | A2 (planner)
    recording: str | None = None    # replay source under recordings/
    speed: float = 20.0             # replay time compression


def job_dir(job_id):
    d = JOBS / job_id
    if not d.exists() or not (d / "job.json").exists():
        raise HTTPException(404, "no such job")
    return d


def emit(d, **kw):
    """Append a job-level event (agent events are written by the agent itself)."""
    kw.setdefault("t", round(time.time(), 3))
    with (d / "events.jsonl").open("a") as f:
        f.write(json.dumps(kw) + "\n")


def set_job(d, **kw):
    j = json.loads((d / "job.json").read_text())
    j.update(kw)
    (d / "job.json").write_text(json.dumps(j, indent=2))
    return j


def verify_job(d, t, label):
    """Fresh judge + binary check of the job's final candidate, outside the agent's sandbox."""
    final = d / "final.lean"
    if not final.exists():
        emit(d, kind="job", state="FAILED", reason="no final candidate")
        set_job(d, state="FAILED")
        return
    emit(d, kind="job", state="CHECKING", label=label)
    set_job(d, state="CHECKING")
    prov_path = d / "summary.json"
    prov = json.loads(prov_path.read_text()) if prov_path.exists() else None
    p = passport.run(final, t, cases=2000, seed=0, provenance=prov)
    (PASSPORTS / f"{p['passport_sha256']}.json").write_text(json.dumps(p, indent=2))
    state = "COMPLETE" if p["status"] == "VERIFIED" else "PARTIAL"
    if prov and prov.get("budget", {}).get("stop") and state != "COMPLETE":
        state = "BUDGET_STOP"
    emit(d, kind="passport", passport_sha256=p["passport_sha256"], status=p["status"],
         requirements={r["id"]: r["status"] for r in p["requirements"]}, label=label)
    emit(d, kind="job", state=state)
    set_job(d, state=state, passport_sha256=p["passport_sha256"])


def run_live(d, t, arm):
    set_job(d, state="DIAGNOSING")
    emit(d, kind="job", state="DIAGNOSING", label="Live")
    cmd = [sys.executable, str(ROOT / "agents/repair.py"), "--task", str(t.root), "--out", str(d),
           "--planner", "none" if arm == "A1" else "muse-wonder-1.0",
           "--model", os.environ.get("PF_LIVE_MODEL", "muse-spark-1.3"),
           "--budget-usd", os.environ.get("PF_JOB_BUDGET_USD", "3"),
           "--budget-wall", os.environ.get("PF_JOB_BUDGET_WALL", "2700")]
    with (d / "agent.log").open("w") as log:
        subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, cwd=ROOT)
    verify_job(d, t, "Live")


def run_replay(d, t, src, speed):
    """Re-emit a recorded session's events with compressed timing; the final check is fresh."""
    set_job(d, state="DIAGNOSING")
    emit(d, kind="job", state="DIAGNOSING", label="Recorded run", recording=src.name)
    events = [json.loads(l) for l in (src / "events.jsonl").read_text().splitlines() if l.strip()]
    prev = None
    for e in events:
        if prev is not None:
            time.sleep(min(2.0, max(0.0, (e["t"] - prev) / speed)))
        prev = e["t"]
        e = {**e, "recorded_t": e["t"], "t": round(time.time(), 3)}
        if e.get("kind") == "write":
            v = src / f"candidate_v{e['version']:03d}.lean"
            if v.exists():
                shutil.copy(v, d / v.name)
        with (d / "events.jsonl").open("a") as f:
            f.write(json.dumps(e) + "\n")
    for name in ("final.lean", "summary.json"):
        if (src / name).exists():
            shutil.copy(src / name, d / name)
    verify_job(d, t, "Fresh check of stored artifact")


@app.post("/api/jobs")
def create_job(body: ForgeRequest, request: Request):
    try:
        t = taskmod.load(body.task)
    except FileNotFoundError:
        raise HTTPException(404, "no such task")
    if body.mode == "live":
        if mode() != "live":
            raise HTTPException(503, "live sessions are disabled; replay mode is available")
        take_quota(request)
    elif body.mode == "replay":
        src = RECORDINGS / (body.recording or "")
        if not body.recording or not (src / "events.jsonl").exists() or ".." in body.recording:
            raise HTTPException(404, "no such recording")
    else:
        raise HTTPException(400, "mode must be live or replay")
    job_id = uuid.uuid4().hex[:12]
    d = JOBS / job_id
    d.mkdir()
    (d / "job.json").write_text(json.dumps({"id": job_id, "task": t.id, "mode": body.mode, "arm": body.arm,
                                            "recording": body.recording, "state": "CREATED",
                                            "created": time.time()}, indent=2))
    emit(d, kind="job", state="CREATED")
    target = (lambda: run_live(d, t, body.arm)) if body.mode == "live" else \
        (lambda: run_replay(d, t, RECORDINGS / body.recording, body.speed))
    threading.Thread(target=target, daemon=True).start()
    return json.loads((d / "job.json").read_text())


@app.get("/api/jobs/{job_id}")
def get_job(job_id: str):
    d = job_dir(job_id)
    j = json.loads((d / "job.json").read_text())
    versions = sorted(p.name for p in d.glob("candidate_v*.lean"))
    j["versions"] = len(versions)
    return j


@app.get("/api/jobs/{job_id}/candidate/{version}")
def get_candidate(job_id: str, version: int):
    d = job_dir(job_id)
    f = d / f"candidate_v{version:03d}.lean"
    if not f.exists():
        raise HTTPException(404, "no such version")
    return {"version": version, "source": f.read_text(), "sha256": taskmod.sha256(f)}


TERMINAL = {"COMPLETE", "PARTIAL", "FAILED", "TIMEOUT", "BUDGET_STOP"}


@app.get("/api/jobs/{job_id}/events")
async def job_events(job_id: str, request: Request):
    """Server-sent events: one per record, with monotonic ids; resumes from Last-Event-ID."""
    d = job_dir(job_id)
    start = int(request.headers.get("last-event-id", "-1")) + 1

    async def gen():
        seq, pos = 0, 0
        while True:
            f = d / "events.jsonl"
            if f.exists():
                with f.open("rb") as fh:
                    fh.seek(pos)
                    chunk = fh.read()
                end = chunk.rfind(b"\n")
                lines = chunk[:end].decode().splitlines() if end >= 0 else []
                pos += end + 1
                for line in lines:
                    if not line.strip():
                        continue
                    if seq >= start:
                        yield f"id: {seq}\ndata: {line}\n\n"
                    seq += 1
                    e = json.loads(line)
                    if e.get("kind") == "job" and e.get("state") in TERMINAL:
                        return
            if await request.is_disconnected():
                return
            await asyncio.sleep(0.3)

    return StreamingResponse(gen(), media_type="text/event-stream",
                             headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


# Verification and Passports

class VerifyRequest(BaseModel):
    task: str = "payout-flagship"
    source: str


@app.post("/api/verify")
def verify(body: VerifyRequest):
    """Synchronous fresh check of submitted candidate source (no model calls)."""
    if len(body.source) > 200_000:
        raise HTTPException(413, "candidate too large")
    try:
        t = taskmod.load(body.task)
    except FileNotFoundError:
        raise HTTPException(404, "no such task")
    f = pathlib.Path(tempfile.mkdtemp(prefix="pf-verify-")) / "Solution.lean"
    f.write_text(body.source)
    p = passport.run(f, t, cases=1000, seed=0)
    (PASSPORTS / f"{p['passport_sha256']}.json").write_text(json.dumps(p, indent=2))
    return p


@app.get("/api/passports/{sha}")
def get_passport(sha: str):
    f = PASSPORTS / f"{sha}.json"
    if not all(c in "0123456789abcdef" for c in sha) or not f.exists():
        raise HTTPException(404, "no such passport")
    return json.loads(f.read_text())


@app.get("/api/passports/{sha}/comment")
def passport_comment(sha: str):
    return {"markdown": passport.markdown(get_passport(sha))}


# Payout sidecar for the TypeScript app

BUILDS_ALLOWED = {"buggy": "candidate/Solution.lean", "repaired": "evidence/muse-repair-002/Solution.lean"}
_build_lock = threading.Lock()


def built_project(which):
    t = taskmod.load()
    src = t.root / BUILDS_ALLOWED[which]
    sha = taskmod.sha256(src)
    d = BUILDS / sha
    with _build_lock:
        if not (d / ".lake/build/bin" / t.exe).exists():
            shutil.rmtree(d, ignore_errors=True)
            ws = judge.load_workspace(str(src))
            tmp = judge.fresh_project(ws, judge.candidate_files(ws), t)
            r = judge.in_container(tmp, f"lake build {t.exe} 2>&1 | tail -c 2000")
            if r["exit_code"] != 0 or not (tmp / ".lake/build/bin" / t.exe).exists():
                raise HTTPException(500, "sidecar build failed")
            shutil.move(str(tmp), d)
    return t, d, sha


class PayoutRequest(BaseModel):
    build: str = "repaired"         # buggy | repaired
    state: dict
    request: dict


@app.post("/api/payout")
def payout(body: PayoutRequest):
    if body.build not in BUILDS_ALLOWED:
        raise HTTPException(400, "build must be buggy or repaired")
    t, d, sha = built_project(body.build)
    line = json.dumps({"state": body.state, "request": body.request})
    if len(line) > 20_000:
        raise HTTPException(413, "input too large")
    (d / "in.jsonl").write_text(line + "\n")
    r = judge.in_container(d, f".lake/build/bin/{t.exe} < in.jsonl")
    out = r["output_tail"].strip().splitlines()
    if not out:
        raise HTTPException(500, "sidecar produced no output")
    res = json.loads(out[-1])
    exe = d / ".lake/build/bin" / t.exe
    return {"build": body.build, "solution_sha256": sha, "executable_sha256": taskmod.sha256(exe),
            "result": res, "elapsed_ms": r["elapsed_ms"]}


# Results

@app.get("/api/results")
def results():
    out = {}
    for p in sorted((ROOT / "results").glob("e*-*/e*.json")):
        data = json.loads(p.read_text())
        out[p.parent.name] = data.get("summary", data)
    return out


@app.get("/api/recordings")
def recordings():
    return sorted(p.parent.name for p in RECORDINGS.glob("*/events.jsonl"))
