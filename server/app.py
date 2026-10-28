"""ProofForge API: forge jobs (live or replayed), event streams, verification, Passports,
the payout sidecar, and results.

Statuses shown to clients come only from runner records: agent events, judge and
binary-check results, and Passports built by harness/passport.py.

Run: .venv/bin/uvicorn server.app:app --port 8000
Environment (admission, quotas and spending are documented in server/controls.py):
  PF_MODE=live|replay     replay refuses live model jobs; the admin endpoint overrides it
  PF_JOB_BUDGET_USD=3     per live job cap at standard-tier list prices
  PF_JOB_BUDGET_WALL=2700 per live job wall clock; the process is killed 300 s after it
  PF_VERIFY_DEADLINE_S=240, PF_CHALLENGE_DEADLINE_S=45, PF_PAYOUT_DEADLINE_S=20
                          request-wide limits on Lean and binary runs; a check stopped by
                          its limit is reported UNRESOLVED, never REFUTED
  PF_PREWARM=1            build sidecars and hidden variants at startup
  PF_DATA=runs            jobs, Passports, builds and server.db
"""
import asyncio, json, os, pathlib, shutil, signal, subprocess, sys, tempfile, threading, time, uuid

from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import StreamingResponse
from pydantic import BaseModel

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "harness"))
import binary_check, judge, passport, task as taskmod  # noqa: E402
from server import controls  # noqa: E402

DATA = pathlib.Path(os.environ.get("PF_DATA", ROOT / "runs"))   # a persistent volume on the host
JOBS = DATA / "jobs"
PASSPORTS = DATA / "passports"
BUILDS = DATA / "builds"
RECORDINGS = ROOT / "recordings"
for d in (JOBS, PASSPORTS, BUILDS):
    d.mkdir(parents=True, exist_ok=True)

app = FastAPI(title="ProofForge API", version="0.1")
app.add_middleware(CORSMiddleware, allow_origins=os.environ.get("PF_CORS", "*").split(","),
                   allow_methods=["GET", "POST"], allow_headers=["*"])

CTRL = controls.Controls()
LIVE = {}               # job id -> agent process, for the operator stop
WARM = threading.Event()


def mode():
    return CTRL.mode()


def seconds(name, default):
    return float(os.environ.get(name, str(default)))


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
    free = shutil.disk_usage(JOBS).free
    return {"ok": True, "ready": WARM.is_set(), "judge_image": judge.image_id(), "in_image": judge.IN_IMAGE,
            "disk_free_gb": round(free / 2**30, 1), "live_jobs": len(LIVE), **CTRL.state()}


@app.get("/api/tasks")
def tasks(split: str | None = None):
    return [task_summary(t) for t in taskmod.all_tasks(split) if (t.root / "spec/locked.json").exists()]


@app.get("/api/tasks/{task_id}")
def task_detail(task_id: str):
    return task_summary(public_task(task_id), detail=True)


# Jobs

class ForgeRequest(BaseModel):
    task: str = "payout-flagship"
    mode: str = "replay"            # live | replay
    arm: str = "A2"                 # A1 (no planner) | A2 (planner)
    recording: str | None = None    # replay source under recordings/
    speed: float = 20.0             # replay time compression, 1 to 100


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


_job_lock = threading.Lock()


def write_json(path, obj):
    """Replace `path` atomically, so a concurrent reader sees the old or the new content,
    never a truncated file."""
    tmp = path.with_name(f".{path.name}.{uuid.uuid4().hex}.tmp")
    tmp.write_text(json.dumps(obj, indent=2))
    os.replace(tmp, path)


def set_job(d, **kw):
    with _job_lock:
        j = json.loads((d / "job.json").read_text())
        j.update(kw)
        write_json(d / "job.json", j)
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
    if prov and prov.get("budget"):
        emit(d, kind="summary", budget=prov["budget"], versions=prov.get("versions"),
             accepted_in_session=prov.get("accepted_in_session"))
    try:
        CTRL.checks.acquire()
    except HTTPException:
        emit(d, kind="job", state="QUEUED", reason="waiting for a check slot")
        CTRL.checks.acquire(wait=3600)
    try:
        p = passport.run(final, t, cases=2000, seed=0, provenance=prov)
    finally:
        CTRL.checks.release()
    write_json(PASSPORTS / f"{p['passport_sha256']}.json", p)
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
    wall = seconds("PF_JOB_BUDGET_WALL", 2700)
    cmd = [sys.executable, str(ROOT / "agents/repair.py"), "--task", str(t.root), "--out", str(d),
           "--planner", "none" if arm == "A1" else "muse-wonder-1.0",
           "--model", os.environ.get("PF_LIVE_MODEL", "muse-spark-1.3"),
           "--budget-usd", os.environ.get("PF_JOB_BUDGET_USD", "3"), "--budget-wall", str(wall)]
    with (d / "agent.log").open("w") as log:
        proc = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, cwd=ROOT, start_new_session=True)
        LIVE[d.name] = proc
        try:
            proc.wait(timeout=wall + 300)
        except subprocess.TimeoutExpired:
            stop_process(proc)
        finally:
            LIVE.pop(d.name, None)
    summary = d / "summary.json"
    CTRL.store.settle(d.name, json.loads(summary.read_text()).get("budget", {}).get("usd_list")
                      if summary.exists() else None)
    if json.loads((d / "job.json").read_text()).get("stopped"):
        emit(d, kind="job", state="FAILED", reason="stopped by the operator")
        set_job(d, state="FAILED")
        return
    verify_job(d, t, "Live")


def stop_process(proc):
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    proc.wait()


def run_replay(d, t, src, speed):
    """Re-emit a recorded session's events with compressed timing; the final check is fresh."""
    set_job(d, state="DIAGNOSING")
    emit(d, kind="job", state="DIAGNOSING", label="Recorded run", recording=src.name)
    events = [json.loads(l) for l in (src / "events.jsonl").read_text().splitlines() if l.strip()]
    prev = None
    speed = min(100.0, max(1.0, speed))
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


def public_task(task_id):
    """A listed task by id; paths and hidden variants are not reachable from requests."""
    try:
        t = taskmod.load(task_id) if "/" not in task_id and ".." not in task_id else None
    except FileNotFoundError:
        t = None
    if t is None or t.split == "hidden":
        raise HTTPException(404, "no such task")
    return t


@app.post("/api/jobs")
def create_job(body: ForgeRequest, request: Request):
    return start_job(public_task(body.task), body, request)


def start_job(t, body: ForgeRequest, request: Request):
    job_id = uuid.uuid4().hex[:12]
    if body.mode == "live":
        if mode() != "live":
            raise HTTPException(503, "live sessions are disabled; replay mode is available")
    elif body.mode == "replay":
        src = RECORDINGS / (body.recording or "")
        if not body.recording or "/" in body.recording or ".." in body.recording or not (src / "events.jsonl").exists():
            raise HTTPException(404, "no such recording")
    else:
        raise HTTPException(400, "mode must be live or replay")
    gates = [CTRL.jobs] + ([CTRL.live] if body.mode == "live" else [])
    held = []
    try:
        for g in gates:
            g.acquire()
            held.append(g)
        CTRL.quota(request, body.mode)
        if body.mode == "live":
            CTRL.reserve_live(job_id, float(os.environ.get("PF_JOB_BUDGET_USD", "3")))
    except HTTPException:
        for g in held:
            g.release()
        raise
    d = JOBS / job_id
    d.mkdir()
    job = {"id": job_id, "task": t.id, "mode": body.mode, "arm": body.arm,
           "recording": body.recording, "state": "CREATED", "created": time.time()}
    write_json(d / "job.json", job)
    emit(d, kind="job", state="CREATED")
    work = (lambda: run_live(d, t, body.arm)) if body.mode == "live" else \
        (lambda: run_replay(d, t, RECORDINGS / body.recording, body.speed))

    def target():
        try:
            work()
        except Exception as e:  # a job never ends without a terminal event
            emit(d, kind="job", state="FAILED", reason=f"server error: {type(e).__name__}")
            set_job(d, state="FAILED")
        finally:
            for g in held:
                g.release()

    threading.Thread(target=target, daemon=True).start()
    return job


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
HEARTBEAT_S = 15


def recover_jobs():
    """A restart ends every job that was running: mark each with a terminal event, so that
    clients waiting on its stream stop waiting. Unsettled live reservations stay charged."""
    for f in JOBS.glob("*/job.json"):
        j = json.loads(f.read_text())
        if j.get("state") not in TERMINAL:
            emit(f.parent, kind="job", state="FAILED", reason="server restarted during the job")
            set_job(f.parent, state="FAILED")


recover_jobs()


@app.get("/api/jobs/{job_id}/events")
async def job_events(job_id: str, request: Request):
    """Server-sent events: one per record, with monotonic ids; resumes from Last-Event-ID."""
    d = job_dir(job_id)
    start = int(request.headers.get("last-event-id", "-1")) + 1

    async def gen():
        seq, pos, quiet = 0, 0, time.monotonic()
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
                        quiet = time.monotonic()
                    seq += 1
                    e = json.loads(line)
                    if e.get("kind") == "job" and e.get("state") in TERMINAL:
                        return
            if await request.is_disconnected():
                return
            if time.monotonic() - quiet > HEARTBEAT_S:   # keeps proxies from closing an idle stream
                yield ": keepalive\n\n"
                quiet = time.monotonic()
            await asyncio.sleep(0.3)

    return StreamingResponse(gen(), media_type="text/event-stream",
                             headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


# Verification and Passports

class VerifyRequest(BaseModel):
    task: str = "payout-flagship"
    source: str


@app.post("/api/verify")
def verify(body: VerifyRequest, request: Request):
    """Synchronous fresh check of submitted candidate source (no model calls)."""
    if len(body.source) > 200_000:
        raise HTTPException(413, "candidate too large")
    t = public_task(body.task)
    with CTRL.checks.hold(wait=10):
        CTRL.quota(request, "verify")
        with tempfile.TemporaryDirectory(prefix="pf-verify-") as tmp, \
                judge.time_limit(seconds("PF_VERIFY_DEADLINE_S", 240)):
            f = pathlib.Path(tmp) / "Solution.lean"
            f.write_text(body.source)
            p = passport.run(f, t, cases=1000, seed=0)
    write_json(PASSPORTS / f"{p['passport_sha256']}.json", p)
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


def built_project(t, src):
    """Build the task's executable from one candidate file once; cached by source hash."""
    sha = taskmod.sha256(src)
    d = BUILDS / f"{t.id}-{sha[:16]}"
    with _build_lock:
        if not (d / ".lake/build/bin" / t.exe).exists():
            shutil.rmtree(d, ignore_errors=True)
            ws = judge.load_workspace(str(src))
            tmp = judge.fresh_project(ws, judge.candidate_files(ws), t)
            r = binary_check.build(tmp, t)
            if r["exit_code"] != 0:
                raise HTTPException(500, "sidecar build failed")
            shutil.move(str(tmp), d)
    return d, sha


def passports_for(solution_sha):
    """Stored Passports whose candidate file has this hash, newest first."""
    out = []
    for f in sorted(PASSPORTS.glob("*.json"), key=lambda f: f.stat().st_mtime, reverse=True):
        p = json.loads(f.read_text())
        if solution_sha in p.get("solution", {}).get("files", {}).values():
            out.append({"passport_sha256": p["passport_sha256"], "status": p["status"],
                        "task": p["task"]["id"], "generated": p["generated"]})
    return out


@app.get("/api/passports")
def find_passports(solution_sha256: str):
    return passports_for(solution_sha256)


class PayoutRequest(BaseModel):
    build: str = "repaired"         # buggy | repaired
    state: dict
    request: dict


@app.post("/api/payout")
def payout(body: PayoutRequest, request: Request):
    if body.build not in BUILDS_ALLOWED:
        raise HTTPException(400, "build must be buggy or repaired")
    line = json.dumps({"state": body.state, "request": body.request})
    if len(line) > 20_000:
        raise HTTPException(413, "input too large")
    if not WARM.is_set():
        raise HTTPException(503, "the sidecar builds are warming up; retry shortly", headers={"Retry-After": "30"})
    CTRL.quota(request, "payout")
    t = taskmod.load()
    d, sha = built_project(t, t.root / BUILDS_ALLOWED[body.build])
    with tempfile.TemporaryDirectory(dir=d, prefix="in-") as tmp, \
            judge.time_limit(seconds("PF_PAYOUT_DEADLINE_S", 20)):
        name = pathlib.Path(tmp).name
        (d / name / "in.jsonl").write_text(line + "\n")
        r = judge.in_container(d, f".lake/build/bin/{t.exe} < {name}/in.jsonl")
    if judge.TIMEOUT_MARK in r["output_tail"]:
        raise HTTPException(504, "the sidecar did not answer within its time limit")
    out = r["output_tail"].strip().splitlines()
    if not out:
        raise HTTPException(500, "sidecar produced no output")
    res = json.loads(out[-1])
    exe = d / ".lake/build/bin" / t.exe
    found = passports_for(sha)
    return {"build": body.build, "solution_sha256": sha, "executable_sha256": taskmod.sha256(exe),
            "passport_sha256": found[0]["passport_sha256"] if found else None,
            "result": res, "elapsed_ms": r["elapsed_ms"]}


# Live challenge: a hidden flagship variant. A witness comes from the binary check within
# the response contract; a repair, if requested, continues as a background job.

HIDDEN = ROOT / "hidden"


class ChallengeRequest(BaseModel):
    variant: str
    repair: bool = False


@app.get("/api/challenge/variants")
def challenge_variants():
    return sorted(p.name for p in HIDDEN.glob("*/task.json") for p in [p.parent])


@app.post("/api/challenge")
def challenge(body: ChallengeRequest, request: Request):
    d = HIDDEN / body.variant
    if ".." in body.variant or not (d / "task.json").exists():
        raise HTTPException(404, "no such variant")
    if not WARM.is_set():
        raise HTTPException(503, "the hidden variants are warming up; retry shortly", headers={"Retry-After": "30"})
    t = taskmod.Task(d)
    t0 = time.monotonic()
    with CTRL.challenges.hold():
        CTRL.quota(request, "challenge")
        with judge.time_limit(seconds("PF_CHALLENGE_DEADLINE_S", 45)):
            project, _ = built_project(t, t.start)
            b = binary_check.property_tests(project, t, 300, int(time.time()) % 1000, {})
    if b["status"] == "TIMEOUT":
        raise HTTPException(504, "no result within the challenge time limit; the result is unresolved")
    b["binary_sha256"] = (project / "binary.sha256").read_text().strip()
    out = {"variant": body.variant, "elapsed_ms": int((time.monotonic() - t0) * 1000),
           "status": "REFUTED" if b["status"] == "REFUTED" else "UNRESOLVED",
           "violations": b["violations"], "witness": b["witnesses"][0] if b["witnesses"] else None,
           "executable_sha256": b.get("binary_sha256"), "label": "Live"}
    if body.repair and mode() == "live":
        out["repair_job"] = start_job(t, ForgeRequest(task=t.id, mode="live"), request)["id"]
    return out


def prewarm():
    """Build the payout sidecars and every hidden variant once, so first requests are warm."""
    t = taskmod.load()
    for rel in BUILDS_ALLOWED.values():
        try:
            built_project(t, t.root / rel)
        except HTTPException:
            pass
    for d in sorted(HIDDEN.glob("*/task.json")):
        ht = taskmod.Task(d.parent)
        try:
            built_project(ht, ht.start)
        except HTTPException:
            pass


def warm():
    try:
        prewarm()
    finally:
        WARM.set()


if os.environ.get("PF_PREWARM", "1") == "1":
    threading.Thread(target=warm, daemon=True).start()
else:
    WARM.set()


# Operator controls

class ModeRequest(BaseModel):
    mode: str                       # live | replay
    stop_live: bool = False         # also kill running live jobs


@app.get("/api/admin/state")
def admin_state(request: Request):
    CTRL.admin(request)
    return {**CTRL.state(), "live_jobs": sorted(LIVE)}


@app.post("/api/admin/mode")
def admin_mode(body: ModeRequest, request: Request):
    """Kill switch: replay mode refuses new live jobs at once and survives restarts."""
    CTRL.admin(request)
    if body.mode not in ("live", "replay"):
        raise HTTPException(400, "mode must be live or replay")
    CTRL.store.put("mode", body.mode)
    stopped = []
    if body.stop_live:
        for job_id, proc in list(LIVE.items()):
            set_job(JOBS / job_id, stopped=True)
            stop_process(proc)
            stopped.append(job_id)
    return {**CTRL.state(), "stopped": stopped}


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
