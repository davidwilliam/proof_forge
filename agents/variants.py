"""Parallel short variants for a goal that stays open after its first dialog.

When the first obligation dialog on a goal (a required theorem, a planner lemma, a skeleton helper)
ends without proving it, K short dialogs (`--variants K`, `--variant-turns T`) run at the same
time, each in its own copy of the session workspace and each with a different framing of the same
goal: a different route with the first attempt's failure notes, a decomposition into small helper
lemmas, library theorems ranked below the ones the first dialog saw (or, without the library, case
splitting on the definitions), unfolding and case splitting. The first variant whose candidate
proves the goal (its own proof free of `sorry` and compiling, as in prove_target) wins: the others
are told to stop, the winner's candidate is installed in the session and kept only if it compiles
there. The other variants stop at their next turn or tool call; a model request already sent is
not abandoned, its reply is discarded and its tokens are charged.

Budget: every variant calls the model through Session.call on the run's one Budget (thread safe),
so each request is charged its worst case before it is sent and settled from the reported usage at
list price, exactly as a sequential turn; requests in flight at the same time are all charged
before they are sent, so the dollar cap holds. Lean runs of the variants go through the host's
container slots like any other. A0 never runs variants (agents/baseline.py has no obligation
dialogs).
"""
import copy, pathlib, re, shutil, subprocess, sys, tempfile, threading, time

from budget import BudgetExceeded, list_cost  # noqa: E402

TURNS = 2
DEFAULT_K = 2

FRAMINGS = [
    ("retry", "Take a different route from the first attempt (its end is quoted above): do not repeat a step "
              "that failed there."),
    ("decompose", "Split the proof: first state and prove, each with its own try_snippet, one to three small "
                  "helper lemmas that isolate the hard step (one case, one inequality, one unfolding), then prove "
                  "the target from them."),
    ("library", "Look for a library theorem that does the hard step (the declarations listed above rank below "
                "the ones the first attempt was shown; search_library finds more), apply it and prove its "
                "hypotheses."),
    ("cases", "Unfold every definition the statement names, split on every `if` and `match` (split, by_cases, "
              "cases) and close each branch with simp, omega or grind; if one branch does not close, say which."),
]


def settings(a):
    """(K, turns): K = 0 means off."""
    k = getattr(a, "variants", 0) or 0
    return max(0, int(k)), max(1, int(getattr(a, "variant_turns", TURNS) or TURNS))


def framings(s, k):
    """The K framings of a session: without the library the library framing is skipped."""
    fs = [f for f in FRAMINGS if f[0] != "library" or s.library]
    return [fs[i % len(fs)] for i in range(k)]


def clone_tree(src, dst):
    """Copy a workspace (copy-on-write clones where the file system has them)."""
    if sys.platform == "darwin":
        r = subprocess.run(["cp", "-cR", str(src), str(dst)], capture_output=True)
    else:
        r = subprocess.run(["cp", "-a", "--reflink=auto", str(src), str(dst)], capture_output=True)
    if r.returncode != 0:
        shutil.rmtree(dst, ignore_errors=True)
        shutil.copytree(src, dst, symlinks=True)


def fork(s, tag):
    """A session for one variant: its own workspace copy and output directory, the run's budget,
    its events forwarded to the run's log with `variant` set."""
    v = copy.copy(s)
    base = pathlib.Path(tempfile.mkdtemp(prefix="pf-variant-"))
    v.ws = base / "ws"
    clone_tree(s.ws, v.ws)
    v.out = s.out / "variants" / tag
    v.out.mkdir(parents=True, exist_ok=True)
    v.version = 0
    v.events = []
    v.accepted = False
    v.targets = set(s.targets)
    v.refuted = dict(s.refuted)
    v.notes = dict(s.notes)
    v.compiled = {}
    v.portfolio_seen = set(getattr(s, "portfolio_seen", set()))
    v.extra_tools = set()
    v.goal_tool = False          # the persistent Lean session belongs to the main session
    v.__dict__.pop("lean_server", None)
    v.refute_samples = 0
    v.variants_k = 0
    v.log = lambda **kw: s.log(variant=tag, **kw)
    v._variant_base = base
    return v


def prompt(s, spec, t, framing, plan_text=""):
    import ledger, repair
    src = s._source()
    m = re.search(rf"theorem\s+{re.escape(t)}\b[^\n]*(?:\n(?!theorem|lemma|def|end )[^\n]*)*", src)
    stmt = (m.group(0).split(":= by")[0].split(":= sorry")[0] if m else t).strip()
    key, text = framing
    hints = ""
    if key == "library" and s.library and s.lib_index:
        hits = [e for e in s.lib_index.search(repair.obligation_query(s, stmt), limit=30) if e["kind"] != "module"][8:16]
        hints = repair.fin_lib.render(hits, sig_chars=300) if hits else ""
    notes = repair.notes_text(s, t)
    prior = ledger.prompt_notes(getattr(s, "prior_notes", {}) or {}, t)
    defs = ", ".join(f"`{d}`" for d in s.task.definitions)
    return (f"{spec}\n\n=== candidate/Solution.lean (current) ===\n{repair.compact_view(s, src, keep={t})}\n\n"
            + (f"Proof plan from the architect:\n{plan_text}\n\n" if plan_text else "")
            + (f"The first attempt at this goal ended like this:\n{notes}\n\n" if notes else "")
            + (f"{prior}\n\n" if prior else "")
            + (f"ProofForgeFin declarations:\n{hints}\n\n" if hints else "")
            + f"Your task now: prove `{stmt}`, in at most a few turns. {text} Develop the proof with try_snippet; a "
            f"clean snippet that proves `{t}` replaces its sorry automatically. Do not change {defs} or anything "
            "already proved. You may use the other helper lemmas in the file even if they are still sorry.")


def proved(v, t):
    """The variant's goal is done as in prove_target: its own proof has no sorry and compiles."""
    import repair
    text = repair.decl_text(v, t)
    return bool(text) and "sorry" not in text and v.check_status([t]).get(t) != "ERROR"


def run(s, a, system, spec, t, label, plan_text=""):
    """Run the variants for goal `t`; returns True when a winner's candidate is installed."""
    import repair
    k, turns = settings(a)
    if k <= 0 or s.budget.past_deadline():
        return False
    done_goals = s.__dict__.setdefault("variant_goals", set())
    if t in done_goals:
        return False
    done_goals.add(t)
    fs = framings(s, k)
    base_src = s._source()
    stop = threading.Event()
    lock = threading.Lock()
    finished = threading.Condition(lock)
    state = {"winner": None, "running": len(fs)}
    stats = s.__dict__.setdefault("variant_stats", {"goals": 0, "won": 0, "variants": 0, "turns": 0, "usd_list": 0.0,
                                                     "won_turns": 0, "won_usd_list": 0.0, "lost_turns": 0,
                                                     "lost_usd_list": 0.0})
    stats["goals"] += 1
    stats["variants"] += len(fs)
    per = [{"framing": f[0], "turns": 0, "usd_list": 0.0, "ok": False, "error": None} for f in fs]
    t0 = time.monotonic()
    tools = {"try_snippet", "replace_declaration", "read_file"} | repair.lib_tools(s)
    threads, forks = [], []

    def work(i, v):
        rec = per[i]
        orig = v.call

        def call(model, messages, purpose, **kw):
            r, u = orig(model, messages, purpose, **kw)
            c = list_cost(model, u or {})
            with lock:
                rec["turns"] += 1
                rec["usd_list"] += c
                stats["turns"] += 1
                stats["usd_list"] += c
            return r, u
        v.call = call
        ok = False
        try:
            ok, _ = repair.dialog(v, a.model, a.effort, system, prompt(v, spec, t, fs[i], plan_text), tools, turns,
                                  lambda: stop.is_set() or proved(v, t), f"v{i}-{fs[i][0]}:{t}", stop=stop)
            ok = ok and not stop.is_set() and proved(v, t)
        except BudgetExceeded as e:
            rec["error"] = f"budget: {e}"
        except Exception as e:   # one variant failing does not stop the others or the run
            rec["error"] = f"{type(e).__name__}: {e}"[:300]
        with lock:
            rec["ok"] = ok
            if ok and state["winner"] is None:
                state["winner"] = i
                stop.set()
            state["running"] -= 1
            finished.notify_all()
        s.log(kind="variant_end", goal=t, index=i, framing=fs[i][0], ok=ok, turns=rec["turns"],
              usd_list=round(rec["usd_list"], 4), error=rec["error"], won=state["winner"] == i)
        if state["winner"] != i:
            shutil.rmtree(v._variant_base, ignore_errors=True)

    s.log(kind="variants", goal=t, label=label, k=len(fs), turns=turns, framings=[f[0] for f in fs])
    for i in range(len(fs)):
        v = fork(s, f"{t}-{i}")
        forks.append(v)
        th = threading.Thread(target=work, args=(i, v), daemon=True)
        threads.append(th)
    s.__dict__.setdefault("variant_threads", []).extend(threads)
    for th in threads:
        th.start()
    with lock:
        while state["winner"] is None and state["running"] > 0:
            left = s.budget.remaining_wall()
            if left is not None and left <= 0:
                stop.set()
                break
            finished.wait(timeout=5 if left is None else max(0.1, min(5, left)))
    win = state["winner"]
    ok = False
    if win is not None:
        v = forks[win]
        wsrc = v._source()
        if s._source() == base_src and wsrc != base_src:
            s._save(wsrc, f"variant {fs[win][0]} {t}")
            if "error:" in s.compile(2000)["output_tail"]:
                s._save(base_src, f"revert variant {t}")
            else:
                s.targets |= v.targets
                ok = repair.own_sorry_free(s, t)
        shutil.rmtree(v._variant_base, ignore_errors=True)
    with lock:
        if ok:
            stats["won"] += 1
            stats["won_turns"] += sum(p["turns"] for p in per)
            stats["won_usd_list"] += sum(p["usd_list"] for p in per)
        else:
            stats["lost_turns"] += sum(p["turns"] for p in per)
            stats["lost_usd_list"] += sum(p["usd_list"] for p in per)
    s.log(kind="variants_result", goal=t, ok=ok, winner=None if win is None else fs[win][0],
          ms=int((time.monotonic() - t0) * 1000),
          variants=[{k2: (round(v2, 4) if isinstance(v2, float) else v2) for k2, v2 in p.items()} for p in per])
    return ok


def join(s, timeout=None):
    """Wait for variant threads still finishing a request (their charges settle)."""
    for th in s.__dict__.get("variant_threads", []):
        left = s.budget.remaining_wall()
        th.join(timeout if timeout is not None else (None if left is None else max(1.0, left + 60)))


def summary(s, a=None):
    k, turns = settings(a) if a is not None else (getattr(s, "variants_k", 0), TURNS)
    rec = {"k": k, "turns": turns}
    st = s.__dict__.get("variant_stats")
    if st:
        rec.update({kk: (round(vv, 4) if isinstance(vv, float) else vv) for kk, vv in st.items()})
    return rec
