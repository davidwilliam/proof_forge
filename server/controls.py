"""Admission, quotas, spending and the kill switch for the public API.

State that must survive a restart (daily quotas, the live spending ledger, the operating
mode) is kept in SQLite under PF_DATA (default runs/). Concurrency limits are per process.

Environment (defaults in parentheses):
  PF_DATA                 directory for server.db (runs/)
  PF_CLIENT_IP_HEADER     header carrying the client address set by the host's proxy, for
                          example fly-client-ip or x-forwarded-for (unset: socket peer)
  PF_ADMIN_KEY            secret for /api/admin/*; unset disables the admin endpoints
  PF_JUDGE_KEY            requests with X-Judge-Key get the judge quotas
  PF_QUOTA_<KIND>         per-client daily quota for live, replay, verify, challenge, payout
                          (2, 30, 20, 40, 300); judge quotas are PF_JUDGE_QUOTA_<KIND>
                          (30, 300, 200, 400, 3000)
  PF_DAILY_LIVE_USD       live spending per UTC day at list prices, all clients (30)
  PF_MAX_JOBS             concurrent jobs of any mode (6)
  PF_MAX_LIVE             concurrent live jobs (1)
  PF_CHECK_SLOTS          concurrent fresh checks: verify requests and job final checks (2)
  PF_CHALLENGE_SLOTS      concurrent challenge requests (2)
"""
import contextlib, os, pathlib, sqlite3, threading, time

from fastapi import HTTPException, Request

ROOT = pathlib.Path(__file__).resolve().parent.parent
QUOTA = {"live": 2, "replay": 30, "verify": 20, "challenge": 40, "payout": 300}
JUDGE_QUOTA = {"live": 30, "replay": 300, "verify": 200, "challenge": 400, "payout": 3000}


def env_int(name, default):
    return int(os.environ.get(name, str(default)))


def day():
    return time.strftime("%Y-%m-%d", time.gmtime())


class Store:
    """Daily quotas, the live spending ledger and the operating mode, in one SQLite file."""

    def __init__(self, path=None):
        self.path = pathlib.Path(path or pathlib.Path(os.environ.get("PF_DATA", ROOT / "runs")) / "server.db")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.lock = threading.Lock()
        with self.db() as c:
            c.execute("PRAGMA journal_mode=WAL")
            c.execute("CREATE TABLE IF NOT EXISTS quota (who TEXT, day TEXT, kind TEXT, n INTEGER, "
                      "PRIMARY KEY (who, day, kind))")
            c.execute("CREATE TABLE IF NOT EXISTS spend (job TEXT PRIMARY KEY, day TEXT, "
                      "reserved REAL, settled REAL)")
            c.execute("CREATE TABLE IF NOT EXISTS setting (key TEXT PRIMARY KEY, value TEXT)")

    @contextlib.contextmanager
    def db(self):
        c = sqlite3.connect(self.path, timeout=10, isolation_level=None)
        try:
            yield c
        finally:
            c.close()

    def take(self, who, kind, limit):
        """Count one request against today's quota; False when the quota is used up."""
        with self.lock, self.db() as c:
            c.execute("BEGIN IMMEDIATE")
            row = c.execute("SELECT n FROM quota WHERE who=? AND day=? AND kind=?", (who, day(), kind)).fetchone()
            n = row[0] if row else 0
            if n >= limit:
                c.execute("ROLLBACK")
                return False
            c.execute("INSERT OR REPLACE INTO quota VALUES (?, ?, ?, ?)", (who, day(), kind, n + 1))
            c.execute("COMMIT")
            return True

    def used(self, who, kind):
        with self.db() as c:
            row = c.execute("SELECT n FROM quota WHERE who=? AND day=? AND kind=?", (who, day(), kind)).fetchone()
        return row[0] if row else 0

    def spent_today(self, c=None):
        """Live spending today: settled amounts, plus the full reservation of unsettled jobs."""
        def q(c):
            return c.execute("SELECT COALESCE(SUM(COALESCE(settled, reserved)), 0) FROM spend WHERE day=?",
                             (day(),)).fetchone()[0]
        if c is not None:
            return q(c)
        with self.db() as c:
            return q(c)

    def reserve(self, job, usd, cap):
        """Reserve a live job's full per-job cap against the daily cap; False if it does not fit."""
        with self.lock, self.db() as c:
            c.execute("BEGIN IMMEDIATE")
            if self.spent_today(c) + usd > cap + 1e-9:
                c.execute("ROLLBACK")
                return False
            c.execute("INSERT INTO spend VALUES (?, ?, ?, NULL)", (job, day(), usd))
            c.execute("COMMIT")
            return True

    def settle(self, job, usd):
        """Replace a reservation by the job's recorded spend. A job without a record keeps its
        full reservation, since its spend is unknown."""
        if usd is None:
            return
        with self.lock, self.db() as c:
            c.execute("UPDATE spend SET settled=? WHERE job=?", (float(usd), job))

    def get(self, key, default=None):
        with self.db() as c:
            row = c.execute("SELECT value FROM setting WHERE key=?", (key,)).fetchone()
        return row[0] if row else default

    def put(self, key, value):
        with self.lock, self.db() as c:
            c.execute("INSERT OR REPLACE INTO setting VALUES (?, ?)", (key, value))


class Gate:
    """Non-blocking concurrency limit; `hold` raises 503 when every slot is taken, or waits up
    to `wait` seconds first."""

    def __init__(self, name, slots):
        self.name, self.slots = name, slots
        self.sem = threading.BoundedSemaphore(slots)
        self.active = 0
        self.lock = threading.Lock()

    def acquire(self, wait=0.0):
        got = self.sem.acquire(timeout=wait) if wait > 0 else self.sem.acquire(blocking=False)
        if not got:
            raise HTTPException(503, f"{self.name} capacity in use; retry shortly",
                                headers={"Retry-After": "15"})
        with self.lock:
            self.active += 1

    def release(self):
        with self.lock:
            self.active -= 1
        self.sem.release()

    @contextlib.contextmanager
    def hold(self, wait=0.0):
        self.acquire(wait)
        try:
            yield
        finally:
            self.release()

    def state(self):
        return {"active": self.active, "slots": self.slots}


class Controls:
    def __init__(self, store=None):
        self.store = store or Store()
        self.jobs = Gate("job", env_int("PF_MAX_JOBS", 6))
        self.live = Gate("live job", env_int("PF_MAX_LIVE", 1))
        self.checks = Gate("check", env_int("PF_CHECK_SLOTS", 2))
        self.challenges = Gate("challenge", env_int("PF_CHALLENGE_SLOTS", 2))

    # Identity

    def is_judge(self, req: Request):
        key = os.environ.get("PF_JUDGE_KEY")
        return bool(key) and req.headers.get("x-judge-key") == key

    def client(self, req: Request):
        if self.is_judge(req):
            return "judge"
        header = os.environ.get("PF_CLIENT_IP_HEADER")
        if header and req.headers.get(header):
            return req.headers[header].split(",")[0].strip()
        return req.client.host if req.client else "unknown"

    def quota(self, req: Request, kind):
        judge = self.is_judge(req)
        limit = env_int(f"PF_JUDGE_QUOTA_{kind.upper()}" if judge else f"PF_QUOTA_{kind.upper()}",
                        (JUDGE_QUOTA if judge else QUOTA)[kind])
        if not self.store.take(self.client(req), kind, limit):
            raise HTTPException(429, f"daily {kind} quota reached ({limit}); replay mode is available")

    # Mode and spending

    def mode(self):
        """Operating mode: the stored setting (set through the admin endpoint) overrides PF_MODE."""
        return self.store.get("mode") or os.environ.get("PF_MODE", "live")

    def daily_cap(self):
        return float(os.environ.get("PF_DAILY_LIVE_USD", "30"))

    def reserve_live(self, job, usd):
        if not self.store.reserve(job, usd, self.daily_cap()):
            raise HTTPException(503, "today's live spending limit is reached; replay mode is available")

    def admin(self, req: Request):
        key = os.environ.get("PF_ADMIN_KEY")
        if not key or req.headers.get("x-admin-key") != key:
            raise HTTPException(403, "admin key required")

    def state(self):
        return {"mode": self.mode(), "live_spent_today_usd": round(self.store.spent_today(), 4),
                "daily_live_cap_usd": self.daily_cap(),
                "gates": {g.name: g.state() for g in (self.jobs, self.live, self.checks, self.challenges)}}
