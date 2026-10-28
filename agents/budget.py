"""Per-task budget for E1 arms: a dollar cap over all model calls and a wall-clock cap
that includes Lean checking and tool time.

Budget dollars are computed at standard-tier list prices for every model, including
calls served by Contributor tiers, so that arms are compared on the same scale.
Actual spend (at the tier actually used) is tracked separately.

The caps are hard limits for the work they bound:
  - every model attempt gets a max_tokens and a timeout such that its worst-case list cost
    (an upper bound on input tokens, all priced uncached, plus max_tokens of output) fits
    the dollars left and it ends by the deadline; an attempt that cannot fit is not made;
  - the worst case is charged before the attempt is sent and replaced by the reported
    usage only when a complete response arrives in time; lost, late or usage-less
    responses stay charged at the worst case;
  - a response completed after the deadline is discarded, and no tool runs after it;
  - every Lean tool run in the agent process is cut off at the deadline (judge.DEADLINE).
The candidate on disk at the deadline is the run's result. After the deadline the agent
only selects the newest compiling version it already produced (repair.finish); judging
of that candidate by the shared evaluator is outside the budget and identical for all arms.
"""
import time

# USD per 1M tokens: (input, cached input, output).
STANDARD = {
    "muse-spark-1.3": (1.25, 0.15, 4.25),
    "muse-spark-1.2": (1.25, 0.15, 4.25),
    "muse-spark-1.1": (1.25, 0.15, 4.25),
    "muse-wonder-1.0": (4.00, 0.20, 20.00),
}
CONTRIBUTOR = {
    "muse-spark-1.3-contributor": ((0.10, 0.002, 0.20), "muse-spark-1.3"),
    "muse-spark-1.2-contributor": ((0.10, 0.002, 0.20), "muse-spark-1.2"),
}


def cost(prices, usage):
    p, c, o = prices
    prompt = usage.get("prompt_tokens", 0)
    cached = (usage.get("prompt_tokens_details") or {}).get("cached_tokens", 0)
    return ((prompt - cached) * p + cached * c + usage.get("completion_tokens", 0) * o) / 1e6


def list_cost(model, usage):
    if model in CONTRIBUTOR:
        model = CONTRIBUTOR[model][1]
    return cost(STANDARD[model], usage)


def actual_cost(model, usage):
    if model in CONTRIBUTOR:
        return cost(CONTRIBUTOR[model][0], usage)
    return cost(STANDARD[model], usage)


PER_MESSAGE_TOKENS = 64
FIXED_TOKENS = 2048


def _list_prices(model):
    return STANDARD[CONTRIBUTOR[model][1]] if model in CONTRIBUTOR else STANDARD[model]


class BudgetExceeded(Exception):
    pass


class Budget:
    def __init__(self, usd=None, wall_s=None):
        self.usd_cap, self.wall_cap = usd, wall_s
        self.t0 = time.monotonic()
        self.usd_list = self.usd_actual = 0.0
        self.by_model = {}
        self.stop = None
        self.unknown_usage = 0        # settled calls whose response reported no usage
        self.lost_attempts = 0        # attempts whose response never arrived (worst case kept)
        self.bound_violations = 0     # reported input above the bound (should stay 0)
        self.reserved_open = 0

    def input_bound(self, prompt_bytes, n_messages):
        """Upper bound on input tokens. With a byte-level BPE tokenizer every token covers
        at least one byte of UTF-8 text, so the request's byte count bounds the text tokens;
        per-message and fixed overheads cover the chat template and special tokens."""
        return prompt_bytes + PER_MESSAGE_TOKENS * n_messages + FIXED_TOKENS

    def call_limits(self, model, prompt_bytes, n_messages, max_tokens, timeout, min_tokens=1024):
        """(max_tokens, timeout) for the next attempt so that its worst case, every input
        token uncached at list price plus max_tokens of output, fits the dollars left and it
        ends by the deadline; raises BudgetExceeded when it cannot."""
        self.check()
        if self.wall_cap is not None:
            timeout = min(timeout, self.remaining_wall())
            if timeout < 10:
                self.stop = "wall"
                raise BudgetExceeded("wall")
        if self.usd_cap is not None:
            p, _, o = _list_prices(model)
            prompt_cost = self.input_bound(prompt_bytes, n_messages) * p / 1e6
            left = self.usd_cap - self.usd_list - prompt_cost
            max_tokens = min(max_tokens, int(left / (o / 1e6)))
            if max_tokens < min_tokens:
                self.stop = "usd"
                raise BudgetExceeded("usd")
        return max_tokens, timeout

    def reserve(self, model, prompt_bytes, n_messages, max_tokens):
        """Charge an attempt's worst case before it is sent. settle() replaces it with the
        reported usage; an attempt that never settles (lost response, timeout) stays charged
        at its worst case."""
        worst = {"prompt_tokens": self.input_bound(prompt_bytes, n_messages), "completion_tokens": max_tokens}
        tok = {"model": model, "worst": worst, "list": list_cost(model, worst), "actual": actual_cost(model, worst)}
        self.usd_list += tok["list"]
        self.usd_actual += tok["actual"]
        self.reserved_open += 1
        return tok

    def settle(self, tok, usage):
        """Replace a reservation with the reported usage, or keep its worst case when the
        response carries no usage."""
        self.usd_list -= tok["list"]
        self.usd_actual -= tok["actual"]
        self.reserved_open -= 1
        if not usage or usage.get("http_error") or not (usage.get("prompt_tokens") or usage.get("completion_tokens")):
            self.unknown_usage += 1
            usage = tok["worst"]
        elif usage.get("prompt_tokens", 0) > tok["worst"]["prompt_tokens"]:
            self.bound_violations += 1   # reported input exceeded the bound; recorded, charged as reported
        self.charge(tok["model"], usage)

    def lost(self, tok):
        """An attempt whose response was not received: its worst case stays charged."""
        self.reserved_open -= 1
        self.lost_attempts += 1
        m = self._model(tok["model"])
        m["calls"] += 1
        m["usd_list"] += tok["list"]
        m["usd_actual"] += tok["actual"]

    def remaining_wall(self):
        return None if self.wall_cap is None else self.wall_cap - self.elapsed()

    def deadline(self):
        """Monotonic deadline, or None."""
        return None if self.wall_cap is None else self.t0 + self.wall_cap

    def past_deadline(self):
        return self.wall_cap is not None and self.elapsed() >= self.wall_cap

    def _model(self, model):
        return self.by_model.setdefault(model, {"calls": 0, "prompt": 0, "cached": 0, "completion": 0,
                                                "usd_list": 0.0, "usd_actual": 0.0})

    def charge(self, model, usage):
        """Record one settled call at its reported usage."""
        usage = usage or {}
        m = self._model(model)
        m["calls"] += 1
        m["prompt"] += usage.get("prompt_tokens", 0)
        m["cached"] += (usage.get("prompt_tokens_details") or {}).get("cached_tokens", 0)
        m["completion"] += usage.get("completion_tokens", 0)
        lc, ac = list_cost(model, usage), actual_cost(model, usage)
        m["usd_list"] += lc
        m["usd_actual"] += ac
        self.usd_list += lc
        self.usd_actual += ac

    def elapsed(self):
        return time.monotonic() - self.t0

    def check(self):
        """Raise BudgetExceeded once either cap is reached; called before every model call."""
        if self.stop is None:
            if self.usd_cap is not None and self.usd_list >= self.usd_cap:
                self.stop = "usd"
            elif self.wall_cap is not None and self.elapsed() >= self.wall_cap:
                self.stop = "wall"
        if self.stop:
            raise BudgetExceeded(self.stop)

    def summary(self):
        el = self.elapsed()
        return {"usd_cap": self.usd_cap, "wall_cap_s": self.wall_cap, "stop": self.stop,
                "usd_list": round(self.usd_list, 4), "usd_actual": round(self.usd_actual, 4),
                "elapsed_s": round(el, 1), "unknown_usage_calls": self.unknown_usage,
                "lost_attempts": self.lost_attempts, "input_bound_violations": self.bound_violations,
                "wall_overrun_s": round(max(0.0, el - self.wall_cap), 1) if self.wall_cap else 0.0,
                "by_model": {k: {**v, "usd_list": round(v["usd_list"], 4), "usd_actual": round(v["usd_actual"], 4)}
                             for k, v in self.by_model.items()}}
