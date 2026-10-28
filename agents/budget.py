"""Per-task budget for E1 arms: a dollar cap over all model calls and a wall-clock cap
that includes Lean checking and tool time.

Budget dollars are computed at standard-tier list prices for every model, including
calls served by Contributor tiers, so that arms are compared on the same scale.
Actual spend (at the tier actually used) is tracked separately.

The caps are hard limits for the work they bound:
  - every model call gets a max_tokens and a timeout such that its worst-case list cost
    (estimated prompt priced as uncached input, plus max_tokens of output) fits the dollars
    left and it ends by the deadline; a call that cannot fit is not made;
  - a call whose usage is not reported is charged its worst case;
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


class BudgetExceeded(Exception):
    pass


class Budget:
    def __init__(self, usd=None, wall_s=None):
        self.usd_cap, self.wall_cap = usd, wall_s
        self.t0 = time.monotonic()
        self.usd_list = self.usd_actual = 0.0
        self.by_model = {}
        self.stop = None
        self.unknown_usage = 0

    def remaining_wall(self):
        return None if self.wall_cap is None else self.wall_cap - self.elapsed()

    def deadline(self):
        """Monotonic deadline, or None."""
        return None if self.wall_cap is None else self.t0 + self.wall_cap

    def call_limits(self, model, prompt_chars, max_tokens, timeout, min_tokens=1024):
        """(max_tokens, timeout) for the next call so that its worst case fits the budget;
        raises BudgetExceeded when it cannot."""
        self.check()
        if self.wall_cap is not None:
            timeout = min(timeout, self.remaining_wall())
            if timeout < 10:
                self.stop = "wall"
                raise BudgetExceeded("wall")
        if self.usd_cap is not None:
            p, _, o = STANDARD[CONTRIBUTOR[model][1]] if model in CONTRIBUTOR else STANDARD[model]
            prompt_cost = (prompt_chars / 3.0) * p / 1e6   # about 3 characters per token, priced uncached
            left = self.usd_cap - self.usd_list - prompt_cost
            max_tokens = min(max_tokens, int(left / (o / 1e6)))
            if max_tokens < min_tokens:
                self.stop = "usd"
                raise BudgetExceeded("usd")
        return max_tokens, timeout

    def charge(self, model, usage, worst_case=None):
        """Record one call. `worst_case` = (prompt_chars, max_tokens) is charged when the
        response carries no usage."""
        usage = usage or {}
        if not usage.get("prompt_tokens") and not usage.get("completion_tokens") and worst_case:
            chars, mt = worst_case
            usage = {"prompt_tokens": int(chars / 3.0) + 1, "completion_tokens": mt, "usage_unknown": True}
            self.unknown_usage += 1
        m = self.by_model.setdefault(model, {"calls": 0, "prompt": 0, "cached": 0, "completion": 0,
                                             "usd_list": 0.0, "usd_actual": 0.0})
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
                "wall_overrun_s": round(max(0.0, el - self.wall_cap), 1) if self.wall_cap else 0.0,
                "by_model": {k: {**v, "usd_list": round(v["usd_list"], 4), "usd_actual": round(v["usd_actual"], 4)}
                             for k, v in self.by_model.items()}}
