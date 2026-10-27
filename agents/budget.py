"""Per-task budget for E1 arms: a dollar cap over all model calls and a wall-clock cap
that includes Lean checking and tool time.

Budget dollars are computed at standard-tier list prices for every model, including
calls served by Contributor tiers, so that arms are compared on the same scale.
Actual spend (at the tier actually used) is tracked separately.
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

    def charge(self, model, usage):
        usage = usage or {}
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
        return {"usd_cap": self.usd_cap, "wall_cap_s": self.wall_cap, "stop": self.stop,
                "usd_list": round(self.usd_list, 4), "usd_actual": round(self.usd_actual, 4),
                "elapsed_s": round(self.elapsed(), 1),
                "by_model": {k: {**v, "usd_list": round(v["usd_list"], 4), "usd_actual": round(v["usd_actual"], 4)}
                             for k, v in self.by_model.items()}}
