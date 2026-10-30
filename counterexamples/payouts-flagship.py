"""Counterexample adapter for the payouts-flagship tasks: they share the specification of the
payout flagship in `formal/`, so this loads `payout-flagship.py`."""
import importlib.util, pathlib

_spec = importlib.util.spec_from_file_location("cex_payout_flagship", pathlib.Path(__file__).with_name("payout-flagship.py"))
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)
instance = _mod.instance
