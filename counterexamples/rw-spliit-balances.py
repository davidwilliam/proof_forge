"""Counterexample adapter for rw-spliit-balances: it shares the allocation specification of
rw-moneyphp-allocate, so this loads `rw-moneyphp-allocate.py`."""
import importlib.util, pathlib

_spec = importlib.util.spec_from_file_location("cex_allocation", pathlib.Path(__file__).with_name("rw-moneyphp-allocate.py"))
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)
instance = _mod.instance
