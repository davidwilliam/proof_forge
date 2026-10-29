"""Task lookup by id: benchmark tasks, real-world tasks and the flagship; no Docker calls.

`bin/proofforge verify` loads a Passport's task by its id, so real-world task ids must resolve.
"""
import pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "harness"))
import task as taskmod  # noqa: E402


def test_ids_resolve_in_every_task_directory():
    assert taskmod.load("payout-flagship").root == ROOT / "formal"
    assert taskmod.load("queues-ring-b1").root == ROOT / "tasks" / "queues-ring-b1"
    assert taskmod.load("rw-gomoney-split").root == ROOT / "realworld" / "tasks" / "rw-gomoney-split"


def test_unknown_id_is_an_error():
    try:
        taskmod.load("no-such-task")
    except FileNotFoundError:
        return
    raise AssertionError("unknown task id resolved")
