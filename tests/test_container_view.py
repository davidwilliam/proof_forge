"""The container's view of a workspace (harness/judge.py, view_check and output_name).

Docker Desktop's VM can serve a file the host rewrote with its previous size, so Lean compiled a
truncated Scratch.lean or Solution.lean (`unexpected end of input` before the end of the file),
and can keep the entry of a file the host deleted, so `lean ... > .deps.txt` failed with "No such
file or directory". judge.in_container now starts the script only once the container sees the
host's version of every input file, and outputs the host reads get names no run used before.

Without Docker: the manifest lists the input files only, output names are new each time.
With Docker (the pinned image): a container that sees a truncated input does not run the script
and a new one runs it once the view is right; a view that stays wrong raises StaleView; a
consistent view runs the script once and keeps its exit code.

Run: python3 tests/test_container_view.py [--quick]   (--quick skips the Docker runs)
"""
import pathlib, subprocess, sys, tempfile, time
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / "harness")]
import judge  # noqa: E402

FULL = "theorem t : True := by\n  trivial\n\ntheorem u : 1 + 1 = 2 := by\n  rfl\n"


def project():
    d = pathlib.Path(tempfile.mkdtemp(prefix="pf-view-test-"))
    (d / "candidate").mkdir()
    (d / "candidate/Solution.lean").write_text(FULL)
    (d / "lakefile.toml").write_text('name = "t"\n')
    (d / ".lake/build").mkdir(parents=True)
    (d / ".lake/build/Solution.olean").write_bytes(b"\0" * 10)
    (d / judge.output_name("deps")).write_text("output of an earlier run\n")
    return d


def test_manifest_lists_input_files_only():
    d = project()
    m = dict(judge.view_manifest(d))
    assert sorted(m) == ["candidate/Solution.lean", "lakefile.toml"], m
    assert m["candidate/Solution.lean"] == judge.sha256_bytes(FULL.encode())


def test_output_names_are_never_reused():
    names = {judge.output_name("deps") for _ in range(1000)}
    assert len(names) == 1000 and all(n.startswith(".deps-") and n.endswith(".txt") for n in names)


def test_truncated_view_waits_for_the_hosts_version():
    """The recorded failure: the container reads Solution.lean cut at an earlier size. The host's
    manifest is the full file while the container sees the cut one, until the pause before the
    next container. The script runs once, on the full file."""
    d = project()
    sol = d / "candidate/Solution.lean"
    manifest = judge.view_manifest(d)
    sol.write_text(FULL[:30])
    pauses, sleep = [], time.sleep

    def pause(seconds):
        if seconds == 0.2:   # waiting for a container slot
            return sleep(seconds)
        pauses.append(seconds)
        sol.write_text(FULL)
    with patch.object(judge, "view_manifest", return_value=manifest), patch.object(judge.time, "sleep", pause):
        r = judge.in_container(d, "echo ran >> .runs; cat candidate/Solution.lean", timeout=120)
    assert r["exit_code"] == 0, r
    assert r["output_tail"].strip() == FULL.strip(), r["output_tail"]
    assert (d / ".runs").read_text() == "ran\n"
    assert pauses == [0.5] and r["view_wait_s"] == 0.5, (pauses, r)


def test_view_that_stays_wrong_is_an_error():
    d = project()
    manifest = judge.view_manifest(d)
    (d / "candidate/Solution.lean").write_text(FULL[:30])
    with patch.object(judge, "view_manifest", return_value=manifest), patch.object(judge, "VIEW_WAIT", 1.0):
        try:
            judge.in_container(d, "echo ran >> .runs", timeout=120)
        except judge.StaleView as e:
            assert "candidate/Solution.lean" in str(e), e
        else:
            raise AssertionError("a view that stays wrong was not reported")
    assert not (d / ".runs").exists()


def test_consistent_view_runs_the_script_once_with_its_exit_code():
    d = project()
    r = judge.in_container(d, "echo ran >> .runs; wc -c < candidate/Solution.lean; exit 3", timeout=120)
    assert r["exit_code"] == 3 and r["output_tail"].strip() == str(len(FULL.encode())), r
    assert "view_wait_s" not in r and (d / ".runs").read_text() == "ran\n"


DOCKER = {"test_truncated_view_waits_for_the_hosts_version", "test_view_that_stays_wrong_is_an_error",
          "test_consistent_view_runs_the_script_once_with_its_exit_code"}


def have_docker():
    return (not judge.IN_IMAGE and
            subprocess.run(["docker", "image", "inspect", judge.IMAGE], capture_output=True).returncode == 0)


if __name__ == "__main__":
    docker = "--quick" not in sys.argv and have_docker()
    for name, fn in list(globals().items()):
        if not name.startswith("test_"):
            continue
        if name in DOCKER and not docker:
            print(f"skip {name}")
            continue
        fn()
        print(f"ok  {name}")
