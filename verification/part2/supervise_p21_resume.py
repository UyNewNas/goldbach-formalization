#!/usr/bin/env python3
"""Bounded single-worker P2.1 feedback loop. Scheduling hints grant no proof credit."""
import argparse
import hashlib
import json
import os
from pathlib import Path
from functools import lru_cache
import signal
import subprocess
import sys
import time
import threading
from urllib.parse import urlsplit

ROOT = Path("/workspace/p2-1-20261125")
REPO = "UyNewNas/goldbach-formalization"
BASE_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
BASE = Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
BRANCH = "work/p2-1-formal-proof-20261125"
TARGETS = Path("docs/verification/20261125-p2-1/TARGETS.json")
PRIVATE = Path(".lake/p2-private")
LIB = PRIVATE / "lib"
AUDITS = PRIVATE / "audit"
RECORDS = PRIVATE / "records.json"
TOOLS = Path("verification/part2")
NORMAL = TOOLS / "run_winner9_private_checks.py"
AUDIT = TOOLS / "run_winner9_private_audit.py"
TEMPLATE = TOOLS / "winner9_private_audit_template.lean"
COMMON = [TOOLS / "winner9_external_snapshot.py", TOOLS / "inspect_winner9_owner_native.py", NORMAL]
BUCHSTAB = "ImbalancedChen.P5ZU1011AutomaticBuchstabIntervals"
ROOT_MODULES = {BUCHSTAB, "ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQueryAllBranches",
                "ImbalancedChen.P0RationalQueryPublicAPI", "ImbalancedChen.P2HistoricBackendTypeAdapters",
                "ImbalancedChen.P2OriginalCompactQ80Table"}


class BudgetExpired(Exception):
    pass


def say(*args):
    print(*args, flush=True)


def read(path):
    return json.loads(path.read_bytes()) if path.is_file() else {}


def sha(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


@lru_cache(maxsize=2048)
def file_digest(path, stamp):
    value = sha(path)
    if file_stamp(path) != stamp:
        raise ValueError("File changed during scheduling check: " + str(path))
    return value


def file_stamp(path):
    st = path.stat()
    return st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns


def tracked_sha(path):
    return file_digest(path, file_stamp(path))


def key(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def git(*args, **kw):
    return subprocess.check_output(["git", *args], text=True, timeout=18, **kw).strip()


def identity():
    if Path.cwd().resolve() != ROOT or Path(git("rev-parse", "--show-toplevel")).resolve() != ROOT:
        raise ValueError("Wrong private verification worktree")
    if git("symbolic-ref", "--quiet", "HEAD") != "refs/heads/" + BRANCH:
        raise ValueError("Expected the dedicated P2.1 branch")
    url = git("remote", "get-url", "origin")
    parsed = urlsplit(url)
    https = (parsed.scheme == "https" and parsed.hostname == "github.com" and parsed.port in (None, 443)
             and not parsed.query and not parsed.fragment and parsed.path.removesuffix(".git") == "/" + REPO)
    if not https and url not in {"git@github.com:" + REPO + ".git", "ssh://git@github.com/" + REPO + ".git"}:
        raise ValueError("Wrong GitHub repository origin")


def update():
    identity()
    if git("status", "--porcelain", "--untracked-files=no"):
        raise ValueError("Tracked worktree changes prevent fast-forward")
    try:
        git("fetch", "--quiet", "--no-tags", "origin", "refs/heads/" + BRANCH,
            env=dict(os.environ, GIT_TERMINAL_PROMPT="0"))
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError) as error:
        say("FETCH_RETRY", str(error)[:300])
        return None
    head, remote = git("rev-parse", "HEAD"), git("rev-parse", "FETCH_HEAD")
    if head != remote:
        git("merge-base", "--is-ancestor", head, remote)
        git("merge", "--ff-only", "--no-edit", remote)
        say("FAST_FORWARD", head, remote)
    return remote


def selection():
    doc = read(TARGETS)
    rows = {r["module"]: r for r in doc["modules"]}
    roots = [r["module"] for r in doc["roots"]]
    groups = [[n for n, r in rows.items() if (BUCHSTAB in r["used_by_roots"]) == extended]
              for extended in (False, True)]
    if len(doc["modules"]) != 140 or len(roots) != 5 or set(roots) != ROOT_MODULES or list(map(len, groups)) != [132, 8] or any(
            rows[n]["used_by_roots"] != [BUCHSTAB] for n in groups[1]):
        raise ValueError("Unexpected five-root partition")
    for n, r in rows.items():
        if r["source"] != n.replace(".", "/") + ".lean" or tracked_sha(Path(r["source"])) != r["source_sha256"]:
            raise ValueError("Published source differs from TARGETS: " + n)
    graph = {n: [d for d in r["direct_imports"] if d.startswith("ImbalancedChen.")] for n, r in rows.items()}
    closures = {}
    def closure(n):
        if n not in closures:
            closures[n] = {n}.union(*(closure(d) for d in graph[n]))
        return closures[n]
    for n in rows:
        closure(n)
    if [set(g) for g in groups] != [set.union(*(closures[n] for n in roots if n != BUCHSTAB)), closures[BUCHSTAB]]:
        raise ValueError("Published roots and transitive project partition disagree")
    scope = key([doc["roots"], {n: [r["used_by_roots"], r["direct_imports"]] for n, r in rows.items()}])
    tools = {str(p): tracked_sha(p) for p in [*COMMON, AUDIT, TEMPLATE]}
    generation = key([scope, tools, {n: r["source_sha256"] for n, r in rows.items()}])
    return groups, roots, closures, generation


class Failures:
    def __init__(self):
        self.stamps = {}
        self.printed = set()

    def tail(self, name, kind, log):
        if not log:
            return
        p = Path(log).resolve()
        if not p.is_relative_to(PRIVATE.resolve()) or not p.is_file():
            return
        with p.open("rb") as f:
            f.seek(max(0, p.stat().st_size - 16384))
            lines = [line[:480] for line in f.read().decode(errors="replace").splitlines()
                     if not line.startswith("P0_QUEUE_")]
        say("FAIL_LOG", name, kind, str(p), "\n" + "\n".join(lines[-7:]))

    def poll(self, names):
        paths = [RECORDS, *(AUDITS / n / "latest.json" for n in names)]
        for path in paths:
            if not path.is_file():
                continue
            st = path.stat()
            stamp = st.st_ino, st.st_size, st.st_mtime_ns
            if self.stamps.get(path) == stamp:
                continue
            data = read(path)  # Both strict drivers publish these files by atomic replace.
            self.stamps[path] = stamp
            if path == RECORDS:
                for n in names:
                    r = data.get(n, {})
                    ident = (n, "compile", key(r))
                    attempt = (r.get("attempts") or [{}])[-1]
                    provisional = r.get("external_check", {}).get("status") == "PENDING_BATCH_POSTCHECK"
                    actual_code = attempt.get("exit_code") if provisional else r.get("exit_code")
                    if actual_code not in (None, 0) and ident not in self.printed:
                        self.printed.add(ident)
                        say("FAIL_RECEIPT", n, "compile", actual_code, "registry", r.get("exit_code"))
                        self.tail(n, "compile", attempt.get("log") or r.get("log"))
            elif data.get("error"):
                n = path.parent.name
                ident = (n, "audit", data.get("input_sha256"), data["error"],
                         data.get("audit", {}).get("log"), data.get("replay", {}).get("log"))
                if ident not in self.printed:
                    self.printed.add(ident)
                    say("FAIL_RECEIPT", n, str(data["error"])[:600])
                    for stage in ("audit", "replay"):
                        self.tail(n, stage, data.get(stage, {}).get("log"))


def snapshots():
    if BASE.resolve(strict=True) != BASE or tracked_sha(BASE) != BASE_SHA:
        raise ValueError("Wrong authorized 515-provider snapshot")
    if PRIVATE.resolve() != ROOT / PRIVATE:
        raise ValueError("Unexpected private cache location")
    parent = PRIVATE.resolve() / "p21-buchstab-native" / BASE_SHA / tracked_sha(TOOLS / "extend_p21_buchstab_native_snapshot.py")
    path, marker = parent / "EXTERNAL_SNAPSHOT.json", parent / "QUALIFICATION.json"
    if not marker.is_file():
        return [BASE, None]
    q = read(marker)
    if (not path.is_file() or path.resolve() != path or marker.resolve() != marker or
        q.get("status") != "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED" or q.get("parent_sha256") != BASE_SHA or
        q.get("snapshot_sha256") != tracked_sha(path) or q.get("verified_snapshot") != str(path) or
        q.get("compile_credit") is not False or q.get("kernel_credit") is not False or len(read(path)["modules"]) != 518):
        raise ValueError("Invalid controlled Buchstab snapshot")
    return [BASE, path]


def identical_failures(snap, names):
    """A fresh process imports the current git revision's unmodified strict verifier."""
    sys.path.insert(0, str(TOOLS.resolve()))
    import run_winner9_private_audit as audit
    from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes
    ext = ExternalSnapshot(snap, lean=audit.LEAN, mathlib_pin=audit.PIN, project_lib=LIB)
    pin = git("-C", audit.MATHLIB, "rev-parse", "HEAD")
    if pin != audit.PIN:
        raise ValueError("Mathlib pin changed")
    toolchain = {"lean_version": subprocess.check_output([audit.LEAN, "--version"], text=True).strip(),
                 "lean_binary_sha256": tracked_sha(Path(audit.LEAN)), "mathlib_commit": pin}
    matches, records = [], read(RECORDS)
    for n in names:
        r = read(AUDITS / n / "latest.json")
        if r.get("accepted") is not False or r.get("module") != n or not r.get("error"):
            continue
        nodes = audit.project_nodes(ROOT, n)
        mark_project_nodes(nodes, set(ext.modules))
        frozen = audit.snapshot(ROOT, LIB.resolve(), nodes, toolchain, ext)
        if (r.get("input_snapshot") != frozen or r.get("input_sha256") != audit.json_digest(frozen) or
            r.get("source_sha256") != frozen["project"][n]["source_sha256"] or
            r.get("object_sha256") != frozen["project"][n]["object_sha256"] or
            r.get("replay_binding") != audit.replay_context(frozen) or
            r.get("compile_closure_signature") != records.get(n, {}).get("closure_signature")):
            continue
        audit.verify_compilation(records, nodes, frozen)
        replay = r.get("replay", {})
        for stage, result, argv in (("replay", replay, [audit.LEANCHECKER, "--verbose", n]),
                                    ("audit", r.get("audit", {}), None)):
            if not (isinstance(result.get("exit_code"), int) and result["exit_code"] != 0
                    and result.get("inputs_unchanged") is True):
                continue
            if stage == "audit":
                src = result.get("source", "")
                src_path = (ROOT / src).resolve()
                replay_log = (ROOT / replay.get("log", "")).resolve()
                if (replay.get("command") != [audit.LEANCHECKER, "--verbose", n] or
                    not replay_log.is_relative_to((AUDITS / n).resolve()) or not replay_log.is_file() or
                    tracked_sha(replay_log) != replay.get("log_sha256") or
                    not src_path.is_relative_to((AUDITS / n).resolve()) or not src_path.is_file()
                    or result.get("source_sha256") != tracked_sha(src_path)
                    or src_path.read_bytes() != audit.TEMPLATE.read_text().replace(audit.TEMPLATE_TARGET, n).encode()
                    or replay.get("exit_code") != 0 or replay.get("inputs_unchanged") is not True):
                    continue
                argv = [audit.LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
                        "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", src]
            log = (ROOT / result.get("log", "")).resolve()
            if result.get("command") == argv and log.is_relative_to(AUDITS.resolve()) and log.is_file() and tracked_sha(log) == result.get("log_sha256"):
                matches.append(n)
                break
    ext.verify()
    print(json.dumps({"identical_failures": matches}), flush=True)


def run(argv, failures, names, deadline):
    if time.monotonic() >= deadline:
        raise BudgetExpired("supervisor budget")
    say("START", argv[1], len(argv))
    child = None
    summary, pending = {}, []
    completed = False
    try:
        # Latch asynchronous stops until Popen returns the process-group ID.
        # The exec'd child inherits no blocked signal mask.
        watched = (signal.SIGALRM, signal.SIGTERM)
        old = {sig: signal.getsignal(sig) for sig in watched}
        try:
            for sig in watched:
                signal.signal(sig, lambda signum, _: pending.append(signum))
            child = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                     errors="replace", start_new_session=True)
        finally:
            for sig, handler in old.items():
                signal.signal(sig, handler)
        if signal.SIGTERM in pending:
            raise SystemExit(143)
        if pending or time.monotonic() >= deadline:
            raise BudgetExpired("supervisor budget")

        def pump():
            for line in child.stdout:
                print(line, end="", flush=True)
                if line.startswith("{"):
                    try:
                        result = json.loads(line)
                    except ValueError:
                        continue
                    if isinstance(result, dict):
                        summary.clear()
                        summary.update(result)
        reader = threading.Thread(target=pump, daemon=True)
        reader.start()
        while child.poll() is None:
            try:
                child.wait(timeout=min(5, max(0.01, deadline-time.monotonic())))
            except subprocess.TimeoutExpired:
                pass
            failures.poll(names)
            if time.monotonic() >= deadline:
                raise BudgetExpired("supervisor budget")
        reader.join()
        completed = True
    finally:
        if child is not None:
            if not completed:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                child.wait()
            child.stdout.close()
    failures.poll(names)
    say("END", argv[1], child.returncode)
    return child.returncode, summary


def progress(targets, closure, result, code):
    reached = set.union(*(closure[n] for n in targets))
    if not {"failed_or_blocked", "pending", "roots", "exit_code", "total", "successful_closure", "complete"} <= result.keys():
        raise ValueError(f"Normal driver exit {code} without a complete progress summary; see driver output")
    failed, pending = set(result["failed_or_blocked"]), set(result["pending"])
    passed = reached - failed - pending
    if (result.get("roots") != targets or result.get("exit_code") != code or result.get("total") != len(reached)
        or not failed | pending <= reached or failed & pending or result.get("successful_closure") != len(passed)
        or bool(result.get("complete")) != (not failed and not pending)):
        raise ValueError("Normal driver returned inconsistent progress")
    return passed, failed, pending


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--budget-seconds", type=int, default=3300, choices=range(1, 3301), metavar="1..3300")
    parser.add_argument("--match", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("modules", nargs="*", help=argparse.SUPPRESS)
    args = parser.parse_args()
    deadline = time.monotonic() + args.budget_seconds
    signal.setitimer(signal.ITIMER_REAL, args.budget_seconds)
    identity()
    if args.match:
        if args.match not in snapshots():
            raise ValueError("Unapproved failure-comparison snapshot")
        identical_failures(args.match, args.modules)
        return
    failures = Failures()
    names = [r["module"] for r in read(TARGETS)["modules"]]
    failures.poll(names)
    snapshots()
    head, state, phases = None, None, {}
    while True:
        if time.monotonic() >= deadline:
            raise BudgetExpired("supervisor time budget")
        current = update()
        if current and head != current:
            head = current
            try:
                refreshed = selection()
                if state is None or refreshed[-1] != state[-1]:
                    phases.clear()
                state = refreshed
            except (KeyError, ValueError, OSError) as error:
                say("WAIT_FOR_CONSISTENT_TARGETS", current, str(error)[:300])
                state = None
        if not current or not state:
            time.sleep(20)
            continue
        groups, roots, closures, generation = state
        names = groups[0] + groups[1]
        snaps = snapshots()
        ready = []
        for index, (group, snap) in enumerate(zip(groups, snaps)):
            if snap is None:
                break
            sid = (generation, str(snap), tracked_sha(snap))
            if sid not in phases:
                targets = [n for n in roots if (n == BUCHSTAB) == bool(index)]
                phases[sid] = {"normal": targets, "compiled": set(), "audits": None, "passed": set()}
            phase = phases[sid]
            if phase["normal"]:
                targets = phase["normal"]
                budget = min(900, max(1, int(deadline-time.monotonic()-15)))
                argv = [sys.executable, str(NORMAL), *targets, "--workers", "1", "--threads", "1",
                        "--memory-mb", "11264", "--time-budget-seconds", str(budget), "--external-snapshot", str(snap)]
                code, result = run(argv, failures, names, deadline)
                passed, failed, pending = progress(targets, closures, result, code)
                phase["compiled"].update(passed)
                phase["normal"] = sorted(n for n in pending if not closures[n] & failed)
                say("NORMAL_PROGRESS", len(passed), len(failed), len(pending))
                break
            if phase["audits"] is None:
                candidates = sorted(phase["compiled"])
                failed_before = [n for n in candidates if read(AUDITS / n / "latest.json").get("error")]
                held = set()
                if failed_before:
                    argv = [sys.executable, str(Path(__file__).resolve()), "--match", str(snap), *failed_before]
                    code, result = run(argv, failures, names, deadline)
                    if code or "identical_failures" not in result:
                        raise ValueError("Cannot validate prior failure bindings")
                    held = set(result["identical_failures"])
                    if not held <= set(failed_before):
                        raise ValueError("Unrequested receipt matched")
                phase["audits"] = sorted(set(candidates) - held)
                say("HELD_IDENTICAL_FAILURES", sorted(held))
                break
            if phase["audits"]:
                batch = phase["audits"][:8]
                argv = [sys.executable, str(AUDIT), *batch, "--memory-mb", "11264", "--external-snapshot",
                        str(snap), "--summary-name", "p21-supervisor-observations.json"]
                code, result = run(argv, failures, names, deadline)
                rows = result.get("modules", {})
                accepted = sum(r.get("accepted") is True for r in rows.values())
                if (set(rows) != set(batch) or result.get("requested") != len(batch) or
                    result.get("accepted") != accepted or result.get("all_accepted") != (accepted == len(batch)) or
                    code != int(accepted != len(batch))):
                    raise ValueError(f"Audit driver exit {code} without a matching complete summary; see driver output")
                phase["passed"].update(n for n, r in rows.items() if r["accepted"] is True)
                del phase["audits"][:len(batch)]
                break
            ready.append(phase["passed"] == set(group) and phase["compiled"] == set(group))
        else:
            if ready == [True, True]:
                say("READY_FOR_EXPORT", "strict driver evidence is available for separate export")
                return
        if ready == [] and snaps[0] is not None:
            continue
        if len(ready) == sum(p is not None for p in snaps):
            time.sleep(20)


if __name__ == "__main__":
    def expired(*_):
        raise BudgetExpired("supervisor time budget")
    signal.signal(signal.SIGALRM, expired)
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    try:
        main()
    except BudgetExpired as error:
        say("OBSERVATION_END", str(error))
        sys.exit(2)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        say("SUPERVISOR_PRECONDITION_OR_DRIVER_FAILURE", str(error))
        sys.exit(1)
