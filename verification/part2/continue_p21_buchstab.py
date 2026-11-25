#!/usr/bin/env python3
"""Prepared continuation only; original strict drivers remain authoritative."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import uuid

BASE_HEAD = "95e6ce9a6ae8a150d87c2bacc46e3c95b0c264e5"
BASE_TARGETS = "5f670207b5725acbd52f6be6c8cc1e25174f5e1314d3ac07b5b9a346e630058e"
PINS = {
    "supervise_p21_resume.py": "4d38c8046cdc43d01b5d00d67d3c5bcd34244d581ab6fa6bde545724a7fb8ff7",
    "run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "winner9_private_audit_template.lean": "9b06e11c365836a2e118e91788947057e96249e2dcbbd7a46a7f4fa9d2c5d7eb",
    "winner9_external_snapshot.py": "a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
    "inspect_winner9_owner_native.py": "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
    "finalize_p21.py": "1d7eb859f5ff5a63a5de256a9adbe5dcc2fd0aeb298a558a2168dc560a5a8b7d",
    "extend_p21_buchstab_native_snapshot.py": "af9b5397ae5ade235a2875354d7d0f24f811719bb2c7201a84128c3fbac82bd6",
    "export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
    "check_p21_joint_imports.py": "d8a47b1ed3c8e7173b923967b7e12a46aee494b08be0bf7d24ee0f0197cbccc9",
    "repack_winner9_private_evidence.py": "bf20e2992d7f798b3bf5b00d054b56503796ff29822e1bb8ae03bff4b166cb5b",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


BASE_SUMMARY_NAME = "p21-bulk-515-9713a57ee3b64b0f98a9a89c37df83fa.json"
BASE_SUMMARY_SHA = "10f2104a43ab80f6418620127c53e3f405e6e69c5fd7568993af1f8532fa56b1"
SNAPSHOT_SHAS = [
    "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27",
    "c5cad817345114053f6ac64573fef64c35c3c773a0496bb5fca63986b71ffe53",
]


def accepted(summary, names):
    require(set(summary["modules"]) == set(names)
            and summary["requested"] == summary["accepted"] == len(names)
            and summary["all_accepted"] is True
            and all(row["accepted"] is True for row in summary["modules"].values()),
            "Incomplete original owned audit summary")


def check_target_delta(before, after, base):
    require(before["roots"] == after["roots"], "Root scopes or public targets changed")
    old = {r["module"]: r for r in before["modules"]}
    new = {r["module"]: r for r in after["modules"]}
    require(old.keys() == new.keys(), "Project membership changed")
    permitted = {"ImbalancedChen.P5ZU1011AutomaticBuchstabNodes",
                 "ImbalancedChen.P5ZU1011AutomaticBuchstabWidthStep"}
    changed = {name for name in old if old[name]["source_sha256"] != new[name]["source_sha256"]}
    require(changed == permitted and not permitted.intersection(base),
            "Expected only the Buchstab node index and width cast proof repairs")
    for name, row in old.items():
        expected = dict(row)
        if name in permitted:
            expected["source_sha256"] = new[name]["source_sha256"]
        require(expected == new[name], "Source, imports or scope changed outside authorized delta: " + name)
    for key in ("lean_toolchain", "mathlib_commit", "import_parser"):
        require(before[key] == after[key], "Changed verification context: " + key)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--targets-sha256", required=True)
    args = parser.parse_args()
    require(re.fullmatch("[0-9a-f]{40}", args.head) and re.fullmatch("[0-9a-f]{64}", args.targets_sha256),
            "Use the full published commit and TARGETS SHA-256")
    require(sys.flags.optimize == 0, "Python optimization must be disabled")
    root = Path("/workspace/p2-1-20261125")
    require(Path.cwd().resolve() == root, "Wrong dedicated worktree")
    tools = root / "verification/part2"

    def check_tools():
        for name, expected in PINS.items():
            require(digest(tools / name) == expected, "Changed original tool: " + name)

    check_tools()
    sys.path.insert(0, str(tools))
    import supervise_p21_resume as s

    head = s.update(expected=args.head, require_sparse=True)
    require(head == args.head, "Unexpected published head")
    check_tools()
    s.git("merge-base", "--is-ancestor", BASE_HEAD, head)
    old_manifest = subprocess.check_output(["git", "show", BASE_HEAD + ":" + str(s.TARGETS)])
    require(hashlib.sha256(old_manifest).hexdigest() == BASE_TARGETS, "Changed original TARGETS")
    require(digest(s.TARGETS) == args.targets_sha256, "Changed published TARGETS")
    groups, _, _, generation = s.selection()
    base, native = groups
    check_target_delta(json.loads(old_manifest), s.read(s.TARGETS), set(base))

    base_summary = s.AUDITS / BASE_SUMMARY_NAME
    raw = base_summary.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == BASE_SUMMARY_SHA, "Changed original 132-owner summary")
    summary = json.loads(raw)
    accepted(summary, base)
    rows = summary["modules"].values()
    require(sum(row["declarations"] for row in rows) == 18398
            and sum(row["reused"] is True for row in rows) == 119, "Original audit counts differ")
    snapshots = s.snapshots()
    require(all(snapshots), "Both qualified native snapshots are required")

    def stable():
        s.identity()
        check_tools()
        require(s.sparse_state() and s.git("rev-parse", "HEAD") == head
                and not s.git("status", "--porcelain", "--untracked-files=no"), "Changed worktree")
        require(digest(s.TARGETS) == args.targets_sha256 and s.selection()[-1] == generation,
                "Changed published source or selection")
        require(digest(base_summary) == BASE_SUMMARY_SHA, "Changed original 132-owner summary")
        require(s.snapshots() == snapshots and [digest(p) for p in snapshots] == SNAPSHOT_SHAS,
                "Changed qualified native snapshot")

    def no_export():
        require(not list((s.PRIVATE / "exports").glob("p21-final-*")),
                "An original finalization attempt exists; inspect it before another export")

    def run(label, argv):
        print(label, json.dumps(argv), flush=True)
        subprocess.run(argv, check=True)

    stable()
    no_export()
    print("P21_BASE_SUMMARY_RETAINED", str(base_summary), BASE_SUMMARY_SHA, "owners=132", flush=True)
    snapshot = str(snapshots[1])
    run("P21_BUCHSTAB_NORMAL_COMMAND", [sys.executable, "-B", str(s.NORMAL), s.BUCHSTAB,
        "--workers", "1", "--threads", "1", "--memory-mb", "11264", "--time-budget-seconds", "900",
        "--external-snapshot", snapshot])
    stable()
    summary_name = f"p21-buchstab-518-{uuid.uuid4().hex}.json"
    summary_path = s.AUDITS / summary_name
    require(not summary_path.exists(), "Unexpected preexisting Buchstab summary")
    run("P21_BUCHSTAB_AUDIT_COMMAND", [sys.executable, "-B", str(s.AUDIT), *sorted(native),
        "--memory-mb", "11264", "--external-snapshot", snapshot, "--summary-name", summary_name])
    accepted(s.read(summary_path), native)
    print("P21_BUCHSTAB_GROUP_ACCEPTED", str(summary_path), digest(summary_path), "owners=8", flush=True)
    stable()
    no_export()
    run("P21_ORIGINAL_FINALIZER_COMMAND", [sys.executable, "-B", str(tools / "finalize_p21.py")])


if __name__ == "__main__":
    main()
