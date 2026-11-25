#!/usr/bin/env python3
"""Check exact source layering and its local graph without invoking Lean."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
BASE_COMMIT = "d20acdf13882e17d97833064f5e7c54f3192b03c"
CORE = "ImbalancedChen.Part3FiniteLambdaOverLogCore"
FINITE = "ImbalancedChen.Part3FiniteLambdaOverLogDictionary"
ALLK = "ImbalancedChen.Part3AllKLambdaChartCorrection"
FAMILY = "ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound"
DECLARATIONS = (
    "lambdaOverLog", "lambdaOverLog_zero", "lambdaOverLog_one",
    "lambdaOverLog_prime", "lambdaOverLog_prime_pow",
    "lambdaOverLog_off_prime_powers", "lambdaOverLog_pointwise_split",
    "finite_lambdaOverLog_split", "proper_term_has_prime_exponent",
)


def require(value: bool, message: str) -> None:
    if not value:
        raise ValueError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def check(data: bytes, pin: dict, label: str) -> None:
    require(sha(data) == pin["sha256"], label + ": SHA256 mismatch")
    if "bytes" in pin:
        require(len(data) == pin["bytes"], label + ": size mismatch")
    if "git_blob" in pin:
        require(blob(data) == pin["git_blob"], label + ": Git blob mismatch")


def relative(repo: Path, name: str) -> Path:
    path = repo / name
    require(not Path(name).is_absolute() and path.resolve().is_relative_to(repo), "invalid repository path")
    return path


def imports(data: bytes) -> list[str]:
    return [name for line in data.decode().splitlines() if line.startswith("import ")
            for name in line[len("import "):].split()]


def main() -> None:
    require(len(sys.argv) == 1, "this verifier accepts no arguments")
    here = Path(__file__).resolve().parent
    repo = here.parents[3]
    manifest_bytes = (here / "ADOPTION_MANIFEST.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    require(manifest["schema"] == "p15_finite_lambda_original_source_layering_v1", "schema mismatch")
    require(manifest["source_base_commit"] == BASE_COMMIT, "source base mismatch")
    require(manifest["new_Lean_acceptance_claimed"] is False, "new acceptance claim")
    check(Path(__file__).read_bytes(), manifest["verifier"], "verifier")
    env = dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0")
    before = {}
    for module, pin in manifest["preimages"].items():
        require(module in (FINITE, ALLK, FAMILY), "unexpected preimage module")
        result = subprocess.run(
            ["git", "-c", "protocol.allow=never", "show", BASE_COMMIT + ":" + pin["canonical_path"]],
            cwd=repo, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        )
        require(result.returncode == 0, "required local Git preimage unavailable")
        check(result.stdout, pin, "Git preimage " + module)
        require(relative(repo, pin["snapshot_path"]).read_bytes() == result.stdout, "preimage snapshot mismatch")
        before[module] = result.stdout
    require(set(before) == {FINITE, ALLK, FAMILY}, "preimage set mismatch")

    ranges = manifest["declaration_ranges"]
    require(tuple(row["name"] for row in ranges) == DECLARATIONS, "declaration set/order mismatch")
    for row in ranges:
        part = before[FINITE][row["old_start_byte"]:row["old_end_byte_exclusive"]]
        check(part, row, "original declaration " + row["name"])
        require(row["full_name"] == "ImbalancedChen.Part3.FiniteLambdaOverLogDictionary." + row["name"], "public declaration name changed")

    core = b"".join(
        part["literal"].encode() if "literal" in part else
        before[FINITE][part["start_byte"]:part["end_byte_exclusive"]]
        for part in manifest["core_construction"]
    )
    finite = before[FINITE]
    for row in reversed(ranges):
        finite = finite[:row["old_start_byte"]] + finite[row["old_end_byte_exclusive"]:]
    finite = manifest["finite_added_import"].encode() + finite
    replacement = manifest["allk_import_replacement"]
    require(before[ALLK].count(replacement["before"].encode()) == 1, "AllK original import multiplicity")
    allk = before[ALLK].replace(replacement["before"].encode(), replacement["after"].encode(), 1)
    require(allk[len(replacement["after"].encode()):] == before[ALLK][len(replacement["before"].encode()):], "AllK non-import bytes changed")
    expected = {CORE: core, FINITE: finite, ALLK: allk}
    require(set(manifest["postimages"]) == set(expected), "postimage set mismatch")
    for module, data in expected.items():
        pin = manifest["postimages"][module]
        check(data, pin, "reconstructed postimage " + module)
        require(relative(repo, pin["canonical_path"]).read_bytes() == data, "canonical postimage mismatch")
        require(relative(repo, pin["snapshot_path"]).read_bytes() == data, "postimage snapshot mismatch")
    require(imports(core) == ["Mathlib"], "Core literal imports differ")
    require(relative(repo, manifest["preimages"][FAMILY]["canonical_path"]).read_bytes() == before[FAMILY], "Family full source changed")
    for row in ranges:
        part = core[row["new_start_byte"]:row["new_end_byte_exclusive"]]
        check(part, row, "relocated declaration " + row["name"])
    sorted_pin = manifest["sorted_theorem_preservation"]
    original_sorted = before[FINITE][sorted_pin["old_start_byte"]:sorted_pin["old_end_byte_exclusive"]]
    check(original_sorted, sorted_pin, "original sorted theorem")
    require(finite.count(original_sorted) == 1, "sorted theorem not preserved exactly once")

    pattern = r"^(?:def|theorem|lemma|abbrev|axiom|opaque) (?:" + "|".join(DECLARATIONS) + r")\b"
    census = subprocess.run(["rg", "-n", pattern, "ImbalancedChen"], cwd=repo,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False, text=True)
    require(census.returncode == 0, "canonical declaration census unavailable")
    lines = census.stdout.splitlines()
    require(len(lines) == 9, "canonical declaration count differs")
    require(all(line.startswith("ImbalancedChen/Part3FiniteLambdaOverLogCore.lean:") for line in lines), "duplicate or old canonical declaration owner")

    observation_pin = manifest["source_only_observation"]
    observation_bytes = relative(repo, observation_pin["repository_path"]).read_bytes()
    check(observation_bytes, observation_pin, "saved source-only observation")
    observation = json.loads(observation_bytes)
    observed = {row["module"]: row for row in observation["rows"]}
    require(set(observed) == {FINITE, ALLK}, "source-only observation set mismatch")
    for module, row in observed.items():
        require(row["source_matches"] is True and row["source"]["sha256"] == sha(before[module]), "source-only observation source mismatch")
        require(all(value is None for value in row["outputs"].values()), "observed compiled object present")

    graph_pin = manifest["static_graph_review"]
    graph_bytes = relative(repo, graph_pin["repository_path"]).read_bytes()
    check(graph_bytes, graph_pin, "graph review")
    graph = json.loads(graph_bytes)
    old_pin = graph["before386_source_manifest"]
    old_bytes = relative(repo, old_pin["repository_path"]).read_bytes()
    check(old_bytes, old_pin, "preserved old386 manifest")
    old = json.loads(old_bytes)
    require(len(old["project_sources"]) == 386, "old386 count mismatch")
    seen = set()
    todo = list(graph["next_stage_six_targets"])
    require(len(todo) == 6 and CORE in todo, "next-stage targets mismatch")
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        pin = graph["after_project_sources"][module]
        data = relative(repo, pin["path"]).read_bytes()
        check(data, pin, "after source graph " + module)
        dependencies = [name for name in imports(data) if name.startswith("ImbalancedChen.")]
        require(dependencies == pin["project_imports"], "after import graph mismatch")
        todo.extend(dependencies)
    require(len(seen) == 168 and seen == set(graph["after_project_sources"]), "after graph closure mismatch")
    require(FINITE not in seen and ALLK in seen and FAMILY in seen, "full-provider layering boundary mismatch")
    require(graph["extra45_retained_count"] == 3 and graph["extra45_outside_new_closure_count"] == 42, "extra45 graph count mismatch")
    print(json.dumps({"status": "PASS_EXACT_SOURCE_LAYERING_STATIC_ONLY", "manifest_sha256": sha(manifest_bytes),
                      "original_declarations_preserved": 9, "unique_canonical_owner": CORE,
                      "Core_literal_imports": imports(core), "AllK_only_import_changed": True,
                      "Family_full_source_unchanged": True, "sorted_theorem_preserved": True,
                      "old_source_closure": 386, "next_source_closure": 168, "next_targets": 6,
                      "extra45_retained": 3, "extra45_outside_next_closure": 42,
                      "Lean_invocations": 0, "new_Lean_acceptance": False}, ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (KeyError, ValueError, OSError, UnicodeError) as error:
        print(json.dumps({"status": "HOLD", "reason": str(error)}, ensure_ascii=False), file=sys.stderr)
        raise SystemExit(1)
