#!/usr/bin/env python3
"""Read-only source/cache census for the four original owners and Full87 bridge.

This tool does not invoke Lean, Lake, a compiler, or an object loader.  It writes
only its requested JSON report.  Cache matches are candidates, never acceptance.
Run it in the isolated worktree after installing the four matching refactors.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


GOLDBACH_PIN = "09b97db5764ade1246bfb77206baa1b124760958"
MATHLIB_PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
ARCHITECT_PIN = "78dd66840d3efe8c824c699fc03381cec817c271"
CHECKPOINT_SHA = "aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a"
ROOTS = [
    "ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows",
    "ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows",
    "ImbalancedChen.P2OriginalDescendingEighthLogSemantics",
    "ImbalancedChen.P2OriginalThirdMinorantLogDictionary",
    "ImbalancedChen.P2Winner9OriginalFull87Bridge",
]
CANDIDATES = Path("docs/source-only/20261124-p2-winner9-original-full87")
NATIVE_PREFIXES = {"MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd", "Goldbach"}
STANDARD_PREFIXES = {
    "Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq", "Cli",
    "Plausible", "ProofWidgets", "LeanSearchClient", "ImportGraph", "Lake",
}


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_file(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def git(root: Path, *args: str) -> bytes:
    return subprocess.check_output(
        ["git", "-c", "protocol.allow=never", "-C", str(root), *args],
        env=dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0"))


def source_tokens(text: str) -> str:
    """Erase nested comments and strings, retaining line positions for imports."""
    result, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            if text[i] == "\\":
                result.extend("  ")
                i += 2
            elif text[i] == '"':
                string = False
                result.append(" ")
                i += 1
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            result.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            string = True
            result.append(" ")
            i += 1
        else:
            result.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated comment/string in selected Lean source")
    return "".join(result)


def imports(text: str) -> list[str]:
    result = []
    for line in source_tokens(text).splitlines():
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", line)
        if not match:
            continue
        names = match.group(1).split()
        if names and names[0] == "all":
            names = names[1:]
        if not names or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", n) for n in names):
            raise ValueError("Unrecognized import syntax: " + line)
        result.extend(names)
    return list(dict.fromkeys(result))


def checked_tree(root: Path, pin: str) -> tuple[dict, dict[str, str]]:
    head = git(root, "rev-parse", "HEAD").decode().strip()
    if head != pin:
        raise ValueError(f"Wrong fixed dependency pin: {root}: {head}")
    dirty = git(root, "status", "--porcelain", "--untracked-files=no").decode()
    if dirty:
        raise ValueError("Tracked dependency source/configuration changed: " + str(root))
    objects = {}
    for entry in git(root, "ls-tree", "-r", "-z", pin).split(b"\0"):
        if entry:
            info, path = entry.split(b"\t", 1)
            mode, kind, oid = info.decode().split()
            if kind == "blob":
                objects[path.decode()] = oid
    return {"root": str(root), "commit": head, "tracked_clean": True}, objects


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--baseline-root", type=Path, default=Path("/workspace/goldbach-p2"))
    parser.add_argument("--goldbach-root", type=Path)
    parser.add_argument("--architect-root", type=Path)
    parser.add_argument("--mathlib-root", type=Path, default=Path("/workspace/compile-deps/mathlib"))
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    root, baseline = args.project_root.resolve(), args.baseline_root.resolve()
    out = args.out.resolve()
    if root == baseline or out.is_relative_to(baseline):
        raise ValueError("Use a disjoint verification worktree and report path")
    if out.exists():
        raise ValueError("Refusing to overwrite a prior inspection report")
    native = (args.goldbach_root or baseline / ".lake/packages/goldbach").resolve()
    architect = (args.architect_root or baseline / ".lake/packages/LeanArchitect").resolve()
    mathlib = args.mathlib_root.resolve()
    receipt = json.loads((root / CANDIDATES / "DEFINITION_RECEIPT.json").read_text())
    for row in receipt["modules"]:
        if sha_file(root / row["path"]) != row["sha256"]:
            raise ValueError("Definition core differs from selected candidate: " + row["path"])
    for row in receipt["refactors"]:
        if row["active_at_baseline"]:
            if sha_file(root / row["path"]) != row["normalized_refactored_sha256"]:
                raise ValueError("Matching owner refactor is not installed: " + row["path"])
    bridge = Path("ImbalancedChen/P2Winner9OriginalFull87Bridge.lean")
    if (root / bridge).read_bytes() != (root / CANDIDATES / bridge).read_bytes():
        raise ValueError("Bridge differs from the selected source-only candidate")
    packages, trees = {}, {}
    for name, path, pin in [
        ("goldbach", native, GOLDBACH_PIN), ("mathlib", mathlib, MATHLIB_PIN),
        ("LeanArchitect", architect, ARCHITECT_PIN),
    ]:
        if path.is_dir():
            packages[name], trees[name] = checked_tree(path, pin)
        else:
            packages[name] = {"root": str(path), "commit": pin, "missing": True}
    if "goldbach" not in trees or "mathlib" not in trees:
        raise ValueError("The fixed native source and Mathlib checkouts are required")
    nodes, missing, boundaries, visiting, order = {}, {}, set(), set(), []

    def visit(name: str) -> None:
        if name in visiting:
            raise ValueError("Import cycle involving " + name)
        if name in nodes or name in missing or name in boundaries:
            return
        prefix = name.split(".", 1)[0]
        if prefix == "ImbalancedChen":
            package, directory = "project", root
        elif prefix in NATIVE_PREFIXES:
            package, directory = "goldbach", native
        elif prefix == "Architect":
            package, directory = "LeanArchitect", architect
        elif prefix in STANDARD_PREFIXES:
            boundaries.add(name)
            return
        else:
            raise ValueError("Unrecognized dependency boundary: " + name)
        relative = name.replace(".", "/") + ".lean"
        path = directory / relative
        if not path.is_file():
            missing[name] = str(path)
            return
        data = path.read_bytes()
        if package != "project" and trees[package].get(relative) != blob_sha(data):
            raise ValueError("Dependency source is not its exact pinned Git blob: " + str(path))
        tokens = source_tokens(data.decode())
        findings = sorted(set(re.findall(
            r"\b(?:sorry|admit|sorryAx|axiom|native_decide|unsafe|implemented_by|extern|include_str|include_bin)\b", tokens)))
        deps = imports(data.decode())
        nodes[name] = {"package": package, "path": str(path), "relative": relative,
                       "sha256": sha_bytes(data), "git_blob_sha1": blob_sha(data),
                       "bytes": len(data), "imports": deps,
                       "static_review_tokens": findings}
        visiting.add(name)
        for dep in deps:
            visit(dep)
        visiting.remove(name)
        order.append(name)

    for name in ROOTS:
        visit(name)
    selected = {n: r for n, r in nodes.items() if r["package"] != "project"}
    native_roots = sorted({dep for row in nodes.values() if row["package"] == "project"
                           for dep in row["imports"] if dep.split(".")[0] in NATIVE_PREFIXES})
    old_selector = root / "docs/source-only/20261113-resume/coherent-cache-tools/inputs/P2_NATIVE_398_CHECKPOINT_SELECTION.json"
    selection = json.loads(old_selector.read_text())
    old_matches = sorted(row["module"] for row in selection["rows"]
                         if row["module"] in selected
                         and selected[row["module"]]["sha256"] == row["source"]["sha256"])
    checkpoint = None
    if args.checkpoint:
        if sha_file(args.checkpoint) != CHECKPOINT_SHA:
            raise ValueError("Wrong original checkpoint bytes")
        cp = json.loads(args.checkpoint.read_text())
        if not cp["runtime_audit_valid"] or not cp["all_dependency_source_pins_valid"]:
            raise ValueError("Original runtime/pin audit did not pass")
        current_pins = {p["name"]: p["rev"] for p in json.loads((root / "lake-manifest.json").read_text())["packages"]}
        if any(not p["pin_matches"] or current_pins.get(p["name"]) != p["rev"] for p in cp["packages"]):
            raise ValueError("Original/current locked dependency pins differ")
        candidates, rejected = {}, {}
        for row in cp["all_guarded_package_compilations"]:
            name = row.get("module")
            if name not in selected:
                continue
            reasons = []
            if row.get("classification") != "PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND":
                reasons.append("ORIGINAL_QUARANTINE")
            if row["source"]["sha256"] != selected[name]["sha256"]:
                reasons.append("SOURCE_MISMATCH")
            if reasons:
                rejected.setdefault(name, []).extend(reasons)
            else:
                candidates[name] = row
        payloads = {r["payload"]: r["bytes"] for row in candidates.values()
                    for r in row.get("facet_files", []) if r.get("payload")}
        checkpoint = {
            "sha256": CHECKPOINT_SHA, "source_matching_candidate_count": len(candidates),
            "source_matching_candidate_modules": sorted(candidates), "rejected": rejected,
            "required_without_source_matching_checkpoint": sorted(set(selected) - candidates.keys()),
            "all_candidate_facet_payload_bytes": sum(payloads.values()),
            "all_candidate_facet_payload_count": len(payloads),
            "actual_physical_import_runtime_and_output_rebind": "NOT_YET_PERFORMED",
            "kernel_replay": "NOT_YET_PERFORMED", "accepted_objects": 0,
        }
    # Detect changes during this read-only census; hashes are the report's identity.
    for row in nodes.values():
        if sha_file(Path(row["path"])) != row["sha256"]:
            raise ValueError("Source changed during inspection: " + row["path"])
    for name, path, pin in [("goldbach", native, GOLDBACH_PIN), ("mathlib", mathlib, MATHLIB_PIN),
                            ("LeanArchitect", architect, ARCHITECT_PIN)]:
        if name in trees:
            if git(path, "rev-parse", "HEAD").decode().strip() != pin or git(path, "status", "--porcelain", "--untracked-files=no").strip():
                raise ValueError("Dependency checkout changed during inspection: " + name)
    result = {
        "schema": "p2-owner-native-source-census-v1", "script_sha256": sha_file(Path(__file__)),
        "status": "INCOMPLETE_MISSING_SOURCE" if missing else "SOURCE_GRAPH_COMPLETE_CACHE_ACCEPTANCE_PENDING",
        "project_root": str(root), "roots": ROOTS, "packages": packages,
        "counts": dict(Counter(row["package"] for row in nodes.values())),
        "direct_native_roots": native_roots, "native_source_count": len(selected),
        "project_source_count": len(nodes) - len(selected), "topological_order": order,
        "nodes": nodes, "missing": missing, "standard_boundaries": sorted(boundaries),
        "static_review_findings": {n: r["static_review_tokens"] for n, r in nodes.items() if r["static_review_tokens"]},
        "old398_source_match_count": len(old_matches), "old398_source_match_modules": old_matches,
        "checkpoint": checkpoint, "source_compiler_or_object_loader_invocations": 0,
        "source_or_baseline_modifications": 0, "cache_acceptance": False,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({k: result[k] for k in ("status", "counts", "native_source_count", "project_source_count", "old398_source_match_count", "missing", "static_review_findings", "checkpoint")}, indent=2))
    print("REPORT", out)
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
