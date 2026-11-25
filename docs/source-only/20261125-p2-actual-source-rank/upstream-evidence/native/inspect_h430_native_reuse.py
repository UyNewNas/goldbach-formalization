#!/usr/bin/env python3
"""Read pinned active/research native sources and inventory historical reuse.

Only --out is written. No Lean/Lake/object loader, cache install, qualification,
source change, or network call is performed. Active package sources retain
priority; research sources are selected only when the active module is absent.
Every selected source must be the exact blob at the fixed package commit.
This is a separate census; it does not change frozen Winner9 caller policies.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

GOLDBACH_PIN = "09b97db5764ade1246bfb77206baa1b124760958"
ARCHITECT_PIN = "78dd66840d3efe8c824c699fc03381cec817c271"
PARSER_SHA = "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d"
OLD_CENSUS_SHA = "ba08551ba6a326527d938439b96c06efa829e028bda88fc1497898645e282cc1"
OLD_SNAPSHOT_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
CHECKPOINT_SHA = "aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a"
NATIVE = {"MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd", "Goldbach", "Architect"}
STANDARD = {"Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq", "Cli", "Plausible", "ProofWidgets", "LeanSearchClient", "ImportGraph", "Lake"}


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_bound(path: Path, expected: str) -> dict:
    if digest(path) != expected:
        raise ValueError("Historical input identity differs: " + str(path))
    return json.loads(path.read_text())


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--roots-manifest", type=Path, required=True)
    p.add_argument("--helper-dir", type=Path, required=True)
    p.add_argument("--goldbach-root", type=Path, required=True)
    p.add_argument("--architect-root", type=Path, required=True)
    p.add_argument("--old-census", type=Path, required=True)
    p.add_argument("--old-snapshot", type=Path)
    p.add_argument("--checkpoint", type=Path)
    p.add_argument("--object-root", type=Path, action="append", default=[])
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    if args.out.exists():
        raise ValueError("Refusing to replace previous census evidence")
    for directory in (args.goldbach_root, args.architect_root):
        if args.out.resolve().is_relative_to(directory.resolve()):
            raise ValueError("Report must be outside pinned native source trees")
    parser_path = args.helper_dir / "inspect_winner9_owner_native.py"
    if digest(parser_path) != PARSER_SHA:
        raise ValueError("Fixed import parser identity differs")
    spec = importlib.util.spec_from_file_location("h430_existing_source_parser", parser_path)
    parser = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    assert spec.loader is not None
    spec.loader.exec_module(parser)
    old = read_bound(args.old_census, OLD_CENSUS_SHA)
    old_native = {n: x for n, x in old["nodes"].items() if x["package"] != "project"}
    snapshot = read_bound(args.old_snapshot, OLD_SNAPSHOT_SHA) if args.old_snapshot else None
    if snapshot is not None:
        assert snapshot["status"] == "QUALIFIED_NATIVE_INPUTS_ONLY_NOT_PROOF_ACCEPTANCE"
        assert snapshot["qualification"]["status"] == "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED"
    root_manifest = json.loads(args.roots_manifest.read_text())
    roots = sorted({x["module"] for x in root_manifest["direct_native_boundaries"]})
    if len(roots) != 49:
        raise ValueError("This audit is scoped to the selected 49 H430 native roots")
    packages, trees = {}, {}
    for name, directory, pin in [("goldbach", args.goldbach_root, GOLDBACH_PIN), ("LeanArchitect", args.architect_root, ARCHITECT_PIN)]:
        packages[name], trees[name] = parser.checked_tree(directory.resolve(), pin)
    nodes, missing, errors, collisions, standard = {}, {}, {}, {}, set()
    visiting, order = set(), []
    object_roots = [x.resolve() for x in args.object_root]
    if snapshot:
        object_roots.extend(Path(x).resolve() for x in snapshot["runtime"]["lean_path"])
    object_roots = list(dict.fromkeys(object_roots))

    def visit(name: str) -> None:
        prefix = name.split(".", 1)[0]
        if prefix in STANDARD:
            standard.add(name)
            return
        if prefix not in NATIVE:
            errors[name] = "Unexpected boundary; no source selection invented"
            return
        if name in visiting:
            errors[name] = "Import cycle"
            return
        if name in nodes or name in missing or name in errors:
            return
        package = "LeanArchitect" if prefix == "Architect" else "goldbach"
        base = Path(packages[package]["root"])
        relative = name.replace(".", "/") + ".lean"
        alternatives = [relative] if package == "LeanArchitect" else [relative, "research/wu2008/src/" + relative]
        candidates = [r for r in alternatives if r in trees[package] and (base / r).is_file()]
        if not candidates:
            missing[name] = [str(base / r) for r in alternatives]
            return
        relative = candidates[0]
        if len(candidates) > 1 and len({trees[package][r] for r in candidates}) > 1:
            collisions[name] = {"selected": relative, "alternatives": {r: trees[package][r] for r in candidates}, "selection_rule": "retain active source; never overlay a research variant over it"}
        source = base / relative
        raw = source.read_bytes()
        blob = parser.blob_sha(raw)
        if blob != trees[package][relative]:
            errors[name] = "Selected source differs from its immutable Git blob: " + str(source)
            return
        try:
            imports = parser.imports(raw.decode())
        except (ValueError, UnicodeError) as error:
            errors[name] = str(error)
            return
        sha = hashlib.sha256(raw).hexdigest()
        row = {"package": package, "source_path": str(source), "repository_relative_path": relative, "source_kind": "research" if relative.startswith("research/") else "active", "sha256": sha, "git_blob_sha1": blob, "bytes": len(raw), "imports": imports, "old_census_member": name in old_native, "old_census_exact_source": name in old_native and old_native[name]["sha256"] == sha}
        if snapshot and name in snapshot["modules"]:
            historic = snapshot["modules"][name]
            row["old_snapshot_source_match"] = snapshot["files"][historic["source"]]["sha256"] == sha
            row["old_snapshot_provider"] = historic["provider"]
            row["old_snapshot_object"] = historic["object"]
        row["object_presence_only_not_qualification"] = [str(root / (name.replace(".", "/") + ".olean")) for root in object_roots if (root / (name.replace(".", "/") + ".olean")).is_file()]
        nodes[name] = row
        visiting.add(name)
        for dep in imports:
            visit(dep)
        visiting.remove(name)
        order.append(name)

    for name in roots:
        visit(name)
    checkpoint_matches = {}
    if args.checkpoint:
        checkpoint = read_bound(args.checkpoint, CHECKPOINT_SHA)
        for index, row in enumerate(checkpoint["all_guarded_package_compilations"]):
            name = row.get("module")
            if name not in nodes:
                continue
            chosen = nodes[name]
            if row.get("package") != chosen["package"] or row.get("source", {}).get("sha256") != chosen["sha256"]:
                continue
            checkpoint_matches.setdefault(name, []).append({"collection": "all_guarded_package_compilations", "index": index, "classification": row.get("classification"), "source": row.get("source"), "lake_completed_trace": row.get("lake_completed_trace"), "output_bound_command": row.get("output_bound_command"), "missing_actual_import_artifacts": row.get("missing_actual_import_artifacts"), "actual_import_map_sha256": row.get("actual_import_map_sha256"), "facet_count": len(row.get("facet_files", [])), "scope": "matching archived source row only; no descriptor/import/runtime qualification"})
    new = sorted(n for n in nodes if not nodes[n]["old_census_exact_source"])
    result = {"schema": "h430-native-reuse-census-v1", "status": "READ_ONLY_SOURCE_CENSUS_COMPLETE_NOT_QUALIFICATION" if not missing and not errors else "READ_ONLY_SOURCE_CENSUS_INCOMPLETE", "script_sha256": digest(Path(__file__)), "roots_manifest_sha256": digest(args.roots_manifest), "fixed_parser_sha256": PARSER_SHA, "old_census_sha256": OLD_CENSUS_SHA, "old_snapshot_sha256": OLD_SNAPSHOT_SHA if snapshot else None, "checkpoint_sha256": CHECKPOINT_SHA if args.checkpoint else None, "packages": packages, "roots": roots, "nodes": nodes, "topological_order": order, "outside_old_515_exact_source": new, "standard_boundaries": sorted(standard), "active_research_variant_collisions": collisions, "missing": missing, "errors": errors, "source_matching_checkpoint_candidates": checkpoint_matches, "summary": {"direct_roots": len(roots), "native_sources": len(nodes), "source_kinds": dict(Counter(x["source_kind"] for x in nodes.values())), "old_census_exact_source": len(nodes) - len(new), "outside_old_census_exact_source": len(new), "new_with_matching_original_checkpoint_rows": sum(n in checkpoint_matches for n in new), "new_with_any_observed_object": sum(bool(nodes[n]["object_presence_only_not_qualification"]) for n in new), "missing": len(missing), "errors": len(errors), "active_research_variant_collisions": len(collisions)}, "source_compiler_or_object_loader_invocations": 0, "source_or_cache_modifications": 0, "qualification_credit": False, "kernel_credit": False, "limitations": ["Source priority is explicit active-first, then research fallback; collisions are retained for review.", "A historical snapshot digest is checked, but its physical context is not requalified here.", "Object existence and checkpoint source matching do not establish provider, import, runtime, or kernel acceptance."]}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "report": str(args.out), "sha256": digest(args.out), **result["summary"]}, sort_keys=True))
    return 0 if not missing and not errors else 2


if __name__ == "__main__":
    raise SystemExit(main())
