#!/usr/bin/env python3
"""Lossless SOURCE_ONLY carrier split; never invoke Lean or a proof checker.

The frozen Git input is read with `git show`, never reset or checked out. The
original definitions are copied as byte slices. --check performs read-only
static identity, coverage, dependency and deterministic-emission checks.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
BASE = "d41a7bc48b7066cd95c2a9e143a13e494d44b284"
CERT = "ImbalancedChen/Certificates/"
DATA = CERT + "PairedV2FullCertificateData.lean"
MASK = CERT + "PairedV2FullMaskData.lean"
RAW = "verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json"
NS = "ImbalancedChen.Certificates.PairedV2.FullMask"
SUM_NS = NS + ".NaturalSums"
REPORT = "verification/parts/p2/data-split-source-manifest.json"
DEPENDENCIES = "verification/parts/p2/data-split-dependencies.json"
PINS = {
    DATA: "a059e969139810aa89516661609b540968efbf6b1e2c2ab975a8262ce8462309",
    MASK: "19bcfe8f9524fa93fbe3d8eb5f95653c40384655b3eab69f914211e63bdf2f5a",
    RAW: "f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7",
}
PROTECTED = [MASK, RAW, CERT + "PairedV2FullMask.lean",
             CERT + "PairedV2FullChecker.lean", CERT + "PairedV2StripCertificates.lean", "lean-toolchain",
             "lakefile.toml", "lake-manifest.json", "ImbalancedChen.lean"]


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_input(path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)


def json_bytes(value) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()


def module(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def parse_definitions(raw: bytes):
    starts = list(re.finditer(rb"(?m)^def approximations(\d+) : List Approximation :=\n", raw))
    selector = raw.index(b"def approximations : Fin 186")
    assert [int(m[1]) for m in starts] == list(range(326, 512))
    defs = []
    for p, match in enumerate(starts):
        stop = starts[p + 1].start() if p + 1 < len(starts) else selector
        defs.append((int(match[1]), raw[match.start():stop], match.start()))
    return raw[:starts[0].start()], defs, raw[selector:]


def sources_and_report():
    original = git_input(DATA)
    assert sha(original) == PINS[DATA]
    for path in PROTECTED:
        assert (ROOT / path).read_bytes() == git_input(path), f"protected input changed: {path}"
    for path, expected in PINS.items():
        raw = original if path == DATA else (ROOT / path).read_bytes()
        assert sha(raw) == expected, f"frozen input changed: {path}"
    prefix, defs, suffix = parse_definitions(original)
    assert prefix + b"".join(body for _, body, _ in defs) + suffix == original
    groups = [defs[p:p + 16] for p in range(0, 186, 16)]
    footer = f"end {NS}\n".encode()
    first_u = list(map(int, re.search(rb"!\[([^\]]+)\]", (ROOT / MASK).read_bytes())[1].split(b",")))
    assert len(first_u) == 186
    raw_rows = json.loads((ROOT / RAW).read_bytes())["rows"]
    pairs = {(r[1], r[2]): r for r in raw_rows}
    assert len(raw_rows) == len(pairs) == 17572
    sources = {}
    strip_manifest = []
    group_manifest = []
    seen = []
    for b, group in enumerate(groups):
        name = CERT + f"PairedV2FullCertificateDataBlock{b:02}.lean"
        leaf_prefix = prefix + f"-- Lossless carrier {b:02}: original strips {group[0][0]}–{group[-1][0]}.\n\n".encode()
        body = leaf_prefix + b"".join(d for _, d, _ in group) + footer
        sources[name] = body
        group_start = len(strip_manifest)
        for k, declaration, offset in group:
            witness_body = re.fullmatch(rb"def approximations\d+ : List Approximation :=\s*\[\s*(.*?)\s*\]\s*", declaration, re.S)[1].decode()
            witnesses = [tuple(map(int, r.split(","))) for r in re.findall(r"⟨([^⟩]+)⟩", witness_body)]
            assert all(len(r) == 8 and all(v >= 0 for v in r) and r[6] <= r[7] for r in witnesses)
            assert not re.sub(r"⟨[^⟩]+⟩|[\s,]", "", witness_body)
            assert len(witnesses) == 512 - first_u[k - 326]
            expected_pairs = [(k, j) for j in range(first_u[k - 326], 512)]
            assert all(p in pairs for p in expected_pairs)
            seen.extend(expected_pairs)
            new_offset = body.index(declaration)
            assert body.count(declaration) == 1
            entry = {
                "declaration": f"{NS}.approximations{k}", "type": "List Approximation",
                "strip": k, "block": b, "first_u": first_u[k - 326],
                "row_count": len(witnesses), "original_file": DATA, "new_file": name,
                "original_line_start": original[:offset].count(b"\n") + 1,
                "original_line_end": original[:offset + len(declaration.rstrip())].count(b"\n") + 1,
                "new_line_start": body[:new_offset].count(b"\n") + 1,
                "new_line_end": body[:new_offset + len(declaration.rstrip())].count(b"\n") + 1,
                "original_declaration_sha256": sha(declaration),
                "new_declaration_sha256": sha(body[new_offset:new_offset + len(declaration)]),
                "tuple_stream_sha256": sha(json_bytes(witnesses)),
                "E0_rows": sum(pairs[p][0] == "E0" for p in expected_pairs),
                "E1_rows": sum(pairs[p][0] == "E1" for p in expected_pairs),
                "lower_sum": str(sum(r[6] for r in witnesses)),
                "upper_sum": str(sum(r[7] for r in witnesses)),
            }
            assert entry["original_declaration_sha256"] == entry["new_declaration_sha256"]
            strip_manifest.append(entry)
        group_manifest.append({"block": b, "data_module": module(name),
                               "first_strip": group[0][0], "last_strip": group[-1][0],
                               "strips": len(group), "rows": sum(x["row_count"] for x in strip_manifest[group_start:]),
                               "source_bytes": len(body)})
        sums_name = CERT + f"PairedV2NaturalSumsBlock{b:02}.lean"
        old_sums = git_input(sums_name)
        old_import = f"import {module(DATA)}\n".encode()
        assert old_sums.startswith(old_import)
        repaired_sums = old_sums
        for projection in (1, 2):
            rewrite = ("  rw [" + ", ".join(f"strip{k}_sums.{projection}" for k, _, _ in group) + "]\n").encode()
            redundant = rewrite + b"  decide +kernel\n"
            assert repaired_sums.count(redundant) == 1
            repaired_sums = repaired_sums.replace(redundant, rewrite, 1)
        assert re.findall(rb"\d+", repaired_sums) == re.findall(rb"\d+", old_sums)
        sums = repaired_sums.replace(old_import, f"import {module(name)}\n".encode(), 1)
        lengths = b"\n/-- Each length is checked separately over its original literal list. -/\n"
        for entry in strip_manifest[group_start:]:
            k = entry["strip"]
            lengths += (f"theorem strip{k}_length :\n"
                        f"    approximations{k}.length = 512 - firstU (⟨{k - 326}, by decide⟩ : Fin 186) := by\n"
                        "  rfl\n\n").encode()
        end = f"end {SUM_NS}\n".encode()
        assert sums.endswith(end)
        sums = sums[:-len(end)] + lengths + end
        assert sums.replace(lengths, b"", 1).replace(f"import {module(name)}\n".encode(), old_import, 1) == repaired_sums
        sources[sums_name] = sums
    imports = b"".join(f"import {module(CERT + f'PairedV2FullCertificateDataBlock{b:02}.lean')}\n".encode() for b in range(12))
    original_import, prefix_tail = prefix.split(b"\n", 1)
    assert original_import == b"import ImbalancedChen.Certificates.PairedV2FullChecker"
    sources[DATA] = imports + prefix_tail + suffix
    assert sources[DATA].endswith(suffix), "selector / approximation definitions changed"

    rows_name = CERT + "PairedV2NaturalSumRows.lean"
    old_rows = git_input(rows_name)
    options_start = old_rows.index(f"namespace {SUM_NS}".encode())
    declarations_start = old_rows.index(b"theorem approximation_lengths")
    options = old_rows[options_start:declarations_start]
    generic_start = old_rows.index(b"theorem sum_getD_eq_map")
    strip_start = old_rows.index(b"theorem strip_sum_eq_map")
    generic = old_rows[generic_start:strip_start]
    cons_step = b"  | cons x xs ih =>\n"
    cons_shape = ("    change (∑ j : Fin (xs.length + 1), f ((x :: xs).getD j.val default)) =\n"
                  "      f x + (xs.map f).sum\n").encode()
    assert generic.count(cons_step) == 1
    generic = generic.replace(cons_step, cons_step + cons_shape, 1)
    assembly_rest = old_rows[strip_start:]
    row_imports = old_rows[:old_rows.index(b"\n\n")].replace(
        b"PairedV2FullCertificateData", b"PairedV2FullChecker")
    sources[rows_name] = row_imports + b"\n\n/-! Generic finite list-sum bridge. No certificate-data module is imported. -/\n\n" + options + generic + f"end {SUM_NS}\n".encode()
    # Exact already-compiled/replayed Rows source from P0 run 38673067254.
    assert sha(sources[rows_name]) == "56eebe1e99f8dd6d79da3c49d0bcfb39fcc28f4c2468fdff8446a5876314cfbf"
    assembly_name = CERT + "PairedV2NaturalSumRowAssembly.lean"
    lengths_name = CERT + "PairedV2NaturalSumLengths.lean"
    partition_name = CERT + "PairedV2NaturalSumPartition.lean"
    expected_name = CERT + "PairedV2NaturalSumExpectedLengths.lean"
    assembly_imports = [module(rows_name), module(lengths_name)]
    length_type = old_rows[declarations_start:generic_start].split(b" := by\n", 1)[0]
    old_transport = b"  simpa only [approximation_lengths i] using sum_getD_eq_map (approximations i) f\n"
    new_transport = b"  rw [\xe2\x86\x90 approximation_lengths i]\n  exact sum_getD_eq_map (approximations i) f\n"
    assert assembly_rest.count(old_transport) == 1
    assembly_rest = assembly_rest.replace(old_transport, new_transport, 1)
    old_ofFn = "  rw [← List.sum_ofFn, List.ofFn_comp']\n".encode()
    new_ofFn = ("  rw [← List.sum_ofFn,\n"
                "    List.ofFn_comp' approximations (fun xs => (xs.map f).sum)]\n").encode()
    assert assembly_rest.count(old_ofFn) == 1
    assembly_rest = assembly_rest.replace(old_ofFn, new_ofFn, 1)
    sources[assembly_name] = ("\n".join(f"import {m}" for m in assembly_imports) + "\n\n/-! Original Row/list statements using the separately assembled length theorem.\nNo dependent 186-case proof or full-witness length reduction occurs here. -/\n\n").encode() + options + assembly_rest
    main_name = CERT + "PairedV2NaturalSums.lean"
    old_main = git_input(main_name)
    repaired_main = old_main
    for field in ("lower", "upper"):
        rewrite = ("  rw [" + ", ".join(f"block{b:02}_{field}" for b in range(12)) + "]\n").encode()
        redundant = rewrite + b"  decide +kernel\n"
        assert repaired_main.count(redundant) == 1
        repaired_main = repaired_main.replace(redundant, rewrite, 1)
    assert re.findall(rb"\d+", repaired_main) == re.findall(rb"\d+", old_main)
    partition_start = repaired_main.index(b"/-- All 186 strips in their original order")
    partition_stop = repaired_main.index(b"/-- Exact numerator sum over every `FullMask.Row`")
    partition_body = repaired_main[partition_start:partition_stop]
    partition_imports = [module(DATA), "Mathlib.Data.List.OfFn"] + [module(CERT + f"PairedV2NaturalSumsBlock{b:02}.lean") for b in range(12)]
    sources[partition_name] = ("\n".join(f"import {m}" for m in partition_imports) + "\n\n/-! Original ordered partition, moved verbatim before the length/Row bridges. -/\n\n").encode() + options + partition_body + f"end {SUM_NS}\n".encode()
    repaired_main = repaired_main[:partition_start] + repaired_main[partition_stop:]
    sources[main_name] = repaired_main.replace(f"import {module(rows_name)}\n".encode(), f"import {module(assembly_name)}\n".encode(), 1)
    assert old_main != sources[main_name]

    expected = "[" + ", ".join(str(s["row_count"]) for s in strip_manifest) + "]"
    expected_body = ("/-- The unchanged firstU selector's 186 small natural row counts. -/\n"
                     "def expectedLengths : List ℕ :=\n  " + expected + "\n\n"
                     "theorem firstU_lengths_list :\n"
                     "    List.ofFn (fun i : Fin 186 => 512 - firstU i) = expectedLengths := by\n"
                     "  rfl\n\n")
    sources[expected_name] = (f"import {module(MASK)}\nimport Mathlib.Data.List.OfFn\n\n"
                             "/-! Small scalar-selector certificate; no full certificate-data leaf. -/\n\n").encode() + options + expected_body.encode() + f"end {SUM_NS}\n".encode()
    length_block_names = []
    for b, group in enumerate(groups):
        path = CERT + f"PairedV2NaturalSumLengthsBlock{b:02}.lean"
        length_block_names.append(path)
        entries = strip_manifest[b * 16:b * 16 + len(group)]
        values = "[" + ", ".join(str(s["row_count"]) for s in entries) + "]"
        symbolic = "[" + ", ".join(f"approximations{k}.length" for k, _, _ in group) + "]"
        proof = (f"theorem block{b:02}_lengths :\n"
                 f"    block{b:02}.map List.length = {values} := by\n"
                 f"  change {symbolic} = _\n"
                 "  rw [" + ", ".join(f"strip{k}_length" for k, _, _ in group) + "]\n\n")
        sources[path] = (f"import {module(CERT + f'PairedV2NaturalSumsBlock{b:02}.lean')}\n\n"
                         "/-! Reuse the accepted strip length facts, at most sixteen per module. -/\n\n").encode() + options + proof.encode() + f"end {SUM_NS}\n".encode()
    length_imports = [module(partition_name), module(expected_name)] + [module(p) for p in length_block_names]
    symbolic_append = " ++ (".join(f"block{b:02}.map List.length" for b in range(12)) + " ++ []" + ")" * 11
    blocks_proof = ("theorem blocks_lengths : blocks.flatten.map List.length = expectedLengths := by\n"
                    "  calc\n"
                    f"    blocks.flatten.map List.length = {symbolic_append} := by\n"
                    "      simp only [blocks, List.flatten_cons, List.flatten_nil,\n"
                    "        List.map_append, List.map_nil]\n"
                    "    _ = expectedLengths := by\n"
                    "      rw [" + ", ".join(f"block{b:02}_lengths" for b in range(12)) + "]\n\n")
    length_proof = length_type + b" := by\n" + (
        "  have hlist :\n"
        "      (List.ofFn approximations).map List.length =\n"
        "        List.ofFn (fun i : Fin 186 => 512 - firstU i) :=\n"
        "    (congrArg (List.map List.length) approximations_partition).trans\n"
        "      (blocks_lengths.trans firstU_lengths_list.symm)\n"
        "  have hfn : (fun i : Fin 186 => (approximations i).length) =\n"
        "      (fun i : Fin 186 => 512 - firstU i) :=\n"
        "    List.ofFn_injective\n"
        "      ((List.ofFn_comp' approximations List.length).trans hlist)\n"
        "  exact fun i => congrFun hfn i\n\n").encode()
    sources[lengths_name] = ("\n".join(f"import {m}" for m in length_imports) + "\n\n/-! Layered length assembly over symbolic blocks and small Nat tables.\nNo monolithic dependent cases and no whole-data numerical decision. -/\n\n").encode() + options + blocks_proof.encode() + length_proof + f"end {SUM_NS}\n".encode()

    assert len(seen) == len(set(seen)) == 17572 and set(seen) == set(pairs)
    assert sum(s["E0_rows"] for s in strip_manifest) == 6091
    assert sum(s["E1_rows"] for s in strip_manifest) == 11481
    assert sum(int(s["lower_sum"]) for s in strip_manifest) == 55858378943374979
    assert sum(int(s["upper_sum"]) for s in strip_manifest) == 55858409959907296
    assert sum(re.search(rb"(?m)^def approximations\d+ :", source) is not None for path, source in sources.items()) == 12
    all_decl_matches = [int(m) for p, s in sources.items() for m in re.findall(rb"(?m)^def approximations(\d+) :", s)]
    assert sorted(all_decl_matches) == list(range(326, 512))
    for p, source in sources.items():
        assert not re.search(rb"\b(sorry|axiom|native_decide|unsafe|partial|implemented_by)\b", source), p
    report = {
        "schema": "paired-v2-lossless-data-split-v1", "verification_level": "SOURCE_ONLY",
        "baseline_commit": BASE, "static_scope": "Byte-identical named declarations, literal tuple order and values, complete provenance-grid coverage, unchanged selectors and protected sources. No Lean/kernel acceptance.",
        "original_data_sha256": sha(original), "reconstructed_original_data_sha256": sha(prefix + b"".join(d for _, d, _ in defs) + suffix),
        "original_selector_and_approximation_suffix_sha256": sha(suffix),
        "unchanged_files": {p: sha((ROOT / p).read_bytes()) for p in PROTECTED},
        "old_sum_declaration_types_and_numerals_preserved_byte_for_byte": True,
        "sum_proof_control_flow_repair": "Only remove26 redundant decide +kernel lines after closing rw steps:24 across12 block totals and2 in final totals. Retain all186 strip decision proofs.",
        "generic_row_proof_repair": "Add explicit cons-case Fin (xs.length + 1) shape before original rewrite; emitted source hash pinned to P0 strict/replay success.",
        "original_row_list_bridge_types_preserved_byte_for_byte": True,
        "row_list_proof_repairs": "Reverse rewrite the dependent Fin length before the unchanged generic theorem; explicitly specialize ofFn_comp' to the complete row-sum function.",
        "original_partition_declarations_moved_verbatim": ["blocks", "approximations_partition"],
        "new_length_proofs": {"unchanged_individual_rfl_facts": 186, "small_length_blocks": 12, "max_facts_per_length_block": 16, "scalar_firstU_table_size": 186, "finite_cases_assembly": False, "proof": "Exact original partition; symbolic append/map; twelve kernel length-list equalities; ofFn_comp', ofFn_injective, congrFun.", "new_hypotheses": []},
        "coverage": {"strips": 186, "rows": 17572, "E0": 6091, "E1": 11481,
                     "ordered_strip_range": [326, 511], "exact_once_pairs": True, "data_leaves": 12,
                     "max_strips_per_leaf": 16, "max_rows_per_strip": 191,
                     "max_rows_per_data_leaf": max(g["rows"] for g in group_manifest)},
        "normalization": {"denominator": "100000000000000000000", "lower_numerator": "55858378943374979", "upper_numerator": "55858409959907296", "scope": "Existing K/80-normalized adopted fibres, not complete K."},
        "row_map": strip_manifest, "blocks": group_manifest,
        "generated_sources": {p: sha(s) for p, s in sorted(sources.items())},
        "stages": {"static": "PASS", "compilation": "NOT_RUN", "kernel_replay": "NOT_RUN", "audit": "NOT_RUN", "integration": "NOT_RUN"},
    }
    return sources, report


def dependency_report(sources):
    project = {}
    graph = {}
    external = set()

    def visit(mod):
        if mod in graph:
            return
        path = mod.replace(".", "/") + ".lean"
        if path in sources:
            source = sources[path]
        elif (ROOT / path).is_file():
            source = (ROOT / path).read_bytes()
            assert source == git_input(path), f"unchanged project dependency differs: {path}"
        else:
            assert not mod.startswith("ImbalancedChen."), f"missing project source: {mod}"
            external.add(mod)
            return
        project[path] = sha(source)
        imports = re.findall(r"(?m)^import ([A-Za-z0-9_.]+)\s*$", source.decode())
        graph[mod] = imports
        for imported in imports:
            visit(imported)

    for path in sources:
        visit(module(path))

    def closure(mod):
        seen = set()
        pending = [mod]
        while pending:
            head = pending.pop()
            if head in seen:
                continue
            seen.add(head)
            pending.extend(graph.get(head, []))
        return seen

    pilot = {}
    rows_module = module(CERT + "PairedV2NaturalSumRows.lean")
    assert not any("FullCertificateData" in m for m in closure(rows_module))
    for b in range(12):
        target = module(CERT + f"PairedV2NaturalSumsBlock{b:02}.lean")
        data_modules = sorted(m for m in closure(target) if "FullCertificateData" in m)
        assert data_modules == [module(CERT + f"PairedV2FullCertificateDataBlock{b:02}.lean")]
        pilot[target] = data_modules
    material = {"project_source_closure": dict(sorted(project.items())),
                "pin_files": {p: sha((ROOT / p).read_bytes()) for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]},
                "external_module_frontier": sorted(external)}
    return {"schema": "chen-source-dependency-fingerprint-v1", "baseline": BASE,
            "verification_level": "SOURCE_ONLY", **material,
            "fingerprint_sha256": sha(json_bytes(material)),
            "external_pins": json.loads((ROOT / "lake-manifest.json").read_bytes())["packages"],
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "direct_import_graph": dict(sorted(graph.items())),
            "light_rows_data_dependencies": [], "sum_blocks_data_dependencies": pilot,
            "object_binding": "NOT_RUN; P0 must bind exact objects and complete external import closure."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check files without writing or invoking Lean.")
    args = parser.parse_args()
    sources, report = sources_and_report()
    dependencies = dependency_report(sources)
    outputs = {**sources, REPORT: json_bytes(report), DEPENDENCIES: json_bytes(dependencies)}
    for path, raw in outputs.items():
        if args.check:
            assert (ROOT / path).read_bytes() == raw, f"deterministic output mismatch: {path}"
        else:
            (ROOT / path).write_bytes(raw)
    print(json.dumps({"status": "PASS_STATIC_ONLY", "lean": "NOT_RUN", "modules": len(sources),
                      "coverage": report["coverage"], "manifest_sha256": sha(outputs[REPORT])}))


if __name__ == "__main__":
    main()
