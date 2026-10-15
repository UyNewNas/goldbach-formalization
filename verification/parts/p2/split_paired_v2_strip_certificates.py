#!/usr/bin/env python3
"""Lossless strip-check source split and bounded proof-side Fin assembly.

Only ordinary Python and read-only git show are used. This producer never invokes
Lean, Lake, a checker, an environment audit, CI, installation or publication.
All generated Lean proofs remain candidates until P0 accepts their exact objects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
BASE = "541edd4d626a29bdb4bf7ff5dbef1e9d469057e6"
CERT = "ImbalancedChen/Certificates/"
ORIGINAL = CERT + "PairedV2StripCertificates.lean"
ORIGINAL_SHA = "1b1b9df07b02f151e82c25716df1c95ce9b9fc7f4d846afd4d91f1d6e854c402"
CORE = CERT + "PairedV2StripCertificatesAssemblyCore.lean"
DATA = CERT + "PairedV2FullCertificateData.lean"
NS = "ImbalancedChen.Certificates.PairedV2.FullMask"
DATA_REPORT = "verification/parts/p2/data-split-source-manifest.json"
REPORT = "verification/parts/p2/strip-split-source-manifest.json"
DEPENDENCIES = "verification/parts/p2/strip-split-dependencies.json"
RAW = "verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json"
# Leaves are exactly the pre-existing 16-strip groups, with a final 10-strip leaf.
TREE = (((0, (1, 2)), (3, (4, 5))), ((6, (7, 8)), (9, (10, 11))))


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def json_bytes(value) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()


def git_input(path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)


def module(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def tree_layout():
    leaves = {}
    nodes = []

    def size(t):
        return (10 if t == 11 else 16) if isinstance(t, int) else size(t[0]) + size(t[1])

    def walk(t, expr="k", path="", offset=0):
        n = size(t)
        if isinstance(t, int):
            assert offset == 16 * t
            leaf = {"block": t, "path": path, "size": n, "offset": offset,
                    "embedding": expr, "absolute_ordinals": list(range(offset, offset + n))}
            leaves[t] = leaf
            return t, t
        m, r = size(t[0]), size(t[1])
        le = re.sub(r"\bk\b", f"(Fin.castAdd {r} k)", expr)
        re_ = re.sub(r"\bk\b", f"(Fin.natAdd {m} k)", expr)
        lf, ll = walk(t[0], le, path + "L", offset)
        rf, rl = walk(t[1], re_, path + "R", offset + m)
        assert ll + 1 == rf
        name = "allStrips_checked" if path == "" else f"checkedBlocks{lf:02}_{rl:02}"
        child_name = lambda first, last: (f"stripBlock{first:02}_checked" if first == last
                                         else f"checkedBlocks{first:02}_{last:02}")
        nodes.append({"path": path, "size": n, "left_size": m, "right_size": r,
                      "offset": offset, "embedding": expr, "first_block": lf,
                      "last_block": rl, "theorem": name,
                      "left_theorem": child_name(lf, ll), "right_theorem": child_name(rf, rl)})
        return lf, rl

    assert size(TREE) == 186
    assert walk(TREE) == (0, 11)
    assert len(leaves) == 12 and len(nodes) == 11
    assert max(len(v["path"]) for v in leaves.values()) == 4
    assert [i for b in range(12) for i in leaves[b]["absolute_ordinals"]] == list(range(186))
    return leaves, nodes


def original_declarations(original: bytes):
    assert sha(original) == ORIGINAL_SHA
    matches = list(re.finditer(rb"(?m)^theorem strip(\d+)_checked :", original))
    assert [int(m[1]) for m in matches] == list(range(326, 512))
    aggregate_start = original.index(b"theorem strip_certificates_checked")
    footer_start = original.index(f"end {NS}\n".encode(), aggregate_start)
    prefix = original[:matches[0].start()]
    chunks = []
    for j, match in enumerate(matches):
        stop = matches[j + 1].start() if j + 1 < len(matches) else aggregate_start
        raw = original[match.start():stop]
        k = int(match[1])
        assert raw.count(b"decide +kernel") == 1
        assert raw.endswith(b" := by\n  decide +kernel\n\n")
        indices = re.findall(rb"\(\xe2\x9f\xa8(\d+), by decide\xe2\x9f\xa9 : Fin 186\)", raw)
        assert list(map(int, indices)) == [k - 326] * 3
        assert original[:match.start()].count(b"\n") + 1 == 11 + 4 * (k - 326)
        chunks.append((k, raw, match.start()))
    aggregate = original[aggregate_start:footer_start]
    assert re.findall(rb"exact strip(\d+)_checked j", aggregate) == [str(i).encode() for i in range(326, 512)]
    footer = original[footer_start:]
    assert prefix + b"".join(c[1] for c in chunks) + aggregate + footer == original
    return prefix, chunks, aggregate, footer


def emit_sources():
    original = git_input(ORIGINAL)
    prefix, chunks, aggregate, footer = original_declarations(original)
    frozen_data = json.loads(git_input(DATA_REPORT))
    frozen43 = frozen_data["generated_sources"]
    assert len(frozen43) == 43
    for path, digest in frozen43.items():
        actual = (ROOT / path).read_bytes()
        assert sha(actual) == digest and actual == git_input(path), f"frozen43 changed: {path}"
    protected = {}
    for path, digest in frozen_data["unchanged_files"].items():
        if path == ORIGINAL:
            assert digest == ORIGINAL_SHA
            continue
        actual = (ROOT / path).read_bytes()
        assert sha(actual) == digest and actual == git_input(path), f"protected input changed: {path}"
        protected[path] = digest
    assert len(protected) == 8
    raw = json.loads((ROOT / RAW).read_bytes())
    pairs = {(r[1], r[2]): r for r in raw["rows"]}
    assert len(pairs) == len(raw["rows"]) == 17572
    rows = frozen_data["row_map"]
    assert [s["strip"] for s in rows] == list(range(326, 512))
    covered = [(s["strip"], j) for s in rows for j in range(s["first_u"], 512)]
    assert len(covered) == len(set(covered)) == 17572 and set(covered) == set(pairs)
    assert all(s["row_count"] == 512 - s["first_u"] for s in rows)
    assert sum(pairs[p][0] == "E0" for p in covered) == 6091
    assert sum(pairs[p][0] == "E1" for p in covered) == 11481
    leaves, nodes = tree_layout()
    context = prefix[prefix.index(f"namespace {NS}\n".encode()):]
    old_import = f"import {module(DATA)}\n".encode()
    assert prefix.startswith(old_import)
    sources = {}
    core = (f"import {module(DATA)}\n\n"
            "/-! Proof-side embeddings and a two-branch composition lemma only.\n"
            "The actual Row, approximation, selector and checker are unchanged. -/\n\n").encode() + context
    core += ("namespace StripAssembly\n\n"
             "abbrev StripChecked (i : Fin 186) : Prop :=\n"
             "  ∀ j : Fin (512 - firstU i),\n"
             "    (makeCertificate (⟨i, j⟩ : Row)\n"
             "      (approximation (⟨i, j⟩ : Row))).check = true\n\n"
             "theorem joinChecked {m n : ℕ} (e : Fin (m + n) → Fin 186)\n"
             "    (left : ∀ k : Fin m, StripChecked (e (Fin.castAdd n k)))\n"
             "    (right : ∀ k : Fin n, StripChecked (e (Fin.natAdd m k))) :\n"
             "    ∀ k : Fin (m + n), StripChecked (e k) :=\n"
             "  Fin.addCases (motive := fun k => StripChecked (e k)) left right\n\n").encode()
    for b in range(12):
        info = leaves[b]
        core += (f"/-- Proof-side embedding for original strips {326 + info['offset']}–{325 + info['offset'] + info['size']}. -/\n"
                 f"abbrev indexBlock{b:02} (k : Fin {info['size']}) : Fin 186 :=\n"
                 f"  {info['embedding']}\n\n").encode()
    core += b"end StripAssembly\n\n" + footer
    sources[CORE] = core
    declaration_map = []
    blocks = []
    for b in range(12):
        info = leaves[b]
        path = CERT + f"PairedV2StripCertificatesBlock{b:02}.lean"
        group = chunks[16 * b:16 * b + info["size"]]
        leaf_prefix = prefix.replace(old_import, f"import {module(CORE)}\n".encode(), 1)
        source = leaf_prefix + b"".join(c[1] for c in group)
        source += (f"/-- Bounded composition of the original strip checks, with no new check assumption. -/\n"
                   f"theorem stripBlock{b:02}_checked (k : Fin {info['size']}) :\n"
                   f"    StripAssembly.StripChecked (StripAssembly.indexBlock{b:02} k) := by\n"
                   "  fin_cases k\n").encode()
        source += b"".join(f"  · exact strip{k}_checked\n".encode() for k, _, _ in group)
        source += b"\n" + footer
        assert source[source.index(f"namespace {NS}\n".encode()):].startswith(context)
        for k, declaration, offset in group:
            pos = source.index(declaration)
            assert source.count(declaration) == 1
            assert source[pos:pos + len(declaration)] == declaration
            statement, body = declaration.split(b" := by\n", 1)
            declaration_map.append({"declaration": f"{NS}.strip{k}_checked", "strip": k,
                                    "ordinal": k - 326, "block": b, "old_file": ORIGINAL,
                                    "new_file": path, "old_line_start": original[:offset].count(b"\n") + 1,
                                    "old_line_end": original[:offset + len(declaration.rstrip())].count(b"\n") + 1,
                                    "new_line_start": source[:pos].count(b"\n") + 1,
                                    "new_line_end": source[:pos + len(declaration.rstrip())].count(b"\n") + 1,
                                    "bytes": len(declaration), "old_sha256": sha(declaration),
                                    "new_sha256": sha(source[pos:pos + len(declaration)]),
                                    "type_sha256": sha(statement), "proof_body_sha256": sha(body),
                                    "first_u": rows[k - 326]["first_u"], "rows": rows[k - 326]["row_count"]})
        sources[path] = source
        blocks.append({**info, "tree_path": info["path"], "path": path, "first_strip": group[0][0], "last_strip": group[-1][0],
                       "rows": sum(rows[k - 326]["row_count"] for k, _, _ in group),
                       "verbatim_declarations_sha256": sha(b"".join(c[1] for c in group)),
                       "original_context_sha256": sha(context),
                       "leaf_original_context_sha256": sha(source[source.index(context):source.index(context) + len(context)]),
                       "source_theorem_heads": len(group) + 1,
                       "actual_compiler_inventory": "NOT_RUN; include private/generated declarations"})
    imports = f"import {module(CORE)}\n" + "".join(f"import {module(CERT + f'PairedV2StripCertificatesBlock{b:02}.lean')}\n" for b in range(12))
    wrapper = imports.encode() + prefix[len(old_import):]
    for node in nodes:
        result = f"StripAssembly.StripChecked ({node['embedding']})"
        wrapper += (f"/-- Two-branch proof composition for original strip blocks {node['first_block']:02}–{node['last_block']:02}. -/\n"
                    f"theorem {node['theorem']} : ∀ k : Fin {node['size']}, {result} := by\n"
                    f"  exact StripAssembly.joinChecked (m := {node['left_size']}) (n := {node['right_size']})\n"
                    f"    (fun k : Fin {node['size']} => {node['embedding']})\n"
                    f"    {node['left_theorem']} {node['right_theorem']}\n\n").encode()
    aggregate_header = aggregate.split(b" := by\n", 1)[0]
    wrapper += aggregate_header + b" := by\n  exact allStrips_checked i j\n\n" + footer
    sources[ORIGINAL] = wrapper
    assert len(sources) == 14
    assert wrapper.count(aggregate_header) == 1
    all_checked = [int(n) for s in sources.values() for n in re.findall(rb"(?m)^theorem strip(\d+)_checked :", s)]
    assert sorted(all_checked) == list(range(326, 512))
    assert sum(s.count(b"  decide +kernel\n") for s in sources.values()) == 186
    assert b"fin_cases i" not in wrapper and b"fin_cases" not in core
    assert sum(s.count(b"  fin_cases k\n") for s in sources.values()) == 12
    assert not any(re.search(rb"\b(sorry|axiom|native_decide|unsafe|partial|implemented_by)\b", s) for s in sources.values())
    reconstructed = prefix + b"".join(sources[e["new_file"]][sources[e["new_file"]].index(c[1]):sources[e["new_file"]].index(c[1]) + len(c[1])] for e, c in zip(declaration_map, chunks)) + aggregate + footer
    assert reconstructed == original
    report = {"schema": "p2-lossless-strip-proof-split-v1", "verification_level": "SOURCE_ONLY",
              "baseline": BASE, "original_file": ORIGINAL, "original_source_sha256": ORIGINAL_SHA,
              "reconstructed_original_source_sha256": sha(reconstructed), "original_namespace_options_sha256": sha(context),
              "public_aggregate_type_sha256": sha(aggregate_header), "original_aggregate_sha256": sha(aggregate),
              "original_aggregate_replaced_only_by_closed_proof_composition": True,
              "declarations": declaration_map, "blocks": blocks, "composition_nodes_postorder": nodes,
              "tree": {"binary_nodes": 11, "leaves": 12, "maximum_binary_depth": 4,
                       "maximum_local_fin_cases": 16, "ordered_ordinals": list(range(186)),
                       "no_global_fin186_enumeration": True, "all_children_bound_to_original_checks": True},
              "coverage": {"strips": 186, "rows": 17572, "E0": 6091, "E1": 11481,
                           "pairs_exactly_once": True, "pair_stream_sha256": sha(json_bytes(covered))},
              "frozen43_generated_sources": frozen43, "other_protected_inputs": protected,
              "generated_sources": {p: sha(s) for p, s in sorted(sources.items())},
              "proof_scope": "Original actual Row/approximation/checks only. No new selector, denominator, data, row, checked hypothesis or integral theorem. Generic join inputs are discharged by closed child proofs.",
              "acceptance": "NOT_RUN. Historical compile-only evidence and current prerequisite acceptance retain their original limited scopes."}
    return sources, report


def verify_current_sources(expected_original: bytes | None = None):
    """Joint replacement for the original monolithic byte-protection check.

    Check each old declaration independently, reconstruct the entire old source,
    and demand byte equality of every new core/leaf/wrapper, not just same values.
    This function is read-only and does not depend on either generated report.
    """
    if expected_original is not None:
        assert expected_original == git_input(ORIGINAL)
    sources, report = emit_sources()
    actual_sources = {path: (ROOT / path).read_bytes() for path in sources}
    for path, expected in sources.items():
        assert actual_sources[path] == expected, f"strip split source differs: {path}"
    original = git_input(ORIGINAL)
    prefix, chunks, aggregate, footer = original_declarations(original)
    actual_declarations = []
    for entry, (k, original_declaration, _) in zip(report["declarations"], chunks):
        leaf = actual_sources[entry["new_file"]]
        assert entry["strip"] == k and leaf.count(original_declaration) == 1
        start = leaf.index(original_declaration)
        actual_declaration = leaf[start:start + entry["bytes"]]
        assert actual_declaration == original_declaration
        assert sha(actual_declaration) == entry["old_sha256"] == entry["new_sha256"]
        actual_declarations.append(actual_declaration)
    assert prefix + b"".join(actual_declarations) + aggregate + footer == original
    return {"mode": "lossless_split_joint_protection", "original_file": ORIGINAL,
            "original_source_sha256": report["original_source_sha256"],
            "reconstructed_original_source_sha256": report["reconstructed_original_source_sha256"],
            "original_declarations_compared_individually": 186,
            "namespace_options_preserved": True, "public_aggregate_type_sha256": report["public_aggregate_type_sha256"],
            "exact_generated_sources": report["generated_sources"],
            "protects": "Every original declaration byte plus original-file reconstruction and exact deterministic core/leaves/wrapper; no removed protection."}


def dependency_report(sources):
    project, graph, external = {}, {}, set()

    def visit(mod):
        if mod in graph:
            return
        path = mod.replace(".", "/") + ".lean"
        if path in sources:
            raw = sources[path]
        elif (ROOT / path).is_file():
            raw = (ROOT / path).read_bytes()
            assert raw == git_input(path), f"unchanged dependency changed: {path}"
        else:
            assert not mod.startswith("ImbalancedChen."), f"missing project module: {mod}"
            external.add(mod)
            return
        project[path] = sha(raw)
        graph[mod] = re.findall(r"(?m)^import ([A-Za-z0-9_.]+)\s*$", raw.decode())
        for dep in graph[mod]:
            visit(dep)

    visit(module(ORIGINAL))
    def closure(m):
        result, todo = set(), [m]
        while todo:
            head = todo.pop()
            if head not in result:
                result.add(head)
                todo.extend(graph.get(head, []))
        return result
    leaf_closures = {}
    for b in range(12):
        name = module(CERT + f"PairedV2StripCertificatesBlock{b:02}.lean")
        reachable = closure(name)
        data = sorted(m for m in reachable if "PairedV2FullCertificateData" in m)
        assert data == sorted([module(DATA)] + [module(CERT + f"PairedV2FullCertificateDataBlock{i:02}.lean") for i in range(12)])
        assert not any("PairedV2NaturalSum" in m for m in reachable)
        assert [m for m in reachable if re.search(r"PairedV2StripCertificatesBlock\d+$", m)] == [name]
        leaf_closures[name] = {"project_modules": sorted(m for m in reachable if m in graph), "data_modules": data}
    def acyclic(m, active, done):
        if m in done or m not in graph:
            return
        assert m not in active, f"import cycle: {m}"
        for d in graph[m]:
            acyclic(d, active | {m}, done)
        done.add(m)
    acyclic(module(ORIGINAL), set(), set())
    pins = {p: sha((ROOT / p).read_bytes()) for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]}
    material = {"project_source_closure": dict(sorted(project.items())), "pin_files": pins,
                "external_module_frontier": sorted(external)}
    return {"schema": "p2-strip-split-source-dependencies-v1", "verification_level": "SOURCE_ONLY", "baseline": BASE,
            **material, "fingerprint_sha256": sha(json_bytes(material)), "direct_import_graph": dict(sorted(graph.items())),
            "leaf_closures": leaf_closures, "graph_acyclic": True,
            "external_pins": json.loads((ROOT / "lake-manifest.json").read_bytes())["packages"],
            "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "object_binding": "NOT_RUN. All check leaves require the actual common FullData object and its twelve data leaves. P0 must bind exact transitive objects and audit moved/private/generated declarations."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Read-only deterministic source and manifest check.")
    args = parser.parse_args()
    sources, report = emit_sources()
    deps = dependency_report(sources)
    outputs = {**sources, REPORT: json_bytes(report), DEPENDENCIES: json_bytes(deps)}
    for path, raw in outputs.items():
        if args.check:
            assert (ROOT / path).read_bytes() == raw, f"deterministic strip output mismatch: {path}"
        else:
            (ROOT / path).write_bytes(raw)
    verify_current_sources(expected_original=git_input(ORIGINAL))
    print(json.dumps({"status": "PASS_STATIC_ONLY", "lean": "NOT_RUN", "modules": len(sources),
                      "original_declarations": len(report["declarations"]), "coverage": report["coverage"],
                      "max_binary_depth": 4, "source_manifest_sha256": sha(outputs[REPORT])}))


if __name__ == "__main__":
    main()
