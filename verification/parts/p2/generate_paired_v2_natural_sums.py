#!/usr/bin/env python3
"""Generate source-only exhaustive natural sums from unchanged paired-v2 witnesses.

This producer and its static report are not mathematical proof receipts. Each
strip sum is an ordinary-kernel Lean obligation over the frozen original list.
Use --check to verify determinism and source/data/partition identity without Lean.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
CERT = Path("ImbalancedChen/Certificates")
DATA = CERT / "PairedV2FullCertificateData.lean"
MASK = CERT / "PairedV2FullMaskData.lean"
RAW = Path("verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json")
PINS = {
    str(DATA): "a059e969139810aa89516661609b540968efbf6b1e2c2ab975a8262ce8462309",
    str(MASK): "19bcfe8f9524fa93fbe3d8eb5f95653c40384655b3eab69f914211e63bdf2f5a",
    str(RAW): "f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7",
}
NS = "ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums"
HEADER = """/-! Exhaustive natural-number endpoint sums, generated from unchanged witnesses.
The source generator is untrusted. Acceptance requires P0's Lean/kernel gates.
A strip is the largest numerical reduction: at most 191 rows. No checker is
rerun here, no Q160 value is substituted, and no native evaluator is trusted. -/
"""
OPTIONS = f"\nnamespace {NS}\n\nopen scoped BigOperators\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
FOOTER = f"\nend {NS}\n"

ROWS = """import ImbalancedChen.Certificates.PairedV2FullCertificateData
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-! The finite-row/list bridge does not evaluate numerical endpoints.
The length equality rules out the fallback branch of `getD` for every adopted
row. The existing `Row` sigma type still determines exact once-only coverage. -/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem approximation_lengths : ∀ i : Fin 186,
    (approximations i).length = 512 - firstU i := by
  decide +kernel

theorem sum_getD_eq_map (xs : List Approximation) (f : Approximation → ℕ) :
    (∑ j : Fin xs.length, f (xs.getD j.val default)) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [Fin.sum_univ_succ]
    change f x + (∑ j : Fin xs.length, f (xs.getD j.val default)) =
      f x + (xs.map f).sum
    rw [ih]

theorem strip_sum_eq_map (i : Fin 186) (f : Approximation → ℕ) :
    (∑ j : Fin (512 - firstU i), f (approximation ⟨i, j⟩)) =
      ((approximations i).map f).sum := by
  change (∑ j : Fin (512 - firstU i),
    f ((approximations i).getD j.val default)) = _
  simpa only [approximation_lengths i] using sum_getD_eq_map (approximations i) f

theorem sum_rows_eq_list (f : Approximation → ℕ) :
    (∑ r : Row, f (approximation r)) =
      ((List.ofFn approximations).map (fun xs => (xs.map f).sum)).sum := by
  rw [Fintype.sum_sigma]
  simp_rw [strip_sum_eq_map]
  rw [← List.sum_ofFn, List.ofFn_comp']

end ImbalancedChen.Certificates.PairedV2.FullMask.NaturalSums
"""


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def read_inputs():
    for path, expected in PINS.items():
        assert sha((ROOT / path).read_bytes()) == expected, f"frozen input changed: {path}"
    raw = json.loads((ROOT / RAW).read_text())
    pairs = {(r[1], r[2]): r for r in raw["rows"]}
    assert len(raw["rows"]) == len(pairs) == 17572
    first_u = list(map(int, re.search(r"!\[([^\]]+)\]", (ROOT / MASK).read_text()).group(1).split(",")))
    assert len(first_u) == 186
    text = (ROOT / DATA).read_text()
    parsed = re.findall(r"def approximations(\d+) : List Approximation :=\s*\[\s*(.*?)\s*\]", text, re.S)
    assert [int(k) for k, _ in parsed] == list(range(326, 512))
    strips = []
    seen = []
    for k_text, body in parsed:
        k = int(k_text)
        witnesses = [tuple(map(int, r.split(","))) for r in re.findall(r"⟨([^⟩]+)⟩", body)]
        assert all(len(r) == 8 and all(v >= 0 for v in r) and r[6] <= r[7] for r in witnesses)
        assert len(witnesses) == 512 - first_u[k - 326]
        assert not re.sub(r"⟨[^⟩]+⟩|[\s,]", "", body)
        expected_pairs = [(k, j) for j in range(first_u[k - 326], 512)]
        assert all(p in pairs for p in expected_pairs)
        seen.extend(expected_pairs)
        strips.append({"t_index": k, "first_u": first_u[k - 326], "rows": len(witnesses),
                       "lower": sum(r[6] for r in witnesses), "upper": sum(r[7] for r in witnesses),
                       "E0_rows": sum(pairs[p][0] == "E0" for p in expected_pairs),
                       "E1_rows": sum(pairs[p][0] == "E1" for p in expected_pairs)})
    assert len(seen) == len(set(seen)) == 17572 and set(seen) == set(pairs)
    assert sum(s["E0_rows"] for s in strips) == 6091
    assert sum(s["E1_rows"] for s in strips) == 11481
    assert sum(s["lower"] for s in strips) == 55858378943374979
    assert sum(s["upper"] for s in strips) == 55858409959907296
    return strips


def emit_sources(strips):
    emitted = {CERT / "PairedV2NaturalSumRows.lean": ROWS}
    blocks = [strips[k:k + 16] for k in range(0, len(strips), 16)]
    for b, group in enumerate(blocks):
        name = f"block{b:02}"
        lines = ["import ImbalancedChen.Certificates.PairedV2FullCertificateData", "", HEADER, OPTIONS]
        lines += [f"def {name} : List (List Approximation) :=", "  [" + ", ".join(f"approximations{s['t_index']}" for s in group) + "]", ""]
        for s in group:
            k = s["t_index"]
            lines += [f"theorem strip{k}_sums :", f"    (approximations{k}.map Approximation.lower).sum = {s['lower']} ∧",
                      f"      (approximations{k}.map Approximation.upper).sum = {s['upper']} := by", "  decide +kernel", ""]
        for field, projection in [("lower", 1), ("upper", 2)]:
            total = sum(s[field] for s in group)
            terms = [f"(approximations{s['t_index']}.map Approximation.{field}).sum" for s in group]
            expression = " + (".join(terms) + " + 0" + ")" * (len(terms) - 1)
            lines += [f"theorem {name}_{field} :", f"    ({name}.map (fun xs => (xs.map Approximation.{field}).sum)).sum = {total} := by",
                      f"  change {expression} = {total}",
                      "  rw [" + ", ".join(f"strip{s['t_index']}_sums.{projection}" for s in group) + "]", "  decide +kernel", ""]
        lines += [FOOTER]
        emitted[CERT / f"PairedV2NaturalSumsBlock{b:02}.lean"] = "\n".join(lines)
    lines = ["import ImbalancedChen.Certificates.PairedV2NaturalSumRows"]
    lines += [f"import ImbalancedChen.Certificates.PairedV2NaturalSumsBlock{b:02}" for b in range(len(blocks))]
    lines += ["", HEADER, OPTIONS,
              "/-- All 186 strips in their original order, grouped only for proof assembly. -/",
              "def blocks : List (List (List Approximation)) :=",
              "  [" + ", ".join(f"block{b:02}" for b in range(len(blocks))) + "]", "",
              "/-- Definitional identity, with no numerical or source-ordinal sampling. -/",
              "theorem approximations_partition : List.ofFn approximations = blocks.flatten := by", "  rfl", ""]
    for field in ["lower", "upper"]:
        total = sum(s[field] for s in strips)
        lines += [f"/-- Exact numerator sum over every `FullMask.Row`, at the unchanged 10^20 scale. -/",
                  f"theorem {field}_numerator_sum :", f"    (∑ r : Row, (approximation r).{field}) = {total} := by",
                  "  rw [sum_rows_eq_list, approximations_partition]",
                  "  simp only [blocks, List.flatten_cons, List.flatten_nil, List.map_append,",
                  "    List.map_nil, List.sum_append, List.sum_nil]",
                  "  rw [" + ", ".join(f"block{b:02}_{field}" for b in range(len(blocks))) + "]",
                  "  decide +kernel", ""]
    lines += [FOOTER]
    emitted[CERT / "PairedV2NaturalSums.lean"] = "\n".join(lines)
    return emitted, blocks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check existing sources; write no files.")
    args = parser.parse_args()
    strips = read_inputs()
    sources, blocks = emit_sources(strips)
    report = {
        "schema": "paired-v2-natural-sums-source-v1", "verification_level": "SOURCE_ONLY",
        "static_scope": "Frozen input hashes, exact once-only pair coverage, group preservation, natural arithmetic, deterministic emission. No Lean/compiler/kernel verification.",
        "inputs": PINS, "rows": 17572, "strips": 186, "E0_rows": 6091, "E1_rows": 11481,
        "block_count": len(blocks), "maximum_strips_per_block": 16,
        "maximum_rows_per_numerical_kernel_reduction": max(s["rows"] for s in strips),
        "lower_numerator": "55858378943374979", "upper_numerator": "55858409959907296",
        "denominator": "100000000000000000000",
        "normalization": "Existing makeCertificate lower/upper divide these natural endpoints by 10^20. The existing local integral contains K/80; these are not bounds on the complete K coefficient.",
        "directed_witnesses": "Unchanged independently rounded natural witnesses from FullCertificateData. Original Q160 endpoints remain provenance only.",
        "strips_manifest": strips,
        "blocks_manifest": [{"name": f"block{b:02}", "first_strip": group[0]["t_index"],
                             "last_strip": group[-1]["t_index"], "rows": sum(s["rows"] for s in group),
                             "lower": str(sum(s["lower"] for s in group)),
                             "upper": str(sum(s["upper"] for s in group))} for b, group in enumerate(blocks)],
        "generated_sources": {str(path): sha(body.encode()) for path, body in sources.items()},
    }
    for path, body in sources.items():
        if args.check:
            assert (ROOT / path).read_bytes() == body.encode(), f"generated source mismatch: {path}"
        else:
            (ROOT / path).write_text(body, encoding="utf-8", newline="\n")
    report_path = ROOT / "verification/parts/p2/natural-sums-source-manifest.json"
    report_bytes = (json.dumps(report, indent=2, ensure_ascii=False) + "\n").encode()
    if args.check:
        assert report_path.read_bytes() == report_bytes, "static manifest mismatch"
    else:
        report_path.write_bytes(report_bytes)
    print(json.dumps({"status": "STATIC_SOURCE_CHECK_PASS", "lean_status": "NOT_RUN",
                      "generated_modules": len(sources), "rows": report["rows"], "strips": report["strips"],
                      "blocks": len(blocks), "manifest_sha256": sha(report_bytes)}))


if __name__ == "__main__":
    main()
