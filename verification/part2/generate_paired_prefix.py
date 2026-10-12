#!/usr/bin/env python3
"""Emit an exact adopted E0 prefix and its proof-producing Lean checks.

The source hash binds every row to the frozen full witness. Python suggests
independent rational logarithm enclosures; only successful Lean compilation
and kernel replay certify the integral bounds. No stored Q160 endpoint is
used to justify a new numerical enclosure.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

from import_paired_v2 import (
    A, H, D, K, SOURCE_COMMIT, SOURCE_PATH, SOURCE_BLOB, SOURCE_SHA256,
    EXPECTED_COLUMNS, LOG_SCALE, CELL_SCALE, coordinates, rational_log_bounds,
    floor, ceil, lean_rat,
)


def lookup(name: str, typ: str, values: list[str], count: int) -> list[str]:
    lines = [f"def {name} (i : Fin {count}) : {typ} :=", "  match i.val with"]
    lines += [f"  | {i} => {value}" for i, value in enumerate(values[:-1])]
    lines += [f"  | _ => {values[-1]}", ""]
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--count", type=int, default=4)
    parser.add_argument("--emit-dir", type=Path)
    parser.add_argument("--check-generated", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if not 1 <= args.count <= 6091:
        raise SystemExit("The E0 prefix count must be between 1 and 6091.")
    raw = args.source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA256
    assert hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest() == SOURCE_BLOB
    source = json.loads(raw)
    assert source["row_columns"] == EXPECTED_COLUMNS
    assert source["omega_argument_threshold"] == "7/3"
    assert source["omega_lower"] == "11/20" and Q(source["K"]) == K
    assert len(source["rows"]) == 17572
    rows = source["rows"][:args.count]
    decoded = []
    for ordinal, row in enumerate(rows):
        group, i, j, ztext, lost, stored_lo, stored_hi = row
        assert group == "E0" and int(lost) == 0
        assert type(i) is int and type(j) is int and 0 <= i < 512 and 0 <= j < 512
        tl, tr, ul, ur = coordinates(i, j)
        z = Q(ztext)
        assert z == min(ul, 3 * (1 - tr - ur) / 13)
        assert 0 < A < z <= ul < ur <= H < tl < tr <= D
        assert Q(57, 64) - Q(5, 2) * tl - ul <= 2 * A
        log_t = rational_log_bounds(tr / tl, 1)
        log_u = rational_log_bounds(ur / ul, 1)
        log_z = rational_log_bounds(z / A, 6)
        bracket_lo, bracket_hi = 1 / A - (1 + log_z[1]) / z, 1 / A - (1 + log_z[0]) / z
        assert log_t[0] >= 0 and log_u[0] >= 0 and bracket_lo >= 0
        lower = Q(floor(K / 80 * log_t[0] * log_u[0] * bracket_lo * CELL_SCALE), CELL_SCALE)
        upper = Q(ceil(K / 80 * log_t[1] * log_u[1] * bracket_hi * CELL_SCALE), CELL_SCALE)
        decoded.append(dict(ordinal=ordinal, i=i, j=j, z=z, tl=tl, tr=tr, ul=ul, ur=ur,
                            log_t=log_t, log_u=log_u, log_z=log_z, lower=lower, upper=upper))
    assert len({(r["i"], r["j"]) for r in decoded}) == args.count
    stream = "".join(",".join(map(str, row)) + "\n" for row in rows).encode()
    prefix_digest = hashlib.sha256(stream).hexdigest()
    lower_total = sum((r["lower"] for r in decoded), Q(0))
    upper_total = sum((r["upper"] for r in decoded), Q(0))
    count = args.count
    namespace = f"ImbalancedChen.Certificates.PairedV2.Prefix{count}"
    stem = f"PairedV2Prefix{count}"
    lines = ["import ImbalancedChen.Certificates.PairedV2Data", "", "/-!",
             "Deterministic adopted-source import. Regenerate with",
             f"`verification/part2/generate_paired_prefix.py --count {count}`.",
             f"Frozen manuscript: {SOURCE_COMMIT}", f"Original source: {SOURCE_PATH}",
             f"Original SHA256: {SOURCE_SHA256}", f"Original git blob: {SOURCE_BLOB}",
             f"Selected source ordinals: 0..{count - 1}; all E0, all discarded Q80 = 0.",
             f"Selected row stream SHA256: {prefix_digest}",
             "The stored Q160 bounds are provenance in the source/report, not proof premises.",
             "-/", "", f"namespace {namespace}", ""]
    lines += lookup("rowIndices", "ℕ × ℕ", [f"({r['i']}, {r['j']})" for r in decoded], count)
    lines += lookup("rowZ", "ℚ", [lean_rat(r["z"]) for r in decoded], count)
    lines += [f"def rowOrdinal (i : Fin {count}) : ℕ := i.val", ""]
    for r in decoded:
        n = r["ordinal"]
        lines += [f"def certificate{n:04d} : PairedIntegralCertificate where",
                  "  K := K", "  a := a", f"  tl := tLower {r['i']}",
                  f"  tr := tUpper {r['i']}", f"  ul := uLower {r['j']}",
                  f"  ur := uUpper {r['j']}", f"  Z := {lean_rat(r['z'])}"]
        for label, q, terms, bounds in [
                ("T", r["tr"] / r["tl"], 1, r["log_t"]),
                ("U", r["ur"] / r["ul"], 1, r["log_u"]),
                ("Z", r["z"] / A, 6, r["log_z"])]:
            lines += [f"  log{label} :=", f"    {{ argument := {lean_rat(q)}",
                      f"      terms := {terms}", f"      lower := {lean_rat(bounds[0])}",
                      f"      upper := {lean_rat(bounds[1])} }}"]
        lines += [f"  lower := {lean_rat(r['lower'])}", f"  upper := {lean_rat(r['upper'])}", ""]
    lines += lookup("certificates", "PairedIntegralCertificate",
                    [f"certificate{r['ordinal']:04d}" for r in decoded], count)
    lines += [f"def lowerBound : ℚ := {lean_rat(lower_total)}",
              f"def upperBound : ℚ := {lean_rat(upper_total)}", "", f"end {namespace}", ""]
    data_text = "\n".join(lines)
    unfold_checks = [
        "PairedIntegralCertificate.check", "PairedIntegralCertificate.Valid",
        "RationalLogCertificate.check", "RationalLogCertificate.Valid",
        "PairedIntegralCertificate.productLower", "PairedIntegralCertificate.productUpper",
        "PairedIntegralCertificate.bracketLower", "PairedIntegralCertificate.bracketUpper",
        "logSeriesLower", "logSeriesUpper", "logParameter", "Finset.sum_range_succ",
        "tLower", "tUpper", "uLower", "uUpper", "a", "h", "d", "mu", "K",
    ]
    defs = ", ".join(f"certificate{n:04d}" for n in range(count))
    proof = [f"import ImbalancedChen.Certificates.{stem}Data",
             "import ImbalancedChen.Certificates.PairedV2Geometry", "", "/-!",
             f"Actual first {count} adopted E0 cells. Each numerical check has its own",
             "proof term, then the accepted checker bounds the sum of real integrals.",
             "This prefix includes row 0; it is not an additional gain to add to row 0.",
             "The finite sum is not asserted equal to the full mask or to a union integral.",
             "-/", "", f"namespace {namespace}", "", "open MeasureTheory Set",
             "open scoped BigOperators Interval", ""]
    for n in range(count):
        proof += [f"theorem row{n:04d}_checked : certificate{n:04d}.check = true := by",
                  "  norm_num [" + ", ".join([f"certificate{n:04d}"] + unfold_checks) + "]", ""]
    proof += [f"theorem certificates_checked (i : Fin {count}) : (certificates i).check = true := by",
              "  fin_cases i"]
    proof += [f"  · exact row{n:04d}_checked" for n in range(count)]
    proof += ["", f"theorem geometry_checked (i : Fin {count}) :",
              "    E0Geometry (rowIndices i).1 (rowIndices i).2 (rowZ i) := by",
              "  fin_cases i <;>",
              "    norm_num [E0Geometry, rowIndices, rowZ, tLower, tUpper, uLower, uUpper, a, h, d, mu]", "",
              f"theorem certificate_inputs (i : Fin {count}) :",
              "    (certificates i).K = K ∧ (certificates i).a = a ∧",
              "      (certificates i).tl = tLower (rowIndices i).1 ∧",
              "      (certificates i).tr = tUpper (rowIndices i).1 ∧",
              "      (certificates i).ul = uLower (rowIndices i).2 ∧",
              "      (certificates i).ur = uUpper (rowIndices i).2 ∧",
              "      (certificates i).Z = rowZ i := by",
              "  fin_cases i <;> norm_num [certificates, rowIndices, rowZ, " + defs + "]", "",
              f"theorem fibre_argument (i : Fin {count}) {{t u z w : ℝ}}",
              "    (hs : openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w) :",
              "    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧",
              "      (h : ℝ) < t ∧ t < (d : ℝ) ∧",
              "      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z :=",
              "  (geometry_checked i).fibre_argument hs", "",
              f"theorem fibre_nonempty (i : Fin {count}) :",
              "    ∃ t u z w : ℝ, openFibreSupport (rowIndices i).1 (rowIndices i).2 (rowZ i) t u z w :=",
              "  (geometry_checked i).fibre_nonempty", "",
              f"noncomputable def rowIntegral (i : Fin {count}) : ℝ :=",
              "  pairedLocalIntegral (K : ℝ) a (tLower (rowIndices i).1)",
              "    (tUpper (rowIndices i).1) (uLower (rowIndices i).2)",
              "    (uUpper (rowIndices i).2) (rowZ i)", "",
              f"noncomputable def integral : ℝ := ∑ i : Fin {count}, rowIntegral i", "",
              f"theorem rowIntegral_eq_certificate (i : Fin {count}) :",
              "    rowIntegral i = pairedLocalIntegral ((certificates i).K : ℝ)",
              "      (certificates i).a (certificates i).tl (certificates i).tr",
              "      (certificates i).ul (certificates i).ur (certificates i).Z := by",
              "  rcases certificate_inputs i with ⟨hK, ha, htl, htr, hul, hur, hZ⟩",
              "  rw [hK, ha, htl, htr, hul, hur, hZ]", "  rfl", "",
              "/-- The finite sum exposes the actual fourfold manuscript kernel. -/",
              "theorem integral_semantics :",
              f"    integral = ((K : ℝ) / 80) * ∑ i : Fin {count},",
              "      ∫ t in (tLower (rowIndices i).1 : ℝ)..(tUpper (rowIndices i).1 : ℝ),",
              "      ∫ u in (uLower (rowIndices i).2 : ℝ)..(uUpper (rowIndices i).2 : ℝ),",
              "      ∫ z in (a : ℝ)..(rowZ i : ℝ), ∫ w in (a : ℝ)..z,",
              "        1 / (t * u * z ^ 2 * w) := by",
              "  simp only [integral, rowIntegral, pairedLocalIntegral, pairedFibreKernel_eq, Finset.mul_sum]", "",
              f"theorem lower_sum : (∑ i : Fin {count}, (certificates i).lower) = lowerBound := by",
              "  norm_num [certificates, lowerBound, Fin.sum_univ_succ, " + defs + "]", "",
              f"theorem upper_sum : (∑ i : Fin {count}, (certificates i).upper) = upperBound := by",
              "  norm_num [certificates, upperBound, Fin.sum_univ_succ, " + defs + "]", "",
              "/-- Concrete acceptance, checker soundness, and actual-object equality. -/",
              "theorem integral_bounds : (lowerBound : ℝ) ≤ integral ∧ integral ≤ (upperBound : ℝ) := by",
              "  have hs := PairedIntegralCertificate.sum_check_sound Finset.univ certificates",
              "    (fun i _ => certificates_checked i)",
              "  rw [lower_sum, upper_sum] at hs",
              "  simpa only [integral, ← rowIntegral_eq_certificate] using hs", "",
              "theorem integral_pos : 0 < integral := by",
              "  exact lt_of_lt_of_le (by norm_num [lowerBound]) integral_bounds.1", "",
              f"end {namespace}", ""]
    generated = {stem + "Data.lean": data_text, stem + ".lean": "\n".join(proof)}
    for name, content in generated.items():
        data = content.encode()
        if args.emit_dir:
            args.emit_dir.mkdir(parents=True, exist_ok=True)
            (args.emit_dir / name).write_bytes(data)
        if args.check_generated:
            assert (args.check_generated / name).read_bytes() == data, name
    report = dict(source_commit=SOURCE_COMMIT, source_path=SOURCE_PATH,
                  source_sha256=SOURCE_SHA256, source_git_blob=SOURCE_BLOB,
                  count=count, original_ordinals=list(range(count)), original_rows=rows,
                  prefix_row_stream_sha256=prefix_digest, group="E0", discarded_Q80_sum=0,
                  log_scale=LOG_SCALE, cell_scale=CELL_SCALE,
                  candidate_lower=str(lower_total), candidate_upper=str(upper_total),
                  candidate_lean_status="REQUIRES_SEPARATE_STRICT_COMPILE_KERNEL_REPLAY_AND_AUDIT",
                  generated_sha256={name: hashlib.sha256(text.encode()).hexdigest()
                                    for name, text in generated.items()})
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "original_rows"}, indent=2))


if __name__ == "__main__":
    main()
