#!/usr/bin/env python3
"""Decode the frozen adopted paired-v2 witness without floating point.

This is reproducible provenance/decoding, not a proof of a real integral.
The Lean checker and the genuine integral identity provide that proof for
the explicitly instantiated row. The complete aggregate reported here is
an independently computed candidate until its Lean checks are supplied.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
from pathlib import Path

SOURCE_COMMIT = "ba6ec11d800eccc54406490631895e174de85766"
SOURCE_PATH = "verification/data/corpus-renewal-paired-certificate-v2-20261010.json"
SOURCE_BLOB = "49499697cca96de5f7b779e95077874ce5f9d119"
SOURCE_SHA256 = "f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7"
EXPECTED_COLUMNS = ["group", "t_index", "u_index", "exact_Z", "discarded_floor_Q80",
                    "extra_lower_Q160", "extra_upper_Q160"]
A, H, D, MU, K = Q(417, 5000), Q(19, 125), Q(59, 250), Q(25, 128), Q(8452171, 1250000)
LOG_SCALE, CELL_SCALE = 10**15, 10**20


def floor(q: Q) -> int:
    return q.numerator // q.denominator


def ceil(q: Q) -> int:
    return -((-q.numerator) // q.denominator)


@lru_cache(None)
def rational_log_bounds(q: Q, n: int) -> tuple[Q, Q]:
    assert q >= 1 and n >= 0
    x = (q - 1) / (q + 1)
    lo = 2 * sum((x ** (2 * j + 1) / (2 * j + 1) for j in range(n)), Q(0))
    hi = lo + 2 * x ** (2 * n + 1) / (1 - x*x)
    return Q(floor(lo * LOG_SCALE), LOG_SCALE), Q(ceil(hi * LOG_SCALE), LOG_SCALE)


def coordinates(i: int, j: int) -> tuple[Q, Q, Q, Q]:
    return (MU + (D - MU) * i / 512, MU + (D - MU) * (i + 1) / 512,
            A + (H - A) * j / 512, A + (H - A) * (j + 1) / 512)


def lean_rat(q: Q | int) -> str:
    q = Q(q)
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator} / {q.denominator}"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--emit", type=Path, help="Write the deterministic first-row Lean data module.")
    parser.add_argument("--check-generated", type=Path, help="Check an existing generated module byte for byte.")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    raw = args.source.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    blob = hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()
    assert digest == SOURCE_SHA256, ("source SHA256 mismatch", digest)
    assert blob == SOURCE_BLOB, ("source git blob mismatch", blob)
    source = json.loads(raw)
    assert source["row_columns"] == EXPECTED_COLUMNS
    assert source["omega_argument_threshold"] == "7/3"
    assert source["omega_lower"] == "11/20"
    assert Q(source["K"]) == K
    rows = source["rows"]
    assert len(rows) == 17572
    groups: dict[str, list[tuple[int, int]]] = {"E0": [], "E1": []}
    integer_sum, floor_sum, crossing = [0, 0], 0, 0
    first = None
    for ordinal, row in enumerate(rows):
        assert isinstance(row, list) and len(row) == 7
        label, i, j, z_text, lost_text, old_lo, old_hi = row
        assert label in groups and type(i) is int and type(j) is int
        assert 0 <= i < 512 and 0 <= j < 512
        tl, tr, ul, ur = coordinates(i, j)
        z, lost = Q(z_text), int(lost_text)
        assert z == min(ul, 3 * (1 - tr - ur) / 13)
        assert 0 < A < z <= ul < ur <= H < tl < tr <= D
        assert 1 - tr - ur >= Q(13, 3) * z
        assert lost >= 0 and int(old_lo) <= int(old_hi)
        rmax, rmin = Q(57, 64) - Q(5, 2)*tl - ul, Q(57, 64) - Q(5, 2)*tr - ur
        if label == "E0":
            assert rmax / A <= 2 and lost == 0
        else:
            assert 2 < rmax / A <= Q(9, 4)
            if rmin / A < 2:
                crossing += 1
                assert lost == 0
        lt, lu, lz = (rational_log_bounds(tr/tl, 1), rational_log_bounds(ur/ul, 1),
                      rational_log_bounds(z/A, 6))
        blo, bhi = 1/A - (1+lz[1])/z, 1/A - (1+lz[0])/z
        assert lt[0] >= 0 and lu[0] >= 0 and blo >= 0
        lo, hi = K/80*lt[0]*lu[0]*blo, K/80*lt[1]*lu[1]*bhi
        integer_sum[0] += floor(lo * CELL_SCALE)
        integer_sum[1] += ceil(hi * CELL_SCALE)
        floor_sum += lost
        groups[label].append((i, j))
        if ordinal == 0:
            first = dict(row=row, tl=tl, tr=tr, ul=ul, ur=ur, z=z, lt=lt, lu=lu, lz=lz)
    assert len(groups["E0"]) == 6091 and len(groups["E1"]) == 11481
    assert len(set(groups["E0"] + groups["E1"])) == 17572
    for label, mask in groups.items():
        assert mask == sorted(set(mask))
        stream = "".join(f"{i},{j}\n" for i, j in mask).encode()
        assert hashlib.sha256(stream).hexdigest() == source["groups"][label]["mask_sha256"]
    rowstream = "".join(",".join(map(str, row)) + "\n" for row in rows).encode()
    assert hashlib.sha256(rowstream).hexdigest() == source["row_stream_sha256"]
    assert crossing == 227 and floor_sum == 11290806845175652020270
    assert first is not None and first["row"][:3] == ["E0", 422, 510]
    lo_total, hi_total = (Q(v, CELL_SCALE) for v in integer_sum)
    assert lo_total > Q(558583, 10**9)
    lines = [
        "import ImbalancedChen.Certificates.PairedCertificateChecker", "",
        "/-! Deterministic data import; run verification/part2/import_paired_v2.py.",
        f"Frozen manuscript commit: {SOURCE_COMMIT}",
        f"Source path: {SOURCE_PATH}", f"Source git blob: {SOURCE_BLOB}",
        f"Source SHA256: {SOURCE_SHA256}",
        "The Q160 endpoints below are provenance only. The new certificate uses",
        "independent rational logarithm checks and proves its own weaker bounds.", "-/", "",
        "namespace ImbalancedChen.Certificates.PairedV2", "",
        'def firstGroup : String := "E0"', "def firstOrdinal : ℕ := 0",
        "def firstTIndex : ℕ := 422", "def firstUIndex : ℕ := 510",
        "def a : ℚ := 417 / 5000", "def h : ℚ := 19 / 125",
        "def d : ℚ := 59 / 250", "def mu : ℚ := 25 / 128",
        "def K : ℚ := 8452171 / 1250000", "",
        "def tLower (i : ℕ) : ℚ := mu + (d - mu) * i / 512",
        "def tUpper (i : ℕ) : ℚ := mu + (d - mu) * (i + 1) / 512",
        "def uLower (j : ℕ) : ℚ := a + (h - a) * j / 512",
        "def uUpper (j : ℕ) : ℚ := a + (h - a) * (j + 1) / 512", "",
        f"def firstZ : ℚ := {lean_rat(first['z'])}",
        f"def firstDiscardedQ80 : ℕ := {first['row'][4]}",
        f"def firstStoredLowerQ160 : ℤ := {first['row'][5]}",
        f"def firstStoredUpperQ160 : ℤ := {first['row'][6]}", "",
        "def firstCertificate : PairedIntegralCertificate where",
        "  K := K", "  a := a", "  tl := tLower firstTIndex", "  tr := tUpper firstTIndex",
        "  ul := uLower firstUIndex", "  ur := uUpper firstUIndex", "  Z := firstZ",
    ]
    for label, q, n, bounds in [("T",first["tr"]/first["tl"],1,first["lt"]),
                                ("U",first["ur"]/first["ul"],1,first["lu"]),
                                ("Z",first["z"]/A,6,first["lz"])]:
        lines.extend([f"  log{label} :=",
                      f"    {{ argument := {lean_rat(q)}",
                      f"      terms := {n}",
                      f"      lower := {lean_rat(bounds[0])}",
                      f"      upper := {lean_rat(bounds[1])} }}"])
    lines.extend(["  lower := 31703 / 1000000000000", "  upper := 31704 / 1000000000000", "",
                  "end ImbalancedChen.Certificates.PairedV2", ""])
    lean_source = "\n".join(lines)
    if args.emit:
        args.emit.parent.mkdir(parents=True, exist_ok=True)
        args.emit.write_text(lean_source, encoding="utf-8", newline="\n")
    if args.check_generated:
        assert args.check_generated.read_bytes() == lean_source.encode()
    report = {
        "source_commit": SOURCE_COMMIT, "source_path": SOURCE_PATH,
        "source_sha256": digest, "source_git_blob": blob,
        "rows_decoded": len(rows), "groups": {key: len(value) for key,value in groups.items()},
        "crossing_E1_cells": crossing, "discarded_floor_Q80_sum": str(floor_sum),
        "first_original_row": first["row"],
        "independent_candidate_log_terms": {"outer": 1, "inner": 6},
        "independent_candidate_log_scale": LOG_SCALE, "independent_candidate_cell_scale": CELL_SCALE,
        "independent_candidate_aggregate_lower": str(lo_total),
        "independent_candidate_aggregate_upper": str(hi_total),
        "adopted_extra_gross_lower": "558583/1000000000",
        "aggregate_lean_status": "NOT_CERTIFIED_BY_THIS_PYTHON_REPLAY",
        "generated_lean_sha256": hashlib.sha256(lean_source.encode()).hexdigest(),
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
