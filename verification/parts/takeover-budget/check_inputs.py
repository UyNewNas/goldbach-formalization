"""Check the quoted eighteen-term budget against pinned manuscript JSON.

This checks file provenance and exact arithmetic only. It does not replay any
integral certificate, prove a sieve-policy identity, or certify actual counts.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

PIN = "ba6ec11d800eccc54406490631895e174de85766"

POSITIVE = [
    ("four_over_theta", "certify_extended_prefix.json", "theta", F(2000, 299)),
    ("first_integral", "certify_extended_prefix.json", "first_integral_upper_exact", F(7179974843999672947, 2**73)),
    ("third_compact", "certify_extended_prefix.json", "third_integral_upper_exact", F(144590669409566793572719, 2**80)),
    ("third_tail", "numerical-primitive-adversarial-20261009.json", "independent_tail_upper_Q112", F(319683857488126290909150567, 2**111)),
]

GAINS = [
    ("fourth", "stronger-fourth-independent-replay.json", "gain_lower", F(10601625247768616959055, 2**78)),
    ("fifth_subdivision", "independent_fifth_subdivision_replay.json", "stored_gain_verified", F(3037921066812732539869, 2**78)),
    ("fifth_new", "fifth-new-coverage-independent-audit.json", "gains.new_disjoint", F(1648717268323516459667, 2**80)),
    ("sixth_expanded", "sixth-prefix-expanded-independent-audit.json", "gain_lower", F(145496122603609407505, 2**77)),
    ("second_fallback", "second-prefix-upper-fallback-independent-review-20261009.json", "no_grid_coarse_lower", F(640339, 15210735000)),
    ("third_fallback", "third-prefix-upper-fallback-independent-review-20261009.json", "selected_lower", F(3097012678584315027795429, 2**96)),
    ("sixth_jensen_replacement", "sixth-log-moment-jensen-independent-20261009.json", "new_gain", F(1208544915921356327515701, 2**96)),
    ("sixth_tent33_descending", "sixth-tent33-descending-independent-20261009.json", "gain_lower", F(148834609033428677786865, 2**96)),
    ("sixth_tent34_ascending", "sixth-tent34-ascending-independent-20261009.json", "gain_lower", F(306737545112876482463163, 2**96)),
    ("sixth_tent34_descending", "sixth-tent34-descending-independent-20261009.json", "gain_lower", F(187277743940187526723019, 2**96)),
    ("sixth_lower_clip", "sixth-lower-clip-window-independent-20261009.json", "gain_lower", F(670429887277013841791829, 2**96)),
    ("sixth_lower_desc34", "sixth-lower-desc34-window-independent-20261009.json", "gain_lower", F(198410119216276585672773, 2**95)),
    ("sixth_lower_local_selected", "sixth-lower-local-additions-independent-20261009.json", "selected_gain", F(5023185001132087792027, 2**93)),
    ("sixth_nonsingleton", "sixth-nonsingleton-independent-20261009.json", "gain_lower", F(581521529176619227721, 2**92)),
    ("eighth_radial_replacement", "eighth-radial-independent-20261009.json", "whole_cell_max", F(74558208451675327462975, 2**96)),
    ("eighth_family_new", "eighth-prefix-family-independent-20261009.json", "new_gain_lower", F(1222997719565324892497827, 2**96)),
    ("eighth_descending", "eighth-prefix-descending-independent-20261009.json", "gain_lower", F(467454156274267811817033, 2**96)),
    ("eighth_unequal_replacement", "eighth-unequal-moment-independent-20261009.json", "new_gain", F(1033407531585213315823239, 2**96)),
]

WEAK_REPLACEMENTS = [
    ("sixth_previous", "sixth-log-moment-jensen-independent-20261009.json", "previous_gain", F(1201130581437641342320905, 2**96)),
    ("eighth_original_seed", "eighth-radial-independent-20261009.json", "old_whole_cell_gain", F(74010257929342545968375, 2**96)),
    ("eighth_unequal_previous", "eighth-unequal-moment-independent-20261009.json", "previous_gain", F(509255822034269351804717, 2**95)),
]

SAVED_STATE = [
    ("saved_old_base", "lichtman-current-upper-density-assembly-20261009.json", "base_density.exact_extended_upper", F(1230679674488580033396846301, 180734410032387061618573312)),
    ("saved_45_raw", "lichtman-current-upper-density-assembly-20261009.json", "upper_ledger_steps.6.raw", F(304556572495608040799486465978131124810963, 45041307097235144895836810885600378880000)),
]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manuscript", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.manuscript.resolve()
    head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    if head != PIN:
        raise RuntimeError(f"Manuscript pin mismatch: {head}")
    rows = []
    for label, filename, key, expected in POSITIVE + GAINS + WEAK_REPLACEMENTS + SAVED_STATE:
        relative = "verification/data/" + filename
        pinned = subprocess.check_output(["git", "-C", str(root), "show", PIN + ":" + relative])
        local = (root / relative).read_bytes()
        # Git-for-Windows may check JSON out with CRLF; compare normalized UTF-8
        # and record both hashes rather than silently asserting byte identity.
        if local.replace(b"\r\n", b"\n") != pinned.replace(b"\r\n", b"\n"):
            raise RuntimeError(f"Working-copy JSON differs from pinned blob: {relative}")
        value = json.loads(pinned)
        for component in key.split("."):
            value = value[int(component)] if isinstance(value, list) else value[component]
        actual = F(value)
        transform = "identity"
        if label == "four_over_theta":
            actual = 4 / actual
            transform = "4 / field"
        if actual != expected:
            raise RuntimeError(f"Exact input mismatch for {label}: {actual} != {expected}")
        rows.append({"label": label, "path": relative, "key": key,
                     "field": value, "transform": transform, "exact": str(actual),
                     "pinned_blob_sha256": hashlib.sha256(pinned).hexdigest(),
                     "working_copy_sha256": hashlib.sha256(local).hexdigest()})
    e18 = sum(t[3] for t in POSITIVE) - sum(t[3] for t in GAINS)
    v = F(145007961227048312210593427530128000784681,
          23614616815395219647148489905589651442237440000)
    gap = F(8452171, 1250000) - e18 - 2*v
    assert e18 == F(9979708415836147068815329797395632360011359959,
                    1475913550962201227946780619099353215139840000)
    assert gap == F(4143109497000719526277372268621665971743329,
                   491971183654067075982260206366451071713280000000)
    assert v > 0 and gap > 0
    weak_gains = [row[3] for row in GAINS]
    for index, replacement in zip([6, 14, 17], WEAK_REPLACEMENTS):
        assert replacement[3] <= weak_gains[index]
        weak_gains[index] = replacement[3]
    eweak = sum(t[3] for t in POSITIVE) - sum(weak_gains)
    simple_reserve = F(1, 200000)
    weak_simple_gap = F(8452171, 1250000) - eweak - 2*simple_reserve
    assert weak_simple_gap > F(1, 100000)
    new_base = sum(t[3] for t in POSITIVE)
    old_base, old_45_raw = [row[3] for row in SAVED_STATE]
    increments = [GAINS[i][3] - weak[3]
                  for i, weak in zip([6, 14, 17], WEAK_REPLACEMENTS)]
    assert e18 == old_45_raw + new_base - old_base - increments[2]
    assert eweak == old_45_raw + new_base - old_base + increments[0] + increments[1]
    result = {"status": "PASS_EXACT_INPUTS_AND_RATIONAL_ARITHMETIC_ONLY",
              "scope": __doc__.strip(), "manuscript_pin": PIN, "inputs": rows,
              "E18": str(e18), "reserve_each": str(v), "gap": str(gap),
              "E18_weak": str(eweak), "simple_reserve_each": str(simple_reserve),
              "weak_simple_gap": str(weak_simple_gap),
              "display_only": {"E18": float(e18), "reserve_each": float(v), "gap": float(gap),
                               "E18_weak": float(eweak), "weak_simple_gap": float(weak_simple_gap)},
              "replacement_slots_one_based": [7, 15, 18],
              "saved_45_ledger_arithmetic_match": True,
              "policy_semantics_proved_by_ledger_match": False,
              "analytic_integral_or_policy_claim": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("status", "E18", "reserve_each", "gap", "display_only")}, indent=2))

if __name__ == "__main__":
    main()
