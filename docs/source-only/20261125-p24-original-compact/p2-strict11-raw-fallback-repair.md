# Strict11: raw fallback proof expressions

Actual input: `d9ef4403bf8007efafb9264c9c03779abc24c3dd`. The completed original P2 strict run accepted 299/321 modules (298 reused, one fresh: OrdinaryOuterMinimum); RawFallbackAllOld is the only direct failure. Full evidence: `p2-strict-symbolic-11.log`, 5203 bytes, SHA256 `eba20326993251356a8bb2eb3ab6b25d8d959bd060dfdd8dc37b8d4fa83533f4`.

Only `ImbalancedChen/ActualThirdOriginalP4AOrdinaryRawFallbackAllOld.lean` is changed here:

- At the original lines 71 and 210, remove the `ring` after `field_simp` which the actual compiler reports has no remaining goal. Other `ring` calls remain.
- In `v_endpoint_min_le`, rewrite specifically `VariableEnvelope.v_eq_min t`, leaving both endpoint values on the left intact. Give the two linear intermediate bounds the explicit types `A l ≤ A t` and `C u ≤ C t`, using only the existing hypotheses `l ≤ t` and `t ≤ u`. This removes the unresolved intermediate right sides shown as metavariables in the actual lines 91/92 errors.
- In `raw_B_floor_le`, normalize the integer numeral cast with `simp only [Int.cast_ofNat] at hh` before the existing `rw [he]`. This aligns `↑(256 : ℤ)` with the real numeral in `he`. The floor quotient on the left stays integer division. Explicitly type the final intermediate bound `B (realBox b 2) ≤ B (t 2)`, using the existing `t ≤ realBox b`.

Frozen 1106 correspondence was checked against `certify_extended_prefix.py` (`chen-imbalanced-semiprimes` commit `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`, local SHA256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`): `v_lo` retains the floors with divisors 2 and 64, and `phi_range` retains the floor with divisor 256 and the final cap minimum (lines 116–160). The numerical appendix's directed-arithmetic and enclosure conventions are unchanged. These repairs concern elaboration, cast normalization, and solved tactics. The given interval hypotheses already imply the typed affine bounds; no additional mathematical assumption or substantive gap is introduced. In particular, floor-to-real division remains an inequality valid for arbitrary integer numerators and positive denominators; no numerator nonnegativity assumption is added.

Before SHA256: `137580167df8e97fbac78d3383222f1e2396ac9853eb1e6e593c7effdaea2e15`.

Frozen candidate SHA256: `92abb6db49e5ea435b56a39c55adcacacc7ebe6c363ac86b96aab3009d799f79`.

Static comparison against the actual input preserves all 17 theorem headers, all computational declarations (none in this file), the sole import, and options/attributes byte for byte. The original cap assertion, endpoint selection, and all guards remain unchanged. Scoped `git diff --check` passed. No Lean compilation, remote job, index change, or commit was performed. The candidate requires the original strict checker; this note grants no new compile, finite-certificate, or independent-kernel acceptance.
