# Strict09: outer-minimum expression repairs and bounded fallback reuse

Actual input: `7acdbd5be3d84fd257d1c44561cccdb6ae76c8dd`. Complete log: `p2-strict-symbolic-09.log`, 6,328 bytes, SHA-256 `b4082cbcad8176446ced442a92979541b9381fc13176953d533d4025d10080f9`. The batch completed with 297/321 successful modules (293 reused, 4 fresh).

## Actual OuterMinimum errors

Only three proof sites change in `ActualThirdOriginalP4AOrdinaryOuterMinimum.lean`:

- Line 174: use `_root_.add_le_add hdiv (le_refl (-1 : ℝ))` so the transported inequality has `-1` on the same side of each addition as the target.
- Line 183: delete the `ring` after `field_simp`; the complete log explicitly reports that no goals remain.
- Line 204: replace the preceding broad `push_cast` with `simp only [Int.cast_sub]`. This expands the three numerator subtractions while retaining the original `T₀`/`D₀` casts for the existing `htheta` rewrite. No replacement numerical constant is introduced; the subsequent nonzero-denominator proof remains unchanged.

These are expression/API and redundant-tactic issues, with no new mathematical hypothesis or substantive proof gap. The file has no `field_simp <;> ring` sequence to rewrite; its remaining multi-goal `cases p <;> exact hj` is preserved.

## Explicitly blocked-source reuse

At root's request, `ActualThirdOriginalP4AOrdinaryRawFallbackAllOld.lean` receives only the same addition-transport replacement and two deletions of `ring` after the local `he` denominator identities. The latter identities are the reverse of the OuterMinimum identity: `(A-x-y-z)/z = (A-x-y)/z-1`. In the OLD case, unfolding the existing `actualOldArgument` produces exactly this form; each site already supplies `z ≠ 0`. Other scale/cast `field_simp`/`ring` proofs are left intact.

**RawFallbackAllOld was only blocked in strict09. These are static same-shape pre-repairs, not repairs backed by a direct failure or a PASS for that module. Both candidates still require actual compilation.**

## Preserved scope and frozen hashes

Rechecked the frozen 1106 numerical appendix's affine-box/integral enclosure paragraphs and `certify_extended_prefix.py` lines 280–336: raw/clipped bounds and decay gates precede the optional Jensen minimum, followed by mass multiplication and final upward rounding. Producer SHA-256: `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`, publication commit `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. This operation order is unchanged, as are OuterMinimum's clamp/no-tightening premises and RawFallback's original cap-positivity assertion.

| File | Before SHA-256 | Candidate SHA-256 | Preserved declarations |
| --- | --- | --- | --- |
| OuterMinimum | `93984c7ace6336d052b181197282ab12ac852ed64fed78f80a815b284a726212` | `ba02a18b1f4369505e14c75bdd507d46391ffa6086ace8bb073a0061c18f9dd2` | 16 theorem headers, 14 complete computational blocks, 2 imports |
| RawFallbackAllOld | `bd81a7f73560a9d0ad51c2b45b3ff4b1bb55a5f17bec7209ffaee6a6b6f52b43` | `137580167df8e97fbac78d3383222f1e2396ac9853eb1e6e593c7effdaea2e15` | 17 theorem headers, no computational declarations, 1 import |

Mechanical comparison is against the actual input pin; scoped `git diff --check` passes. No options, proof escapes, guards, imports or computational definitions change. Only these two files and this note were edited; no index, commit, ref, remote or compiler action was taken. No former source-bound style exception is requested for the changed candidates.
