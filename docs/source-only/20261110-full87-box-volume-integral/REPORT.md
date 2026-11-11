# P1.4 — full original 87-Cell inner-box volume and same-Source integral transfer

## Recovery and immutable facts
- Read verified prior live branch HEAD `be2efd01c561080672e6c0ad0ba21638837afe4c` (other40 box-gap packet), with its full Lean source, REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF, and the preceding original strict-positivity/quantitative-gap/remaining47 modules. Root AGENTS.md is absent (404).
- Isolated branch `chatgpt/p1-full87-box-volume-integral-20261110`, created from that SHA; first code commit `8a8f53b637b26fca5b016fa17bee8d29e7b1a131`. New source: `P4AOriginalFull87BoxVolumeIntegral.lean` (133 nonempty/total source lines before trailing newline; Git blob `5e347cb851489186552221f3704ee9ed57cceaf7`).
- Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, checked lines 400–485 and exact blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Eighth-saving formula remains `4(M-R6)/((R6-S8)(M-S8) prod t_i)`.
- Fixed Lean 4 v4.33.0-rc1, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and native `09b97db5764ade1246bfb77206baa1b124760958`. No changes to c=49044063/25000000 or K=8452171/1250000.

## Actual new manuscript-internal candidate
The prior original affine proof supplies, for EVERY original Cell c and every t in the SAME original radius r=1/100000000 inner box, the pointwise inequality

`q := (4/(9*mu^10))*(1/125000) <= originalKernel(c,t)`, where `mu=25/128`.

The new source expresses the existing box as `Set.pi univ (fun j => Ioo (centre c j-r) (centre c j+r))`, and uses **pinned mathlib's real product-Lebesgue measure** identity `Real.volume_pi_Ioo_toReal` to derive

`volume(sourceInnerBox(c)).toReal = (2*r)^8`.

On the very same source and same kernel, integrability is inherited from the original finite-volume kernel proof; `setIntegral_mono_on` compares the constant q on that real box; `setIntegral_mono_set` uses the original source inclusion and nonnegative ideal kernel to transfer the integral. Proposed conclusion:

`(2*r)^8 * q <= integral_{sourceSet c} originalKernel(c,t) dt` for all 87 original Cells.

Exact rational offline sanity check (Python fractions, NOT Lean):
- `(2*r)^8 = 1/39062500000000000000000000000000000000000000000000000000000000 = 2.56e-62`.
- `q = 590295810358705651712/13411045074462890625 ≈ 44.01564584`.
- `q*(2*r)^8 = 8192/7270142102516844798674490457646157892668270505964756011962890625 ≈ 1.1268005335362038e-60`.

These numbers are intentionally tiny compared to the frozen rational `saved87` selected signed endpoint. The candidate only solves the **local inner-box-to-full-Source quantitative integral transfer**, not the archived selected quadrature or the actual arithmetic gain. No archive endpoint is assumed or substituted.

## Verification and boundaries
- Actual local `lean --version`, `lake --version`, `elan --version` return 127 (not found). No pinned mathlib/native local dependency tree. `SOURCE_ONLY / UNEVALUATED / UNCOMPILED`; Lean source could still contain elaboration errors. No kernel replay, transitive axiom audit, or independent proof validation.
- Pinned mathlib `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` was fetched and the exact `Real.volume_pi_Ioo_toReal` statement inspected. This is an API inspection, NOT elaboration.
- No new axiom/sorry/admit/native_decide/unsafe; no new synthetic source, parent, mask, certificate, externally supplied asymptotic or reserve. The original source owner/trim, beta signs, occurrence counts and physical policies were not modified.
- No main/master modification, CI dispatch, Codex, pin upgrade, or new computation resources.

## Still open
1. Source-only import staging, actual Lean elaboration/type repair, kernel replay and axiom trace.
2. Authentic `*.witness.json` saved87 byte archive and independent numerical interval certificate replay: this very small inner-box bound is NOT the archived coefficient gain.
3. Physical N-dependent prime tuples in original Sources; actual sixth `actualParent` with common fourth/fifth ancestry; original strategy signed full-q beta occurrence lists and multiplicities.
4. Original ordinary-continuation asymptotic identification; exact primitive discrepancy and modulus/centre-prime error bounds, low/high q, raw/finite/filtered losses; rank9, changed/tagged; separate compiler and density reserves, all with the SAME `H_N` and fixed-before-N parameters.
5. External §4 PP is `REGISTERED_NOT_PROVED / NOT_CALLED`. Do not implement large classical distribution projects.

Next run: read live branch/this handoff first; if exact toolchain still absent, prioritize restoring authentic saved87 numerical witness bytes or attacking the physical dynamic-parent/signed ordinary bridge, not producing another small local positivity bound.
