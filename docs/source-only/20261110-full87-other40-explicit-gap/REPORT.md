# P1.4 — actual complementary 40-family affine gap; common 87-cell inner-box kernel
## Exact recovery and fixed scope
- Resumed independently checked HEAD `ff516bd5bc98285d02f97ea703a2d742d1205196`, branch `chatgpt/p1-full87-remaining45-certified-gap-20261109`. Its actual REPORT.md, HANDOFF.md, REGISTRY.json, INPUT_BOUNDARY.md, full 185-line Lean source and relevant original Source dictionary, 40 family literal rows, prior geometry and integral/kernel controls were read. Root AGENTS.md was absent (404; tree did not list another AGENTS.md).
- This isolated branch: `chatgpt/p1-full87-other40-explicit-gap-20261110`, created from that exact SHA. Only this new proof packet is written, with [skip ci]. No main/master writes or CI dispatch.
- Manuscript still pinned to `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, especially equation `eq:current-eighth-saving`. The original residual is 4(M-R6)/[(R6-S8)(M-S8)prod t]. No change to `c=49044063/25000000`, `K=8452171/1250000`.
- Fixed toolchain Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.

## New manuscript-internal candidate proof, genuine original row indices
- Fifteen **descending** cells: `OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i 16`. The exact semantic row is `newExpr - oldExpr`, i.e. the original `newCap - comparison` for selected mask129 and old raw winner6. Reuse the already authored all-96-rows affine slack proof to get ≥1/125000 over its actual radius-1e-8 inner box.
- Thirteen **ascendingPair** cells: `OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i 18`. It is its own `newExpr - oldExpr`, not the descending cap or selected mask. Reuse the genuine all-97-rows slack proof for ≥1/125000 over the original radius-1e-8 box.
- Twelve **H3** cells: `P4AOriginalFirstFailureH3Literal.sourceAffineRows i (commonRow 19)`, whose original 37-row semantic theorem identifies it with `M8 - R6`. Reuse the full 99-row first-failure slack certificate for ≥1/125000 on its original box. Preserve real H3 old-plane failures and historical gates; no new Source guard.
- These are the previously missing **40 cells = 15+13+12**. The preceding proof has a stronger 1/20000 lower on the other 47 actual remaining-family cells. Case splitting the unchanged `P4AOriginalFull87SourceDictionary.Cell` gives the **full 87-cell** pointwise lower, for every `c` and every `t` in its existing `sourceInnerBox c`:
```text
1/125000 <= newCap c t - comparison c t
(4/(9*mu^10))*(1/125000) <= kernel c t
```
- The kernel bound follows by multiplying the *same* exact cap-gap by the positive original denominator factor, and transitivity with `scaledCapGap_le_kernel` on the same original Source. No monotonicity of signed savings or archive order permutation is used.

## Additional independent exact rational sanity checks (NOT Lean)
Using the 40 frozen *existing candidate centre* matrices directly (denominator 10^8) and original affine formulas:
- Descending minimal centre cap gap: `2398/200000000`, cell d12.
- AscendingPair minimal centre cap gap: `2380/200000000`, cell p5.
- H3 minimal centre cap gap: `1981/200000000`, cell h0.
All 40 centre gaps positive and ≥1/125000, consistent with the older full literal-row margins and radius perturbation. This does NOT re-evaluate all 3889 rows this run, nor validate the imported candidate proof in Lean.

## Actual verification and missing obligations
- `lean --version`, `lake --version`, `elan --version`: all exit **127**, command not found. Pinned `.lake` and mathlib/native dependency tree absent in this execution environment. Did not install or upgrade anything. Only `SOURCE_ONLY / UNEVALUATED / UNCOMPILED`.
- New source commit `f141021fe7fa3b77bdb92cd3204fef9636224fec`, Git blob `ab9dd93f7e8e28cfe748cf5cf98cc1e00c5f0df6`, 171 lines, already remotely read back. Static forbidden escape-token scan zero. This is not elaboration, kernel replay, transitive axiom audit, or independent mathematical validation. Import staging is still required for source-only files, and the imported candidates are not kernel-checked.
- Still NOT proved: exact box-volume-to-full-source **quantitative integral** inequality, original 87 `*.witness.json` numerical endpoints/signed gain, physical prime tuples in those Sources, N-dependent `actualParent` and shared fourth/fifth history, Rosser-signed full-q occurrence/multiplicity, ordinary asymptotic identification, raw/finite/filtered and low/high-q payments, rank9/changed/tagged and both separate compiler/density reserves relative to identical `H_N`. Do not claim this tiny local box lower equals saved87 or a reserve payment.
- External §4 PP remains `REGISTERED_NOT_PROVED / NOT_CALLED`; no PNT/Mertens/BV/spectral project was started.

Next substantive step: with the exact pinned toolchain, stage all source-only modules as their declared `ImbalancedChen.*` imports, elaborate and repair real errors; then establish the 8D box volume and the integral transfer for all87 using the original source measure and original kernel, not synthetic archived integrals. Restore authentic saved87 witness bytes and only then prove actual physical signed gain relative to the same parent/rho.
