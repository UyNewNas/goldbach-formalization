# P1.4 — original full87 strict positive source integrals (SOURCE_ONLY)

## Recovery and frozen identity
- Verified live predecessor `407b3f997908fd6fb9ee2b05bf3c9944405ec4eb` on `chatgpt/p1-full87-quantitative-gap-integral-20261109`, after reading complete source, REPORT, REGISTRY, INPUT_BOUNDARY and HANDOFF. No concurrent branch move observed. Branch `chatgpt/p1-full87-strict-positive-source-integral-20261109`, source commit `6b5d520efd5c56e1654b8255c002c05a25fd8b23`, original Git blob `bb4a532975b067cd4167458b84bb2955a644748b`.
- Source: `P4AOriginalFull87StrictPositiveSourceIntegral.lean`. This packet changes no main/master, old drafts, manuscript, external input packages, actual parent definitions or pins.
- Fixed manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`, c `49044063/25000000`, K `8452171/1250000`.

## Concrete new internal candidate argument
- Reuses the exact previously sourced original centres and strict affine-box membership (14 ascending; 16 seed/winner9/fifty; 17 H5/H7; 15 descending; 13 ascendingPair; 12 H3). Shrinks all six *original* families' boxes to the common coordinate radius `10^-8` and proves `sourceInnerBox c ⊆ sourceSet c` by actual constructor cases; no Cell identification by archive order and no newly licensed mask.
- Since the inner box is a nonempty open set in the same eight-dimensional Lebesgue space, `volume (sourceSet c) > 0` for each original Cell. An individual interior point would not suffice: this explicitly supplies positive source measure.
- The original cap gap `newCap c t - comparison c t` is strictly positive *on the original Source*, and previously proved-in-candidate-form integrable there. Using its positive-measure support and `integral_pos_iff_support_of_nonneg_ae`, concludes `0 < ∫ t in sourceSet c, (newCap c t - comparison c t)`.
- Combined with predecessor's **same-source** quantitative `(4/(9*mu^10)) * gap ≤ kernel`, and positive scale, concludes `0 < ∫ t in sourceSet c, kernel c t` for all 87 cells.
- This removes the mathematical *measure-zero point* gap between ideal-kernel pointwise positivity and qualitative integral positivity, but does **not** prove any original selected rational quantitative lower endpoint, saved87 quadrature, actual dynamic parent equality or signed physical saving.

## Actual verification
- GitHub connector created branch from exact baseline and source commit; fetched source content back and verified Git blob `bb4a532975b067cd4167458b84bb2955a644748b`, 222 source lines, and zero forbidden proof-escape tokens. These are not elaboration or kernel checks.
- Local command results: `lean --version` exit 127, `lake --version` exit 127, `elan --version` exit 127; no local Lean checkout or pinned mathlib/native tree. Did not run local Lean/Lake, kernel replay, axioms audit or independent review. Proof body remains **UNEVALUATED**; possible elaboration and mathlib-lemma compatibility errors remain.
- GitHub manuscript `verification/full-numerical-source-manifest.json` lists original `*.witness.json` checksums, while the inspected frozen `verification/data` (76 entries) has no matching original `*.witness.json` source bytes. No original saved87 witness replay or integral certification.
- Source-only proofs require module path adaptation before a compatible local typecheck. No new CI, Codex, user workstation, toolchain upgrades, forced push, main/master changes or extra resources. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**, not green.

## Remaining real obligations
1. Find original saved87 integral witness files and authenticate directed simplex/quadrature lower endpoints or derive fully checkable positive quantitative same-source cap-gap integral bounds. Current strictly positive integral gives *no specified positive constant* or `H_N` saving.
2. Identify original ideal source cap/comparison with true `N`-dependent `actualParent`, shared fourth/fifth history, actual prime tuple Source membership, original retained signed Rosser beta and complete occurrence multiplicities; no ideal-to-physical leap.
3. Same `W_N` and legal PP integer `X`, exact primitive discrepancy, modulus/centre-prime corrections, all low/high-q/ordinary/filtered losses and changed/tagged/rank9, two independent reserve payments relative to same `H_N`, quantifier order.
4. Import-stage Lean typecheck, kernel replay, transitive axioms inspection, independent mathematical verification.

The external §4 PP package remains `REGISTERED_NOT_PROVED / NOT_CALLED`. P1.4 parent remains **YELLOW**.
