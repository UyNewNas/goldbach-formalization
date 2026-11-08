# P5.6 → h34 — literal U3/U4 UPPER H430 query phase

2026-11-08 UTC. **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

- Repository/branch: `UyNewNas/goldbach-formalization` / `chatgpt/p5-h34-request-admission-20261105`.
- Previous verified HEAD: `84d6024352e9484b5523d3b0ee5f0f7027b32edd`.
- New mathematical Lean source commit: `ee2072ab8f37aebaaac3d522d7f2e9be72b95fb2`. Blob: `077f359befa4be4ed99fbfcb0e7ebabdb06e17b6`.
- New single source module: `Part5OriginalH430TrueUpperU34Phase.lean`, 157 lines, 14 theorem candidates, one definition; earlier source files unchanged.
- Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` / `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Pinned Lean v4.33.0-rc1; pinned Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

## Actual manuscript-internal mathematical increment

The prior packets analyzed the ordinary **lower** h-start for original tagged q receivers. The frozen manuscript instead assigns U3/U4 upper costs to the **upper H430** kernel `H430(max(2,L/a))` in the enhanced range. This packet directly imports the existing concrete `ImbalancedChen.Part5OriginalU34H430Integrable` upper coefficient, **not** a new abstract receiver/owner filter.

That actual upper module fixes `mainResidual(t)=v(t)-t`, `tailResidual(t)=1/2-t`, `tailCutoff=57/224`, U3 using main below that cutoff and tail above, U4 using main throughout its domain `[a,59/250)`, and the actual `H430Numerators` finite upper-floor lookup.

This packet proves the following *candidate proof bodies*.

1. The tail clamp begins exactly at `1/2-2a=833/2500`, strictly **after** the U3 switch and strictly before `1/3`. The band `[833/2500,1/3)` has exact width `1/7500` and a rational interior point `3333/10000`. Therefore the upper H430 clamp at 2 cannot be discarded as an endpoint-only case.
2. The true U3 upper main phase `[a,57/224)` has unclamped `(v(t)-t)/a`. This uses the real min of both affine branches `A(t)` and `C(t)`, not an insufficient coarse residual estimate.
3. The true U3 upper tail has two distinct actual regimes: for `57/224 ≤ t < 833/2500`, the lookup uses `(1/2-t)/a`; for `833/2500 ≤ t < 1/3`, the lookup uses exactly the upper H430 knot `2`. The correct branch weight remains `4/(L*t)`.
4. The true U4 upper kernel `[a,59/250)` always reads the unclamped `(v(t)-t)/a` H430 argument; it does not use the lower h-start or an H248 substitute.

These are literal pointwise equalities for the **genuine upper U3/U4 integrable coefficient**, not a proof that a particular original q/tag receiver belongs to any full/selected/inherited count source. They do NOT create a fake count-stage owner, historical receipt, signed Euler payment or shared root Q. In particular the `H430` upper table is preserved, and the prior `H248` terms elsewhere are unchanged.

## Remaining genuine manuscript-internal obligations

The real U3/U4 upper **original selected-count** receiver source, its actual owner/history, root count weight, `z0` and full/selected/inherited stage matching remain OPEN. The literal upper-coefficient map is only a necessary lookup phase. Cross-q/tag event collisions and the arithmetic vs true historical mass gap, all rejected/cutoff/erased lanes, signed Euler complete suffix and first-excluded signs remain OPEN. So do the all-action CLOSED-CELL count induction, base/switched/seed/floor, feedback-to-integral/Theta/count, manuscript-local PP/same-rho, native mass and ONE common 430+11 causal refinement.

No P1.4, P3.6, default branch, production file, manuscript, toolchain, or CI configuration change. No new external analytic result, custom axiom, target-equivalent premise or proof escape was introduced.

## Verification and next step

The authenticated GitHub math commit, blob and exact one-file diff were read back. A static marker scan did not find forbidden proof escapes. **NOT RUN:** Lean parsing/elaboration/compilation, kernel replay, transitive axiom audit, independent review or finite numerical430 certification. The finite certificates remain **UNEVALUATED**, green credit zero.

**NEXT:** Follow the real upper U3/U4 original count-source back from these exact H430 coefficients, and bind the physical tagged q receivers, full/selected/inherited gates and true owner/root weights. Do not substitute the ordinary lower h-start or turn this phase lemma into a count payment.

**完整 h34 稿内证明仍未闭合。**
