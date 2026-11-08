# P5.6 → h34 — genuine resolved physical marked gates

Date: 2026-11-09 (China). Dedicated branch: `chatgpt/p5-h34-request-admission-20261105`.
Incoming verified HEAD: `d94fefa12d56fff2433ac5a0500ff76e7b06e2c5`.
New mathematical source commit: `d58d92ab4df5b4c88d336fdcf055451d808021be`.
Source path: `docs/source-only/20261109-p5-h34-actual-resolved-physical-gates/Part5OriginalH430ActualResolvedPhysicalGates.lean`.
Source Git blob: `fc7d45762d4eba0ece9baf5b6acb1381b35c6fed`.
Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`.
Toolchain retained: Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## What this specific packet changes

Previous source-only packet `d877089` had a legitimate exact pushforward from real resolved request-list Fin positions to a finite marked-product sigma, and its `activeProduct_Theta_pos` required **external caller-supplied geometric gates**: each actual product d > 0, and Q/d > 1. This new packet removes those gates **from that particular manuscript-internal consumer**, not by postulating them, but by using the actual `rootHistory_support` theorem and its original root/precision/tau/prime window.

- `actual_level_parent_product_pos` derives true parentProduct > 0 for every generated level-list occurrence. Its proof projects the literal `parentWindow_logs` lower bound from `rootHistory_support`. It does not impose a new positive-product field.
- `actual_level_quotient_gt_one` uses the *same root-specific physical Q*, exact `Q=d*N^L`, and the already-proved `frozenResidualFloor_pos <= L`. Because N>=4, it derives `(N:Real)^L > 1` and exactly `Q/d > 1`. There is no fictitious q=d identification.
- `activeProduct_Theta_pos_from_root_geometry` passes these two derived gates into the installed `activeProduct_Theta_pos`. Only the genuine geometric root assumptions and **nonemptiness of the actual resolved level** remain. No arithmetic selected-count source has been added to the hypotheses.

All statements are candidate Lean proof bodies, not Lean-checked theorems. The result is a narrow primitive-gate closure for the real finite resolved marked family, NOT a global h34 closure.

## Why the unresolved count problem remains

The generated product d is an original *request-history parent product*; arithmetic receiver q in original U3/U4 is separate. This packet does not prove a map q/tag → resolved history position, an injective/bounded-capacity payment, the actual full/selected/inherited selected-count filter, a bound on the previously identified q-count minus 5 Phi deficit, or the original H430 selected-count-to-Theta estimate. The nonempty-level hypothesis is not universally asserted: generations may have no resolved position and cannot be assigned a positive Theta by fiat.

Real manuscript-internal obligations also remain: request-level CLOSED-CELL count induction (not only action-value partition); original root count and mark weights; six rejection lanes, signed Euler suffix, Rosser native history, base/switched/seed/floor, feedback to integral and count; PP/same-rho and one common nested 430+11 causal refinement. No P1.4/P3.6 work and no external analytic proof extension.

## Verification and execution limits

- Authenticated repository write permission, prior branch HEAD, source-only scope and original 20261105 REPORT/REGISTRY/EXTERNAL_INPUTS were read. Existing 20261109 resolved-product source, the exact `rootHistory_support` and all-action source were inspected. This is a fast-forward on the h34 branch only; no merge, force push or production import change.
- Source blob was verified by reading it back at the mathematical commit. Static forbidden-proof-escape scan was run before submission. These are TEXT checks, not Lean elaboration, kernel replay or transitive axiom audit.
- Container has Git but **no lean/lake/elan executables**. `git ls-remote` against GitHub failed because `github.com` DNS could not be resolved. The pinned Lean/mathlib dependencies therefore were not provisioned for compilation.
- Existing full-root CI does not automatically install source-only modules; it was not triggered just to manufacture an unrelated green check. No CI configuration or dependency change. This packet has **NOT** passed Lean/Lake compile, kernel replay or transitive-axiom audit. Prior finite numerical430 and inherited certificates remain **UNEVALUATED**. No green node.
- No `sorry`, `admit`, custom `axiom`, `unsafe` proof or `native_decide` workaround introduced.

## Next concrete action

On a provisioned copy of the **pinned** Lean toolchain, stage the exact held source-only dependency path (including the prior actual resolved-product module) without replacing production files; compile this module and immediately repair actual elaboration errors, if any. Then pursue a real q/tag to selected marked-history **consumer**, preserving the physical Q, history position and any unmatched signed receipts, rather than producing further unconditional finite-sum identities.

**完整h34稿内证明仍未闭合。**
