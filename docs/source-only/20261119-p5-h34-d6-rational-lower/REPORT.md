# P5.6 h34 — first actual D6 rational lower-certificate component

Date: 2026-11-19 (Asia/Shanghai).
Incoming HEAD: `fb59a2b17eb31470bb183d5e718449272055c4a7`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Toolchain remains `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## New mathematical source
The previous packet merely exposed the seven-integral condition `lambda >= 13/100`. This one discharges an ACTUAL numerical piece rather than postulating a real-integral value.

- `d6_full_cell_rational_arithmetic`: the precise unchanged D6 rational Darboux bound using a **two-term** logarithmic lower series on the full true outer interval `[50/227,100/353]` is at least `103/1000`. All its arithmetic is proposed to be checked by Lean `norm_num`.
- `actual_d6Log_ge_103_over_1000`: consumes the existing manuscript-local `d6_rational_cell_integral_lower` soundness theorem and the true D6 `Ioo`-to-interval-integral equality, retaining its untruncated rho<2 part.
- `original_singleton_coefficient_nonneg` and `original_pair_coefficient_nonneg`: prove nonnegativity using original 3 singleton supports and 4 supported pair domains, without conflating D5/6/7/8 or altering comparison licences.
- `other_pair_log_terms_nonneg`, `actual_lambda_ge_d6_over_five`, `actual_lambda_ge_103_over_5000`, `actual_feedback_model_partial_lower`: compose the unchanged original seven-term identity and normalization to obtain only a genuine PARTIAL coefficient lower bound.

Independent rational-arithmetic cross-check (not a substitute for Lean): the one-cell/two-term D6 Darboux expression is approximately **0.1038484040**, strictly above 0.103. The target seven-piece coefficient `lambda >= 0.13` requires the full sum to be at least 0.65; this packet does NOT establish that. The one-cell lower sacrifices too much margin to close the final numerical target by itself; subdivision and D5/D7/D8/three-singleton certificates remain necessary.

## Real boundaries
This source does NOT prove the original fixed `20249/1000000` intercept is paid by an analytic count source. It does NOT imply the adopted Q80 seed is below the frozen analytic F on every first-60 closed cell. No correct base/seed or m->m+1 CLOSED-CELL count induction is claimed.

Original U3/U4 selected/full/inherited counts, owner/root norm7/2, six exclusions, same-Q/PP, native-history signed payment, integration-Theta-count and common430+11 refinement all remain manuscript-INTERNAL. No new external result, axiom, `sorry`, `admit`, `unsafe`, toolchain upgrade, CI config edit or change to c/K/row norm12 was made.

## Verification
Connected GitHub branch/parent, initial task REPORT/REGISTRY/EXTERNAL_INPUTS and source imports were read. The environment has no Lean/Lake/Elan and no installed fixed source-only import closure. Native git access fails DNS resolution, but the authenticated GitHub connector is writable. No Lean compilation, kernel replay, transitive-axiom audit or finite certified numerical replay was performed. Text-level checks cannot give formal credit.

Next: stage and compile this module with the original fixed imports; repair any actual errors, then build a sufficiently sharp multi-cell rational certificate for D6 and the original three singletons plus D5/D7/D8 support pieces to prove the true `lambda >= 13/100`. Independently pay the fixed intercept and the original analytic F CLOSED-CELL seed.
