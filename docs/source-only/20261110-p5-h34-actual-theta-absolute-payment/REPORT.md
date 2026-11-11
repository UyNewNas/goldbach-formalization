# P5.6 / h34 — physical Theta-normalization absolute-payment ledger

Date: 2026-11-11 UTC. Base HEAD: `a681ec7151ac84a81eb227953d0de9cd39cada8b`.
Reused isolated branch: `chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109`.
File: `Part5OriginalH430ActualThetaAbsolutePayment.lean`.
Fixed manuscript remains `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`. Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Exact new manuscript-internal content

The prior packet `Part5OriginalH430ActualNextTableThetaFloorBridge` proved a *candidate* literal equality between unweighted request reads and the physical Theta-weighted original edge consumer, leaving a signed `actualThetaReadCorrection` with no known sign. This packet does **not** set it to zero, assume Theta=1, or import a new arithmetic counting license.

1. `actualThetaAbsolutePayment` is the literal finite sum of `|levelMark| * |thetaAtom(parent real Q, real previous product) - 1| * |requestValue(iterate(g+1), actual request)|` over all genuine history Fin positions. It is not a generic request for an unknown small bound.
2. `actual_theta_absolute_payment_nonneg` and `actual_theta_correction_abs_le_payment` show a positive, noncancelling, entirely explicit bound on the signed normalization correction. The latter is proved by the sum/absolute-value triangle inequalities, not by positivity of request values.
3. `actual_theta_correction_signed_interval` makes both directions explicit, allowing the negative correction to be safely replaced by the positive budget.
4. `actual_theta_absolute_payment_all_actions` splits the budget over actual retention, Buchstab and original 106 bank winning positions; unresolved values vanish. No multiplicities or scalar/specified-cell differences are erased.
5. `actual_source_debt_theta_absolute_payment_upper` combines the earlier *conditional* base/floor source-gap ledger with this pointwise budget and retains the correct **minus** Q80 floor credit and prime-child payment. It derives a sign-safe source-debt upper bounded by **the explicit unpaid positive Theta budget**, not by an invented 12Theta or epsilonTheta fee.

The source gap and Theta payment remain **unpaid** at original arithmetic counting level. In particular, there is no proof here that the payment is small uniformly in N or that true U3/U4 full/selected/inherited owner and root counting weights match the feedback history.

## Validation and ownership

The authenticated repository grants push. At start the dedicated branch HEAD was `a681ec7151ac84a81eb227953d0de9cd39cada8b`, matching the previous verified handoff; no GitHub Actions job was in progress at the initial check. This is an additive file in the already-owned h34 branch; no previous source packet, production module, P1.4/P3.6, pinned manuscript, toolchain, or CI configuration was changed. Other automation file owners were untouched.

Runtime check: git available, but Lean/Lake/Elan absent from PATH, and github.com DNS resolution failed in the execution container. The fixed source-only import closure is not staged. **No Lean parser/elaborator/compile, kernel replay, axiom audit, numerical430 or finite-certification run was completed.** Static/source integrity inspection is not a substitute. Zero new green credit. This packet's Lean statements remain candidates until a real pinned-toolchain build.

## Next actual manuscript-local obligation

Identify and prove a **genuine** bound for `actualThetaAbsolutePayment` from the same original U3/U4 root/count owner, not an arbitrary positive payment budget. Independently obtain base/seed/floor CLOSED-CELL predecessor control and the two bank/Buchstab new-table source-gap budgets, then combine with true full/selected/inherited filters, PP/same-rho, native-history mass, outer Theta/count and the common 430+11 refinement. First compile this module and its direct source-only dependencies under the frozen toolchain.

**完整h34稿内证明仍未闭合。**
