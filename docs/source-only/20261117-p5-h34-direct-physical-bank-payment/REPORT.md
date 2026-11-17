# P5.6 → h34: direct selected-bank physical-error payment

Date: 2026-11-17. Previous committed branch HEAD: `530da0330dc3a57a2d5e2390146e8759049dec0f`, branch `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Fixed manuscript map: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (2026-10-10), NOT the later frozen manuscript.
Fixed toolchain: Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Genuine source increment

New module: `Part5OriginalH430DirectPhysicalBankPayment.lean`.

The last packet `Part5OriginalH430TrueRootFinWaveBridge` matched the *physical* source wave with the actual 430 Fin levels. The older `BankSurplusPhysicalSplit` controlled a *raw predecessor* candidate gap and consequently exposed an absolute child-Theta drift. That is not the same debt as the physical source term in the new root telescope.

This packet works directly with `physicalDefectAt` on the genuine selected 106-bank position. A pointwise positive-part comparison gives, for `x = theta * actualQ80Read`, `y = theta * idealCellProfile`, and `z = actual edgeValue`,

    max(0, x-z) <= max(0, x-y) + |z-y|.

It is applied **before** each positive history-mark sum. The existing `uniform_level_bank_supply` pays the total selected applied error by `epsilon * bankPhysicalTheta`, using one threshold before all N, root, precision, p and generations. This leaves only the *true read-vs-ideal positive excess*, instead of the old candidate-minus-raw gap and a separate absolute child-Theta drift.

A concrete root theorem combines this with the *actual* root Fin-wave bridge:

    weightedRequest430(root) <= positive zero-generation seed
      + sum_{g=0}^{429} (BuchstabPhysicalPositiveSource_g
          + BankTrueReadIdealPositiveExcess_g + epsilon*BankPhysicalTheta_g).

The theorem is manuscript-internal and conditional only on the pinned existing analytic bank supplier's exact stated domain. Neither Buchstab nor the true-read ideal excess nor the seed has been bounded by the required final count budget.

The source intentionally does **not** identify the generated request root with the full original U3/U4 selected-count source, prove base/fixed/switched/seed/floor inequalities, resolve original root weight 7/2, or infer a smooth 430+11 joint nested refinement.

## Verification boundary

The current container was checked and has no `lean`, `lake` or `elan` executable, no pinned installed source-only dependency closure, and native GitHub DNS resolution fails. The connector can write/read GitHub files but cannot run a pinned Lean build. No Actions configuration was altered or alternate version installed. Therefore Lean compilation, kernel replay, transitive axiom audit, and finite guards are not evaluated. Static text inspection is not a substitute. **No green nodes**.

## Remaining manuscript-local work

True-read bank positive overshoot against original base/fixed/feedback and exact Q80 floor; strict-prime Buchstab positive physical deficit; zero-generation seed and switched/fixed bases; full original U3/U4 source/owner/filter/rejection multiplicities and root 7/2; PP/same-rho, signed Euler and native-history; integral–Theta–count identification and single common 430+11 causal refinement. Exact fixed-import staging, compiling, replay and axiom audits remain open.

Next: recover the fixed toolchain/import closure and compile this packet; then relate the true Q80 bank read to its literal selected candidate and bound the **true-read ideal positive excess**, together with the Buchstab physical positive source, without inventing a count owner or using signed-total cancellation.

**完整h34稿内证明仍未闭合。**
