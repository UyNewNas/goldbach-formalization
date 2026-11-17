# P5.6 → h34: literal integer-Q80 selected-bank physical excess

Date: 2026-11-17. Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Previous verified HEAD: `38dcb7f2464a580257b15ff9650f77812f27dbcf`.
Mathematical source commit: `8e7e3685567eabc4edb17f5a0c28232393144b38`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (do not switch to November manuscript).
Pinned Lean: `leanprover/lean4:v4.33.0-rc1`; Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**SOURCE_ONLY / UNCOMPILED / UNEVALUATED / PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN.**

## Actual mathematical increment

New source: `Part5OriginalH430LiteralBankQ80PhysicalExcess.lean` (198 lines, 3 definitions, 6 theorem declarations).

The preceding `Part5OriginalH430DirectPhysicalBankPayment` derived a one-sided physical bank source estimate, with an unpaid positive excess of the true selected Q80 request read over the true same-Q bank ideal. This packet makes that selected reading literal, without using the scalar owner to replace a specified-cell request:

- `literalChosenBankQ80` is the exact original integer `P2Selected430LiteralActionData.candidate (iterate g) (rows (slotOfAction a)) / 2^80`.
- `selected_bank_true_read_eq_literal_q80` uses the ACTUAL `Selected` certificate at each original selected Fin history slot (the selected resolver supplies its own cell), and the preexisting `selected_value` theorem.
- `true_read_ideal_excess_eq_literal_q80` transfers that literal identity into the full original mark-weighted positive physical bank source, without quotienting repeated occurrences.
- `selected_literal_q80_le_real_candidate` uses the existing finite candidate upper bound, and `literal_q80_excess_le_real_candidate_excess` combines it with theta nonnegativity derived from the already admitted root geometry. Positive parts are compared **pointwise before summing**.
- Two root-level theorem bodies replace the previous read-excess by the exact literal Q80 excess, retaining the original `bankPhysicalAppliedAbs` or pinned uniform `epsilon * bankPhysicalTheta` allowance.

The exact gap `bankLiteralQ80IdealExcess` is **not paid**. Its real-candidate upper envelope `bankRealCandidateIdealExcess` is also **not paid**. They must not be mistaken for a small coefficient error, nor can the original signed total error be used to bound their positive parts. The packet supplies no numerical430 replay or count-source identity.

## Validation and compatibility boundary

Read the initial `20261105-p5-h34-request-admission/{REPORT.md,REGISTRY.json,EXTERNAL_INPUTS.md}`, then the actual latest handoff `20261117-p5-h34-direct-physical-bank-payment` and related `ActualQ80CandidateSurplus`, `RequestedReads`, `RequestedCandidateLevel`, `DecisionProvenance`, `SelectedBankGlobalFloorBaseLedger` sources before this increment. No P1.4/P3.6 or other workstream file is modified.

The active container was checked: neither `lean`, `lake` nor `elan` exists on PATH. A pinned source-only installed import closure is not present. Native GitHub DNS lookup did not resolve. The connected GitHub API enabled source read/write, not Lean compilation. Therefore **no compile invocation, no successful typecheck, no kernel replay, no transitive axiom audit and no finite certificate replay** are recorded. Structural/text inspection only, no formal-green credit. Staging the source file alone is not a complete installed build.

The frozen c/K, 7/2 root coefficient norm, 12 bank row norm, genuine alpha, same Q, selected-cell/scalar distinction, repeated history marks and 430+11 budget are unchanged. The only new write is this h34 source-only packet; CI, master and pinned dependencies are untouched.

## Remaining manuscript-internal obligations

1. Quantitatively pay the **positive** true selected bank Q80/real candidate–ideal gap, including its exact original base/fixed/feedback/floor directions; do not misuse a signed aggregate estimate.
2. Pay the actual strict-prime Buchstab physical positive gap and the correct zero-generation seed/base/fixed/switched/floor in the same root.
3. Prove the complete original U3/U4 full/selected/inherited count-source, its genuine owner, rejection multiplicities, q/tag receipts, and 7/2 outer root weights; existing request-history source is not a count-source identity.
4. Complete manuscript-local PP/same-rho, signed Euler and native-history mass payments, integral–Theta–count identification and one 430+11 nested causal refinement.
5. Reconstruct pinned source-only import closure and run the incremental Lean/Lake compilation, kernel replay, axiom audit and finite guards.

Next meaningful mathematical action: use the old integer bank quotient/remainder ledger to split the genuine `bankLiteralQ80IdealExcess` into fixed/base/floor and real feedback components under the **same** selected request and same Q, then seek positive-part estimates. Prioritize rebuilding the pinned imports to validate these candidate proofs.

**完整h34稿内证明仍未闭合。**
