# P3.1 actual coefficient mass budget implementation plan

**Goal:** Specialize the accepted common six-piece hard-tail estimate to the original actual mode coefficients and replace its source absolute mass by the original finite raw-label budget.

**Architecture:** Recover the smallest original coefficient definition and norm-proof closure, preserving the original namespaces and formulas. Recover the two original raw-label declarations separately, bound their actual finite carriers with the original endpoint/frequency counts, then compose these suppliers with the frozen accepted six-piece tail. Record the exact common cutoff after substituting `R = x^epsilon / 10` without claiming a uniform full-family error estimate.

**Tech stack:** Lean 4.33.0-rc1 (`62eed1db4d67327ec8120be05f1a1b0847d74561`), Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, the existing Part 3 continuation verifier, and the existing P1 accepted dependency cache.

**Spec:** `../p31-common-hard-tail-20261127/NEXT_P31_STEP.md`, the 1106 analytic appendix at manuscript commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`, and the original source fragments identified in this round's intake.

## Constraints and review focus

- Reuse reliable existing local and remote work; perform a bounded delta audit before selecting recovered fragments.
- Preserve every previously accepted Lean provider byte-for-byte. The baseline for this round is `e63206af301eb31c3518794fe5f9a1816e61f3b6`.
- Keep `gamma2` outside branch conjugation, retain the actual signed shortened block and residue indicator, and derive coefficient bounds from `MediumAdmissible` and the actual definitions.
- Keep the source's full signed `f` interval, including its endpoints. Apply mass monotonicity only with nonnegative norm summands.
- Quantify the tail constant before all scales, source data, modes, and signs. The cutoff substitution requires `x > 0` and preserves an exact `Nat.ceil` equality.
- Do not formalize new manuscript-external analytic inputs, introduce proof placeholders or new axioms, or identify the local coefficient budget with the still-unproved full-family error budget.
- Write proofs in this local Git-backed checkout. Cloud jobs receive exact source bytes and only compile or inspect them.

## Tasks

- [x] Recover the original actual coefficient definitions and their norm proofs in `ImbalancedChen/Part3ActualModeCoefficientNormsCore.lean`, with a minimal import closure and a per-fragment provenance manifest.
- [x] Recover `rawLabelBudget` and `sourceAbsMass_le_rawLabelBudget` in `ImbalancedChen/Part3ActualHardTailLabelBudget.lean`; prove the finite nonzero-source mass comparison using the existing source definition.
- [x] Recover the three original finite cardinality suppliers in `ImbalancedChen/Part3ActualLabelBudgetCardinality.lean` and derive the actual count bound `(2*F+1)*((Q2+1)*(2*H))^2`, keeping the full signed closed interval and its endpoint allowance.
- [x] Implement `ImbalancedChen/Part3ActualModeSmoothMassTail.lean` by specializing the accepted six-piece theorem to the actual coefficients, then substituting the manuscript cutoff. State remaining reconstruction and family-budget obligations explicitly.
- [x] Extend the existing verifier with one new target group and source-intake rules only. Preserve existing groups, shared audit body, full inventory and transitive-axiom checks, source/object binding, and provider freezing.
- [ ] Compile the exact integration targets, repair only diagnosed errors, independently review the mathematical interfaces and verifier extension, and publish a pinned source commit.
- [ ] Run the complete strict compile, individual kernel replay, declaration inventory, three-axiom gate, dependency source/object gate, and existing regression checks at that fixed commit.
- [ ] Commit unchanged verification receipts and the honest remaining P3.1 boundary in an evidence-only descendant.

The user's continuing implementation and GitHub-publication instructions already authorize this plan. No additional approval step is required.
