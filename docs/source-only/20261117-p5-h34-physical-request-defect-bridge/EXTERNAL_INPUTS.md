# P5.6/h34 — physical request wave external inputs (2026-11-17)

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Lean version: `v4.33.0-rc1`. Mathlib version: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic inputs: NONE. No external proofs implemented.**

## Reused fixed basic algebra

- Existing Lean/Mathlib `List.map`, `List.sum`, finite list induction, `ring`, `simp`, `rw` and real arithmetic. Used in `edgeValue_eq_raw_plus_theta`, `waveAccount_add`, `actual_request_local_defect_exact` and the root telescope. Their transitive axiom closure is not separately audited.

## Reused manuscript-local (NOT external) source-only interfaces

- `Part5OriginalH430RequestedReads.requestValue`, `resolve`, `iterate`: actual scalar versus specified-cell request reads, used by `iteratedRequest` and the selected/exterior lemmas.
- `Part5OriginalH430RequestedBranches.children`, `edgeWeight`, `edgeValue`, `nextRequest`, `exterior_children_empty`: actual chosen request and physical same-Q child source, used by `childThetaDrift`, `edgeValue_eq_raw_plus_theta`, `exterior_physical_gap_zero`.
- `Part5OriginalH430ActualRequestAllActionWave.actualStep`, `step_retained`, `step_exterior_zero`, `waveAccount`: actual preceding iterate physical step, used by `physicalStepDefect`, `selected_retention_physical_gap`, `exterior_physical_gap_zero`, `root_iterated_request_exact_physical_wave`.
- `Part5OriginalH430RequestWaveTelescoping.localDefect`, `root_eq_terminal_plus_defects`, `selected_retention_defect`, `terminalSeed`: actual chosen request-wave telescope, used by `actual_request_local_defect_exact`, `selected_retention_total_gap`, `root_iterated_request_exact_physical_wave`.
- Existing source-only `thetaAtom` and `parentProduct` definitions are used at the **same physical Q** in `physicalStepDefect` and `childThetaDrift`. Their genuine manuscript-local payment consumers remain OPEN.

## Not externally delegated

The correct full U3/U4 count diagnostic, selected/inherited owner, Q80 closed-cell induction, quantitative Buchstab/retention payment, correct Theta-normalization signed control, PP/same-rho consumer compatibility, native-history quality and outer 430+11 common nested causal refinement remain manuscript-local proof obligations. Neither an axiom nor a target-equivalent count hypothesis has been introduced.

No compiled theorem, kernel replay, transitive-axiom check, external source-version verification beyond the pinned records, or finite certificate is claimed.
