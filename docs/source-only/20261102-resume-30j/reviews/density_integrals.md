SOURCE_REVIEW_PASS for the frozen J/all22_suppliers local integral dictionary and equal slot replacement. Full22 actual suppliers and common-policy density remain OPEN. This is an independent mathematical source review: compiled=false, kernel_verified=false, formal_credit=0.

The exact reviewed packet is:

| File | Raw SHA-256 |
|---|---|
| all22_suppliers/P4AOriginalSecondPhysicalIntegral.lean | `80a1bc31857ad989262c6c7f20dfce08cba657700aa54d3ff7b9f4c5dba037c0` |
| all22_suppliers/REGISTRY.json | `666036ce4dea6fc55c17b34c008261e2ca4ab7ec116378a85469ea5d9faaeed8` |
| all22_suppliers/REPORT.md | `4bcff62c0f6c5b78a35bf08b1e5ce7db43bb99d634bfa893b990eb4cb16b6983` |

Paths above are relative to `docs/source-only/20261102-resume-30j/`. Every registered local source/reference pin was recomputed and matched. Exact dependency and reference pins are retained in `density_integrals.json`; this is not a full transitive import audit.

The source was compared with J README/TASKS, original manuscript lines 360-514 (SHA `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`), the original second-prefix note (SHA `355954ab0d4d1d23ce6045a4baa2dee3b71f124a8550e8f1eae71fbcae70821d`), and current `AboveMuSecondCoarse.lean` (SHA `85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`). The original catalog selects entry 5, `above_mu_second_coarse_only`, field `no_grid_coarse_lower = 640339/15210735000`. The finer certificate is an alternative enclosure of this same saving.

The substantive checks pass within the stated source-only scope:

- Lines 28-82 independently define the original rational integral over `mu<x<rho`, `25/32-3*x<y<x`, with the original envelope, factor four and coordinate order. There is no factorial. The closed-region denominator bounds retain `x>=mu`, `y>=3/16` and both residuals `>=rho`, including the seam and the degenerate fibre.
- Lines 84-202 use a globally continuous clamped extension that equals the physical kernel throughout the integration region. Continuous moving-endpoint integrals supply both outer-row integrability results; fibre integrability pays the split at `y=mu`. No integrability or additivity premise is left in the endpoint theorem.
- Lines 204-254 perform genuine affine substitutions in both variables. With `h=1/384`, the substitutions are `x=mu+h*u` and `y=mu+k*h*u*v`, giving signed factor `k*h^2*u`. The scalar-multiplied affine theorem covers zero slope, so `u=0` requires neither division nor a discarded fibre.
- Lines 256-314 correctly handle the negative orientation. The `k=-3` oriented interval runs from `mu` down to the lower boundary, and its signed chart integral is negative. Reversing the physical row cancels that sign. The `k=1` row has positive orientation. The proved fibre split then gives `physicalSaving = totalChartIntegral` for the whole original iterated rational integral.
- Lines 316-338 transport the existing analytic coarse endpoint by that equality. No endpoint or physical/chart identity is assumed. The ledger adds back the already-counted chart saving and subtracts the equal physical saving exactly once. Both original reserves and `K=8452171/1250000` remain unchanged; no twenty-third saving is introduced.

The relevant affine, congruence and adjacent-interval signatures were inspected at the manifest's exact revision in [Mathlib interval integrals](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean). The moving-endpoint continuity theorem is available from the candidate's direct [DominatedConvergence import](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean). These source checks do not establish successful elaboration.

The current first-sharp endpoint proposal and its selected-K consumer were read, so older comments describing that endpoint as unpaid were not treated as current evidence. The partial-ledger theorem still inherits that uncompiled proof chain, including its unexecuted finite rational comparison. This review does not validate that guard numerically or confer kernel credit on any predecessor. The physical slot-5 dictionary itself does not assume the first-integral endpoint.

The remaining gap is explicit and substantial. The source note's lines 75-86 and 152-166 require the same causal policy, rank-three restoration, preserved below-mu witnesses, control of the disabled-small-third difference, and a common finite approximation chosen before N grows. This packet proves the rational endpoint integral dictionary; it does not prove the residual sieve-profile/density bridge, common-policy telescope, or full physical coefficient bound. Remaining supplier histories, catalog13 cap distinctions, full87 geometry, catalog21/22 increments, and expenditure within both reserves remain separate obligations. H transfer_power's report/registry were read and none of those distinctions is altered here.

No mathematical defect was found in this local route. Accept the narrow source step while retaining P4A.4 actual_all22 and P4A.5 hdensity OPEN. No compiler, build, CI, finite mathematical replay, Git, quota query or subagent was used. Only these two review files were written; author, production and predecessor sources were left untouched.
