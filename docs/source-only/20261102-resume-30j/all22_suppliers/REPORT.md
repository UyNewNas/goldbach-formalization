# J / all22_suppliers: catalog 5 physical integral supplier

Status: **local source step implemented; full original all22 target OPEN; uncompiled; kernel_verified=false; formal_credit=0**. Only this assigned directory was written. The assignment records gpt-6-astra / xhigh; runtime model identity was not separately queried.

The new result identifies the original whole physical second-prefix saving integral with the two chart integrals already bounded by `Certificates.AboveMuSecondCoarse`. It supplies the missing analytic change of variables, rather than another rational endpoint calculation or a fourth independent supplier. The original first sharp endpoint was inspected in `P2OriginalFirstIntegralEndpoint` and `P4AActualFirstIntegralSelectedK` and reused without duplication.

## Original source and exact scope

The current manuscript, SHA `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, lines 360–514, requires actual successive-parent differences, four base terms minus twenty-two savings, and two separate original reserves. The adopted catalog's entry 5 is `above_mu_second_coarse_only`, field `no_grid_coarse_lower`, exactly `640339/15210735000`. Its independent result explicitly distinguishes this coarse value from the finer 2048-cell alternative; no fine value, PASS field or replay result is used as proof here.

The original source note is `../chen-imbalanced-semiprimes/proof-library/source/second-prefix-upper-fallback-20261009.tex`, SHA `355954ab0d4d1d23ce6045a4baa2dee3b71f124a8550e8f1eae71fbcae70821d`. Its precise obligations are:

- Lines 22–57: the physical domain `mu<x<rho`, `25/32-3*x<y<x`, actual old level `v(x)` and new level `v(y)`, with restored third nodes permitted.
- Lines 59–73: the physical rational integral, factor four, and no ordered-slot factorial.
- Lines 75–86: endpoint scope, common finite approximation and the small-third-tail error; no identity for an arbitrary frozen finite coarse tree.
- Lines 88–129: two affine charts, their orientation/Jacobian and the adopted coarse endpoint.
- Lines 152–166: strict-buffer realization before N grows.

The earlier coarse supplier proves the two chart integrals and a pointwise pullback identity, but explicitly leaves the physical integral dictionary open. This delivery closes that particular gap for the original iterated `(x,y)` integral. It does not assert a new general two-dimensional change-of-variables theorem or a new finite-policy density theorem.

The H transfer_power report and registry were read. Its catalog13 `actual_cap` distinction between R0, comparison D33 and unchanged final mask34 cap M is preserved: this delivery does not touch those sources, turn a comparison into an action, or add any cap family. Catalog21/22 remain increments. Dedicated compact, saving16, saving19 and fifth work is untouched.

## New proof bodies

`P4AOriginalSecondPhysicalIntegral.lean` independently defines

    physicalSaving = integral x=mu..rho, integral y=(25/32-3*x)..x,
      4*(v(y)-v(x))/(x*y*(v(x)-x-y)*(v(y)-x-y)).

Here `mu=25/128`, `rho=19/96` and `v` is the original two-branch envelope. `physicalDomain_iff` identifies its physical fibres with the existing source domain.

`physical_denominator_bounds` derives, on the full closed physical region, `x>=mu`, `y>=3/16`, and both residual denominators `>=rho`. In particular the proof covers the seam `y=mu` and the zero-width fibre `x=mu`. A continuous extension clamps denominator factors only outside this region. Its equality to the real kernel is proved on the region, and moving-endpoint continuity pays the negative and positive outer integrability obligations. `physical_fibre_intervalIntegrable`, `physical_row_split`, `physical_outer_intervalIntegrable` and `physicalSaving_eq_split` then prove the actual split at `y=mu` with no integrability premise.

`orientedPhysicalChart_eq_pullback` applies affine interval substitution twice: first `x=mu+h*u`, then `y=mu+k*h*u*v`, with `h=1/384`. The signed factor is exactly `k*h^2*u`. The `k=-3` inner interval runs from mu down to the lower physical boundary; reversing that interval supplies the required minus sign and hence the absolute Jacobian. The proof never divides by u and retains u=0. It uses the existing pointwise kernel identity only after performing genuine integral substitutions.

The resulting closed declarations are:

- `physicalSaving_eq_totalChartIntegral`: exact equality to the two existing chart integrals.
- `original_physical_saving_ge_catalog_five`: the original rational endpoint is a conclusion about the whole physical integral, with no endpoint or integral-identity hypothesis.
- `physicalSecondLedger_eq_threeSupplierLedger`: replace the already-counted chart saving once by its physical integral.
- `physicalSecondLedger_with_original_reserves_lt_K`: consume that exact replacement in the current partial ledger, retaining `K=8452171/1250000`, both original reserves, and all other entries literally.

The ledger is `threeSupplierLedger + actualCoarseSecondSaving - physicalSaving`. This is an equal replacement, not an extra saving. The theorem remains a bound for the partial ledger with other quoted slots, not a bound on the complete actual raw functional or the physical coefficient rho.

## Remaining original obligations

The following are not hypotheses hidden in the new theorem; they remain open work outside its scope:

1. Attach this endpoint physical integral to the limiting signed density of the actual common causal policy. In particular, permit rank-three restoration, preserve below-mu higher witnesses, control the disabled-small-third difference, and choose strict buffers/partitions before N grows. No arbitrary old frozen finite tree identity is supplied.
2. Bind the ordinary residual sieve-profile expression to that same policy and its endpoint limit. The new independent integral is the source note's second, rational expression; this file does not construct the full prime-density asymptotic.
3. Realize the remaining original saving sources and compact positive term on one common policy; preserve actual-parent histories, actual_cap distinctions, the full87 domains, catalog21/22 increment accounting, and both original reserves. No omitted catalog supplier is inferred from the physical slot5 identity.
4. Review and elaborate the new source and its imports. All full P4A density, P4B and main-theorem targets remain open.

There is no established manuscript contradiction. This is a missing formal integral dictionary, with a direct analytic proof route.

## Verification and installation

Install the one file as `ImbalancedChen/P4AOriginalSecondPhysicalIntegral.lean` after its registered current production imports. The direct local import and the inspected mathematical suppliers have exact raw hashes in REGISTRY. The dependency inventory does not claim an audit of the full transitive import graph.

Manual review checked the two affine orientations, residual lower bounds, seam split, zero-width fibre and single replacement accounting. The relevant Mathlib APIs were inspected at the manifest's exact revision: [affine interval substitution and interval congruence](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean) and [continuous parametric interval integrals](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean). No local Mathlib installation or hash is invented.

No compiler, Lean/lake/build, CI, finite mathematical decision execution, producer/replay, bulk literal generation, Git action, quota call or subagent was used. Static text/hash inspection only; independent review remains pending. Proposed `norm_num` and `ring` bodies were not executed. Source presence and the predecessor's proof bodies confer no new kernel credit.
