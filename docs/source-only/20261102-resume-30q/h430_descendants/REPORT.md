# Q14 — actual descendant limits, active knot strips and a physical Buchstab budget

**Partial source increment; the full descendant/common-realization target remains OPEN.** Three new Lean sources supply actual local deductions. They do not supply the immutable430 history, the outer parent-prime Theta integral, or a common 441-generation smooth arithmetic realization. `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `task_complete=false`, `ready_to_install=false`; finite proof bodies/guards remain **UNEVALUATED**.

Only this Q directory was written. No compiler, Lean/lake, CI, numerical replay, proof-guard evaluation, Git operation, installation, old-file edit or child agent was used.

## Governing evidence and reuse

Read Q BRIEF, both P H430 REPORT/REGISTRY files, P review `t25_review_h430.md`, Q03 `q03_original_gap_triage/REPORT.md`, the actual manuscript 857–895, completion note 272–289, and the relevant M/O/P and production sources. The governing manuscript SHA256 is `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`; the completion note SHA256 is `8597fd1dc01d3fc49e5b31d28afeab3cf48e88ae23908fb6777a1c23f5b360e5`.

The manuscript requires preceding generations, maxima of alternatives, closed support minima, seed-only430, the actual U3/U4 clamp, one pre-N nested refinement, norm12, root norm7/2, depth440 and the loss `(12^441-1)/11`. The completion note explicitly retains inherit/equality regions and says finite depth alone does not discretize continuous children. None of those requirements is replaced here.

Exact implemented sources are reused rather than rewritten:

- P `Part5OriginalH430MovingBuchstabAtoms`: actual moving primitive dictionary; `startAtomDensity_integrable`; `startAbsoluteError_bounds`. The old interval-strip proof is not duplicated.
- P `Part5OriginalH430FrozenTableRootMass`: `frozenQuery_tendsto`, and the already supplied non-clamp root H430 term. No root table-weight proof is repeated.
- O `Part5OriginalH430FrozenPerturbation`: same-coordinate `realize_slots_eq`, `realize_ceiling_eq`, `actual_descendant_residual_loss`, root-loss bound and the exact moving-pair physical quotient.
- O `Part5OriginalH430PhysicalMassPerturbation`: `physicalWeight=4/(word.prod*residual)`, singleton insertion and Buchstab Jacobian. The new source retains this complete-prefix factor.
- O `Part5OriginalH430FrozenRootMass`: the explicit positive `finiteTau n=min(1/12,1/(n+1))` and `levelError_finiteTau_tendsto`.
- Production physical node/transition/graph, true singleton/pair profiles, closed table atom definitions, and `RenewalFiniteErrorPropagationP5.localBudget` are unchanged.

Production, prior source-only directories and explicit hidden `.lake/proof-continuation/source-reviews/drafts` paths were searched. No matching supplied descendant-limit/physical-start budget was found in this bounded search. The hidden `20261028-Transfer-Sol6-start-telescope-phase3/P2LowerStartPhysicalOwnerTelescope.lean` hit was read: it is the distinct L1/L2 ordinary first-exit reciprocal-totient telescope and itself leaves its physical-to-continuous approximation open. It is not this H430 supplier. No unavailable source was copied or silently treated as installed. REGISTRY pins direct and relevant transitive sources.

## New actual deductions

### 1. Same-Program descendant limits without assuming frozen admission

`Part5OriginalH430DescendantLimits.lean`, SHA256 `c2e801c844b1e5b445e6279df28fd23cccf38342e10ec696e954824a9822f469`.

For one literal Program and its same physical appended coordinates, put

`p = realize(code,z,sourceRoot k 0 t)` and

`p_n = realize(code,z,frozenRoot n k (finiteTau n) t)`.

`frozenDescendant_residual_tendsto:119` uses the already proved exact root-loss identity and holds for every Program. `realize_argument_tendsto:82` inducts over the original local transitions; `frozenDescendant_argument_tendsto:135` only assumes the **ideal** `Member`. It does not require `Member` for any `p_n`, nor equality of ideal/frozen indicators. The zero-, one- and two-prime formulas are all treated: constants stay constant, inherited arguments read the preceding state, and D7/D8 retain their unclamped moving quotient.

`frozenDescendant_alpha_tendsto:192` and `frozenDescendant_weight_tendsto:207` keep the same full marked word. Alpha's numerator remains `1-word.sum`; there is no reset to two. The actual positive ceiling is derived from `LocalDomain` and propagated by `perform_ceiling_pos:159` / `realize_ceiling_pos:173`, with the literal root giving `idealDescendant_ceiling_pos:181`. These are not arithmetic count licences.

`constant_child_arguments:226` retains every transport/W1-fixed/W2-fixed knot value exactly. Retain is handled by the convergence induction's unchanged-argument branch. Neither is declared a proper null wall.

### 2. Active knot strips in the same physical coordinates

`Part5OriginalH430ActiveKnotPullbacks.lean`, SHA256 `595ee1c5550376f3cdfbdc8e983ac0531e3e97d74243eb3bf05a9d17ef42e46c`.

For positive parent residual `L` and positive fresh coordinate `x`, `query_sub_knot:55` proves that the actual child argument minus a scalar knot `c` is `N/D`, with positive denominator:

| Active query | Numerator N | Denominator D | Slope in L |
| --- | --- | --- | --- |
| Buchstab, either direction | `L-(c+1)x` | `x` | `1` |
| W1/W2 singleton, actual anchor s0 | `(s0-c)L-s0*x` | `L` | `s0-c` |
| W2 fixed pair | `(s0-c)L-s0*(x+y)` | `L` | `s0-c` |
| W2 moving pair D7/D8 | `L-(c+1)x-y` | `x` | `1` |

`query_knot_comparisons:91` gives the actual closed, strict and equality comparisons. `actual_knotNumerator_error:128` derives `|N_ideal-N_frozen| ≤ |slope|*levelError` from the exact same-coordinate root loss, with no assumed approximation error. `actual_active_knot_change_strip:142` proves that a changed closed comparison is inside the resulting **closed** physical strip. It keeps equality in the budget.

This file covers active query numerators, not every W1/W2 admission gate. It does not prove a global null-fibre theorem or the mass of these strips against the parent-prime measure. Positive frozen residual is a local denominator premise here; the first file separately proves it eventually along any admitted ideal path. Zero-prime comparisons are deliberately excluded from the active-query type.

### 3. Actual ceiling, complete parent weight, Jacobian and absolute Buchstab error

`Part5OriginalH430BuchstabPhysicalBudget.lean`, SHA256 `3035244dba603222d96c79e79bce017d7c6ccaba36b9322a7c352ab42a95a2a8`.

The actual ceiling was not present in the unconstrained moving primitive domain. If `C=p.ceiling`, the exact new start is

`a_+(p)=max(max(2,p.argument-1), L/C-1)` and

`a_-(p)=max(p.argument-1, L/C-1)` (the lower action also needs `p.argument≥2`).

`actual_buchstab_domain:72` derives these starts from the full literal `LocalDomain` after `x=L/(w+1)`: the prime ceiling gives `L/C-1≤w`, while `w≥1` gives the new square. No fixed table-cell start or `StartMatches` premise is used. The unused native coordinate is explicitly zero padding.

`physicalAtomPullback_eq:110` retains each original closed `FloorAtom`, including singleton knot atoms. `actual_buchstab_Jacobian:129` and `physicalAtomDensity_eq:157` give the literal identity

`[L/(w+1)^2] * physicalWeight(child) = physicalWeight(parent) * buchstabKernel(w)`

on the admitted pullback, including the actual full parent word factor. Upper Buchstab reads lower h (`tableAtomSet true`); lower Buchstab reads upper H. No lower/upper polarity or adjacent minimum is changed.

Let `P=physicalWeight(p)`, `Q=physicalWeight(q)`, and let A/B be the two actual effective starts. `weightedAtomError_bounds:225` proves the **absolute** integral bound, before any signed cancellation,

`∫ |P*atom(A)-Q*atom(B)| ≤ 4|P-Q| + |Q||A-B|`.

The factor 4 is the length of the actual common scalar ambient `[1,5]` and uses `buchstabKernel≤1`; the start part directly reuses P's proved strip inequality. No atom mass is divided out. `coefficient_difference_le:259` then bounds the difference of the actual atom integrals.

`buchstabBudget:275` is a literal specialization of production `localBudget` to **one ordinary Buchstab action**, zero base, its closed `FloorAtom` children, and the supplied old array's exact `floorAtomValue`. `buchstabBudget_bounds:287` derives

`localBudget ≤ floorBound(nums) * (4|P-Q|+|Q||A-B|)`.

This is a derived estimate, not a consumer taking that estimate as a premise. Arbitrary `nums` here records the array role; it is not an identification with an immutable430 predecessor array.

For the actual `p_n` above, the new limit theorems prove `a_+(p_n)→a_+(p)` and `P_n→P`. `actual_upper_weightedAtomError_tendsto:335` and `actual_upper_physicalAtomError_tendsto:352` therefore give a true absolute error tending to zero for the physical candidate's **LocalDomain-filtered w-pullback** densities at each fixed ideal physical prefix. The last theorem supplies positive ceiling and eventual positive frozen residual from the first file rather than assuming them. `actual_upper_buchstabBudget_tendsto:320` supplies the corresponding one-action budget. `actual_lower_buchstabBudget_tendsto:370` covers the strict actual parent range `s>2`; it expressly does not delete or silently settle the lower `s=2` equality stratum. The PhysicalNode candidate can be formed regardless of the endpoint TypedNode's upper/lower flag; an actual next Program edge additionally requires `incomingAllowed` and its `cellMember`.

## Exact remaining boundary

1. **Full native-coordinate moving admission.** No theorem yet controls the symmetric difference of the entire ideal/frozen `Member` domains on all native prefix variables. `actual_buchstab_domain` is precisely a `LocalDomain` equivalence; it does not include `TypedNode.incomingAllowed`, next-step `cellMember` or source-history ownership. W1/W2 admission gates, lower `s=2` inheritance, and the measure of the active knot strips still require their full proper/identity classification and parent integration. The new same-coordinate scalar strips are not that theorem.
2. **Coordinate and measure distinction.** `coefficient_eq_physicalIntegral` is an integral in `w` of the explicitly defined physical Jacobian pullback. At the two parents, `x=L/(w+1)` is a different physical map. The file proves the pointwise Jacobian identity and absolute error in this common `w` space; it does not supply a change-of-variables theorem identifying both original native-x integrals, or a same-native-x L1 theorem.
3. **Actual parent Theta.** The continuous factor `4/(word.prod*L)` is retained and its local variation is derived. It is not the arithmetic `C(BN)/phi(B)/log(Q/B)` mass law. Integration over the real parent prime family, joint measurability/positive-cutoff domination there, and absolute zero-Theta handling in that arithmetic passage remain open.
4. **Normalization and immutable history.** The new one-action coefficients contain the full parent physicalWeight. Their total mass is therefore not automatically at most12. They cannot be inserted as the normalized transition row in `iterate_430_rounds_11_depth` without the actual Theta normalization. The original fixed/feedback/switched bases, all 70/36 actions, labels and multiplicities, selected old arrays, and immutable seed-only430 preceding-generation history are not instantiated here. No claim is made that a Unit/zero-base specialization provides them.
5. **Common smooth realization.** No simultaneous nested smooth family or uniform pre-N threshold for all actual 441 generation occurrences is constructed. The fixed `1/50` table grid has not become finer. The new limit compares two genuinely moving starts, so its arbitrary accuracy does not rely on the invalid fixed-grid argument. The original norm12, norm7/2, depth440 and `(12^441-1)/11` remain unchanged and uninstantiated for this full task.
6. **Other required sources.** The full root `(upperAmplitude-H430)*branchWeight` term still needs the continuous upperAmplitude component. Positive D5-bad/Gamma9–21 switched costs remain separate labelled bases. Q13's stable `Part5OriginalH430RootSourceDictionary` was inspected: it supplies a geometric classical/enhanced/ell_aux distinction and selected root/BV progress, not a complete H430 root count licence. Q14 imports none of those claims and does not alter physical residual, alpha or source history to use an analytic cover.

Thus the new deductions are class **(2), supplied omitted local analysis** at source level. Their elaboration/API status is class **(1), unchecked**. The full arithmetic common-refinement/Theta/immutable-history composition remains class **(3), a potentially substantive missing construction**. This work proves neither an original-manuscript counterexample nor full closure of `P5.6.eight_suppliers` or the current main.md yellow descendant leaf.

## Static verification

Relevant local Mathlib sources for limits, division, indicator positivity, Bochner integrals and interval volume were read. New source-token scans found no admissions, axioms, evaluation directives or unsafe code. SHA256, source-byte counts, declared names and import mappings are recorded in REGISTRY; these checks do not execute proof bodies. The new direct project imports still refer to source-only M/O/P dependencies at their intended `ImbalancedChen.*` module paths. They were not installed, elaborated or kernel-checked.

Parent-assigned Q26 independently read all three candidates, including the final positive-ceiling and absolute-L1 additions, and found no definite local mathematical blocker in the explicitly restricted range. Its independent report remains the review authority; this is not a compiler or kernel acceptance claim.
