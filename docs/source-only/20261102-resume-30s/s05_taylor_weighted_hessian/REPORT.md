# S05 — full signed weighted Taylor diagonal Hessian

**SOURCE ONLY / UNCOMPILED / kernel_verified=false / formal_credit=0.**

The assigned analytic Hessian step is source-complete in two new Lean files. They prove the actual coordinate product and chain rules and the exact original `M[i]` bound for the complete signed affine Taylor integrand. They assume neither a Hessian estimate nor a Taylor/floor/integral licence. The original raw kernel is identified with this extension through R04's proved finite-branch conversion.

**The whole D02 yellow node is not closed by S05.** Actual archive finite facts, the rational-data cast of `M[i]`, five-dimensional integration, original stored-old binding and the whole old-branch terminal belong to the coordinated S07/S06/S08 assembly. The new sources and all inherited sources remain uncompiled here. Root alone owns remote kernel evidence and color changes.

## Original requirement and exact source inspection

The manuscript `chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:367–375` preserves actual ancestors and makes the fourth/fifth/sixth changes successive replacements, without another copy of the same gain. Its SHA256 is `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.

The specific analytic requirement is the complete integrand and derivative paragraph in `goldbach-research/fifth-prefix-taylor-pilot.tex`, especially the smooth-box reduction, explicit derivative bounds and final formula

\[
G=w\,d,\quad w=\frac4{t_1t_2t_3t_4t_5^2},\quad
d=\frac{\log(s_n-1)}{s_n}-\frac{\log(s_o-1)}{s_o},
\]
\[
M_i=w_+\{q_i m_1\delta+2k_i
\min[m_1(D_{ni}+D_{oi}),\ m_1T_i+m_2\delta D_{oi}]
+m_2(D_{ni}^2+D_{oi}^2)+m_1(E_{ni}+E_{oi})\}.
\]

The original `certify_fifth_prefix_taylor_pilot.py:39–94` was read directly before authoring. Its branch checks, vertex ranges, `m1/m2`, correlated gap, `D/E/T`, power 2 in the last slot, cancellation minimum and `M.append` expression agree with the formulas above. The surrounding original TeX and the original main manuscript were read, not inferred from later consumer structures. No original program or data computation was executed.

The frozen R04 nine-source REPORT/REGISTRY and R25 independent review were read. Production, all source-only paths and ignored `.lake/proof-continuation/source-reviews/drafts` were searched for existing Taylor/Hessian work. Existing R04 logarithm/profile, branch/actual-owner, affine-ratio and weight proofs are reused. The existing one-dimensional midpoint proof is assigned to S06 and was not reconstructed here.

## New sources and exact exported interfaces

### `P5OriginalTaylorWeightedAxisCalculus.lean`

Import: `ImbalancedChen.P5OriginalTaylorWeightDerivatives` at its exact frozen R04 source.

The functions `axisDifference`, `axisDifferenceSlope`, `axisDifferenceCurvature` are respectively

\[
d=f(s_n)-f(s_o),\quad d'=f'(s_n)s_n'-f'(s_o)s_o',
\]
\[
d''=(f''(s_n)(s_n')^2+f'(s_n)s_n'')
 -(f''(s_o)(s_o')^2+f'(s_o)s_o'').
\]

`axisKernel`, `axisKernelSlope`, `axisKernelCurvature` use the actual R04 `axisWeight`, its first derivative and its second derivative. `hasDerivAt_axisKernel` and `hasDerivAt_axisKernelSlope` prove their derivative relationship from `HasDerivAt.mul`, `sub` and composition with the actual profile derivatives. The second derivative is exactly `w''*d + 2*w'*d' + w*d''`.

`original_affine_kernel_on_axis` identifies this coordinate function with the full `affineTaylorSignedKernel new old (Function.update t i x)`. This is an equality derived from the actual affine quotient and full weight, not an input asserting that a supplied function is the integrand.

`continuousAt_axisKernelCurvature`, `continuousOn_axisKernelCurvature` and `continuousOn_affineTaylorSignedKernel` supply the continuity needed for the original one-dimensional midpoint proof and its product-box assembly. They use only nonzero positive coordinates and profile arguments greater than 1. `axisKernelCurvature_rebase` lets the midpoint proof evaluate the same genuine second derivative at any updated box point.

The interval endpoints and cap seams cause no additional derivative premise: the smooth affine extension agrees with the original raw kernel on the entire closed box by R04. No claim is made that the raw max function continues with this derivative outside that box. The stronger original range `[2,4]` is used by the bound; smoothness of the extension only requires arguments greater than 1.

### `P5OriginalTaylorWeightedHessian.lean`

Import: the preceding new module.

`pilotSecondBound` is the original `dii`. `pilotHessian` is exactly the original `M[i]`, with the R04 actual normalized `raw.lower` endpoints and original `pilotD`, `pilotE`, `pilotT`, `pilotK`, `pilotR`, `pilotWMax`, `pilotM1`, `pilotM2`, `pilotFirstBound` definitions. It is not enlarged to hide a lost cancellation or an incorrect fifth-coordinate denominator.

`original_second_chain_bound` proves the bound for both new and old second chain-rule terms by actual `firstCurvature` and `firstSlope` bounds. `original_axisKernelCurvature_le_pilotHessian` then proves

\[
|\operatorname{axisKernelCurvature}(n,o,t,i,t_i)|
 \le\operatorname{pilotHessian}(raw,n,o,a,s_n^{max},s_o^{max},\delta,i).
\]

Its full remaining mathematical input list is: positive original lower endpoints, `t ∈ rawClosedBox raw`, `2 ≤ a ≤ s_o(t) ≤ s_n(t) ≤ 4`, `s_n(t) ≤ snMax`, `s_o(t) ≤ soMax`, `s_n(t)-s_o(t) ≤ delta`, and nonpositive fifth residual coefficients. These are primitive original range/box data; no derivative bound is an input. R04 supplies all factor estimates used internally.

`original_selected_axisKernelCurvature_le_pilotHessian` specializes to the original `newPlane raw newSide` and `selectedOldPlane oldSides selected` and discharges both coefficient signs from the original tent/W definitions.

`original_signed_weighted_hessian` combines this bound with R04 `original_signed_kernel_eq_affine`. Its only extra input is `BranchFacts`, whose fields are rational active-side, selected membership and signed affine-dominance checks. There is no target-equivalent cap-equality, Hessian or integral field.

## Actual-data coordination and premises

S07's `P5OriginalTaylorRationalData` reconstructs `newAffine`, `oldAffine`, `aMin`, `newMax`, `oldMax`, `gap` and `hessianQ` from the actual ten-column `FifthWireRow`. Its `actual_ranges raw h t ht` supplies exactly the primitive real range inputs above from `TaylorFiniteFacts`; it was read and checked against this interface. The original `hessianQ` differs from `pilotHessian` only by rational-to-real casts, squares written as products, and the equivalent first-four-slot branch of `TQ`.

S06 now supplies the single `hessianQ_cast` bridge and `actual_hessian_bound` in `P5OriginalTaylorActualMidpointIntegral.lean`. The latter states, for the same actual row and `TaylorFiniteFacts raw`, that the absolute genuine axis curvature is at most `(hessianQ raw i : ℝ)`; it directly consumes the S05 selected-plane theorem and S07 `actual_ranges`. Those two declarations were read. Thus the actual-data consumer has no free maxima/gap/plane parameters and no caller-supplied Hessian bound. S05 does not duplicate those casts or new finite bodies. S06 received the exact names, argument order, continuity and rebase interfaces. S08 received the unchanged formula and scope. S25 independently read both new files against the original TeX/Python and frozen R04 factors and reported no mathematical mismatch; Lean API/kernel status remains pending. Exact reused source/declaration hashes and the concrete remote targets are in `REGISTRY.json`.

Premises removed in this analytic step:

- Assumed first/second derivatives of the complete signed weighted integrand.
- Assumed continuity of its second coordinate derivative.
- Assumed full diagonal Hessian bound or a pre-certified `M[i]` licence.
- Caller-supplied signs for the actual new/old residual coefficients.
- An assumed equality of a chosen affine old cap with the actual raw fifteen-mask-plus-W envelope; the original R04 `BranchFacts` conversion is used instead.

Remaining beyond S05:

- Actual closed finite `TaylorFiniteFacts` and original stored-old source bindings for the archive; S07's closed source bodies are not executed by S05.
- Reliable verification of S06's supplied rational cast/actual Hessian specialization and the five-dimensional `1/24` integration terminal, plus the final whole original fifth-floor assembly in S08.
- The independent original parent Jensen path and final fixed `oldBranchDefectQ` treatment in the whole D02 terminal.
- Exact-source dependency staging, elaboration, kernel checking and axiom output on the pinned Lean/mathlib revisions, performed only by root's authorized remote workflow.

No constants, grid, argument range, coefficient normalization, reciprocal-prime density, signed old term or stored-floor semantics changed. The original strict `s_o<s_n` implies the weak ordering sufficient for the analytic estimate. No new out-of-manuscript mathematical goal or additional reserve charge was introduced.

## Difficulty classification and verification boundary

This fills a **fillable omitted deduction**: the manuscript already states the correct chain/product formulas, but their combination into the full weighted Hessian was absent from R04. No evidence of a substantive manuscript gap or bad archive row was found. Uncompiled tactic/API and dependency-path issues are separate formal expression risks, not mathematical counterexamples.

No local Lean, Lake, compiler, build, proof guard, numerical producer/replay, Git/remote mutation or child agent was run. Only source/text/JSON/byte/hash inspection and authored Lean/report/registry text were used. There are no new finite reduction bodies in S05.

The remote verification owner should stage the exact two modules and their pinned import closure; compile `ImbalancedChen.P5OriginalTaylorWeightedHessian`; check the named derivative, continuity, bound and actual-signed terminal declarations; and record `#print axioms` for those terminals and S06's eventual actual-data specialization. A CI pass alone would not close D02 if S07/S06/S08 original scope is still missing. The exact remote commit and same-source kernel receipt do not exist in this source-only delivery.
