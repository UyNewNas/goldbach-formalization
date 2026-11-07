# R15 / D13 — actual native Buchstab measure and full root amplitude

**PARTIAL_SOURCE_INCREMENT. Full D13 remains OPEN.** Two new source files supply a genuine native-coordinate integral conversion and the complete continuous U3/U4 root-coefficient approximation, respectively. `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `ready_to_install=false`; all proof bodies and inherited finite guards are **UNEVALUATED**. The full Program-Member weighted symmetric difference, all W1/W2 native branch measures and outer arithmetic parent-Theta integration are not supplied by this delivery.

Only `docs/source-only/20261102-resume-30r/h430_native_weights` was written. No Lean/Lake/compiler, guard, CI, numerical replay, Git mutation, production/old-file edit or child-agent dispatch occurred. After the application restart, this directory had no partial file; work resumed from the already-read sources.

## Exact governing sources and deduplication

Read R BRIEF/DISPATCH, Q03 `NEXT_DIRECT_PROOF_REVIEW.md` D13, Q14 REPORT/REGISTRY and Q26's complete H430 review. The manuscript was read at 857–895, especially 867–877 and 887–892; the completion note at 272–289. Their raw SHA256 values are `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` and `8597fd1dc01d3fc49e5b31d28afeab3cf48e88ae23908fb6777a1c23f5b360e5`.

The original claim keeps preceding generations, closed support minima, seed-only430, norm12, root norm7/2, depth440, the `101^-440` floor and one nested finite approximation. The U3/U4 argument is `max(2,L/a)`, and its positive-measure clamp is a real state. The new results preserve these meanings without claiming their complete simultaneous realization.

Production, all `docs/source-only`, and ignored `.lake/proof-continuation/source-reviews/drafts` were searched for `upperAmplitude`, native/physical coefficient suppliers and Jacobian integral APIs. Relevant hidden copies are the `20261024z-P5/same-strategy-dictionary/Part5OriginalU34H430Integrable.lean` source and three `20261024zz-GitSourceCheckpoint/batch*/snapshot/ImbalancedChen` copies. They are the existing amplitude continuity/integrability source, not the frozen full-coefficient limit. Existing production Mellin/reciprocal integral files were used only to check the already-established JacobianOneDim calling pattern. Q14's pointwise Jacobian and w-space absolute error and P's table/clamp convergence are reused, not credited again.

The four hidden copies are byte-identical to the readable production amplitude file: 7,396 bytes, SHA256 `43100583552a7962551d32f85d88dcd088f1e4a8ae7cc8477de5317073e30358`. These exact reuse pins are also recorded in REGISTRY.

A read-only pinned public-source probe was attempted at `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`: the guessed root `ImbalancedChen/Part5OriginalU34H430Integrable.lean` URL returned HTTP404; the exact-revision Git tree API returned an unauthenticated rate-limit error. These failed probes are recorded as **UNVERIFIED REMOTE PATH**, not as absence of an external theorem. No remote bytes were silently substituted. The actual local production sources and actual UNC Mathlib source bytes were available and read; those are the pinned evidence used below. The remote scan is therefore incomplete.

## New actual native-coordinate deduction

`Part5OriginalH430NativeBuchstabMeasure.lean`, SHA256 `48492c4460192c9b6f6612370d7c14fa03e022287d5af399e621bc6d9395608c`, 12,002 bytes.

The native point has the one active coordinate `x` and zero padding in the unused slot. `nativeAtomDomain` is the **literal** set

`{x | LocalDomain p (buchstabShape upper) (nativePoint x) ∧ child.argument ∈ tableAtomSet upper b}`.

`nativeAtomCoefficient` integrates `physicalWeight(child)` against native Lebesgue `dx` on that set. The integrand remains `4/(completeMarkedWord.prod * physicalResidual)`. Its parent residual and inherited ceiling are never reconstructed from an analytic cover level.

- `nativeAtomDomain_eq_image` derives the exact image under `x=L/(w+1)` of `Icc(physicalStart,5) ∩ tableAtomSet upper b`, using the native inverse query `L/x-1`. Every closed floor atom, including singleton knot atoms, is retained.
- `nativeMap_hasDerivAt`, `nativeMap_injOn` and `nativeMap_abs_deriv` prove the decreasing map's derivative, single-valued inverse and absolute Jacobian. Thus this one-coordinate branch has multiplicity one. This does not count W1/W2 labelled occurrences.
- `nativeAtomDomain_measurable` proves measurability in `x`, by a positive-half-line inverse-query preimage. `nativeAtom_integrable` uses Mathlib's actual injective change-of-variables integrability theorem and the existing continuous Buchstab kernel on a compact interval.
- `nativeAtomCoefficient_eq` proves the genuine native `dx` set integral equals Q14's `coefficient`. It uses `integral_image_eq_integral_abs_deriv_smul`; it does not rename the old w-space integral or assume the desired equality.
- `nativeAtomCoefficient_difference_le` now bounds **two original native integrals**, applying the preceding theorem separately with each parent's different map. `actual_upper_nativeAtomCoefficient_tendsto` supplies the actual same-Program descendant integral limit from the already-derived physical residual, ceiling, weight and start limits. Its sole path premise is the ideal Program `Member`; frozen `Member` is not assumed.

The lower-direction set/equality/integrability results require `2 ≤ p.argument`, not strict `2 < p.argument`, so they include the local `s=2` boundary. This does not supply stability of the lower guard when a frozen argument crosses below 2; the original equality/inherit treatment in the full family remains necessary.

The new absolute bound concerns the absolute **difference of native integrals**. It is not a same-native-x L1 estimate: for two different residuals the maps `x_p(w)` and `x_q(w)` differ. Q14's one-action w-L1 result is left in its original scope, and is never called normalized norm12.

## Complete continuous root coefficient

`Part5OriginalH430FullRootAmplitude.lean`, SHA256 `7d1e1764f276d4faaf5a3eb15f93a4ddb04e5768915ef2b7f14b1c0951fb753e`, 16,001 bytes.

`idealFullCoefficient` is exactly

`(upperAmplitude(idealQuery)-H430(idealQuery)) * branchWeight(sourceResidual)`.

`frozenFullCoefficient` is the corresponding expression with the **actual** frozen query and frozen physical root weight. `idealFullCoefficient_eq_branch`, `idealFullCoefficient_U3/U4` and `original_U3/U4_integral` identify the ideal expressions with the original production coefficients and original half-open U3/U4 integration intervals. The closed-band convenience changes only endpoints of Lebesgue measure zero, not the positive-measure clamp.

The proof obtains a finite amplitude bound from production `continuousOn_upperAmplitude` on `[2,6]`. All ideal and frozen root queries are proved to lie in that interval; downward freezing gives the upper bound even before the positive-residual mesh threshold. The globally clipped continuous extension is used only for measurability and continuity arguments, and is proved equal to the actual amplitude at every root query. No estimate on the target error is a premise.

`frozenAmplitude_tendsto` handles the continuous term. `frozenRootWeight_tendsto` is derived from O's literal `rootWeight_error`, while P's `ae_frozen_H430_tendsto` supplies the already-proved closed-table convergence. Their product gives `ae_frozenFullCoefficient_tendsto`. Both complete coefficients are measurably integrable at the stated fine meshes, with a derived bound `(B+floorBound H430Numerators)*weightEnvelope`.

`rootFullAbsoluteError_tendsto` then proves

`∫_{rootBand k} |idealFullCoefficient - frozenFullCoefficient_n| → 0`.

This is a full weighted L1 estimate, before cancellation. A zero replacement at finitely/cofinally-excluded coarse indices is only an auxiliary domination device: the proof derives eventual fine mesh and then transfers back to the actual sequence. It does not alter the approximants used in the conclusion. `actual_root_full_mass_difference` bounds the original integral difference by this genuine L1 error.

`full_clamp_error` handles the entire positive-measure ideal clamp explicitly: P's exact clamp preservation makes both query values 2, and the error equals `|upperAmplitude 2-H430 2|` times the actual root-weight error. No clamp fibre was removed as a null set, and the H430 adjacent-minimum lookup is unchanged.

`exists_common_full_root_precision` chooses one finite `n` and positive `finiteTau n` for **both complete original roots**, before arithmetic `N`. This closes the previously listed continuous-upperAmplitude root component. It is not the common refinement for every descendant occurrence or all 441 generations.

## Exact reuse and remaining mathematical boundary

REGISTRY gives raw byte hashes, intended modules, imports and declarations for both new sources and direct/relevant transitive dependencies. In particular:

- Q14 supplies `physicalStart`, `physicalAtomPullback_eq`, `actual_buchstab_Jacobian`, `coefficient_difference_le` and actual descendant physical limits. Their former pointwise/w-pullback scope is preserved.
- P supplies `frozenQuery_tendsto`, `ideal_clamp_preserved` and `ae_frozen_H430_tendsto`. This is exact reuse of its proper-fibre and table work.
- O supplies complete-prefix `physicalWeight`, `rootWeight_error`, measurable weights, `weightEnvelope` and `finiteTau`; M supplies literal roots, bands, frozen levels and their range bounds.
- Production supplies the canonical `upperAmplitude`, literal H430 closed lookup and literal physical transition/local domains. Mathlib supplies the actual one-dimensional Jacobian and dominated-convergence APIs.

Remaining dependencies are not hidden in a new target-equivalent record:

1. **Full Member and all branches.** The native set above is LocalDomain plus the actual table atom. It does not yet add incomingAllowed, cellMember, source-history ownership or all old-prefix gates. R14's full-domain work must provide those actual filters and their joint measurability/mass control. W1/W2 singleton/pair native-coordinate measure conversion and original labelled multiplicities are still unprovided here.
2. **Same-native-x/global absolute domain error.** The entire ideal/frozen Member symmetric difference, all native prefix variables, the lower `s=2` inheritance strata and the actual parent integral require further proof. A pointwise path limit is not a global integrated theorem.
3. **Arithmetic parent Theta and normalization.** Continuous `4/(word.prod*L)` is not yet identified with the arithmetic `C(BN)/(phi(B)*log(Q/B))` law. Full outer parent-prime integration, zero-Theta absolute handling and normalized all-action row mass remain R16 obligations. No division by a zero cell mass or claim of norm12 occurs here.
4. **Immutable history and common realization.** All actual predecessor arrays, bases, source/count licences and 441-generation jointly nested choices remain required. The new two-root common precision neither changes the constants nor supplies the immutable induction's `hmass/hlocal`.
5. **Validation.** Source-only dependencies retain intended import paths and are not installed by this task. Lean elaboration and kernel validation were prohibited and remain outstanding.

The two supplied local deductions are class **II** (fillable omitted analysis now expressed in source). Unexecuted elaboration/API is class **I**. The remaining full native-family/arithmetic/common-realization construction retains class **III** risk; its simpler unperformed W1/W2 change-of-variable pieces can be class II without upgrading the full target. This is not evidence of a manuscript counterexample.

R28 has independently read both candidates and the relevant source APIs and reported no substantive blocker within these restricted mathematical conclusions. Its final independent review governs acceptance; this report claims neither compilation nor kernel credit.

## Static validation

Only source text, declaration/import mapping, raw bytes and hashes were checked. Admission/axiom/evaluation/unsafe token scans of the two candidates found no hits. No proof body was executed. The report and registry are exact-source bookkeeping, not numerical or formal verification.
