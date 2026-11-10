# T06 actual mixed Fourier source checkpoint

The whole assigned yellow terminal remains **OPEN**. These two new Lean files are source candidates, uncompiled and kernel unverified. No color change or full P3.6, hUpper, hLower, or main theorem closure follows from them. The exact source bytes and declaration locations are registered in REGISTRY.json.

## Original statement and difficulty classification

I reread `paper/source/modules/distribution-prime-product-completion-20261010.txt` at manuscript commit `9731290e8f53cffda44129906cde6a965eaa869b`: §2 lines72–115 requires a smooth complete-product trim, the same original group dyadic factors and all labelled HB variables; §4 lines153–171 requires the actual mixed derivative integral D, product-Cauchy pointwise Fourier decay, normalized L1 and uniform H truncation. The cutoff arguments are group sums and the complete sum, so their cross derivatives cannot be replaced with products of six independently estimated norms. The same physical rho/count/exact mean must survive separation.

The corresponding local module has SHA256 `a953b3233c1249b4791830da33b76a58b19ca110a5e1b5b6172b3248a00053e1` and Git blob `5e59d2881181b29446e5786584d6442e7a96fe04`. The local manuscript body has SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` and Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Read-only `git hash-object` agrees with the two blobs at the pinned manuscript commit. Thus the versions used here were checked, rather than assumed equivalent.

The current public P3 branch was checked read-only through GitHub's ref endpoint: `chatgpt/p3-internal-original-w-20261105` remained at `5bf9a3b41cdfdb85eb0edabe925ed448a8e3ab3e`. There was no successor to reuse. All predecessor source reads use that immutable snapshot.

Classification:

1. **Formal/API work:** exact real/complex derivative conversion, ordinary occurrence derivative transport and chart-base translation. New proofs may still have elaboration/API errors; no local proof execution was permitted.
2. **Fillable omitted mathematics:** the true repeated six-coordinate mixed product identity, zero germs outside support, integration on the actual compact support, and applying the old list Leibniz rule to the coupled actual geometric chart. The new source supplies these candidates.
3. **Remaining scope, not a demonstrated manuscript counterexample:** concrete actual caller coverage, the integrated-only geometric class, arbitrary complex original weights, and total atlas/label/resolution aggregation are not supplied for the entire terminal. No new substantive mathematical gap is asserted.

## Reuse recovered before new work

The latest P3 REGISTRY accurately says that its new six-slot product is only a product of separate derivative norms. It does not summarize all stronger older source packets already in the same tree:

- `20261028-resume-30c/pp_derivatives/P5ActualEtaPsiOccurrenceBudget.lean` constructs actual eta, chi, group psi, complete-product trim, real ambient W and fixed plateau. Its `exists_actualChart_word_budget` already includes all coupled group/trim cross terms via the old ordered list allocation theorem.
- `20261028-resume-30c/pp_fourier/P5ActualAllRankOccurrenceFourierBridge.lean` already proves actual mixedD, normalized L1/H and integer atom recovery, including `same_rho_hb_weighted_tensor_integral`. It uses the actual Euclidean/Pi measure transport and Fourier inversion. None of these were reconstructed here.
- `20261102-resume-30j/upper_pp/P4BArbitraryWidthUpperPairOccurrence.lean` already gives the **concrete current real rank-two upper-pair** chart and its actual `C/width^24` word/mixedD budget. It does not require an abstract Family input.
- `20261105-p3-integrated-original-w/P3OriginalWIntegratedDerivative.lean` already handles primitive **integrated** original W derivatives with the actual U5/HB multiplier, yielding `originalWD <= C*M*(mesh+1)^(2*d)` and the displayed polylog degree. This remains a distinct route. Its primitive actual W-family membership is not proven by the old all-rank Family field.
- All existing true Fourier, IBP, Fubini, H-box, inversion, same-rho arithmetic, weighted-gamma, offshift and target-diagonal modules remain unchanged. No new arithmetic moment or medium/spectral assumption was added.

## New source and exact interfaces

`P3ActualHBChildMixedFourier.lean` uses the **already defined** real original chi from the old actual eta/psi packet. `childLog_ofReal` identifies its complexification with the existing P3 `logChild`; it does not choose a different cutoff. `childLog_iterated_ofReal` is the necessary scalar conversion. `exists_childLog_global_budget` consumes the latest P3 compact finite-order C_K, extends it using actual zero germs, and adds no dyadic, target or modulus factor.

`occWord_childTensor` proves the actual ordinary mixed derivative is the product of individual derivatives at the **list occurrence counts**, including repeated coordinates. `childTensor_mixed_support` and `childTensor_mixed_integral_bound` give actual compact support and an actual Lebesgue L1 bound. The exact support is the original closed logarithmic box.

`shiftedChildTensor` retains the real difference between the original dyadic base `2^j` and the Fourier rectangle's lower base U. Its offset is `log(U_i/2^j_i)`. `shiftedChildTensor_physical`, `six_childTensor_eq_smoothTensor` and `refinedEuclideanChart_six_integer_atom` identify the factors with the original actual positional smooth HB tensor, before absolute values. The finite child sum restores the original individual dyadic tensor exactly. No labels, padding units, multiplicities, complete product, coefficients or rho are collapsed.

`refinedChart = actualChart * shiftedChildTensor` retains the original ambient W, coupled original group psi, actual complete-product eta and compact plateau. `occWord_refinedChart_exact` exposes the full ordered LIST allocation sum. `exists_refined_fourier_budgets` consumes the earlier actual chart word bound and the existing Euclidean mixed integral/Fourier chain. It exposes D, product-Cauchy decay, normalized L1 and H error with one C,B preceding T, rank, owner maps, scales, offsets and child labels.

**This all-rank route retains `A : Family kStar`.** The hidden pinned Family's `mixedEuler` is a pointwise **supremum** bound on the original ambient W, and the Family is real-valued. It is stronger than merely integrated Euler norms. No actual all-caller Family was constructed here, and it cannot be used to remove the genuine `PhysicalIntegratedClass` obligation by renaming it.

`P3ActualUpperPairChildFourier.lean` removes that abstract Family for the **concrete current real upper rank-two source**. It imports the actual arbitrary-width occurrence chart unchanged. `refinedUpper_integer_atom` recovers the original normalized upper-pair Licence, complete trim and grouped psi on each actual atom, times the original smooth individual HB children. `refinedUpper_children_sum` restores the individual dyadic tensor.

`exists_refinedUpper_fourier_width_budget` gives the actual coupled refined upper source's D, pointwise product-Cauchy decay, normalized Fourier L1 and H error with cost `C/width^24`. The constant is chosen before physical width, N, owner/scales, offsets and child labels. Its genuine legal-width/gap hypotheses are retained; no selected-width surrogate is used.

`exists_refinedUpper_resolution_polylog_budget` substitutes actual width `1/(resolution+1)` and gives `D <= C*log(N)^(24*B)` from `resolution+1 <= log(N)^B`, retaining the same width-gap condition. The preceding width theorem supplies the matching pointwise/L1/H bounds at that same width. **HB dimension d<=12 is distinct from growing resolution(N).** This is a per-chart uniformity result; it does not pay the number/total restoring norm of all resolution-dependent atlas pieces.

## Removed and remaining premises

Removed within the new scoped candidates:

- The unsupported identification of the six one-dimensional derivative-norm product with the actual six-dimensional mixed derivative.
- A support/derivative-integrability hypothesis for the selected actual child tensor.
- A dyadic-label-dependent derivative constant, and the false identification of the lower base U with `2^j`.
- An assumed derivative budget for the combined actual chart times the child, including its cross terms.
- Independent Fourier pointwise/L1/H/inversion hypotheses for this smooth compact refined chart: the unchanged old Fourier theorems supply them.
- The abstract all-rank Family input for the concrete real upper-pair arbitrary-width route.

Still required for the **entire assigned yellow terminal**:

- Remote elaboration, expanded-type and transitive-axiom/kernel checks for these exact bytes and their entire source-only import graph. The old graph itself has source-only status.
- Exact actual geometric family/mesh membership for every remaining lower, marked/HB, empty-Gamma, high-rank and enhanced caller. The general Family theorem is not such an instantiation.
- The original integrated-only class for all genuine physical W_T and the corresponding arbitrary complex original profiles. Complex Fourier values of a real lift do not establish arbitrary complex W coverage.
- Actual U5/root-atlas resolution choice and total piece/restoring-norm aggregation, with constants chosen before N. The old root-atlas m(N) and the bounded HB occurrence dimension are separate objects.
- A same-source connection between all retained actual smooth children and the complete actual finite source dictionary, plus all corresponding (S) scale/range licences.
- The complete same-Q/rho arithmetic payment after the full modulus sum, exact product=T, mean/totient, rough/square collisions, and all branch coverage. These remain outside the analytic source conversion. Existing paid weighted-gamma/offshift results must be reused, not charged a second time.
- The original Medium(M) and true automorphic/spectral supplier remain independent. Nothing here asserts either.

Independent T10 review returned **SOURCE-LEVEL SCOPED PASS** on the final Lean SHA256 values `88da0602726a095332e8f2a32510eacf2afd9ccb2ab303c78bc271cb7fc97ab1` and `56a13fc4c39981762cb47a2f4916558889299d29fb280cb1287824a98f24eb86`. The review specifically checked repeated occurrence counts, exact fixed-label child restoration, translated integer factors, coupled cross terms, pre-parameter constants, all three original (F) clauses, and the actual legal-width upper-pair profile. It preserves the stated full-scope boundaries and is not an elaboration or kernel check. T07 confirmed the same-Q marked-box count licence is separate; T08 confirmed spectral and geometric inputs remain distinct. This checkpoint provides no new green claim.

## Verification policy

Only source/text/Git-object/JSON/hash inspection was used. No Lean, Lake, elan, LSP, diagnostics, proof guard, numerical/finite execution, author test script, local build, Git mutation, remote mutation/CI, quota call or child spawn was run. Read-only GitHub ref/file access and immutable local Git reads were used. Root owns the remote checks and any publication. Ordinary source scans and hashes are not proof verification.
