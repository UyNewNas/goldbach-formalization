# S20 — native-basis normalized Fourier coefficients and original row functionals

**Whole assigned yellow scope is not source-complete.** This packet supplies the actual same-basis Fourier normalization that was left between R21's local K classifiers and the existing native cusp basis. It does not supply the full normalized Kuznetsov identity. The original yellow terminal remains:

> 真实normalized trace/Fourier乘积、完整连续谱/ABL/gap及含全部费用的统一7/32能量

S20 owns its normalized-trace/Fourier-product part; S21 owns the full spectral classes and S22 owns the actual classical energy estimates. No green recommendation, no true trace or energy premise removed, and no claim that a missing formal source disproves the manuscript.

`compiled=false; kernel_verified=false; formal_credit=0; whole_assigned_yellow_scope_source_complete=false`. No local Lean/Lake/compiler, guards, numerical production/replay, Git/remote mutation, child agents or quota calls were run. Only the assigned S20 directory was written. The two sources are candidates for root's remote staging and kernel review, not verified exports.

## Original statement and concrete objects

Read the original `manuscript-body.tex:238–254`, `distribution-medium-completion-20261010.txt:349–380`, and the full `final-classical-input-correspondence-20261010.txt`. They invoke the normalized trace at every actual level `z`, trivial character, cusps infinity and one, scaling matrices `Id` and `[[sqrt(z),0],[sqrt(z),1/sqrt(z)]]`, with arbitrary complex primary coefficients independent of height and one common completed m interval/phase. They do not permit a replacement coefficient packet to stand for the spectral expansion.

R21 already supplies the full positive-modulus arithmetic input from the original R20 source. Reuse, without a new count of progress:

* `OriginalFullModulusCuspInput20261102.bareCuspTerm_hasSum`, `bareCuspTerm_summable` and `fullModulusRow_eq_normalized_cusp_sum` retain all positive `c` with `(c,z)=1`, including `c=1`, and the actual compact test. The outside factor is `M*sqrt(Z)`; the cusp modulus is `c*sqrt(z)`.
* The second signed index is the existing `traceIndex D k negativeM z n`, not merely the primary y-sign. `traceBeta` is the original modulated beta times the inverse cusp phase `e(-traceIndex/z)`.
* R21 `realQuotientWhittakerRho`, `realQuotientWhittakerR`, and `realQuotientWhittakerR_eq_old_quotientR` remain unchanged. The old `quotientR` is not the paper's R: its additional `sqrt(abs(n))` must still be divided out.

The new basis is not chosen afresh. Its index is exactly `actualCuspBasisIndex z hz`, its Hilbert vectors are exactly `actualCuspHilbertBasis z hz`, its real eigenvalues are exactly `actualCuspNativeEigenvalue z hz`, and its functions are exactly the previously supplied `actualCuspSmoothProfile z hz`. The only spectral branch test is the original eigenvalue being at most `1/4`. The threshold uses the real-order `K_0` branch; above threshold the order is `i*sqrt(lambda-1/4)`. No gap assumption or spectrum truncation is used.

## Supplied source bodies

`Part3ActualCuspBasisWhittakerCoefficients.lean`, intended module `ImbalancedChen.Part3ActualCuspBasisWhittakerCoefficients`, namespace `ActualCuspBasisWhittakerCoefficients20261102`:

* `basisFrame_smooth:65`, `basisFrame_periodic:69`, and `basisFrame_native_PDE:75` apply the existing same smooth family to the existing normalized cusp frames. The native PDE, smoothness and period one are discharged, not fields in a new spectral structure.
* `basisFrame_raw_strip_energy:93` obtains actual spatial strip integrability for every `Y>0`. The existing exact normalized high-cusp map at height 2 supplies the high tail. The existing compact-frame Lp theorem on `upperRectangle 0 1 Y 2` supplies the remaining band. The existing canonical raw-chart transport then gives literal `dx dy/y^2` on `PeriodCell × (Y,infinity)`. No assumed Fourier norm, local coefficient norm or global-H L2 condition is used.
* `basisModes_ae_original:136` reuses the existing common-conull-height comparison with the original `frameFourier` of the actual Hilbert vector. It does not evaluate an arbitrary L2 representative pointwise on a null horizontal line.
* `basisMode_unique_K_amplitude_tail:151` calls the existing real and imaginary K classifications. `basisRhoK:212` is chosen from that actual theorem. `basisMode_eq_K:216` and `basisMode_unique_K_amplitude:234` establish one unique amplitude for **all positive heights**, all signed nonzero integer indices, and all actual integral normalized cusp frames. To pass from the tail to a given height y the proof uses `Y=min(2,y/2)` and uniqueness on the common tail, never division by a possibly vanishing imaginary K value.
* `basisRhoW:247` and `basisR:250` use `rhoW=rhoK/(2*sqrt(abs(n)))`, `R=sqrt(abs(n))*rhoW`. `basisR_eq_half_native:258`, `basisMode_eq_Whittaker_normalization:265`, `basisMode_eq_normalizedR:274`, and `basisR_product:283` give the exact factors `R=rhoK/2`, Fourier factor `2*sqrt(y)`, and conjugated product `1/4` for the same native basis. The displayed physical Whittaker expression has no separately invented W function.
* `basis_scaling_infinity:291`, `basis_scaling_one:296`, and `basisMode_eq_fixed_scaling_integral:300` identify the actual matrices and literal Fourier integral. The new Fourier declaration uses pinned Mathlib's `_root_.fourier`, following R23's exact API evidence.

`Part3OriginalNativeCuspFunctionals.lean`, intended module `ImbalancedChen.Part3OriginalNativeCuspFunctionals`, namespace `OriginalNativeCuspFunctionals20261102`:

* `originalMFunctional:36` uses the actual `commonMBlock J j` and common completed phase, with conjugated weight and infinity coefficient of the same basis.
* `originalNFunctional:42` uses the actual `nCarrier D k z`, un-conjugated `traceBeta`, and signed `traceIndex` at the fixed cusp-one scaling.
* `original_native_row_product:49` proves the finite row product is exactly `conj(M_i)*N_i`. This concerns the actual functions just constructed, not arbitrary supplied rho values.
* `original_native_coefficient_product:69` applies the one-quarter identity to the original indices. Their nonzero qualification is derived from the actual carriers and the original nonzero residue assumption. No endpoint, sign, coefficient or future p/c/height dependence is changed.

The last file deliberately makes no assertion that this finite product equals the arithmetic c sum. Such an assertion still needs the full trace, including its other spectral branches.

## Reuse and inherited installation/API holds

Read R21 REPORT/REGISTRY, R23 REPORT and its Fourier namespace evidence, R30 independent spectral review, and directly read the following existing mathematical sources. They are not missing and are not reconstructed here:

* hidden `20261026b-GammaCompactness/Part3ActualFullCuspEigenbasis.lean:94`: the entire native cusp Hilbert basis;
* hidden `20261026b-GammaCompactness/Part3ActualCuspEigenbasisNativeLabels.lean:79`: the same basis in the original native Maass graph;
* hidden `20261026b-AffineRellich/Part3ActualFullCuspLambdaSquaredDomain.lean:45,84,119`: native graph, actual weighted operator domain and operator Parseval;
* hidden `20261026b-ZeroModeHardy/phase16-spectral-kernel/Part3ActualCuspSmoothEigenprofileFamily.lean:42,50,66,106`: one chosen smooth invariant norm-one family;
* hidden `20261027-KernelAction/Part3ActualCuspSmoothFiniteKernelDescent.lean:21,39,110`: actual quotient descent and finite native kernel action;
* hidden `20261026b-CuspWeakModes/Part3ActualEigenNormalizedSmoothFrame.lean` and `Part3ActualEigenOriginalFourierClassicalModes.lean:141`: actual normalized-frame PDE and Fourier comparison;
* production `Part3ActualRealMaassFourierK.lean:77` and hidden `20261026b-ImaginaryKLimitPoint/Part3ActualImaginaryMaassFourierK.lean:35`: both physical K classifications.

All hidden paths above begin `.lake/proof-continuation/source-reviews/drafts/`. Exact bytes, imports, declaration names and hashes are recorded in REGISTRY.

The be3646/0f1f and eigen-regularity holds are inherited. The imaginary chain requires `Part3ImaginaryRadialTailDerivativeL2` source hash `d4d0a1047d6dd5ad881c1c8fac10a5b0d8ecb6bfa278f912ebd4d56c0e3ffc15`, while production has `c51501c5ae949018d44907601ddbb27bd3fdad4c33e45e4f5e4c2ee9086ae09c`. The imported old Fourier mode source still contains the R23-identified `AddCircle.fourier` namespace issue. These require explicit root-owned dependency staging/API resolution. No old target was modified, no hold was silently bypassed, and these holds are not classified as substantive manuscript gaps.

## Exact primary source and unresolved full trace

Reopened the pinned [Drappeau v4](https://arxiv.org/pdf/1504.05549v4), [ABL v1](https://arxiv.org/pdf/2005.13915v1), and [DLMF 13.18.9](https://dlmf.nist.gov/13.18.E9). R21's saved original bytes are reused. Drappeau Lemmas 4.3 and 4.5 fix the cusp modulus and full positive/opposite-sign trace conventions. DLMF's relation gives the physical factor `2*sqrt(abs(n)*y)`; applying `R=sqrt(abs(n))*rhoW` yields the coefficients used here. The primary source statements are not Lean axioms or installed declarations.

For the original `bareCuspTerm`, the missing equality still consists of the full Maass basis contribution, the complete all-singular-cusp continuous integral with outside factor `1/(4*pi)` and measure `dt/cosh(pi*t)`, and the positive-sign holomorphic contribution with its original transform and height `k-1`. The opposite-sign branch has no holomorphic term. The removable value of the positive transform at `t=0` remains the limiting value, not a default zero quotient. The arithmetic side and the native cuspidal coefficients are now explicit; their full spectral identity has not been proved in these files.

The source search covered production, all source-only packets and ignored drafts with `rg -uu`; frozen/publisher duplicates were excluded only when inspecting duplicate bodies. Nearby geometric Poincare Fourier/pairing, radial KL, scalar spectral measure and finite smooth-kernel sources do not supply that identity. S30 independently searched and reached the same bounded conclusion. This is evidence about the searched formal source inventory, not evidence of a mathematical error in the cited manuscript theorem.

S21 reports the full character-pair continuous and weight-k branches remain unsupplied; S22 has not supplied actual A/J/regular/gap energies. Hence no assembly to close the whole yellow terminal is available. Replacing those by fields, setting a spectrum empty, or defining a target by subtraction would not be valid progress and was not done.

## Premise delta and remote target

Removed for the **actual existing cusp basis**: independent smooth-profile/PDE/periodicity/raw strip-L2 inputs, free local K amplitude input, and ambiguity of signed frequency, normalization and fixed scaling. The original index, level positivity, nonzero source residue where needed, and the existing native object definitions remain. There are no new mathematical hypotheses equivalent to the full trace or an energy inequality.

Remaining mathematical work: the normalized full spectral trace itself and the S21/S22 full spectral branches/estimates. Remaining formal work: exact inherited dependency staging/API holds plus elaboration/kernel and axiom evidence. They are separate lists. Actual true trace premises removed = 0; actual true energy premises removed = 0; final `hLower/hUpper` premises removed = 0.

Root's concrete remote target is to stage the exact import closure at Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native upstream `09b97db5764ade1246bfb77206baa1b124760958`, Lean `v4.33.0-rc1`, resolve the explicit inherited installation/API holds, and elaborate the two intended modules. Review should inspect `#print axioms` for `basisMode_unique_K_amplitude`, `basisMode_eq_Whittaker_normalization`, `basisR_product`, and `original_native_row_product`. No same-source verified artifact has been identified for these new bytes. Root alone may dispatch. A passing check of these modules would verify the stated coefficient construction only; it would not certify the unsupplied whole trace.

| New source | Raw SHA256 |
|---|---|
| `Part3ActualCuspBasisWhittakerCoefficients.lean` | `f7be43b6fbc72b75202d581e45bc92d5108ca24c473a523bf3b132f0cb335653` |
| `Part3OriginalNativeCuspFunctionals.lean` | `033cd69f5e76ede14e2d9d85087e376a9213a7d21a03574bda6346456b78a495` |

S30 reviewed the first candidate and identified the new Fourier namespace occurrence; it was corrected to the pinned root declaration. Final independent review is owned by S30. This report does not replace elaboration or that review.
