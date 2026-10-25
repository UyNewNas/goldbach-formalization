import ImbalancedChen.Part3OneCompactFirstGradientIBP
import ImbalancedChen.Part3Gamma0CompactQuotientPullbackLinear
import ImbalancedChen.Part3Gamma0EnergyCompactGradientExtension
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The existing actual energy-completion local gradient is the geometric
weighted weak gradient of the physical projection, against actual compact
tensor tests. Closed test support containers lie in interior K. The proof
uses true one-compact first integration by parts on the actual smooth core
and continuity of L2 test pairings on its actual dense completion.
No approximate sequence, weak-gradient equation, form-domain inclusion
for adjoint vectors, test density or elliptic regularity is assumed.
-/

namespace ImbalancedChen.Part3.Gamma0EnergyGeometricWeakGradient20261025a
noncomputable section
open Set Filter Function MeasureTheory
open UniformSpace
open scoped UpperHalfPlane
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.OneCompactDirichletGreen20261025a
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0CompactCoreGradient20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientMeasureDomination20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientPullbackLinear20261025a
open ImbalancedChen.Part3.Gamma0EnergyCompactGradientExtension20261025a
open ImbalancedChen.Part3.OneCompactFirstGradientIBP20261025a

def testValue (T : CompactTensor) : UpperHalfPlane → ℂ := tensorFunctionH T.horizontal T.vertical
def testDerivative (vertical : Bool) (T : CompactTensor) (z : UpperHalfPlane) : ℂ :=
  tensorGradient vertical T (z.re,z.im)
def firstCoordinate (vertical : Bool) : Fin 2 := if vertical then 1 else 0

theorem testValue_continuous (T : CompactTensor) : Continuous (testValue T) := by
  exact (T.horizontal_smooth.continuous.comp UpperHalfPlane.continuous_re).mul
    (T.vertical_smooth.continuous.comp UpperHalfPlane.continuous_im)

theorem testDerivative_continuous (vertical : Bool) (T : CompactTensor) :
    Continuous (testDerivative vertical T) := by
  have hh := seed_first_derivative_continuous T.horizontal T.horizontal_smooth
  have hv := seed_first_derivative_continuous T.vertical T.vertical_smooth
  cases vertical
  · exact (hh.comp UpperHalfPlane.continuous_re).mul
      (T.vertical_smooth.continuous.comp UpperHalfPlane.continuous_im)
  · exact (T.horizontal_smooth.continuous.comp UpperHalfPlane.continuous_re).mul
      (hv.comp UpperHalfPlane.continuous_im)

theorem testValue_support_subset (T : CompactTensor) :
    support (testValue T) ⊆ compactTensorSupportK T := by
  intro z hz
  constructor
  · by_contra hh
    exact hz (by simp [testValue,tensorFunctionH_eq,image_eq_zero_of_notMem_tsupport hh])
  · by_contra hv
    exact hz (by simp [testValue,tensorFunctionH_eq,image_eq_zero_of_notMem_tsupport hv])

theorem testDerivative_support_subset (vertical : Bool) (T : CompactTensor) :
    support (testDerivative vertical T) ⊆ compactTensorSupportK T := by
  intro z hz
  by_contra hnot
  by_cases hh : z.re ∈ tsupport T.horizontal
  · have hv : z.im ∉ tsupport T.vertical := fun h => hnot ⟨hh,h⟩
    have hv₀ := image_eq_zero_of_notMem_tsupport hv
    have hv₁ := image_eq_zero_of_notMem_tsupport
      (fun h => hv (tsupport_deriv_subset h))
    apply hz
    cases vertical <;> simp [testDerivative,tensorGradient,tensorDx,tensorDy,hv₀,hv₁]
  · have hh₀ := image_eq_zero_of_notMem_tsupport hh
    have hh₁ := image_eq_zero_of_notMem_tsupport
      (fun h => hh (tsupport_deriv_subset h))
    apply hz
    cases vertical <;> simp [testDerivative,tensorGradient,tensorDx,tensorDy,hh₀,hh₁]

def leftTest (vertical : Bool) (T : CompactTensor) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℂ)^2*testDerivative vertical T z
def rightTest (vertical : Bool) (T : CompactTensor) (z : UpperHalfPlane) : GradientFiber :=
  if vertical then !₂[0,(z.im : ℂ)*testValue T z]
  else !₂[(z.im : ℂ)*testValue T z,0]

private theorem continuous_local_memLp {E : Type*} [NormedAddCommGroup E]
    {a : UpperHalfPlane → E} (ha : Continuous a) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    MemLp a 2 ((volume : Measure UpperHalfPlane).restrict K) :=
  (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr
    (ContinuousOn.integrableOn_compact hK (ha.norm.pow 2).continuousOn)

theorem leftTest_continuous (vertical : Bool) (T : CompactTensor) : Continuous (leftTest vertical T) :=
  ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2).mul
    (testDerivative_continuous vertical T)

theorem rightTest_continuous (vertical : Bool) (T : CompactTensor) : Continuous (rightTest vertical T) := by
  have hc := (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul (testValue_continuous T)
  cases vertical <;> apply PiLp.continuous_toLp.comp <;> apply continuous_pi <;>
    intro i <;> fin_cases i
  · exact hc
  · exact continuous_const
  · exact continuous_const
  · exact hc

def leftTestL2 {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool) (T : CompactTensor) :
    LocalScalarL2 K :=
  (continuous_local_memLp (leftTest_continuous vertical T) hK).toLp (leftTest vertical T)

def rightTestL2 {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool) (T : CompactTensor) :
    CompactGradientL2 K :=
  (continuous_local_memLp (rightTest_continuous vertical T) hK).toLp (rightTest vertical T)

theorem leftTest_inner_pullback (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (vertical : Bool) (T : CompactTensor) (f : QuotientL2 N) :
    inner ℂ (leftTestL2 hK vertical T) (compactPullbackL2 N hK f) =
      ∫ z in K, star (testDerivative vertical T z)*f (orbitProjection N z)*(z.im : ℂ)^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(continuous_local_memLp (leftTest_continuous vertical T) hK).coeFn_toLp,
    compactPullbackL2_coe_ae N hK f] with z ht hf
  rw [ht,hf]
  simp only [RCLike.inner_apply',Complex.star_def,leftTest,map_mul,map_pow,Complex.conj_ofReal]
  ring

theorem rightTest_inner (vertical : Bool) (T : CompactTensor) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (g : CompactGradientL2 K) :
    inner ℂ (rightTestL2 hK vertical T) g =
      ∫ z in K, star (testValue T z)*(g z (firstCoordinate vertical))*(z.im : ℂ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(continuous_local_memLp (rightTest_continuous vertical T) hK).coeFn_toLp]
    with z ht
  rw [ht,EuclideanSpace.inner_eq_star_dotProduct]
  cases vertical <;>
    simp [rightTest,firstCoordinate,dotProduct,Fin.sum_univ_two,star_mul,Complex.star_def] <;> ring

theorem core_first_pairing (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K)
    (vertical : Bool) (T : CompactTensor) (hTK : compactTensorSupportK T ⊆ interior K)
    (u : EnergyCore N) :
    inner ℂ (leftTestL2 hK vertical T) (compactPullbackL2 N hK (physicalCore N u)) =
      -inner ℂ (rightTestL2 hK vertical T) (coreGradientL2 N hK u) := by
  have hsub : compactTensorSupportK T ⊆ K := hTK.trans interior_subset
  have hU := quotient_ae_eq_pullback_compact N hK (chosenRepresentative_spec N u).1
  have hF : ContDiffOn ℝ 2 (extendUpper (coreRepresentative N u)) positiveChart :=
    (coreRepresentative_cinfty N u).of_le (by norm_num)
  have hleft : inner ℂ (leftTestL2 hK vertical T) (compactPullbackL2 N hK (physicalCore N u)) =
      ∫ z : UpperHalfPlane, (z.im : ℂ)^2*
        (star (testDerivative vertical T z)*coreRepresentative N u z) := by
    rw [leftTest_inner_pullback]
    calc
      _ = ∫ z in K, (z.im : ℂ)^2*
          (star (testDerivative vertical T z)*coreRepresentative N u z) := by
        apply integral_congr_ae
        filter_upwards [hU] with z hz
        change (u : QuotientL2 N) (orbitProjection N z) = coreRepresentative N u z at hz
        change star (testDerivative vertical T z)*(u : QuotientL2 N) (orbitProjection N z)*_= _
        rw [hz]
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have ht : testDerivative vertical T z=0 := notMem_support.mp
          (fun h => hz (hsub (testDerivative_support_subset vertical T h)))
        simp [ht])
  have hright : inner ℂ (rightTestL2 hK vertical T) (coreGradientL2 N hK u) =
      ∫ z : UpperHalfPlane, (z.im : ℂ)^2*
        (star (testValue T z)*sliceFirst vertical (extendUpper (coreRepresentative N u)) (z.re,z.im)) := by
    rw [rightTest_inner]
    calc
      _ = ∫ z in K, (z.im : ℂ)^2*
          (star (testValue T z)*sliceFirst vertical (extendUpper (coreRepresentative N u)) (z.re,z.im)) := by
        apply integral_congr_ae
        filter_upwards [(weightedCoreGradient_compact_memLp N hK u).coeFn_toLp] with z hz
        change coreGradientL2 N hK u z = weightedCoreGradient N u z at hz
        rw [hz]
        cases vertical <;> simp [weightedCoreGradient,firstCoordinate,sliceFirst] <;> ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have ht : testValue T z=0 := notMem_support.mp
          (fun h => hz (hsub (testValue_support_subset T h)))
        simp [ht])
  rw [hleft,hright]
  have h := canonical_one_compact_first vertical T (extendUpper (coreRepresentative N u)) hF
  simp_rw [ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a.extendUpper_pair] at h
  simpa only [testDerivative,testValue] using h

/-- Dense completion induction is the true core approximation argument:
both sides are continuous L2 testing functionals on the EXISTING E. -/
theorem completed_first_pairing (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K)
    (vertical : Bool) (T : CompactTensor) (hTK : compactTensorSupportK T ⊆ interior K)
    (e : EnergyCompletion N) :
    inner ℂ (leftTestL2 hK vertical T)
      (compactPullbackCLM N hK (physicalProjection N e)) =
    -inner ℂ (rightTestL2 hK vertical T) (completedCompactGradient N hK e) := by
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_eq
      (continuous_const.inner ((compactPullbackCLM N hK).continuous.comp (physicalProjection N).continuous))
      (continuous_const.inner (completedCompactGradient N hK).continuous).neg
  · intro u
    rw [physicalProjection_core,completedCompactGradient_core]
    exact core_first_pairing N hK vertical T hTK u

/-- The literal geometric weak derivative of the physical J-image.
Canonical y^-2 volume requires exactly these y^2 / y test weights. -/
theorem completed_tensor_weak_derivative (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (vertical : Bool) (T : CompactTensor)
    (hTK : compactTensorSupportK T ⊆ interior K) (e : EnergyCompletion N) :
    (∫ z in K, star (testDerivative vertical T z)*
      (physicalProjection N e) (orbitProjection N z)*(z.im : ℂ)^2) =
    -(∫ z in K, star (testValue T z)*
      ((completedCompactGradient N hK e) z (firstCoordinate vertical))*(z.im : ℂ)) := by
  rw [← leftTest_inner_pullback,← rightTest_inner]
  exact completed_first_pairing N hK vertical T hTK e

theorem completed_tensor_weak_products_integrable (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool) (T : CompactTensor)
    (e : EnergyCompletion N) :
    Integrable (fun z => star (testDerivative vertical T z)*
      (physicalProjection N e) (orbitProjection N z)*(z.im : ℂ)^2)
      ((volume : Measure UpperHalfPlane).restrict K) ∧
    Integrable (fun z => star (testValue T z)*
      ((completedCompactGradient N hK e) z (firstCoordinate vertical))*(z.im : ℂ))
      ((volume : Measure UpperHalfPlane).restrict K) := by
  constructor
  · have h := MemLp.integrable_mul (p := 2) (q := 2)
      (continuous_local_memLp (leftTest_continuous vertical T) hK).star
      (quotientLp_pullback_memLp N hK (physicalProjection N e))
    apply h.congr
    exact Eventually.of_forall (fun z => by
      simp only [Pi.mul_apply,leftTest,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
      ring)
  · have h := L2.integrable_inner (𝕜 := ℂ) (rightTestL2 hK vertical T)
      (completedCompactGradient N hK e)
    apply h.congr
    filter_upwards [(continuous_local_memLp (rightTest_continuous vertical T) hK).coeFn_toLp]
      with z ht
    rw [ht,EuclideanSpace.inner_eq_star_dotProduct]
    cases vertical <;>
      simp [rightTest,firstCoordinate,dotProduct,Fin.sum_univ_two,star_mul,Complex.star_def] <;> ring

/-- Every actual finite compact C2 tensor family is allowed, hence in
particular every finite SmoothCompactTensor test. The derivative here is
the literal coordinate derivative of the finite chart seed, not a formal
sum left unidentified with the geometric test. -/
theorem completed_finite_tensor_weak_derivative (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (hTK : finiteCompactTensorSupportK s T ⊆ interior K) (e : EnergyCompletion N) :
    (∫ z in K, star (sliceFirst vertical (finiteChartFunction s T) (z.re,z.im))*
      (physicalProjection N e) (orbitProjection N z)*(z.im : ℂ)^2) =
    -(∫ z in K, star (finiteCoreFunction s T z)*
      ((completedCompactGradient N hK e) z (firstCoordinate vertical))*(z.im : ℂ)) := by
  have hTKi (i : ι) (hi : i ∈ s) : compactTensorSupportK (T i) ⊆ interior K := by
    intro z hz
    exact hTK (mem_iUnion.mpr ⟨⟨i,hi⟩,hz⟩)
  have hD (z : UpperHalfPlane) : sliceFirst vertical (finiteChartFunction s T) (z.re,z.im) =
      ∑ i ∈ s, testDerivative vertical (T i) z := by
    cases vertical
    · exact sliceDx_finiteChartFunction s T (z.re,z.im)
    · exact sliceDy_finiteChartFunction s T (z.re,z.im)
  have hV (z : UpperHalfPlane) : finiteCoreFunction s T z=∑ i ∈ s, testValue (T i) z := rfl
  have hLI (i : ι) (_hi : i ∈ s) :=
    (completed_tensor_weak_products_integrable N hK vertical (T i) e).1
  have hRI (i : ι) (_hi : i ∈ s) :=
    (completed_tensor_weak_products_integrable N hK vertical (T i) e).2
  calc
    _ = ∫ z in K, ∑ i ∈ s, star (testDerivative vertical (T i) z)*
        (physicalProjection N e) (orbitProjection N z)*(z.im : ℂ)^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by simp only [hD,star_sum,Finset.sum_mul])
    _ = ∑ i ∈ s, ∫ z in K, star (testDerivative vertical (T i) z)*
        (physicalProjection N e) (orbitProjection N z)*(z.im : ℂ)^2 := integral_finsetSum s hLI
    _ = ∑ i ∈ s, -(∫ z in K, star (testValue (T i) z)*
        ((completedCompactGradient N hK e) z (firstCoordinate vertical))*(z.im : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact completed_tensor_weak_derivative N hK vertical (T i) (hTKi i hi) e
    _ = _ := by
      rw [Finset.sum_neg_distrib,← integral_finsetSum s hRI]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by simp only [hV,star_sum,Finset.sum_mul])

end
end ImbalancedChen.Part3.Gamma0EnergyGeometricWeakGradient20261025a
