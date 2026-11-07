import ImbalancedChen.Part3ArbitraryCompactFirstGradientIBP
import ImbalancedChen.Part3Gamma0CarrierGradientExhaustion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every actual form-domain vector has the already constructed local vector
L2 gradient as its weak real coordinate derivative against EVERY compact
smooth positive-height plane test. This is proved by actual real derivative
integration by parts on the original smooth core, then continuity on its
genuine dense energy closure. Canonical y^-2 volume, actual orbit pullback,
and the y²/y test weights are explicit. No test-density premise or desired
gradient identity is assumed. No adjoint-defect form membership is claimed.
-/

namespace ImbalancedChen.Part3.Gamma0ArbitrarySmoothWeakGradient20261026b
noncomputable section
open Set Filter MeasureTheory UniformSpace
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a
open MaassWeakOperatorCore20261024zz
open Gamma0CompactGreenProductL120261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CompactCoreGradient20261025a
open Gamma0CompactQuotientMeasureDomination20261025a
open Gamma0CompactQuotientLocalLp20261025a
open Gamma0CompactQuotientPullbackLinear20261025a
open Gamma0EnergyCompactGradientExtension20261025a
open Gamma0EnergyGeometricWeakGradient20261025a
open Gamma0FriedrichsKernelZeroWeakGradient20261025a
open OneCompactFirstGradientIBP20261025a
open CompactC2ProductMollifier20261026a
open ArbitraryCompactFirstGradientIBP20261026b

def chartTestSupport (ψ : Plane → ℂ) : Set UpperHalfPlane :=
  {z | (z.re,z.im) ∈ tsupport ψ}

def arbitraryLeftTest (vertical : Bool) (ψ : Plane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℂ)^2 * directional (coordinateDirection vertical) ψ (z.re,z.im)

def arbitraryRightTest (vertical : Bool) (ψ : Plane → ℂ) (z : UpperHalfPlane) : GradientFiber :=
  if vertical then !₂[0,(z.im : ℂ)*ψ (z.re,z.im)]
  else !₂[(z.im : ℂ)*ψ (z.re,z.im),0]

theorem arbitraryLeftTest_continuous (vertical : Bool) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) : Continuous (arbitraryLeftTest vertical ψ) :=
  ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2).mul
    ((directional_smooth _ hψ).continuous.comp
      (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im))

theorem arbitraryRightTest_continuous (vertical : Bool) {ψ : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) : Continuous (arbitraryRightTest vertical ψ) := by
  have hc := (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (hψ.continuous.comp (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im))
  cases vertical <;> apply PiLp.continuous_toLp.comp <;> apply continuous_pi <;>
    intro i <;> fin_cases i
  · exact hc
  · exact continuous_const
  · exact continuous_const
  · exact hc

private theorem compactContinuous_memLp {E : Type*} [NormedAddCommGroup E]
    {a : UpperHalfPlane → E} (ha : Continuous a) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    MemLp a 2 ((volume : Measure UpperHalfPlane).restrict K) :=
  (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mpr
    (ContinuousOn.integrableOn_compact hK (ha.norm.pow 2).continuousOn)

def arbitraryLeftTestL2 {K : Set UpperHalfPlane} (hK : IsCompact K)
    (vertical : Bool) {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) : LocalScalarL2 K :=
  (compactContinuous_memLp (arbitraryLeftTest_continuous vertical hψ) hK).toLp
    (arbitraryLeftTest vertical ψ)

def arbitraryRightTestL2 {K : Set UpperHalfPlane} (hK : IsCompact K)
    (vertical : Bool) {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) : CompactGradientL2 K :=
  (compactContinuous_memLp (arbitraryRightTest_continuous vertical hψ) hK).toLp
    (arbitraryRightTest vertical ψ)

theorem arbitraryLeftTest_inner_pullback (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (f : QuotientL2 N) :
    inner ℂ (arbitraryLeftTestL2 hK vertical hψ) (compactPullbackL2 N hK f) =
      ∫ z in K, star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
        f (orbitProjection N z) * (z.im : ℂ)^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compactContinuous_memLp (arbitraryLeftTest_continuous vertical hψ) hK).coeFn_toLp,
    compactPullbackL2_coe_ae N hK f] with z ht hf
  rw [ht,hf]
  simp only [RCLike.inner_apply',Complex.star_def,arbitraryLeftTest,map_mul,map_pow,
    Complex.conj_ofReal]
  ring

theorem arbitraryRightTest_inner {K : Set UpperHalfPlane} (hK : IsCompact K)
    (vertical : Bool) {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (g : CompactGradientL2 K) :
    inner ℂ (arbitraryRightTestL2 hK vertical hψ) g =
      ∫ z in K, star (ψ (z.re,z.im)) * g z (firstCoordinate vertical) * (z.im : ℂ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compactContinuous_memLp (arbitraryRightTest_continuous vertical hψ) hK).coeFn_toLp]
    with z ht
  rw [ht,EuclideanSpace.inner_eq_star_dotProduct]
  cases vertical <;>
    simp [arbitraryRightTest,firstCoordinate,dotProduct,Fin.sum_univ_two,star_mul,Complex.star_def] <;>
    ring

theorem core_arbitrary_smooth_first_pairing (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hTK : chartTestSupport ψ ⊆ K)
    (u : EnergyCore N) :
    inner ℂ (arbitraryLeftTestL2 hK vertical hψ)
      (compactPullbackL2 N hK (physicalCore N u)) =
      -inner ℂ (arbitraryRightTestL2 hK vertical hψ) (coreGradientL2 N hK u) := by
  have hU := quotient_ae_eq_pullback_compact N hK (chosenRepresentative_spec N u).1
  have hG : ContDiffOn ℝ 2 (extendUpper (coreRepresentative N u)) positiveChart :=
    (coreRepresentative_cinfty N u).of_le (by norm_num)
  have hDzero (z : UpperHalfPlane) (hz : z ∉ K) :
      directional (coordinateDirection vertical) ψ (z.re,z.im) = 0 := by
    have hn : (z.re,z.im) ∉ tsupport ψ := fun hp => hz (hTK hp)
    simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
  have hVzero (z : UpperHalfPlane) (hz : z ∉ K) : ψ (z.re,z.im) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hp => hz (hTK hp))
  have hleft : inner ℂ (arbitraryLeftTestL2 hK vertical hψ)
      (compactPullbackL2 N hK (physicalCore N u)) =
      ∫ z : UpperHalfPlane, (z.im : ℂ)^2 *
        (star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
          coreRepresentative N u z) := by
    rw [arbitraryLeftTest_inner_pullback]
    calc
      _ = ∫ z in K, (z.im : ℂ)^2 *
          (star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
            coreRepresentative N u z) := by
        apply integral_congr_ae
        filter_upwards [hU] with z hz
        change (u : QuotientL2 N) (orbitProjection N z) = coreRepresentative N u z at hz
        change star _ * (u : QuotientL2 N) (orbitProjection N z) * _ = _
        rw [hz]
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [hDzero z hz,star_zero,zero_mul,mul_zero])
  have hright : inner ℂ (arbitraryRightTestL2 hK vertical hψ) (coreGradientL2 N hK u) =
      ∫ z : UpperHalfPlane, (z.im : ℂ)^2 *
        (star (ψ (z.re,z.im)) *
          sliceFirst vertical (extendUpper (coreRepresentative N u)) (z.re,z.im)) := by
    rw [arbitraryRightTest_inner]
    calc
      _ = ∫ z in K, (z.im : ℂ)^2 *
          (star (ψ (z.re,z.im)) *
            sliceFirst vertical (extendUpper (coreRepresentative N u)) (z.re,z.im)) := by
        apply integral_congr_ae
        filter_upwards [(weightedCoreGradient_compact_memLp N hK u).coeFn_toLp] with z hz
        change coreGradientL2 N hK u z = weightedCoreGradient N u z at hz
        rw [hz]
        cases vertical <;> simp [weightedCoreGradient,firstCoordinate,sliceFirst] <;> ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [hVzero z hz,star_zero,zero_mul,mul_zero])
  rw [hleft,hright]
  have hi := canonical_arbitrary_compact_first vertical hψ hc hs hG
  simp_rw [ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a.extendUpper_pair] at hi
  exact hi

/-- Genuine energy closure of the all-smooth-test identity. Both sides
are continuous L2 functionals on the original actual completion. -/
theorem completed_arbitrary_smooth_first_pairing (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hTK : chartTestSupport ψ ⊆ K)
    (e : EnergyCompletion N) :
    inner ℂ (arbitraryLeftTestL2 hK vertical hψ)
      (compactPullbackCLM N hK (physicalProjection N e)) =
      -inner ℂ (arbitraryRightTestL2 hK vertical hψ) (completedCompactGradient N hK e) := by
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_eq
      (continuous_const.inner ((compactPullbackCLM N hK).continuous.comp
        (physicalProjection N).continuous))
      (continuous_const.inner (completedCompactGradient N hK).continuous).neg
  · intro u
    rw [physicalProjection_core,completedCompactGradient_core]
    exact core_arbitrary_smooth_first_pairing N hK vertical hψ hc hs hTK u

theorem completed_arbitrary_smooth_weak_derivative (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hTK : chartTestSupport ψ ⊆ K)
    (e : EnergyCompletion N) :
    (∫ z in K, star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (physicalProjection N e) (orbitProjection N z) * (z.im : ℂ)^2) =
      -(∫ z in K, star (ψ (z.re,z.im)) *
        (completedCompactGradient N hK e) z (firstCoordinate vertical) * (z.im : ℂ)) := by
  rw [← arbitraryLeftTest_inner_pullback,← arbitraryRightTest_inner]
  exact completed_arbitrary_smooth_first_pairing N hK vertical hψ hc hs hTK e

/-- All displayed scalar products are L1, independently of their weak
identity, by genuine scalar/vector L2 duality on the compact chart. -/
theorem completed_arbitrary_smooth_products_integrable (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (e : EnergyCompletion N) :
    Integrable (fun z => star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (physicalProjection N e) (orbitProjection N z) * (z.im : ℂ)^2)
        ((volume : Measure UpperHalfPlane).restrict K) ∧
    Integrable (fun z => star (ψ (z.re,z.im)) *
      (completedCompactGradient N hK e) z (firstCoordinate vertical) * (z.im : ℂ))
        ((volume : Measure UpperHalfPlane).restrict K) := by
  constructor
  · have h := MemLp.integrable_mul (p := 2) (q := 2)
      (compactContinuous_memLp (arbitraryLeftTest_continuous vertical hψ) hK).star
      (quotientLp_pullback_memLp N hK (physicalProjection N e))
    apply h.congr
    exact Eventually.of_forall (fun z => by
      simp only [Pi.mul_apply,arbitraryLeftTest,star_mul,star_pow,Complex.star_def,
        Complex.conj_ofReal]
      ring)
  · have h := L2.integrable_inner (𝕜 := ℂ) (arbitraryRightTestL2 hK vertical hψ)
      (completedCompactGradient N hK e)
    apply h.congr
    filter_upwards [(compactContinuous_memLp
      (arbitraryRightTest_continuous vertical hψ) hK).coeFn_toLp] with z ht
    rw [ht,EuclideanSpace.inner_eq_star_dotProduct]
    cases vertical <;>
      simp [arbitraryRightTest,firstCoordinate,dotProduct,Fin.sum_univ_two,star_mul,Complex.star_def] <;>
      ring

theorem actual_form_arbitrary_smooth_weak_derivative (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hTK : chartTestSupport ψ ⊆ K)
    (u : actualEnergyFormDomain N) :
    (∫ z in K, star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (u : QuotientL2 N) (orbitProjection N z) * (z.im : ℂ)^2) =
      -(∫ z in K, star (ψ (z.re,z.im)) *
        (completedCompactGradient N hK (actualEnergyLift N u)) z (firstCoordinate vertical) *
          (z.im : ℂ)) := by
  simpa only [actualEnergyLift_projection] using
    completed_arbitrary_smooth_weak_derivative N hK vertical hψ hc hs hTK (actualEnergyLift N u)

end
end ImbalancedChen.Part3.Gamma0ArbitrarySmoothWeakGradient20261026b
