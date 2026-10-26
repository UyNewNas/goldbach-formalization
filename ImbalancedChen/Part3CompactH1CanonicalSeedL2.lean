import ImbalancedChen.Part3CompactH1QuotientEnergyLimit
import ImbalancedChen.Part3CanonicalPlanarL2Unitary

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Ordinary planar L2 convergence with one positive support floor gives
canonical hyperbolic L2 convergence for raw, possibly nonsmooth seeds.
This supplies the missing input to genuine weak-seed Poincare continuity;
no smoothness or periodization-continuity premise is assumed.
-/
namespace ImbalancedChen.Part3.CompactH1CanonicalSeedL220261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open SupportedH1FiniteTensorDensity20261026a ProductKernelL2TranslationAverage20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open GammaCompactSeedH1EnergyTransfer20261026b GammaFiniteSeedCoordinateH1Budget20261026b
open Gamma0WholeChartCoordinateWeakEquation20261026b CanonicalPlanarL2UnitarySourceOnly
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b LocalH1TensorDifferenceABI20261026b
open CompactH1QuotientEnergyLimit20261026b

abbrev HyperbolicSeedL2 := Lp ℂ 2 (volume : Measure UpperHalfPlane)

def upperSeed (F : Plane → ℂ) : UpperHalfPlane → ℂ := coordinateSeed F

theorem toLp_norm_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : X → ℂ} (hF : MemLp F 2 μ) : ‖hF.toLp F‖^2 = ∫ p, ‖F p‖^2 ∂μ := by
  rw [← scalar_L2_integral_sq μ (hF.toLp F)]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with p hp
  rw [hp]

/-- Raw coordinate seed lifting, valid without continuity. -/
theorem upperSeed_memLp {F : Plane → ℂ} (hF : MemLp F 2 volume)
    {a : ℝ} (ha : 0 < a) (hzero : ∀ p : Plane, p.2 < a → F p = 0) :
    MemLp (upperSeed F) 2 (volume : Measure UpperHalfPlane) := by
  let W : Plane → ℂ := fun p => (max a p.2)⁻¹ • F p
  have hcont : Continuous (fun p : Plane => (max a p.2)⁻¹) :=
    (continuous_const.max continuous_snd).inv₀ (fun p => ne_of_gt (ha.trans_le (le_max_left _ _)))
  have hW : MemLp W 2 volume := by
    apply (hF.const_smul a⁻¹).of_le (hcont.aestronglyMeasurable.smul hF.aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      have hmax : 0 < max a p.2 := ha.trans_le (le_max_left _ _)
      have hb : (max a p.2)⁻¹ ≤ a⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le ha (le_max_left a p.2)
      simp only [W,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos hmax.inv_pos,
        abs_of_pos ha.inv_pos]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have heq : inverseFunction W = upperSeed F := by
    funext z
    by_cases hz : F (z.re,z.im) = 0
    · simp only [inverseFunction,W,chartMap,Complex.measurableEquivRealProd_apply,upperSeed,coordinateSeed,hz,smul_zero]
    · have hy : a ≤ z.im := by
        by_contra hy
        exact hz (hzero (z.re,z.im) (lt_of_not_ge hy))
      simp only [inverseFunction,W,chartMap,Complex.measurableEquivRealProd_apply,
        max_eq_right hy,smul_smul,mul_inv_cancel₀ (ne_of_gt z.im_pos),one_smul,upperSeed,coordinateSeed]
  rw [← heq]
  exact inverseFunction_memLp hW

/-- The positive floor pays exactly a^-2 for raw canonical seed norm. -/
theorem upperSeed_norm_sq_le {F : Plane → ℂ} (hF : MemLp F 2 volume)
    {a : ℝ} (ha : 0 < a) (hzero : ∀ p : Plane, p.2 < a → F p = 0) :
    ‖(upperSeed_memLp hF ha hzero).toLp (upperSeed F)‖^2 ≤ (a⁻¹)^2 * ‖hF.toLp F‖^2 := by
  have hsupport : tsupport F ⊆ {p : Plane | a ≤ p.2} := by
    apply closure_minimal ?_ (isClosed_le continuous_const continuous_snd)
    intro p hp
    by_contra hn
    exact hp (hzero p (lt_of_not_ge hn))
  have hpos : tsupport F ⊆ upperChart := fun p hp => ha.trans_le (hsupport hp)
  have hext : extendUpper (upperSeed F) = F := coordinateSeed_extension hpos
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hb (p : Plane) : (p.2⁻¹)^2 * ‖F p‖^2 ≤ (a⁻¹)^2 * ‖F p‖^2 := by
    by_cases hp : a ≤ p.2
    · have hy : 0 < p.2 := ha.trans_le hp
      have hinv : p.2⁻¹ ≤ a⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le ha hp
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_two] using mul_self_le_mul_self (inv_pos.mpr hy).le hinv) (sq_nonneg _)
    · rw [hzero p (lt_of_not_ge hp),norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,mul_zero]
  have hiw : Integrable (fun p : Plane => (p.2⁻¹)^2 * ‖F p‖^2) volume := by
    apply (hi.const_mul ((a⁻¹)^2)).mono'
      ((measurable_snd.inv.pow_const 2).aestronglyMeasurable.mul hi.aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hb p
  rw [toLp_norm_sq,toLp_norm_sq,canonical_seed_mass_coordinate,hext,← integral_const_mul]
  exact integral_mono hiw (hi.const_mul ((a⁻¹)^2)) hb

/-- Simultaneous norm comparison for differences of raw seed classes. -/
theorem upperSeed_sub_norm_sq_le {F G : Plane → ℂ}
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) {a : ℝ} (ha : 0 < a)
    (hFzero : ∀ p : Plane, p.2 < a → F p = 0)
    (hGzero : ∀ p : Plane, p.2 < a → G p = 0) :
    ‖(upperSeed_memLp hF ha hFzero).toLp (upperSeed F) -
      (upperSeed_memLp hG ha hGzero).toLp (upperSeed G)‖^2 ≤
        (a⁻¹)^2 * ‖hF.toLp F - hG.toLp G‖^2 := by
  have hd : ∀ p : Plane, p.2 < a → (F-G) p = 0 := by
    intro p hp
    simp only [Pi.sub_apply,hFzero p hp,hGzero p hp,sub_self]
  have h := upperSeed_norm_sq_le (hF.sub hG) ha hd
  have heq : (upperSeed_memLp (hF.sub hG) ha hd).toLp (upperSeed (F-G)) =
      (upperSeed_memLp hF ha hFzero).toLp (upperSeed F) -
        (upperSeed_memLp hG ha hGzero).toLp (upperSeed G) := by
    apply Lp.ext
    filter_upwards [(upperSeed_memLp (hF.sub hG) ha hd).coeFn_toLp,
      Lp.coeFn_sub ((upperSeed_memLp hF ha hFzero).toLp (upperSeed F))
        ((upperSeed_memLp hG ha hGzero).toLp (upperSeed G)),
      (upperSeed_memLp hF ha hFzero).coeFn_toLp,(upperSeed_memLp hG ha hGzero).coeFn_toLp]
      with z hz hsub hf hg
    rw [hz,hsub,hf,hg]
    rfl
  rw [heq,MemLp.toLp_sub] at h
  exact h

end
end ImbalancedChen.Part3.CompactH1CanonicalSeedL220261026b

