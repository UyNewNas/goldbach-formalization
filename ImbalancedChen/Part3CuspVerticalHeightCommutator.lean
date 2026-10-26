import ImbalancedChen.Part3ActualCuspStripCutoff
import ImbalancedChen.Part3CuspSmoothHeightWeakLocalization
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Physical vertical cutoff commutators for ARBITRARY weighted L2 input.
The existing chi(y/R) supplies its actual derivative bound. A fixed
smooth lower transition is identically one above a and forces positive
compact support [a/2,2R]. On the tail y>a it contributes NO derivative.
The raw-dy commutator chi'_R*u tends strongly to zero by escaping-tail
dominated convergence against the input's actual dy/y^2 square mass.
No raw L2 assumption on u, log cutoff, or commutator convergence premise
occurs. A fixed transition ratio 2 does not make sup|y chi'_R| tend zero;
the integrable escaping tail is the required mechanism.
-/
namespace ImbalancedChen.Part3.CuspVerticalHeightCommutator20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCuspStripCutoff20261025a
open CuspSmoothHeightWeakLocalization20261026b
attribute [local instance] Measure.Subtype.measureSpace

def lowerHeightTransition (a : ℝ) (y : ℝ) : ℝ := Real.smoothTransition (2 * y / a - 1)
def verticalHeightCutoff (a R : ℝ) (y : ℝ) : ℝ :=
  lowerHeightTransition a y * heightCutoff R y

theorem lowerHeightTransition_smooth (a : ℝ) : ContDiff ℝ ∞ (lowerHeightTransition a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const a |>.sub contDiff_const)

theorem lowerHeightTransition_one {a y : ℝ} (ha : 0 < a) (hy : a ≤ y) :
    lowerHeightTransition a y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  change 1 ≤ 2 * y / a - 1
  have h : 2 ≤ 2 * y / a := (le_div_iff₀ ha).mpr (by linarith)
  linarith

theorem lowerHeightTransition_zero {a y : ℝ} (ha : 0 < a) (hy : y ≤ a / 2) :
    lowerHeightTransition a y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  change 2 * y / a - 1 ≤ 0
  have h : 2 * y / a ≤ 1 := (div_le_iff₀ ha).mpr (by linarith)
  linarith

theorem verticalHeightCutoff_smooth (a R : ℝ) : ContDiff ℝ ∞ (verticalHeightCutoff a R) :=
  (lowerHeightTransition_smooth a).mul (heightCutoff_cinfty R)

theorem verticalHeightCutoff_range (a R y : ℝ) :
    0 ≤ verticalHeightCutoff a R y ∧ verticalHeightCutoff a R y ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (2 * y / a - 1)
  have h1 := Real.smoothTransition.le_one (2 * y / a - 1)
  have h2 := chi_nonneg (y / R)
  have h3 := chi_le_one (y / R)
  constructor
  · exact mul_nonneg h0 h2
  · dsimp [verticalHeightCutoff, lowerHeightTransition, heightCutoff]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]

theorem verticalHeightCutoff_eq_one {a R y : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hay : a ≤ y) (hyR : y ≤ R) : verticalHeightCutoff a R y = 1 := by
  rw [verticalHeightCutoff, lowerHeightTransition_one ha hay,
    heightCutoff_eq_one hR (ha.le.trans hay) hyR, one_mul]

theorem verticalHeightCutoff_tsupport {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    tsupport (verticalHeightCutoff a R) ⊆ Icc (a / 2) (2 * R) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  constructor
  · by_contra h
    exact hy (by rw [verticalHeightCutoff, lowerHeightTransition_zero ha (le_of_lt (lt_of_not_ge h)), zero_mul])
  · by_contra h
    exact hy (by rw [verticalHeightCutoff, heightCutoff_eq_zero hR (le_of_lt (lt_of_not_ge h)), mul_zero])

def physicalVerticalCutoff (a R : ℝ) (ha : 0 < a) (hR : 0 < R) : SmoothHeightCutoff where
  function := verticalHeightCutoff a R
  smooth := verticalHeightCutoff_smooth a R
  compact := isCompact_Icc.of_isClosed_subset isClosed_tsupport (verticalHeightCutoff_tsupport ha hR)
  positive_support := fun y hy => lt_of_lt_of_le (half_pos ha) (verticalHeightCutoff_tsupport ha hR hy).1
  nonneg := fun y => (verticalHeightCutoff_range a R y).1
  le_one := fun y => (verticalHeightCutoff_range a R y).2

theorem verticalHeightCutoff_deriv_on_tail {a R y : ℝ} (ha : 0 < a) (hy : a < y) :
    deriv (verticalHeightCutoff a R) y = deriv (heightCutoff R) y := by
  have he : verticalHeightCutoff a R =ᶠ[𝓝 y] heightCutoff R := by
    filter_upwards [gt_mem_nhds hy] with t ht
    rw [verticalHeightCutoff, lowerHeightTransition_one ha ht.le, one_mul]
  exact he.deriv_eq

theorem verticalHeightCutoff_deriv_bound {a R y : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hy : a < y) : |deriv (verticalHeightCutoff a R) y| ≤ derivativeBound / R := by
  rw [verticalHeightCutoff_deriv_on_tail ha hy, deriv_heightCutoff, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right (deriv_chi_bound _) hR.le

theorem verticalHeightCutoff_energy_bound {a R y : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hy : a < y) : y ^ 2 * (deriv (verticalHeightCutoff a R) y) ^ 2 ≤ cutoffEnergyConstant := by
  let z : UpperHalfPlane := ⟨⟨0, y⟩, ha.trans hy⟩
  have hz : z ∈ widthStrip 1 := by simp [widthStrip, z]
  have h := cutoff_vertical_energy_pointwise hR z hz
  have hb : (highWidthStrip 1 R).indicator (fun _ => cutoffEnergyConstant) z ≤ cutoffEnergyConstant := by
    by_cases hmem : z ∈ highWidthStrip 1 R <;> simp [hmem, cutoffEnergyConstant_nonneg]
  simpa only [z, verticalHeightCutoff_deriv_on_tail ha hy] using h.trans hb

theorem physical_functionMeasure_density (a : ℝ) :
    functionMeasure a = (derivativeMeasure a).withDensity
      (fun z : CuspCylinder => (heightDensity z.2 : ℝ≥0∞)) := by
  rw [functionMeasure, cylinderMeasure, heightMeasure,
    prod_withDensity_right heightDensity_continuous.measurable.coe_nnreal_ennreal,
    restrict_withDensity (strictCylinderTail_measurable a)]
  rfl

def commutatorFunction (a R : ℝ) (u : FunctionL2 a) (z : CuspCylinder) : ℂ :=
  (deriv (verticalHeightCutoff a R) (z.2 : ℝ) : ℂ) * u z

theorem commutator_majorant_integrable (a : ℝ) (u : FunctionL2 a) :
    Integrable (fun z : CuspCylinder => cutoffEnergyConstant *
      (heightDensity z.2 : ℝ) * ‖u z‖ ^ 2) (derivativeMeasure a) := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  rw [physical_functionMeasure_density] at h
  have hd := (integrable_withDensity_iff_integrable_smul
    (heightDensity_continuous.measurable.comp measurable_snd)).mp h
  simpa only [NNReal.smul_def, smul_eq_mul, mul_assoc] using hd.const_mul cutoffEnergyConstant

theorem commutator_sq_bound {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (u : FunctionL2 a) (z : CuspCylinder) (hz : a < (z.2 : ℝ)) :
    ‖commutatorFunction a R u z‖ ^ 2 ≤
      cutoffEnergyConstant * (heightDensity z.2 : ℝ) * ‖u z‖ ^ 2 := by
  have he := verticalHeightCutoff_energy_bound ha hR hz
  have hy : 0 < (z.2 : ℝ) := z.2.property
  have hd : (deriv (verticalHeightCutoff a R) (z.2 : ℝ)) ^ 2 ≤
      cutoffEnergyConstant * (heightDensity z.2 : ℝ) := by
    rw [heightDensity_coe, div_pow, one_pow, one_div]
    apply (le_mul_inv_iff₀ (sq_pos_of_pos hy)).mpr
    nlinarith [he]
  simpa only [commutatorFunction, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using mul_le_mul_of_nonneg_right hd (sq_nonneg ‖u z‖)

theorem commutator_memLp {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (u : FunctionL2 a) :
    MemLp (commutatorFunction a R u) 2 (derivativeMeasure a) := by
  have hm : AEStronglyMeasurable (commutatorFunction a R u) (derivativeMeasure a) :=
    ((Complex.continuous_ofReal.comp
      ((verticalHeightCutoff_smooth a R).continuous_deriv (by simp) |>.comp
        (continuous_subtype_val.comp continuous_snd))).stronglyMeasurable.mul
      (Lp.stronglyMeasurable u)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (commutator_majorant_integrable a u).mono' (hm.norm.pow_const 2)
  filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using
    commutator_sq_bound ha hR u z hz.2

def commutatorVector {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (u : FunctionL2 a) :
    DerivativeL2 a := (commutator_memLp ha hR u).toLp (commutatorFunction a R u)

def cutoffRadius (a : ℝ) (n : ℕ) : ℝ := a + (n : ℝ) + 1
theorem cutoffRadius_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < cutoffRadius a n := by
  unfold cutoffRadius
  positivity

theorem cutoffRadius_eventually_gt (a y : ℝ) : ∀ᶠ n : ℕ in atTop, y < cutoffRadius a n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (y - a)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hc : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  dsimp [cutoffRadius]
  linarith

/-- The commutator tends to zero in RAW vertical energy for arbitrary
weighted input; the majorant is actual weighted input mass, not raw L2. -/
theorem commutatorVector_tendsto_zero {a : ℝ} (ha : 0 < a) (u : FunctionL2 a) :
    Tendsto (fun n => commutatorVector ha (cutoffRadius_pos ha n) u) atTop (𝓝 0) := by
  have hlim : ∀ᵐ z ∂derivativeMeasure a, Tendsto (fun n =>
      ‖commutatorFunction a (cutoffRadius a n) u z‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
    apply (tendsto_congr' ((cutoffRadius_eventually_gt a (z.2 : ℝ)).mono fun n hn => ?_)).mpr
    · exact tendsto_const_nhds
    · have hd : deriv (verticalHeightCutoff a (cutoffRadius a n)) (z.2 : ℝ) = 0 := by
        rw [verticalHeightCutoff_deriv_on_tail ha hz.2, deriv_heightCutoff,
          deriv_chi_zero_below (div_pos z.2.property (cutoffRadius_pos ha n))
            ((div_lt_one (cutoffRadius_pos ha n)).mpr hn), zero_div]
      simp [commutatorFunction, hd]
  have hi := tendsto_integral_of_dominated_convergence
    (fun z => cutoffEnergyConstant * (heightDensity z.2 : ℝ) * ‖u z‖ ^ 2)
    (fun n => (commutator_memLp ha (cutoffRadius_pos ha n) u).aestronglyMeasurable.norm.pow_const 2)
    (commutator_majorant_integrable a u)
    (fun n => by
      filter_upwards [ae_restrict_mem (strictCylinderTail_measurable a)] with z hz
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using
        commutator_sq_bound ha (cutoffRadius_pos ha n) u z hz.2)
    (f := fun _ => (0 : ℝ)) hlim
  have hn : Tendsto (fun n => ‖commutatorVector ha (cutoffRadius_pos ha n) u‖ ^ 2)
      atTop (𝓝 0) := by
    have he (n : ℕ) : ‖commutatorVector ha (cutoffRadius_pos ha n) u‖ ^ 2 =
        ∫ z, ‖commutatorFunction a (cutoffRadius a n) u z‖ ^ 2 ∂derivativeMeasure a := by
      have h := L2.inner_def (𝕜 := ℂ) (commutatorVector ha (cutoffRadius_pos ha n) u)
        (commutatorVector ha (cutoffRadius_pos ha n) u)
      simp_rw [inner_self_eq_norm_sq_to_K] at h
      rw [integral_ofReal] at h
      rw [Complex.ofReal_injective h]
      apply integral_congr_ae
      exact (commutator_memLp ha (cutoffRadius_pos ha n) u).coeFn_toLp.fun_comp (fun x : ℂ => ‖x‖ ^ 2)
    simpa only [he, integral_zero] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, sub_zero] using h

end
end ImbalancedChen.Part3.CuspVerticalHeightCommutator20261026b
