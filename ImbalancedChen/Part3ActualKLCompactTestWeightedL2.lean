import ImbalancedChen.Part3ActualKLCompactTestIntegrationByParts
import ImbalancedChen.Part3ImaginaryKAdaptiveContourBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual K_{i tau} transform of every genuine compact C∞ radial test has
finite energy for (2/pi²) tau sinh(pi tau) d tau on tau>0. Two actual H
integrations by parts supply tau^-4, and the proved adaptive contour bound
supplies the exact exponential cancellation. The resulting explicit tail
majorant is a constant times tau^-5. Near zero the same actual bound gives
a uniform finite ceiling. No rapid-decay or Plancherel premise is supplied.
-/

namespace ImbalancedChen.Part3.ActualKLCompactTestWeightedL220261025a

noncomputable section
open Set MeasureTheory Filter
open RadialSchrodingerL2Form20261025a ComplexOrderKBridgeSourceOnly
open ComplexOrderKRadialRegularitySourceOnly
open ActualKLCompactTestIntegrationByParts20261025a
open ImaginaryKAdaptiveContourBound20261025a

def normalization : ℝ := 2 / Real.pi^2
def actualKLWeight (tau : ℝ) : ℝ := normalization * tau * Real.sinh (Real.pi*tau)
def actualKLEnergy (T : RadialTest) (tau : ℝ) : ℝ :=
  actualKLWeight tau * ‖actualKtransform T.function tau‖^2

theorem normalization_pos : 0 < normalization := by unfold normalization; positivity

theorem actualKLWeight_nonneg {tau : ℝ} (htau : 0 ≤ tau) : 0 ≤ actualKLWeight tau := by
  unfold actualKLWeight
  exact mul_nonneg (mul_nonneg normalization_pos.le htau)
    (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le htau))

theorem exists_positive_physical_lower (T : RadialTest) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ tsupport T.function, a ≤ Real.exp r := by
  obtain ⟨L, hL⟩ := T.compact.bddBelow
  exact ⟨Real.exp L, Real.exp_pos L, fun r hr => Real.exp_le_exp.mpr (hL hr)⟩

def testL1 (T : RadialTest) : ℝ := ∫ r : ℝ, ‖T.function r‖
def contourBudget (T : RadialTest) (a : ℝ) : ℝ :=
  testL1 T * Real.exp 1 * (max 0 (Real.log (4/a)) + 2)

theorem testL1_nonneg (T : RadialTest) : 0 ≤ testL1 T := integral_nonneg (fun r => norm_nonneg _)

theorem contourBudget_nonneg (T : RadialTest) (a : ℝ) : 0 ≤ contourBudget T a := by
  unfold contourBudget
  exact mul_nonneg (mul_nonneg (testL1_nonneg T) (Real.exp_pos _).le) (by positivity)

/-- Integrating the actual contour bound uses only the actual compact
support geometry and the finite L¹ norm of the same test. -/
theorem actualKtransform_adaptive_bound (T : RadialTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r) (tau : ℝ) :
    ‖actualKtransform T.function tau‖ ≤
      testL1 T * (Real.exp 1 * Real.exp (-Real.pi*|tau|/2) *
        (Real.log (1+|tau|) + max 0 (Real.log (4/a)) + 1)) := by
  let M := Real.exp 1 * Real.exp (-Real.pi*|tau|/2) *
    (Real.log (1+|tau|) + max 0 (Real.log (4/a)) + 1)
  have hi : Integrable (fun r : ℝ => ‖T.function r‖ * M) :=
    (T.smooth.continuous.integrable_of_hasCompactSupport T.compact).norm.mul_const M
  calc
    _ ≤ ∫ r : ℝ, ‖T.function r * radialK ((tau : ℂ)*Complex.I) r‖ :=
      norm_integral_le_integral_norm
    _ ≤ ∫ r : ℝ, ‖T.function r‖ * M := by
      apply integral_mono (actualKtransform_integrable T.function T.smooth.continuous T.compact tau).norm hi
      intro r
      rw [norm_mul]
      by_cases hr : r ∈ tsupport T.function
      · exact mul_le_mul_of_nonneg_left
          (complexOrderK_imaginary_norm_le_adaptive ha (hsupport r hr) tau) (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hr, norm_zero, zero_mul, zero_mul]
    _ = _ := by rw [integral_mul_const]; rfl

private theorem log_linear_bound {tau : ℝ} (htau : 0 ≤ tau) :
    Real.log (1+tau) ≤ tau := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+tau)
  linarith

/-- No contour endpoint singularity occurs on the low-order interval. -/
theorem actualKtransform_low_bound (T : RadialTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {tau : ℝ} (htau : 0 ≤ tau) (htauUpper : tau ≤ 1) :
    ‖actualKtransform T.function tau‖ ≤ contourBudget T a := by
  have h := actualKtransform_adaptive_bound T ha hsupport tau
  rw [abs_of_nonneg htau] at h
  have he : Real.exp (-Real.pi*tau/2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hl : Real.log (1+tau) ≤ 1 := (log_linear_bound htau).trans htauUpper
  have hn : 0 ≤ Real.log (1+tau) + max 0 (Real.log (4/a)) + 1 := by
    have hp := Real.log_nonneg (show 1 ≤ 1+tau by linarith)
    positivity
  apply h.trans
  unfold contourBudget
  calc
    _ ≤ testL1 T * (Real.exp 1 * 1 *
        (Real.log (1+tau)+max 0 (Real.log (4/a))+1)) := by
      gcongr
    _ ≤ _ := by
      have hL := testL1_nonneg T
      have hE := (Real.exp_pos (1 : ℝ)).le
      nlinarith

private theorem adaptive_linear_high (T : RadialTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {tau : ℝ} (htau : 1 ≤ tau) :
    ‖actualKtransform T.function tau‖ ≤ contourBudget T a * tau * Real.exp (-Real.pi*tau/2) := by
  have hp : 0 ≤ tau := zero_le_one.trans htau
  have h := actualKtransform_adaptive_bound T ha hsupport tau
  rw [abs_of_nonneg hp] at h
  have hlog := log_linear_bound hp
  have hC : 0 ≤ max 0 (Real.log (4/a)) := le_max_left _ _
  have hlinear : Real.log (1+tau)+max 0 (Real.log (4/a))+1 ≤
      (max 0 (Real.log (4/a))+2)*tau := by nlinarith
  apply h.trans
  calc
    _ ≤ testL1 T * (Real.exp 1 * Real.exp (-Real.pi*tau/2) *
        ((max 0 (Real.log (4/a))+2)*tau)) := by gcongr
    _ = _ := by unfold contourBudget; ring

/-- Two true H transfers turn the adaptive contour estimate into an
integrable polynomial tail after the KL exponential weight cancels. -/
theorem actualKtransform_high_bound (T : RadialTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {tau : ℝ} (htau : 1 ≤ tau) :
    ‖actualKtransform T.function tau‖ ≤
      contourBudget (hamiltonianIterate 2 T) a * Real.exp (-Real.pi*tau/2) / tau^3 := by
  have hp : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hs : ∀ r ∈ tsupport (hamiltonianIterate 2 T).function, a ≤ Real.exp r :=
    fun r hr => hsupport r (hamiltonianIterate_support_subset 2 T hr)
  have h := adaptive_linear_high (hamiltonianIterate 2 T) ha hs htau
  have he := congrArg norm (actualKtransform_iterated_hamiltonian 2 T tau)
  have hn : tau^4 * ‖actualKtransform T.function tau‖ =
      ‖actualKtransform (hamiltonianIterate 2 T).function tau‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] using he
  have hmul : tau * (tau^3 * ‖actualKtransform T.function tau‖) ≤
      tau * (contourBudget (hamiltonianIterate 2 T) a * Real.exp (-Real.pi*tau/2)) := by
    calc
      _ = tau^4 * ‖actualKtransform T.function tau‖ := by ring
      _ = _ := hn
      _ ≤ _ := h.trans_eq (by ring)
  have hcancel := (mul_le_mul_left hp).mp hmul
  apply (le_div_iff₀ (pow_pos hp 3)).2
  nlinarith

theorem actualKtransform_stronglyMeasurable (T : RadialTest) :
    StronglyMeasurable (actualKtransform T.function) := by
  have hbase : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      complexOrderIntegrand ((p.1.1 : ℂ)*Complex.I) (Real.exp p.1.2) p.2) := by
    unfold complexOrderIntegrand
    fun_prop
  have hK : StronglyMeasurable (fun p : ℝ × ℝ => radialK ((p.1 : ℂ)*Complex.I) p.2) := by
    exact hbase.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
  exact ((T.smooth.continuous.comp continuous_snd).stronglyMeasurable.mul hK).integral_prod_right'

theorem actualKLEnergy_stronglyMeasurable (T : RadialTest) :
    StronglyMeasurable (actualKLEnergy T) := by
  have hw : Continuous actualKLWeight := by unfold actualKLWeight; fun_prop
  exact hw.stronglyMeasurable.mul ((actualKtransform_stronglyMeasurable T).norm.pow 2)

private theorem sinh_le_exp (x : ℝ) : Real.sinh x ≤ Real.exp x := by
  rw [Real.sinh_eq]
  linarith [Real.exp_pos x, Real.exp_pos (-x)]

theorem actualKLEnergy_low_bound (T : RadialTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {tau : ℝ} (htau : 0 ≤ tau) (htauUpper : tau ≤ 1) :
    actualKLEnergy T tau ≤ normalization * Real.exp Real.pi * (contourBudget T a)^2 := by
  have hf := actualKtransform_low_bound T ha hsupport htau htauUpper
  have hs := sinh_le_exp (Real.pi*tau)
  have he : Real.exp (Real.pi*tau) ≤ Real.exp Real.pi := Real.exp_le_exp.mpr
    (by nlinarith [Real.pi_pos])
  have hfSq := pow_le_pow_left₀ (norm_nonneg _) hf 2
  have hN := normalization_pos.le
  have hweight : normalization * tau * Real.sinh (Real.pi*tau) ≤
      normalization * tau * Real.exp (Real.pi*tau) :=
    mul_le_mul_of_nonneg_left hs (mul_nonneg hN htau)
  unfold actualKLEnergy actualKLWeight
  calc
    _ ≤ normalization * tau * Real.exp (Real.pi*tau) * (contourBudget T a)^2 := by
      exact mul_le_mul hweight hfSq (sq_nonneg _)
        (mul_nonneg (mul_nonneg hN htau) (Real.exp_pos _).le)
    _ ≤ _ := by
      have hte : tau * Real.exp (Real.pi*tau) ≤ Real.exp Real.pi := by
        simpa only [one_mul] using mul_le_mul htauUpper he (Real.exp_pos _).le zero_le_one
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hte hN) (sq_nonneg (contourBudget T a))
      convert hmul using 1 <;> ring

theorem actualKLEnergy_high_bound (T : RadialTest) {a : ℝ} (ha : 0 < a)
    (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {tau : ℝ} (htau : 1 ≤ tau) :
    actualKLEnergy T tau ≤
      (normalization * (contourBudget (hamiltonianIterate 2 T) a)^2) * (tau^5)⁻¹ := by
  have hp : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hf := actualKtransform_high_bound T ha hsupport htau
  have hfSq := pow_le_pow_left₀ (norm_nonneg _) hf 2
  have hN := normalization_pos.le
  have hweight : normalization * tau * Real.sinh (Real.pi*tau) ≤
      normalization * tau * Real.exp (Real.pi*tau) :=
    mul_le_mul_of_nonneg_left (sinh_le_exp _) (mul_nonneg hN hp.le)
  have he : Real.exp (Real.pi*tau) * Real.exp (-Real.pi*tau/2)^2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  unfold actualKLEnergy actualKLWeight
  calc
    _ ≤ normalization * tau * Real.exp (Real.pi*tau) *
        (contourBudget (hamiltonianIterate 2 T) a * Real.exp (-Real.pi*tau/2) / tau^3)^2 := by
      exact mul_le_mul hweight hfSq (sq_nonneg _)
        (mul_nonneg (mul_nonneg hN hp.le) (Real.exp_pos _).le)
    _ = (normalization * (contourBudget (hamiltonianIterate 2 T) a)^2) *
        (Real.exp (Real.pi*tau) * Real.exp (-Real.pi*tau/2)^2) / tau^5 := by
      field_simp [hp.ne']
      ring
    _ = _ := by rw [he]; ring

private theorem inverse_fifth_integrable :
    IntegrableOn (fun tau : ℝ => (tau^5)⁻¹) (Ioi (1 : ℝ)) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-5 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ)<1)
  simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast] using h

/-- Genuine positive-axis weighted-L² finiteness for every actual C∞
compact radial test. This does not assert a transform norm equality. -/
theorem actualKtransform_KL_weighted_square_integrable (T : RadialTest) :
    IntegrableOn (fun tau : ℝ =>
      (2 / Real.pi^2) * tau * Real.sinh (Real.pi*tau) *
        ‖actualKtransform T.function tau‖^2) (Ioi (0 : ℝ)) := by
  obtain ⟨a, ha, hs⟩ := exists_positive_physical_lower T
  have hlow : IntegrableOn (actualKLEnergy T) (Ioc (0 : ℝ) 1) := by
    have hmajor : IntegrableOn (fun _ : ℝ =>
        normalization * Real.exp Real.pi * (contourBudget T a)^2) (Ioc (0 : ℝ) 1) :=
      continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    apply hmajor.mono' (actualKLEnergy_stronglyMeasurable T).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with tau htau
    have hpos : 0 ≤ actualKLEnergy T tau :=
      mul_nonneg (actualKLWeight_nonneg htau.1.le) (sq_nonneg _)
    rw [Real.norm_of_nonneg hpos]
    exact actualKLEnergy_low_bound T ha hs htau.1.le htau.2
  have hhigh : IntegrableOn (actualKLEnergy T) (Ioi (1 : ℝ)) := by
    have hmajor := inverse_fifth_integrable.const_mul
      (normalization * (contourBudget (hamiltonianIterate 2 T) a)^2)
    apply hmajor.mono' (actualKLEnergy_stronglyMeasurable T).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
    have hpos : 0 ≤ actualKLEnergy T tau := mul_nonneg
      (actualKLWeight_nonneg (by linarith)) (sq_nonneg _)
    rw [Real.norm_of_nonneg hpos]
    exact actualKLEnergy_high_bound T ha hs htau.le
  have hset : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi (0 : ℝ) := by
    ext tau
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases le_or_gt tau 1 with ht | ht
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr ht
  have htotal := hlow.union hhigh
  rw [hset] at htotal
  exact htotal

end
end ImbalancedChen.Part3.ActualKLCompactTestWeightedL220261025a
