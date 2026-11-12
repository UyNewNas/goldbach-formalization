import ImbalancedChen.Part3OriginalPositiveStripData
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Termwise integration against the actual complex period-64 test and
the entire odd moment correction with all its exponential weights. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStripMoments20261112
open Set Filter MeasureTheory Complex Metric
open scoped Topology BigOperators ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalFullModulusTestJets20261102 (spectralTest_div_q_integrable)
open ActualPositiveCosineProfile20261112 (testDiv)
open ActualPositiveHolomorphicWeights20261112
open OriginalPositiveJacobiAnger20261112 (oddOrder)
open OriginalPositiveStripData20261112
open private div_smooth from ImbalancedChen.Part3ActualPositiveCosineProfile

def m (ell : D4→ℤ) (Y : ℝ) (j : ℕ) := moment (oddOrder j) (spectralTest ell Y)
def sign (j : ℕ) : ℂ := (-1:ℂ)^j
def coeff (ell : D4→ℤ) (Y : ℝ) (j : ℕ) := sign j*m ell Y j

theorem odd_injective : Function.Injective oddOrder := fun _ _ h => by unfold oddOrder at h; omega

private theorem le_two_pow (n : ℕ) : (n:ℝ)≤(2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n:=n)]

theorem factorial_weight (r : ℕ) {A : ℝ} (hA : 0≤A) :
    Summable (fun j => (oddOrder j:ℝ)^r*A^(oddOrder j)/((oddOrder j).factorial:ℝ)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ <|
    (Real.summable_pow_div_factorial ((2:ℝ)^r*A)).comp_injective odd_injective
  intro j
  simp only [Function.comp_apply,mul_pow]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hA _)
  simpa only [←pow_mul,Nat.mul_comm (oddOrder j) r] using
    (pow_le_pow_left₀ (Nat.cast_nonneg (oddOrder j)) (le_two_pow (oddOrder j)) r)

theorem summable_coeff (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (r : ℕ) {A : ℝ} (hA : 0≤A) :
    Summable (fun j => ‖coeff ell Y j‖*(oddOrder j:ℝ)^r*A^(oddOrder j)) := by
  obtain ⟨C,hC,h⟩ := moment_factorial ell hY
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ <|
    (factorial_weight r (mul_nonneg (by positivity : 0≤8*Y) hA)).mul_left C
  intro j
  simp only [coeff,sign,m,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,mul_pow]
  calc
    _ ≤ (C*(8*Y)^oddOrder j/((oddOrder j).factorial:ℝ))*(oddOrder j:ℝ)^r*A^(oddOrder j) := by
      gcongr; exact h _
    _ = _ := by ring

/-- A bounded geometric multiplier can be integrated against the original
Bessel expansion, with the resulting coefficients exactly the original m_j. -/
theorem integrate_odd (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (b : ℕ→ℂ) (F : ℝ→ℂ)
    {C R : ℝ} (hC : 0≤C) (hR : 0≤R) (hb : ∀ j,‖b j‖≤C*R^(oddOrder j))
    (H : ∀ q : ℝ,0<q → HasSum (fun j => b j*intJ (oddOrder j) q) (F q)) :
    HasSum (fun j => b j*m ell Y j) (∫ q in Ioi (0:ℝ),F q*testDiv ell Y q) := by
  let D := fun j => (C*expMass (16*Y))*((R*(8*Y))^oddOrder j/((oddOrder j).factorial:ℝ))
  have d0 (j : ℕ) : 0≤D j := by dsimp [D]; have := expMass_nonneg (16*Y); positivity
  have sd : Summable D := ( (Real.summable_pow_div_factorial (R*(8*Y))).comp_injective odd_injective).mul_left _
  let f := testDiv ell Y
  have hi : IntegrableOn f (Ioi 0) := (spectralTest_div_q_integrable ell hY).integrableOn
  have integrated := hasSum_integral_of_dominated_convergence (μ:=volume.restrict (Ioi (0:ℝ)))
    (F:=fun j q => b j*intJ (oddOrder j) q*f q) (f:=fun q => F q*f q)
    (fun j q => D j*‖f q‖)
    (fun j => (((intJ_continuous _).const_mul _).mul (div_smooth ell hY).continuous).aestronglyMeasurable)
    (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      rw [norm_mul,norm_mul]
      by_cases z : f q=0
      · simp [z]
      obtain ⟨_,hqB⟩ := div_support ell hY (subset_tsupport _ z)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        _ ≤ (C*R^(oddOrder j))*((16*Y/2)^oddOrder j/((oddOrder j).factorial:ℝ)*expMass (16*Y)) :=
          mul_le_mul (hb j) (intJ_bound _ hq.le hqB) (norm_nonneg _) (by positivity)
        _ = _ := by simp only [D,mul_pow,show 16*Y/2=8*Y by ring]; ring)
    (ae_of_all _ fun q => sd.mul_right _) (by simpa only [tsum_mul_right] using hi.norm.const_mul (∑' j,D j))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq; exact (H q hq).mul_right _)
  apply integrated.congr_fun
  intro j
  simp only [m,moment,f,testDiv]
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun q => by ring

def series (ell : D4→ℤ) (Y : ℝ) (z : ℂ) :=
  ∑' j, coeff ell Y j*Complex.exp (-(oddOrder j:ℂ)*z)

private theorem exp_bound (n : ℕ) (z : ℂ) {R : ℝ} (hz : ‖z‖≤R) :
    ‖Complex.exp (-(n:ℂ)*z)‖≤(Real.exp R)^n := by
  rw [Complex.norm_exp,←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
  simp [Complex.mul_re]
  linarith only [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n : 0≤(n:ℝ))]

theorem series_sum (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (z : ℂ) :
    Summable (fun j => coeff ell Y j*Complex.exp (-(oddOrder j:ℂ)*z)) := by
  apply Summable.of_norm_bounded (g:=fun j => ‖coeff ell Y j‖*(Real.exp ‖z‖)^(oddOrder j))
  · simpa using summable_coeff ell hY 0 (Real.exp_pos ‖z‖).le
  · intro j
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (exp_bound _ _ le_rfl) (norm_nonneg _)

theorem series_deriv (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (z : ℂ) :
    HasDerivAt (series ell Y)
      (∑' j, coeff ell Y j*((-(oddOrder j:ℂ))*Complex.exp (-(oddOrder j:ℂ)*z))) z := by
  let R := ‖z‖+1
  have hz : z∈ball (0:ℂ) R := by simpa [R] using lt_add_one ‖z‖
  have B := hasDerivAt_tsum_of_isPreconnected (summable_coeff ell hY 1 (Real.exp_pos R).le)
    (Metric.isOpen_ball (x:=(0:ℂ)) (ε:=R)) (convex_ball (0:ℂ) R).isPreconnected
    (fun j u _ => by
      convert (((hasDerivAt_id u).const_mul (-(oddOrder j:ℂ))).cexp.const_mul (coeff ell Y j)) using 1 <;> ring)
    (fun j u hu => by
      simp only [norm_mul,norm_neg,Complex.norm_natCast,pow_one]
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_left (exp_bound _ u (by simpa using (Metric.mem_ball.mp hu).le)) (by positivity))
    hz (series_sum ell hY z) hz
  exact B

theorem series_norm (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (z : ℂ) (hx : 0≤z.re) :
    ‖series ell Y z‖ ≤ (∑' j,‖coeff ell Y j‖)*Real.exp (-z.re) := by
  have hs : Summable (fun j => ‖coeff ell Y j‖) := by simpa using summable_coeff ell hY 0 (A:=1) zero_le_one
  rw [←tsum_mul_right]
  apply tsum_of_norm_bounded (hs.mul_right _).hasSum
  intro j
  rw [norm_mul,Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have h1 : (1:ℝ)≤oddOrder j := by exact_mod_cast (show 1≤oddOrder j by dsimp [oddOrder]; omega)
  simp [Complex.mul_re]
  nlinarith only [mul_le_mul_of_nonneg_right h1 hx]

end ImbalancedChen.Part3.OriginalPositiveStripMoments20261112
end
