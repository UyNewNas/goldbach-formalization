import ImbalancedChen.Part3ActualJHeightRadialForcing
import ImbalancedChen.Part3ActualJLargeQEnergyBound
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual forced radial energy and a genuine fixed-height order-derivative
large-q bound. The regularized quantity sqrt(Ew+1)+K/q is decreasing,
where K=8*|t|*sqrt(Eu(1)). Its derivative is proved from the native forced
ODE, Cauchy-Schwarz, and the actual unforced J energy bound.
No energy/variation/forcing estimate is an assumption.
-/

namespace ImbalancedChen.Part3.ActualJHeightEnergyBound20261026b

noncomputable section
open Complex Set
open ActualJImaginaryRadialJet20261026b ActualJRadialEnergyDerivative20261026b
open ActualJLargeQEnergyBound20261026b ActualJHeightRadialForcing20261026b

def forcedRadialEnergy (t q : ℝ) : ℝ :=
  ‖radialWFirst t q‖ ^ 2 + radialPotential t q * ‖radialW t q‖ ^ 2

def forcedEnergySlope (t q : ℝ) : ℝ :=
  -(2 * radialCoefficient t * ‖radialW t q‖ ^ 2 / q ^ 3) +
    2 * inner ℝ (radialWFirst t q) (radialWForcing t q)

def forcingMass (t : ℝ) : ℝ := 8 * |t| * largeQAmplitude t

def regularizedHeightEnergy (t q : ℝ) : ℝ :=
  Real.sqrt (forcedRadialEnergy t q + 1) + forcingMass t / q

def heightLargeQAmplitude (t : ℝ) : ℝ :=
  Real.sqrt (forcedRadialEnergy t 1 + 1) + forcingMass t

theorem forcingMass_nonneg (t : ℝ) : 0 ≤ forcingMass t := by
  exact mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (largeQAmplitude_nonneg t)

theorem forcedRadialEnergy_nonneg (t : ℝ) {q : ℝ} (hq : 0 < q) :
    0 ≤ forcedRadialEnergy t q := by
  unfold forcedRadialEnergy
  exact add_nonneg (sq_nonneg _) (mul_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (radialPotential_ge_one t hq)) (sq_nonneg _))

/-- Exact native forced energy law; the forcing term retains its sign. -/
theorem forcedRadialEnergy_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (forcedRadialEnergy t) (forcedEnergySlope t q) q := by
  have h := ((radialWFirst_q_hasDerivAt t hq).norm_sq).add
    ((radialPotential_hasDerivAt t hq).mul ((radialW_q_hasDerivAt t hq).norm_sq))
  convert h using 1
  · rfl
  · unfold forcedEnergySlope
    simp only [inner_add_right, inner_smul_right]
    rw [real_inner_comm (radialW t q) (radialWFirst t q)]
    ring

theorem radialW_norm_sq_le_forcedEnergy (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖radialW t q‖ ^ 2 ≤ forcedRadialEnergy t q := by
  have h := mul_le_mul_of_nonneg_right (radialPotential_ge_one t hq) (sq_nonneg ‖radialW t q‖)
  unfold forcedRadialEnergy
  nlinarith [sq_nonneg ‖radialWFirst t q‖]

theorem radialWFirst_norm_sq_le_forcedEnergy (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖radialWFirst t q‖ ^ 2 ≤ forcedRadialEnergy t q := by
  unfold forcedRadialEnergy
  exact le_add_of_nonneg_right (mul_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (radialPotential_ge_one t hq)) (sq_nonneg _))

private theorem first_norm_le_regularized (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖radialWFirst t q‖ ≤ Real.sqrt (forcedRadialEnergy t q + 1) :=
  Real.le_sqrt_of_sq_le ((radialWFirst_norm_sq_le_forcedEnergy t hq).trans (by linarith))

theorem radialWForcing_norm_le (t : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ‖radialWForcing t q‖ ≤ forcingMass t / q ^ 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  rw [radialWForcing, norm_smul, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg q)]
  norm_num
  calc
    8 * |t| / q ^ 2 * ‖radialJ t q‖ ≤ 8 * |t| / q ^ 2 * largeQAmplitude t :=
      mul_le_mul_of_nonneg_left (radialJ_norm_le_amplitude t hq) (by positivity)
    _ = forcingMass t / q ^ 2 := by unfold forcingMass; ring

theorem forcedEnergySlope_le (t : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    forcedEnergySlope t q ≤
      2 * forcingMass t * Real.sqrt (forcedRadialEnergy t q + 1) / q ^ 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hneg : 0 ≤ 2 * radialCoefficient t * ‖radialW t q‖ ^ 2 / q ^ 3 := by
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (radialCoefficient_pos t).le)
      (sq_nonneg _)) (by positivity)
  have hinner := real_inner_le_norm (radialWFirst t q) (radialWForcing t q)
  calc
    forcedEnergySlope t q ≤ 2 * (‖radialWFirst t q‖ * ‖radialWForcing t q‖) := by
      unfold forcedEnergySlope
      linarith
    _ ≤ 2 * (Real.sqrt (forcedRadialEnergy t q + 1) * (forcingMass t / q ^ 2)) := by
      apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
      exact mul_le_mul (first_norm_le_regularized t hq0) (radialWForcing_norm_le t hq)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem regularizedHeightEnergy_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (regularizedHeightEnergy t)
      (forcedEnergySlope t q / (2 * Real.sqrt (forcedRadialEnergy t q + 1)) - forcingMass t / q ^ 2) q := by
  have hE := forcedRadialEnergy_hasDerivAt t hq
  have hpos : 0 < forcedRadialEnergy t q + 1 := by linarith [forcedRadialEnergy_nonneg t hq]
  have hs := (hE.const_add 1).sqrt hpos.ne'
  have hd := (hasDerivAt_const q (forcingMass t)).div (hasDerivAt_id q) hq.ne'
  convert hs.add hd using 1 <;> unfold regularizedHeightEnergy <;> ring

theorem regularizedHeightEnergy_deriv_nonpos (t : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    deriv (regularizedHeightEnergy t) q ≤ 0 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hs : 0 < Real.sqrt (forcedRadialEnergy t q + 1) :=
    Real.sqrt_pos.2 (by linarith [forcedRadialEnergy_nonneg t hq0])
  rw [(regularizedHeightEnergy_hasDerivAt t hq0).deriv]
  apply sub_nonpos.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (forcedRadialEnergy t q + 1))).2
  calc
    forcedEnergySlope t q ≤ 2 * forcingMass t * Real.sqrt (forcedRadialEnergy t q + 1) / q ^ 2 :=
      forcedEnergySlope_le t hq
    _ = _ := by ring

theorem regularizedHeightEnergy_antitoneOn (t : ℝ) :
    AntitoneOn (regularizedHeightEnergy t) (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (1 : ℝ))
  · intro q hq
    exact (regularizedHeightEnergy_hasDerivAt t (by linarith [hq])).continuousAt.continuousWithinAt
  · intro q hq
    have hh : 1 ≤ q := interior_subset hq
    exact (regularizedHeightEnergy_hasDerivAt t (by linarith)).differentiableAt.differentiableWithinAt
  · intro q hq
    exact regularizedHeightEnergy_deriv_nonpos t (interior_subset hq)

theorem radialW_norm_le_amplitude (t : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ‖radialW t q‖ ≤ heightLargeQAmplitude t := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hnorm : ‖radialW t q‖ ≤ Real.sqrt (forcedRadialEnergy t q + 1) :=
    Real.le_sqrt_of_sq_le ((radialW_norm_sq_le_forcedEnergy t hq0).trans (by linarith))
  have hE := regularizedHeightEnergy_antitoneOn t (show (1 : ℝ) ∈ Ici 1 by simp) hq hq
  have hc : 0 ≤ forcingMass t / q := div_nonneg (forcingMass_nonneg t) hq0.le
  unfold regularizedHeightEnergy at hE
  unfold heightLargeQAmplitude
  norm_num at hE
  linarith

/-- Actual fixed-height order derivative bound from genuine forced energy. -/
theorem heightOrderJ_large_q_bound (t : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ‖heightOrderJ t q‖ ≤ heightLargeQAmplitude t / Real.sqrt q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have h := radialW_norm_le_amplitude t hq
  rw [radialW, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg q)] at h
  apply (le_div_iff₀ (Real.sqrt_pos.2 hq0)).2
  simpa only [mul_comm] using h

end
end ImbalancedChen.Part3.ActualJHeightEnergyBound20261026b
