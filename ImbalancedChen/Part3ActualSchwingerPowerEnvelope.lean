import ImbalancedChen.Part3ActualKUnequalPositiveShear
import ImbalancedChen.Part3ActualLogCoverKZeroGrowth
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Two genuine analytic inputs for inherited-sheet Macdonald endpoint L1.
Every real-power Schwinger density has absolute convergence, proved by
the actual positive dilation t=sqrt(2c)*u to the literal Schlaefli K
density. The polynomial envelope (t^r+t^-r)exp(-t/2-c/t)/t therefore
is integrable. Separately, the actual nonzero I-minus-I bound and the
independently proved zero-order Cauchy bound give one half-log growth
form for each fixed order |Re(nu)|<r<1/2. No endpoint integral or large
Macdonald identity is assumed.
-/

namespace ImbalancedChen.Part3.ActualSchwingerPowerEnvelope20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKPositiveLaplace20261025a
open ActualKUnequalPositiveShear20261026b
open ActualComplexIPoissonCore20261026b ActualLogCoverKModel20261026b
open ActualLogCoverIPoissonGrowth20261026b ActualLogCoverKZeroGrowth20261026b

def schwingerPowerDensity (a c t : ℝ) : ℝ :=
  Real.exp ((a - 1) * Real.log t - t / 2 - c / t)

def schwingerPowerEnvelope (r c t : ℝ) : ℝ :=
  ((t ^ r + t ^ (-r)) / t) * Real.exp (-t / 2 - c / t)

theorem schwingerPowerDensity_scaled (a : ℝ) {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    schwingerPowerDensity a c (Real.sqrt (2 * c) * u) =
      Real.exp ((a - 1) * Real.log (Real.sqrt (2 * c))) *
        ‖laplaceDensity (a : ℂ) (Real.sqrt (2 * c)) u‖ := by
  have hq : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.mpr (by positivity)
  have hq2 : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by positivity)
  have he : -(Real.sqrt (2 * c) * u) / 2 - c / (Real.sqrt (2 * c) * u) =
      -(Real.sqrt (2 * c) / 2) * (u + u⁻¹) := by
    field_simp [hq.ne', hu.ne']
    nlinarith [hq2]
  have hn : ‖laplaceDensity (a : ℂ) (Real.sqrt (2 * c)) u‖ =
      Real.exp ((a - 1) * Real.log u - (Real.sqrt (2 * c) / 2) * (u + u⁻¹)) := by
    rw [laplaceDensity, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hre : ((a : ℂ) - 1).re = a - 1 := by simp
    rw [hre, Real.rpow_def_of_pos hu, ← Real.exp_add]
    congr 1
    ring
  rw [hn, ← Real.exp_add]
  unfold schwingerPowerDensity
  rw [Real.log_mul hq.ne' hu.ne']
  congr 1
  linear_combination he

/-- The dilation is an actual positive-real change of variables. It
transfers already proved literal Schlaefli L1 for arbitrary real order. -/
theorem schwingerPowerDensity_integrable (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (schwingerPowerDensity a c) positiveMeasure := by
  have hq : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.mpr (by positivity)
  have hcomp : Integrable (fun u => schwingerPowerDensity a c (Real.sqrt (2 * c) * u))
      positiveMeasure := by
    apply ((laplaceDensity_integrable (a : ℂ) hq).norm.const_mul
      (Real.exp ((a - 1) * Real.log (Real.sqrt (2 * c))))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (schwingerPowerDensity_scaled a hc hu).symm
  have h := (integrableOn_Ioi_comp_mul_left_iff (schwingerPowerDensity a c) 0 hq).mp hcomp
  simpa only [mul_zero] using h

theorem schwingerPowerEnvelope_eq_sum (r c : ℝ) {t : ℝ} (ht : 0 < t) :
    schwingerPowerEnvelope r c t = schwingerPowerDensity r c t + schwingerPowerDensity (-r) c t := by
  have hi : t⁻¹ = Real.exp (-Real.log t) := by rw [Real.exp_neg, Real.exp_log ht]
  have hp : (r - 1) * Real.log t - t / 2 - c / t =
      Real.log t * r + (-Real.log t) + (-t / 2 - c / t) := by ring
  have hm : (-r - 1) * Real.log t - t / 2 - c / t =
      Real.log t * (-r) + (-Real.log t) + (-t / 2 - c / t) := by ring
  unfold schwingerPowerEnvelope schwingerPowerDensity
  rw [hp, hm, Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht, div_eq_mul_inv, hi]
  simp only [Real.exp_add]
  ring

theorem schwingerPowerEnvelope_integrable (r : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (schwingerPowerEnvelope r c) positiveMeasure := by
  apply ((schwingerPowerDensity_integrable r hc).add
    (schwingerPowerDensity_integrable (-r) hc)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (schwingerPowerEnvelope_eq_sum r c ht).symm

theorem exp_abs_log_le_powers (r : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.exp (r * |Real.log t|) ≤ t ^ r + t ^ (-r) := by
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht]
  by_cases hl : 0 ≤ Real.log t
  · calc
      _ = Real.exp (Real.log t * r) := by rw [abs_of_nonneg hl]; congr 1; ring
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
  · have hl' : Real.log t ≤ 0 := le_of_not_ge hl
    calc
      _ = Real.exp (Real.log t * (-r)) := by rw [abs_of_nonpos hl']; congr 1; ring
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le

def iHalfLogGrowthConstant (nu : ℂ) (T : ℝ) : ℝ :=
  (complexIPoissonNormMass nu / ‖poissonGammaNormalization nu‖) * Real.exp (|nu.im| * T)

theorem iHalfLogGrowthConstant_nonneg (nu : ℂ) (T : ℝ) : 0 ≤ iHalfLogGrowthConstant nu T := by
  unfold iHalfLogGrowthConstant
  exact mul_nonneg (div_nonneg (complexIPoissonNormMass_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le

theorem logCoverI_norm_le_half_log {nu L : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re)
    {r T : ℝ} (hre : |nu.re| ≤ r) (hphase : |L.im| ≤ T) :
    ‖logCoverI nu L‖ ≤ iHalfLogGrowthConstant nu T *
      Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| := by
  have hr : nu.re * L.re ≤ r * |L.re| := by
    calc
      _ ≤ |nu.re * L.re| := le_abs_self _
      _ = |nu.re| * |L.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  have hi : -nu.im * L.im ≤ |nu.im| * T := by
    calc
      _ ≤ |nu.im * L.im| := by simpa only [neg_mul] using neg_le_abs (nu.im * L.im)
      _ = |nu.im| * |L.im| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hphase (abs_nonneg _)
  have he : nu.re * L.re - nu.im * L.im + |(coverPhysicalArgument L).re| ≤
      |nu.im| * T + r * |L.re| + |(coverPhysicalArgument L).re| := by linarith
  calc
    _ ≤ (complexIPoissonNormMass nu / ‖poissonGammaNormalization nu‖) *
        Real.exp (nu.re * L.re - nu.im * L.im + |(coverPhysicalArgument L).re|) :=
      logCoverI_norm_le_exact hnu L
    _ ≤ (complexIPoissonNormMass nu / ‖poissonGammaNormalization nu‖) *
        Real.exp (|nu.im| * T + r * |L.re| + |(coverPhysicalArgument L).re|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (div_nonneg (complexIPoissonNormMass_nonneg _) (norm_nonneg _))
    _ = _ := by unfold iHalfLogGrowthConstant; simp only [Real.exp_add]; ring

/-- One actual half-log growth form, including zero through its genuine
independent Cauchy derivative estimate, for each fixed small-strip order. -/
theorem exists_logCoverK_half_log_growth {nu : ℂ} {r T : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℂ, |L.im| ≤ T →
      ‖logCoverK nu L‖ ≤ C * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| := by
  by_cases hn : nu = 0
  · subst nu
    simpa only [logCoverK, if_pos rfl] using exists_logCoverKZero_half_log_growth hr hrhalf hT
  have hL : -(1 / 2 : ℝ) < nu.re := by have h := (abs_lt.mp horder).1; linarith
  have hM : -(1 / 2 : ℝ) < (-nu).re := by
    rw [Complex.neg_re]
    have h := (abs_lt.mp horder).2
    linarith
  let A : ℝ := ‖(Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu))‖ *
    (iHalfLogGrowthConstant nu T + iHalfLogGrowthConstant (-nu) T)
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) (add_nonneg
    (iHalfLogGrowthConstant_nonneg _ _) (iHalfLogGrowthConstant_nonneg _ _))
  refine ⟨A + 1, by linarith, ?_⟩
  intro L hphase
  have hp := logCoverI_norm_le_half_log hL horder.le hphase
  have hm := logCoverI_norm_le_half_log hM
    (by simpa only [Complex.neg_re, abs_neg] using horder.le) hphase
  have hs := (norm_sub_le (logCoverI (-nu) L) (logCoverI nu L)).trans (add_le_add hm hp)
  calc
    _ = ‖(Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu))‖ *
        ‖logCoverI (-nu) L - logCoverI nu L‖ := by
      rw [logCoverK, if_neg hn, logCoverKNonintegral, norm_mul]
    _ ≤ ‖(Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu))‖ *
        (iHalfLogGrowthConstant (-nu) T * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| +
          iHalfLogGrowthConstant nu T * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re|) :=
      mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = A * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| := by dsimp [A]; ring
    _ ≤ (A + 1) * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + 1) (Real.exp_pos _).le) (Real.exp_pos _).le

end
end ImbalancedChen.Part3.ActualSchwingerPowerEnvelope20261026b
