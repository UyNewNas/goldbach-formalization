import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24. No acceptance credit.

All integrals below use the literal positive-height Lebesgue coordinate and
the hyperbolic radial density `dy/y²` on a cusp tail `y>Y`, with `Y>0`.
The earlier Part3CuspCylinderMeasure source identifies this with the
positive-height factor of the period-one cusp cylinder measure. The
pointwise density statements expose the exact norm-square integrands.

The oscillatory generalized modes `y^(1/2±it)` and both threshold modes
are not L² on any cusp tail. For positive real ν, the growing
`y^(1/2+ν)` branch is not L²; the decaying `y^(1/2-ν)` branch is L² with
an explicit tail norm. These statements do not establish the existence of
an automorphic eigenfunction, its constant coefficient, or a spectrum.
-/

namespace ImbalancedChen.Part3.CuspConstantModeTailL2SourceOnly

noncomputable section

open Set MeasureTheory

/-- The actual radial hyperbolic norm-square density in real height. -/
def hyperbolicEnergyDensity (F : ℝ → ℂ) (y : ℝ) : ℝ :=
  ‖F y‖ ^ 2 / y ^ 2

/-- This predicate is the concrete `dy/y²` L² criterion on `(Y,∞)`. -/
def TailL2 (F : ℝ → ℂ) (Y : ℝ) : Prop :=
  IntegrableOn (hyperbolicEnergyDensity F) (Ioi Y)

/-- Literal positive-real complex power, with `ε=±1` giving
`y^(1/2±it)`. The norm calculation does not depend on the sign. -/
def continuousPower (ε t y : ℝ) : ℂ :=
  (y : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * ((ε * t : ℝ) : ℂ))

theorem continuousPower_norm (ε t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖continuousPower ε t y‖ = y ^ (1 / 2 : ℝ) := by
  simp [continuousPower, Complex.abs_cpow_eq_rpow_re_of_pos hy]

theorem continuousPower_energy_density (ε t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    hyperbolicEnergyDensity (continuousPower ε t) y = y ^ (-1 : ℝ) := by
  rw [hyperbolicEnergyDensity, continuousPower_norm ε t hy]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    ← Real.rpow_natCast, ← Real.rpow_sub hy]
  congr 1
  ring

/-- Neither sign of the continuous parameter yields a square-integrable
constant mode on a positive cusp tail. -/
theorem continuousPower_not_tailL2 (ε t : ℝ)
    {Y : ℝ} (hY : 0 < Y) : ¬TailL2 (continuousPower ε t) Y := by
  intro h
  have hpow : IntegrableOn (fun y : ℝ => y ^ (-1 : ℝ)) (Ioi Y) :=
    (integrableOn_congr_fun
      (fun y hy => continuousPower_energy_density ε t (hY.trans hy))
      measurableSet_Ioi).mp h
  exact (not_integrableOn_Ioi_rpow_of_neg_one_le
    (a := Y) (s := (-1 : ℝ)) (le_refl _)) hpow

theorem plusContinuousPower_not_tailL2 (t : ℝ)
    {Y : ℝ} (hY : 0 < Y) : ¬TailL2 (continuousPower 1 t) Y :=
  continuousPower_not_tailL2 1 t hY

theorem minusContinuousPower_not_tailL2 (t : ℝ)
    {Y : ℝ} (hY : 0 < Y) : ¬TailL2 (continuousPower (-1) t) Y :=
  continuousPower_not_tailL2 (-1) t hY

/-- Real indicial power `y^(1/2+s)`, embedded in the complex height
space. `s=ν` grows relative to threshold; `s=-ν` decays. -/
def realPowerMode (s y : ℝ) : ℂ :=
  (y ^ ((1 / 2 : ℝ) + s) : ℝ)

theorem realPowerMode_energy_density (s : ℝ)
    {y : ℝ} (hy : 0 < y) :
    hyperbolicEnergyDensity (realPowerMode s) y =
      y ^ (2 * s - 1) := by
  have hp : 0 ≤ y ^ ((1 / 2 : ℝ) + s) :=
    (Real.rpow_pos_of_pos hy _).le
  simp only [hyperbolicEnergyDensity, realPowerMode,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    ← Real.rpow_natCast, ← Real.rpow_sub hy]
  congr 1
  ring

/-- Exact real-power L² criterion at infinity: the indicial shift must be
strictly negative. -/
theorem realPowerMode_tailL2_iff (s : ℝ) {Y : ℝ} (hY : 0 < Y) :
    TailL2 (realPowerMode s) Y ↔ s < 0 := by
  have hcongr : TailL2 (realPowerMode s) Y ↔
      IntegrableOn (fun y : ℝ => y ^ (2 * s - 1)) (Ioi Y) := by
    exact integrableOn_congr_fun
      (fun y hy => realPowerMode_energy_density s (hY.trans hy))
      measurableSet_Ioi
  rw [hcongr, integrableOn_Ioi_rpow_iff hY]
  constructor <;> intro h <;> linarith

theorem growingPower_not_tailL2 {ν Y : ℝ}
    (hν : 0 < ν) (hY : 0 < Y) :
    ¬TailL2 (realPowerMode ν) Y := by
  rw [realPowerMode_tailL2_iff ν hY]
  exact not_lt_of_ge hν.le

theorem decayingPower_tailL2 {ν Y : ℝ}
    (hν : 0 < ν) (hY : 0 < Y) :
    TailL2 (realPowerMode (-ν)) Y := by
  rw [realPowerMode_tailL2_iff (-ν) hY]
  linarith

/-- Exact decaying-branch tail energy:
`∫_Y^∞ |y^(1/2-ν)|² dy/y² = Y^(-2ν)/(2ν)`. -/
theorem decayingPower_tail_energy {ν Y : ℝ}
    (hν : 0 < ν) (hY : 0 < Y) :
    (∫ y in Ioi Y, hyperbolicEnergyDensity (realPowerMode (-ν)) y) =
      Y ^ (-2 * ν) / (2 * ν) := by
  have hexp : -2 * ν - 1 < (-1 : ℝ) := by linarith
  calc
    (∫ y in Ioi Y, hyperbolicEnergyDensity (realPowerMode (-ν)) y) =
        ∫ y in Ioi Y, y ^ (-2 * ν - 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      simpa [mul_neg] using
        (realPowerMode_energy_density (-ν) (hY.trans hy))
    _ = -(Y ^ ((-2 * ν - 1) + 1)) / ((-2 * ν - 1) + 1) :=
      integral_Ioi_rpow_of_lt hexp hY
    _ = Y ^ (-2 * ν) / (2 * ν) := by
      have hexpeq : (-2 * ν - 1) + 1 = -2 * ν := by ring
      rw [hexpeq]
      have hne : (2 * ν) ≠ 0 := by positivity
      field_simp [hne]
      ring

/-- The logarithmic second solution at the repeated threshold root. -/
def thresholdLogMode (y : ℝ) : ℂ :=
  (Real.sqrt y * Real.log y : ℝ)

theorem thresholdLogMode_energy_density {y : ℝ} (hy : 0 < y) :
    hyperbolicEnergyDensity thresholdLogMode y =
      (Real.log y) ^ 2 * y⁻¹ := by
  simp only [hyperbolicEnergyDensity, thresholdLogMode,
    Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_pow, Real.sq_sqrt hy.le]
  field_simp [hy.ne']
  ring

/-- The threshold logarithmic companion has larger energy than `1/y`
once `y>e`; hence it is not L² on any positive cusp tail. -/
theorem thresholdLogMode_not_tailL2 {Y : ℝ} (hY : 0 < Y) :
    ¬TailL2 thresholdLogMode Y := by
  intro h
  let A : ℝ := max Y (Real.exp 1)
  have hYA : Y ≤ A := le_max_left _ _
  have heA : Real.exp 1 ≤ A := le_max_right _ _
  have hA : 0 < A := hY.trans_le hYA
  have hrestricted : IntegrableOn (hyperbolicEnergyDensity thresholdLogMode)
      (Ioi A) := h.mono (Ioi_subset_Ioi hYA) le_rfl
  have hlog : IntegrableOn (fun y : ℝ => y⁻¹) (Ioi A) := by
    apply hrestricted.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hA.trans hy
    have he : Real.exp 1 ≤ y := heA.trans hy.le
    have hlog1 : 1 ≤ Real.log y := by
      simpa only [Real.log_exp] using
        (Real.log_le_log (Real.exp_pos 1) he)
    rw [thresholdLogMode_energy_density hy0]
    have hsq : 1 ≤ (Real.log y) ^ 2 := by nlinarith
    have hinv : 0 ≤ y⁻¹ := inv_nonneg.mpr hy0.le
    have hE : 0 ≤ (Real.log y) ^ 2 * y⁻¹ :=
      mul_nonneg (sq_nonneg _) hinv
    simp only [Real.norm_eq_abs, abs_of_nonneg hinv, abs_of_nonneg hE]
    have hbound := mul_le_mul_of_nonneg_right hsq hinv
    nlinarith
  exact not_integrableOn_Ioi_inv hlog

end
end ImbalancedChen.Part3.CuspConstantModeTailL2SourceOnly
