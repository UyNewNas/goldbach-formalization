import ImbalancedChen.P5U7OriginalScalarCorrection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An unconditional two-sided enclosure for the ACTUAL original U7 scalar
correction. The logarithms are bounded from their real analytic inequalities,
and the resulting quadratic shape is integrated exactly. There is no check,
endpoint, quadrature error, pointwise majorant, or integral bound assumption.
These deliberately modest endpoints do not imply the saved sharp U7 bounds.
-/

namespace ImbalancedChen.P5U7OriginalScalarCorrection

noncomputable section
open Set MeasureTheory

def lowerMultiplier : ℝ := 1 / ((132 / 59 : ℝ) * (73 / 59) * (191 / 59))

def correctionLowerEndpoint : ℝ :=
  (14 / 59 : ℝ) ^ 3 / (6 * (132 / 59) * (73 / 59) * (191 / 59))

def correctionUpperEndpoint : ℝ := (14 / 59 : ℝ) ^ 3 / 36

/-- Both ends of the real original correction vanish. Between them its
two logarithms have a directed quadratic enclosure, with literal d=59/250. -/
theorem scalarCorrectionKernel_bounds {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (132 / 59)) :
    lowerMultiplier * (s - 2) * (132 / 59 - s) ≤ scalarCorrectionKernel s ∧
      scalarCorrectionKernel s ≤ (1 / 6 : ℝ) * (s - 2) * (132 / 59 - s) := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hm0 : 0 < s - 1 := by linarith [hs.1]
  have hp0 : 0 < s + 1 := by linarith [hs.1]
  have hleft : 0 ≤ s - 2 := sub_nonneg.mpr hs.1
  have hright : 0 ≤ (132 / 59 : ℝ) - s := sub_nonneg.mpr hs.2
  have hratio0 : 0 < (191 / 59 : ℝ) / (s + 1) := div_pos (by norm_num) hp0
  have hratio1 : 1 ≤ (191 / 59 : ℝ) / (s + 1) := by
    apply (le_div_iff₀ hp0).mpr
    linarith only [hs.2]
  have hA0 : 0 ≤ Real.log (s - 1) / s :=
    div_nonneg (Real.log_nonneg (by linarith [hs.1])) hs0.le
  have hB0 : 0 ≤ Real.log ((191 / 59 : ℝ) / (s + 1)) := Real.log_nonneg hratio1
  have hAhi0 : Real.log (s - 1) ≤ s - 2 := by
    have h := Real.log_le_sub_one_of_pos hm0
    linarith only [h]
  have hAhi : Real.log (s - 1) / s ≤ (s - 2) / 2 :=
    (div_le_div_of_nonneg_right hAhi0 hs0.le).trans
      (div_le_div_of_nonneg_left hleft (by norm_num) hs.1)
  have hBhi0 : Real.log ((191 / 59 : ℝ) / (s + 1)) ≤
      (132 / 59 - s) / (s + 1) := by
    have h := Real.log_le_sub_one_of_pos hratio0
    have heq : (191 / 59 : ℝ) / (s + 1) - 1 = (132 / 59 - s) / (s + 1) := by
      field_simp [hp0.ne']
      <;> ring
    exact h.trans_eq heq
  have hBhi : Real.log ((191 / 59 : ℝ) / (s + 1)) ≤ (132 / 59 - s) / 3 :=
    hBhi0.trans (div_le_div_of_nonneg_left hright (by norm_num) (by linarith [hs.1]))
  have hAlo0 : (s - 2) / (s - 1) ≤ Real.log (s - 1) := by
    have h := Real.one_sub_inv_le_log_of_pos hm0
    have heq : 1 - (s - 1)⁻¹ = (s - 2) / (s - 1) := by
      field_simp [hm0.ne']
      <;> ring
    rwa [heq] at h
  have hprod : s * (s - 1) ≤ (132 / 59 : ℝ) * (73 / 59) := by
    apply mul_le_mul hs.2 (by linarith [hs.2]) hm0.le
    norm_num
  have hAlo : (s - 2) / ((132 / 59 : ℝ) * (73 / 59)) ≤ Real.log (s - 1) / s := by
    calc
      _ ≤ (s - 2) / (s * (s - 1)) :=
        div_le_div_of_nonneg_left hleft (mul_pos hs0 hm0) hprod
      _ = ((s - 2) / (s - 1)) / s := by
        field_simp [hs0.ne', hm0.ne']
        <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right hAlo0 hs0.le
  have hBlo : (132 / 59 - s) / (191 / 59 : ℝ) ≤
      Real.log ((191 / 59 : ℝ) / (s + 1)) := by
    have h := Real.one_sub_inv_le_log_of_pos hratio0
    have heq : 1 - ((191 / 59 : ℝ) / (s + 1))⁻¹ =
        (132 / 59 - s) / (191 / 59 : ℝ) := by
      field_simp [hp0.ne']
      <;> ring
    rwa [heq] at h
  constructor
  · have h := mul_le_mul hAlo hBlo (div_nonneg hright (by norm_num)) hA0
    calc
      _ = ((s - 2) / ((132 / 59 : ℝ) * (73 / 59))) *
          ((132 / 59 - s) / (191 / 59 : ℝ)) := by unfold lowerMultiplier; ring
      _ ≤ _ := h
  · have h := mul_le_mul hAhi hBhi hB0 (div_nonneg hleft (by norm_num))
    calc
      _ ≤ ((s - 2) / 2) * ((132 / 59 - s) / 3) := h
      _ = _ := by ring

theorem scalarCorrectionKernel_intervalIntegrable :
    IntervalIntegrable scalarCorrectionKernel volume (2 : ℝ) (132 / 59) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact regularCorrection_continuous.continuousOn.congr
    (fun s hs => (regularCorrection_eq hs.1).symm)

private theorem quadratic_shape_integral (c : ℝ) :
    (∫ s in (2 : ℝ)..(132 / 59 : ℝ), c * (s - 2) * (132 / 59 - s)) =
      c * (14 / 59 : ℝ) ^ 3 / 6 := by
  let P : ℝ → ℝ := fun s =>
    c * (-s ^ 3 / 3 + (132 / 59 + 2) * s ^ 2 / 2 - 2 * (132 / 59) * s)
  have hd : ∀ s ∈ uIcc (2 : ℝ) (132 / 59),
      HasDerivAt P (c * (s - 2) * (132 / 59 - s)) s := by
    intro s hs
    have h1 := (((hasDerivAt_id s).pow 3).neg).div_const 3
    have h2 := (((hasDerivAt_id s).pow 2).const_mul (132 / 59 + 2 : ℝ)).div_const 2
    have h3 := (hasDerivAt_id s).const_mul (2 * (132 / 59 : ℝ))
    apply (((h1.add h2).sub h3).const_mul c).congr_deriv
    ring
  have hi : IntervalIntegrable (fun s : ℝ => c * (s - 2) * (132 / 59 - s))
      volume (2 : ℝ) (132 / 59) :=
    ((continuous_const.mul (continuous_id.sub continuous_const)).mul
      (continuous_const.sub continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  dsimp only [P]
  ring

/-- A genuine numerical enclosure of the missing original correction,
from analytic log inequalities and an exact polynomial primitive. It is
strictly weaker than the archived 1024-cell/64-panel sharp endpoints. -/
theorem scalarCorrection_bounds :
    correctionLowerEndpoint ≤ scalarCorrection ∧ scalarCorrection ≤ correctionUpperEndpoint := by
  have hpoly (c : ℝ) : IntervalIntegrable (fun s : ℝ => c * (s - 2) * (132 / 59 - s))
      volume (2 : ℝ) (132 / 59) :=
    ((continuous_const.mul (continuous_id.sub continuous_const)).mul
      (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hlo := intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 132 / 59)
    (hpoly lowerMultiplier) scalarCorrectionKernel_intervalIntegrable
    (fun s hs => (scalarCorrectionKernel_bounds hs).1)
  have hhi := intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 132 / 59)
    scalarCorrectionKernel_intervalIntegrable (hpoly (1 / 6))
    (fun s hs => (scalarCorrectionKernel_bounds hs).2)
  rw [quadratic_shape_integral] at hlo hhi
  constructor
  · change correctionLowerEndpoint ≤ ∫ s in (2 : ℝ)..(132 / 59), scalarCorrectionKernel s
    convert hlo using 1 <;> norm_num [correctionLowerEndpoint, lowerMultiplier]
  · change (∫ s in (2 : ℝ)..(132 / 59), scalarCorrectionKernel s) ≤ correctionUpperEndpoint
    convert hhi using 1 <;> norm_num [correctionUpperEndpoint]

/-- The actual original J7 is enclosed around its genuine rank-three
prime integral; the semiprime correction is neither omitted nor doubled. -/
theorem originalOmegaIntegral_bounds_from_prime_component :
    p5U7ComponentPrimeIntegral + correctionLowerEndpoint ≤ p5U7OriginalOmegaIntegral 1 ∧
      p5U7OriginalOmegaIntegral 1 ≤ p5U7ComponentPrimeIntegral + correctionUpperEndpoint := by
  rw [p5U7Component_integral_split, semiprimeIntegral_eq_scalarCorrection]
  exact ⟨add_le_add_left scalarCorrection_bounds.1 _,
    add_le_add_left scalarCorrection_bounds.2 _⟩

end
end ImbalancedChen.P5U7OriginalScalarCorrection
