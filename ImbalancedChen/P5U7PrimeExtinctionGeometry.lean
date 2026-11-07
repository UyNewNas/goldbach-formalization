import ImbalancedChen.P5U7PrimeSupportThreshold

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Explicit uniform amplitude and support-width estimates for actual prime
cutoff extinction. Both bounds are derived from the literal logarithmic
row and native outer cap, not from an assumed rate or derivative bound.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeExtinctionAmplitude : ℝ := 1/((59/250 : ℝ)*(2/3 : ℝ))

/-- Actual positive-part log-row amplitude is O(H-eta), uniformly over
the original CLOSED outer interval, with H=73/59. -/
theorem p5U7PrimeExtinction_row_amplitude {eta t : ℝ}
    (heta : 0 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ))
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 ≤ max 0 (p5U7PrimeCutoffLogRow eta t) ∧
      max 0 (p5U7PrimeCutoffLogRow eta t) ≤
        p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have he1 : 0 < 1+eta := by linarith
  have hdelta : 0 ≤ (73/59 : ℝ)-eta := sub_nonneg.mpr hetaH
  have hg := p5U7PrimeCutoffLog_geometry heta ht
  have hq : (59/250 : ℝ) ≤ t*(1+eta) := by
    nlinarith [mul_nonneg ht0.le heta,ht.1]
  have hnum : 1-t*(3+eta) ≤ (59/250 : ℝ)*((73/59 : ℝ)-eta) := by
    have hm := mul_le_mul_of_nonneg_right ht.1 (show 0 ≤ 3+eta by linarith)
    nlinarith only [hm]
  have hscale := mul_le_mul_of_nonneg_right hq hdelta
  have harg : (1-2*t)/(t*(1+eta))-1 ≤ (73/59 : ℝ)-eta := by
    have hh : (1-2*t)/(t*(1+eta)) ≤ 1+((73/59 : ℝ)-eta) :=
      (div_le_iff₀ (mul_pos ht0 he1)).mpr (by nlinarith only [hnum,hscale])
    linarith only [hh]
  have hlog : Real.log ((1-2*t)/(t*(1+eta))) ≤ (73/59 : ℝ)-eta :=
    (Real.log_le_sub_one_of_pos hg.1).trans harg
  have hden : (59/250 : ℝ)*(2/3 : ℝ) ≤ t*(1-t) :=
    mul_le_mul ht.1 (by linarith [ht.2]) (by norm_num) ht0.le
  have hrow : p5U7PrimeCutoffLogRow eta t ≤
      p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta) := by
    have hh := (div_le_div_of_nonneg_right hlog hg.2.le).trans
      (div_le_div_of_nonneg_left hdelta (by norm_num) hden)
    convert hh using 1 <;> dsimp only [p5U7PrimeCutoffLogRow,p5U7PrimeExtinctionAmplitude] <;> ring
  have hupper : 0 ≤ p5U7PrimeExtinctionAmplitude*((73/59 : ℝ)-eta) := by
    unfold p5U7PrimeExtinctionAmplitude
    positivity
  exact ⟨le_max_left _ _,max_le hupper hrow⟩

/-- Actual outer support width is O(H-eta), including the zero-width
endpoint eta=H. The same formula is valid throughout the full native range. -/
theorem p5U7PrimeExtinction_support_width {eta : ℝ}
    (heta : 0 ≤ eta) (hetaH : eta ≤ (73/59 : ℝ)) :
    (59/250 : ℝ) ≤ 1/(3+eta) ∧ 1/(3+eta) ≤ (1/3 : ℝ) ∧
      1/(3+eta)-(59/250 : ℝ) ≤ ((59/250 : ℝ)/3)*((73/59 : ℝ)-eta) := by
  have he3 : 0 < 3+eta := by linarith
  have hdelta : 0 ≤ (73/59 : ℝ)-eta := sub_nonneg.mpr hetaH
  have hlo : (59/250 : ℝ) ≤ 1/(3+eta) :=
    (le_div_iff₀ he3).mpr (by nlinarith only [hetaH])
  have hhi : 1/(3+eta) ≤ (1/3 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 3)
      (by linarith only [heta])
  have hid : 1/(3+eta)-(59/250 : ℝ) =
      ((59/250 : ℝ)*((73/59 : ℝ)-eta))/(3+eta) := by
    field_simp [he3.ne']
    <;> ring
  refine ⟨hlo,hhi,?_⟩
  rw [hid]
  have hh := div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 59/250) hdelta)
    (by norm_num : (0 : ℝ) < 3) (show 3 ≤ 3+eta by linarith only [heta])
  convert hh using 1 <;> ring
end
end ImbalancedChen
