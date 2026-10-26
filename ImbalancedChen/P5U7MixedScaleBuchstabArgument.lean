import ImbalancedChen.P5U7OriginalBuchstabLipschitz
import ImbalancedChen.P5U7MixedScaleNativeRate

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Required scalar Buchstab argument transport on the ACTUAL native range
[1,132/59]. The exact source lower exponent d is a positive input through
z>=n^d; no exponent is inferred from the Buchstab argument upper bound.
No global Lipschitz statement below one is used.
-/
namespace ImbalancedChen
noncomputable section
open LiLiuPrereqBuchstab

/-- Exact source log geometry and actual argument shift, with all positive
log denominators derived from n>1,z>1 and the literal z>=n^d wall. -/
theorem p5U7MixedScale_buchstab_log_geometry (n m a z d beta0 : ℝ)
    (hn : 1 < n) (ha : 0 < a) (hz : 1 < z) (hd : 0 < d) (hzpow : n^d ≤ z)
    (hbeta0 : 0 < beta0) (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1) :
    0 < m ∧ 0 < Real.log n ∧ 0 < Real.log z ∧ d*Real.log n ≤ Real.log z ∧
      0 ≤ Real.log n/Real.log z ∧ Real.log n/Real.log z ≤ 1/d ∧
      Real.log (m/a) = Real.log (n/a)+Real.log (m/n) ∧
      0 ≤ (Real.log (n/a)/Real.log z)-(Real.log (m/a)/Real.log z) ∧
      (Real.log (n/a)/Real.log z)-(Real.log (m/a)/Real.log z) ≤ (-Real.log beta0)/Real.log z := by
  have hn0 : 0 < n := zero_lt_one.trans hn
  have hrhopos : 0 < m/n := hbeta0.trans_le hrho0
  have hm0 : 0 < m := (div_pos_iff_of_pos_right hn0).mp hrhopos
  have hmn : m ≤ n := (div_le_one hn0).mp hrho1
  have hln : 0 < Real.log n := Real.log_pos hn
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hlow := Real.log_le_log (Real.rpow_pos_of_pos hn0 d) hzpow
  rw [Real.log_rpow hn0] at hlow
  have hshift : Real.log (m/a) = Real.log (n/a)+Real.log (m/n) := by
    rw [Real.log_div hm0.ne' ha.ne',Real.log_div hn0.ne' ha.ne',Real.log_div hm0.ne' hn0.ne']
    ring
  have hlogrho := Real.log_le_log hbeta0 hrho0
  have hlogdiff : Real.log (n/a)-Real.log (m/a) ≤ -Real.log beta0 := by
    linarith only [hshift,hlogrho]
  have hxy := Real.log_le_log (div_pos hm0 ha) (div_le_div_of_nonneg_right hmn ha.le)
  have hargument := div_le_div_of_nonneg_right hlogdiff hlz.le
  have hid : (Real.log (n/a)/Real.log z)-(Real.log (m/a)/Real.log z) =
      (Real.log (n/a)-Real.log (m/a))/Real.log z := (sub_div _ _ _).symm
  have horder := div_le_div_of_nonneg_right hxy hlz.le
  have hratio := div_le_div_of_nonneg_left hln.le (mul_pos hd hln) hlow
  have hcancel : Real.log n/(d*Real.log n) = 1/d := by
    field_simp [hd.ne',hln.ne']
    <;> ring
  exact ⟨hm0,hln,hlz,hlow,(div_pos hln hlz).le,hratio.trans_eq hcancel,
    hshift,sub_nonneg.mpr horder,by simpa only [hid] using hargument⟩

/-- Actual native omega size and scaled Lipschitz error. The full range
hypotheses include the seam s=2 and prohibit crossing below one. -/
theorem p5U7MixedScale_buchstab_scalar_bounds (n m a z d beta0 : ℝ)
    (hn : 1 < n) (ha : 0 < a) (hz : 1 < z) (hd : 0 < d) (hzpow : n^d ≤ z)
    (hbeta0 : 0 < beta0) (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1)
    (hsM : 1 ≤ Real.log (m/a)/Real.log z)
    (horder : Real.log (m/a)/Real.log z ≤ Real.log (n/a)/Real.log z)
    (hsN : Real.log (n/a)/Real.log z ≤ (132/59 : ℝ)) :
    0 ≤ buchstab (Real.log (n/a)/Real.log z) ∧
      buchstab (Real.log (n/a)/Real.log z) ≤ 1 ∧
      |(Real.log n/Real.log z)*buchstab (Real.log (n/a)/Real.log z)| ≤ 1/d ∧
      (Real.log n/Real.log z)*
        |buchstab (Real.log (m/a)/Real.log z)-buchstab (Real.log (n/a)/Real.log z)| ≤
          (-Real.log beta0)/(d^2*Real.log n) := by
  obtain ⟨_hm,hln,hlz,hlow,hL0,hLbound,_hs,hgap0,hgap⟩ :=
    p5U7MixedScale_buchstab_log_geometry n m a z d beta0 hn ha hz hd hzpow hbeta0 hrho0 hrho1
  have hN1 : 1 ≤ Real.log (n/a)/Real.log z := hsM.trans horder
  have hMmax : Real.log (m/a)/Real.log z ≤ (132/59 : ℝ) := horder.trans hsN
  have hW0 : 0 ≤ buchstab (Real.log (n/a)/Real.log z) :=
    (by norm_num : (0 : ℝ) ≤ 1/2).trans (one_half_le_buchstab hN1)
  have hW1 : buchstab (Real.log (n/a)/Real.log z) ≤ 1 := buchstab_le_one hN1
  have hsize : |(Real.log n/Real.log z)*buchstab (Real.log (n/a)/Real.log z)| ≤ 1/d := by
    rw [abs_of_nonneg (mul_nonneg hL0 hW0)]
    exact (mul_le_mul hLbound hW1 hW0 (one_div_nonneg.mpr hd.le)).trans_eq (mul_one _)
  have hLip := p5U7_buchstab_abs_sub_le ⟨hsM,hMmax⟩ ⟨hN1,hsN⟩
  rw [abs_of_nonpos (sub_nonpos.mpr horder)] at hLip
  have hArg : |buchstab (Real.log (m/a)/Real.log z)-buchstab (Real.log (n/a)/Real.log z)| ≤
      (-Real.log beta0)/Real.log z := by
    have hid : -((Real.log (m/a)/Real.log z)-(Real.log (n/a)/Real.log z)) =
        (Real.log (n/a)/Real.log z)-(Real.log (m/a)/Real.log z) := by ring
    rw [hid] at hLip
    exact hLip.trans hgap
  have hB : 0 ≤ -Real.log beta0 :=
    neg_nonneg.mpr (Real.log_nonpos hbeta0.le (hrho0.trans hrho1))
  have hArgBase := hArg.trans (div_le_div_of_nonneg_left hB (mul_pos hd hln) hlow)
  have hscaled := mul_le_mul hLbound hArgBase (abs_nonneg _) (one_div_nonneg.mpr hd.le)
  have hcancel : (1/d)*((-Real.log beta0)/(d*Real.log n)) =
      (-Real.log beta0)/(d^2*Real.log n) := by
    field_simp [hd.ne',hln.ne']
    <;> ring
  exact ⟨hW0,hW1,hsize,hscaled.trans_eq hcancel⟩
end
end ImbalancedChen
