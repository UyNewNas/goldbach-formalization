import ImbalancedChen.P5U7TerminalPrimeMixedUniform

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Scalar mixed-scale log transport with original n and independent m<=n.
The power lower bound is on m/a, and every logarithmic positivity condition
is derived. No arithmetic mean or slow-log comparison is assumed.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology

/-- Exact log shift and all positive denominator geometry. -/
theorem p5U7MixedScale_log_geometry (n m a alpha beta0 : ℝ)
    (hn : 1 < n) (ha : 0 < a) (halpha : 0 < alpha) (hbeta0 : 0 < beta0)
    (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1) (hx : n^alpha ≤ m/a) :
    0 < m ∧ 0 < Real.log n ∧ 0 < Real.log (m/a) ∧ 0 < Real.log (n/a) ∧
      alpha*Real.log n ≤ Real.log (m/a) ∧
      alpha*Real.log n ≤ Real.log (n/a) ∧
      Real.log (m/a) = Real.log (n/a)+Real.log (m/n) ∧
      0 ≤ Real.log (n/a)-Real.log (m/a) ∧
      Real.log (n/a)-Real.log (m/a) ≤ -Real.log beta0 := by
  have hn0 : 0 < n := zero_lt_one.trans hn
  have hrhopos : 0 < m/n := hbeta0.trans_le hrho0
  have hm0 : 0 < m := (div_pos_iff_of_pos_right hn0).mp hrhopos
  have hmn : m ≤ n := (div_le_one hn0).mp hrho1
  have hxpos : 0 < m/a := div_pos hm0 ha
  have hypos : 0 < n/a := div_pos hn0 ha
  have hln : 0 < Real.log n := Real.log_pos hn
  have hlow := Real.log_le_log (Real.rpow_pos_of_pos hn0 alpha) hx
  rw [Real.log_rpow hn0] at hlow
  have hlogxy := Real.log_le_log hxpos (div_le_div_of_nonneg_right hmn ha.le)
  have hhigh := hlow.trans hlogxy
  have hlx : 0 < Real.log (m/a) := (mul_pos halpha hln).trans_le hlow
  have hly : 0 < Real.log (n/a) := (mul_pos halpha hln).trans_le hhigh
  have hshift : Real.log (m/a) = Real.log (n/a)+Real.log (m/n) := by
    rw [Real.log_div hm0.ne' ha.ne',Real.log_div hn0.ne' ha.ne',Real.log_div hm0.ne' hn0.ne']
    ring
  have hlogrho := Real.log_le_log hbeta0 hrho0
  exact ⟨hm0,hln,hlx,hly,hlow,hhigh,hshift,sub_nonneg.mpr hlogxy,
    by linarith only [hshift,hlogrho]⟩

/-- Both native reciprocal-log kernels are uniformly bounded by 1/alpha. -/
theorem p5U7MixedScale_log_kernel_bounds (n m a alpha beta0 : ℝ)
    (hn : 1 < n) (ha : 0 < a) (halpha : 0 < alpha) (hbeta0 : 0 < beta0)
    (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1) (hx : n^alpha ≤ m/a) :
    0 ≤ Real.log n/Real.log (m/a) ∧ Real.log n/Real.log (m/a) ≤ 1/alpha ∧
      0 ≤ Real.log n/Real.log (n/a) ∧ Real.log n/Real.log (n/a) ≤ 1/alpha := by
  obtain ⟨_hm,hln,hlx,hly,hlow,hhigh,_hs,_h0,_hB⟩ :=
    p5U7MixedScale_log_geometry n m a alpha beta0 hn ha halpha hbeta0 hrho0 hrho1 hx
  have hA : 0 < alpha*Real.log n := mul_pos halpha hln
  have hcancel : Real.log n/(alpha*Real.log n) = 1/alpha := by
    field_simp [halpha.ne',hln.ne']
    <;> ring
  exact ⟨(div_pos hln hlx).le,
    (div_le_div_of_nonneg_left hln.le hA hlow).trans_eq hcancel,
    (div_pos hln hly).le,(div_le_div_of_nonneg_left hln.le hA hhigh).trans_eq hcancel⟩

/-- Actual reciprocal-log transport, with explicit loss O(1/log n).
The same lower exponent alpha pays BOTH original and cutoff denominators. -/
theorem p5U7MixedScale_reciprocal_log_error (n m a alpha beta0 : ℝ)
    (hn : 1 < n) (ha : 0 < a) (halpha : 0 < alpha) (hbeta0 : 0 < beta0)
    (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1) (hx : n^alpha ≤ m/a) :
    |Real.log n/Real.log (m/a)-Real.log n/Real.log (n/a)| ≤
      (-Real.log beta0)/(alpha^2*Real.log n) := by
  obtain ⟨_hm,hln,hlx,hly,hlow,hhigh,_hs,hgap0,hgap⟩ :=
    p5U7MixedScale_log_geometry n m a alpha beta0 hn ha halpha hbeta0 hrho0 hrho1 hx
  have hbeta1 : beta0 ≤ 1 := hrho0.trans hrho1
  have hB : 0 ≤ -Real.log beta0 := neg_nonneg.mpr (Real.log_nonpos hbeta0.le hbeta1)
  have hA : 0 < alpha*Real.log n := mul_pos halpha hln
  have hden : (alpha*Real.log n)^2 ≤ Real.log (m/a)*Real.log (n/a) := by
    simpa only [pow_two] using mul_le_mul hlow hhigh hA.le hlx.le
  have hnum := mul_le_mul_of_nonneg_left hgap hln.le
  have horder := div_le_div_of_nonneg_left hln.le hlx (by linarith only [hgap0])
  have hid : Real.log n/Real.log (m/a)-Real.log n/Real.log (n/a) =
      (Real.log n*(Real.log (n/a)-Real.log (m/a)))/(Real.log (m/a)*Real.log (n/a)) := by
    field_simp [hlx.ne',hly.ne']
    <;> ring
  rw [abs_of_nonneg (sub_nonneg.mpr horder),hid]
  have hh := (div_le_div_of_nonneg_right hnum (mul_pos hlx hly).le).trans
    (div_le_div_of_nonneg_left (mul_nonneg hln.le hB) (sq_pos_of_pos hA) hden)
  have hcancel : (Real.log n*(-Real.log beta0))/(alpha*Real.log n)^2 =
      (-Real.log beta0)/(alpha^2*Real.log n) := by
    field_simp [halpha.ne',hln.ne']
    <;> ring
  exact hh.trans_eq hcancel
end
end ImbalancedChen
