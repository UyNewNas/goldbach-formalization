import ImbalancedChen.P0All32RowOverlapAPI
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/- SOURCEONLY. Uses the actual dense Horner evalList, row, err and omegaHalf
from BuchstabData/assembly. Those sources do not define powerPolyValue or a
Majorant constant. All integrals below use the fixed Lebesgue measure. -/
namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
namespace P0All32BarrierConsumerAPI

open Set MeasureTheory P0All32RowPublicAPI P0All32RowOverlapAPI
noncomputable section

/-- Horner evaluation is continuous, without exposing private derivative APIs. -/
theorem continuous_evalList (p : List ℤ) : Continuous (evalList p) := by
  induction p with
  | nil =>
      change Continuous (fun _ : ℝ => (0 : ℝ))
      exact continuous_const
  | cons x xs ih =>
      change Continuous (fun t : ℝ => (x : ℝ) + t * evalList xs t)
      exact continuous_const.add (continuous_id.mul ih)

theorem continuous_row (c : ℕ) : Continuous (evalList (row c)) := by
  exact continuous_evalList (row c)

theorem continuous_value (c : ℕ) : Continuous (value c) := by
  unfold value
  exact (continuous_row c).comp
    (continuous_const.mul (continuous_id.sub continuous_const))

theorem row_intervalIntegrable (c : ℕ) (a b : ℝ) :
    IntervalIntegrable (evalList (row c)) volume a b := by
  exact (continuous_row c).intervalIntegrable a b

theorem value_intervalIntegrable (c : ℕ) (a b : ℝ) :
    IntervalIntegrable (value c) volume a b := by
  exact (continuous_value c).intervalIntegrable a b

theorem corrected_row_intervalIntegrable (c : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => evalList (row c) t + (err c : ℝ)) volume a b := by
  exact ((continuous_row c).add continuous_const).intervalIntegrable a b

theorem affine_upper_intervalIntegrable (c : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t => (omegaHalf : ℝ) * ((c : ℝ) + t)) volume a b := by
  exact (continuous_const.mul (continuous_const.add continuous_id)).intervalIntegrable a b

/-- Every closed subinterval of a certified row inherits the actual error-aware
pointwise polynomial inequality. The hypotheses describe interval geometry. -/
theorem row_subinterval_upper (k : Fin 32) {a b t : ℝ}
    (ha : rowLeft k ≤ a) (hb : b ≤ rowRight k) (ht : t ∈ Icc a b) :
    evalList (row (cellIndex k)) t + (err (cellIndex k) : ℝ) ≤
      (omegaHalf : ℝ) * ((cellIndex k : ℝ) + t) := by
  exact row_polynomial_upper k ⟨ha.trans ht.1, ht.2.trans hb⟩

/-- Direct Lebesgue interval-integral comparison for one original row. -/
theorem row_subinterval_integral_upper (k : Fin 32) {a b : ℝ}
    (hab : a ≤ b) (ha : rowLeft k ≤ a) (hb : b ≤ rowRight k) :
    (∫ t in a..b, evalList (row (cellIndex k)) t + (err (cellIndex k) : ℝ)) ≤
      ∫ t in a..b, (omegaHalf : ℝ) * ((cellIndex k : ℝ) + t) := by
  exact intervalIntegral.integral_mono_on hab
    (corrected_row_intervalIntegrable (cellIndex k) a b)
    (affine_upper_intervalIntegrable (cellIndex k) a b)
    (fun t ht => row_subinterval_upper k ha hb ht)

/-- The cover selector permits a subinterval to cross row endpoints. -/
theorem covered_subinterval_integral_upper {c : ℕ} {a b : ℝ}
    (hab : a ≤ b) (hcover : ∀ t ∈ Icc a b, CoveredPoint c t) :
    (∫ t in a..b, evalList (row c) t + (err c : ℝ)) ≤
      ∫ t in a..b, (omegaHalf : ℝ) * ((c : ℝ) + t) := by
  exact intervalIntegral.integral_mono_on hab
    (corrected_row_intervalIntegrable c a b)
    (affine_upper_intervalIntegrable c a b)
    (fun t ht => pointwise_polynomial_upper (hcover t ht))

/-- An explicit endpoint majorant for the actual polynomial integral. The
original error is retained and all integrability is supplied internally. -/
theorem covered_subinterval_integral_le_endpoint {c : ℕ} {a b : ℝ}
    (hab : a ≤ b) (hcover : ∀ t ∈ Icc a b, CoveredPoint c t) :
    (∫ t in a..b, evalList (row c) t) ≤
      (b - a) * ((omegaHalf : ℝ) * ((c : ℝ) + b) - (err c : ℝ)) := by
  have hω : (0 : ℝ) ≤ (omegaHalf : ℝ) := by norm_num [omegaHalf]
  have hbound : ∀ t ∈ Icc a b, evalList (row c) t ≤
      (omegaHalf : ℝ) * ((c : ℝ) + b) - (err c : ℝ) := by
    intro t ht
    have hp := pointwise_polynomial_upper (hcover t ht)
    have hm := mul_le_mul_of_nonneg_left
      (add_le_add_left ht.2 (c : ℝ)) hω
    linarith
  have hc : IntervalIntegrable (fun _ : ℝ =>
      (omegaHalf : ℝ) * ((c : ℝ) + b) - (err c : ℝ)) volume a b :=
    continuous_const.intervalIntegrable a b
  have hi := intervalIntegral.integral_mono_on hab
    (row_intervalIntegrable c a b) hc hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi

/-- Explicit cell-10 consumer; no caller-supplied analytic bound. -/
theorem ten_integral_upper {a b : ℝ} (hab : a ≤ b)
    (ha : (15454 / 20359 : ℝ) ≤ a) (hb : b ≤ 1) :
    (∫ t in a..b, evalList (row 10) t) ≤
      (b - a) * ((omegaHalf : ℝ) * (10 + b) - (err 10 : ℝ)) := by
  apply covered_subinterval_integral_le_endpoint hab
  intro t ht
  exact Or.inl ⟨rfl, ha.trans ht.1, ht.2.trans hb⟩

/-- Explicit cell-11 consumer on its original rational coordinate interval. -/
theorem eleven_integral_upper {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ (883 / 10008 : ℝ)) :
    (∫ t in a..b, evalList (row 11) t) ≤
      (b - a) * ((omegaHalf : ℝ) * (11 + b) - (err 11 : ℝ)) := by
  apply covered_subinterval_integral_le_endpoint hab
  intro t ht
  exact Or.inr ⟨rfl, ha.trans ht.1, ht.2.trans hb⟩

end
end P0All32BarrierConsumerAPI
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly

