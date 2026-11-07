import ImbalancedChen.P2HistoricJTableActualUpper

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-25.

Literal certify_conservative_chen.py has NO f_upper/F_upper function and
NO branch on rounded endpoints at three or five. Its real operations are
JTable's double clamp, upper_kernel at line239, and the separately written
fixed-five S3 kernel at line243. This module preserves those expressions.
The lower clamp matters: S5's final true arguments are below three while
an enclosing rounded upper endpoint can still cross three. We prove the
lookup contains zero in this case without assuming that upper index is zero.

The old conservative A=100/1149 is retained. It is not current original
A=417/5000. The theorem is about this actual recovered producer component,
not a numerical evaluation or a final-functional acceptance theorem.
-/

namespace ImbalancedChen.P2HistoricJTableLowerClamp

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open Certificates.P2HistoricJTableInterpreter
open P2HistoricJTableActualUpper

theorem source_lowerIndex_eq_zero {n : ℕ} {sI : I80} {s : ℝ}
    (hsI : sI.Contains s) (hs3 : s ≤ 3) : lowerIndex n sI = 0 := by
  have hl := ((contains_iff sI s).mp hsI).1
  have hscaled : (sI.lo : ℝ) ≤ 3 * (Q : ℝ) := by
    have h := (div_le_iff₀ Q_real_pos).mp hl
    exact h.trans (mul_le_mul_of_nonneg_right hs3 Q_real_pos.le)
  have hlo : sI.lo ≤ 3 * (Q : ℤ) := by exact_mod_cast hscaled
  have hc : clamp sI.lo = 0 := by
    unfold clamp
    have hQ : (0 : ℤ) ≤ Q := by positivity
    rw [min_eq_right (by omega), max_eq_left (by omega)]
  simp [lowerIndex, hc]

/-- A true argument below three forces only the lower index to zero.
The rounded upper endpoint may lie above three; its prefix is still
nonnegative because it encloses an actual nonnegative Darboux integral. -/
theorem sourceLookup_contains_zero {n : ℕ} (hn : 0 < n)
    {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hs3 : s ≤ 3) :
    (sourceLookup n sI).Contains 0 := by
  have hlower := source_lowerIndex_eq_zero hsI hs3 (n := n)
  have hupper := (index_arithmetic n sI).2.1
  have hp := prefix_contains Certificates.P2HistoricLogCallerGuards.logInterval
    source_interval_log_contract hn hupper
  have hb := node_real_bounds hn hupper
  have hnonneg : 0 ≤ ∫ v in (2 : ℝ)..(node n (upperIndex n sI) : ℝ), q v := by
    apply intervalIntegral.integral_nonneg hb.1
    intro v hv
    exact q_nonneg ⟨hv.1, hv.2.trans hb.2⟩
  constructor
  · simp [sourceLookup, lookup, hlower, prefix, I80.decodeLo]
  · exact hnonneg.trans hp.2

/-- Original JTable's lower clamp correctly supplies the reciprocal first
upper strip, even when the rounded interval straddles the knot three. -/
theorem sourceUpper_contains_actual_upper_first_strip {n : ℕ} (hn : 0 < n)
    {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hlo : 0 < sI.lo)
    (hs1 : 1 < s) (hs3 : s ≤ 3) :
    (sourceUpper n sI).Contains (upper s) := by
  have hJ := sourceLookup_contains_zero hn hsI hs3
  have hnum := I80.add_contains (I80.point_contains 1) hJ
  have hquot := historicalDiv_contains hnum hsI hlo
  simpa only [Rat.cast_one, add_zero, ← upper_eq_inv hs1 hs3] using hquot

/-- This is the single genuine JTable source expression on its complete
nonconstant-use domain. There is no invented arithmetic branch at three. -/
theorem sourceUpper_contains_actual_upper_below_five {n : ℕ} (hn : 0 < n)
    {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hlo : 0 < sI.lo)
    (hs1 : 1 < s) (hs5 : s ≤ 5) :
    (sourceUpper n sI).Contains (upper s) := by
  by_cases hs3 : s ≤ 3
  · exact sourceUpper_contains_actual_upper_first_strip hn hsI hlo hs1 hs3
  · exact sourceUpper_contains_actual_upper hn hsI hlo (le_of_not_ge hs3) hs5

/-- The same lower-clamp argument identifies the literal lookup with the
actual numerator minus one throughout (1,5], without an artificial source branch. -/
theorem sourceLookup_contains_actual_H_below_five {n : ℕ} (hn : 0 < n)
    {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hs1 : 1 < s) (hs5 : s ≤ 5) :
    (sourceLookup n sI).Contains (H s - 1) := by
  by_cases hs3 : s ≤ 3
  · rw [H_eq_one hs1 hs3, sub_self]
    exact sourceLookup_contains_zero hn hsI hs3
  · simpa only [min_eq_left hs5] using
      sourceLookup_contains_actual_H hn hsI (le_of_not_ge hs3)

def conservativeA : ℚ := 100 / 1149

theorem conservativeA_pos : (0 : ℝ) < (conservativeA : ℝ) := by
  norm_num [conservativeA]

theorem conservativeA_point_lo_pos : 0 < (I80.point conservativeA).lo := by
  change 0 < ⌊conservativeA * (Q : ℚ)⌋
  apply lt_of_lt_of_le (show (0 : ℤ) < 1 by norm_num)
  apply Int.le_floor.mpr
  norm_num [conservativeA, Q]

/-- Literal source line240: its only division before JTable is delta/I(A),
and its final divisor is the original interval product delta*t. -/
def sourceUpperKernel (n : ℕ) (t delta : I80) : I80 :=
  historicalDiv
    ((I80.point 4).mul ((I80.point 1).add
      (sourceLookup n (historicalDiv delta (I80.point conservativeA)))))
    (delta.mul t)

def actualUpperKernel (t delta : ℝ) : ℝ :=
  4 * upper (delta / (conservativeA : ℝ)) / ((conservativeA : ℝ) * t)

theorem sourceUpperKernel_contains_actual {n : ℕ} (hn : 0 < n)
    {tI deltaI : I80} {t delta : ℝ}
    (htI : tI.Contains t) (hdI : deltaI.Contains delta)
    (hden : 0 < (deltaI.mul tI).lo) (ht : 0 < t)
    (hs1 : 1 < delta / (conservativeA : ℝ))
    (hs5 : delta / (conservativeA : ℝ) ≤ 5) :
    (sourceUpperKernel n tI deltaI).Contains (actualUpperKernel t delta) := by
  have hr := historicalDiv_contains hdI (I80.point_contains conservativeA)
    conservativeA_point_lo_pos
  have hJ := sourceLookup_contains_actual_H_below_five hn hr hs1 hs5
  have hnum := I80.mul_contains (I80.point_contains 4)
    (I80.add_contains (I80.point_contains 1) hJ)
  have hquot := historicalDiv_contains hnum (I80.mul_contains hdI htI) hden
  have hd : 0 < delta := by
    have h := (lt_div_iff₀ conservativeA_pos).mp hs1
    linarith [conservativeA_pos]
  have heq : (4 : ℝ) * (1 + (H (delta / (conservativeA : ℝ)) - 1)) /
      (delta * t) = actualUpperKernel t delta := by
    dsimp [actualUpperKernel, H]
    field_simp [conservativeA_pos.ne', ht.ne', hd.ne']
    <;> ring
  simpa only [Rat.cast_ofNat, heq] using hquot

/-- The separate original S3 fixed-five expression, source line243.
Its lower endpoint describes the cap, not the true upper factor past five. -/
def sourceFixedFiveKernel (n : ℕ) (t : I80) : I80 :=
  historicalDiv
    ((I80.point 4).mul ((I80.point 1).add (sourceLookup n (I80.point 5))))
    ((I80.point (5 * conservativeA)).mul t)

def actualFixedFiveKernel (t : ℝ) : ℝ :=
  4 * upper 5 / ((conservativeA : ℝ) * t)

theorem sourceFixedFiveKernel_contains_cap {n : ℕ} (hn : 0 < n)
    {tI : I80} {t : ℝ} (htI : tI.Contains t) (ht : 0 < t)
    (hden : 0 < ((I80.point (5 * conservativeA)).mul tI).lo) :
    (sourceFixedFiveKernel n tI).Contains (actualFixedFiveKernel t) := by
  have hJ := sourceLookup_contains_actual_H_below_five hn (I80.point_contains 5)
    (by norm_num) (by norm_num)
  have hnum := I80.mul_contains (I80.point_contains 4)
    (I80.add_contains (I80.point_contains 1) hJ)
  have hquot := historicalDiv_contains hnum
    (I80.mul_contains (I80.point_contains (5 * conservativeA)) htI) hden
  have heq : (4 : ℝ) * (1 + (H 5 - 1)) /
      ((5 * (conservativeA : ℝ)) * t) = actualFixedFiveKernel t := by
    dsimp [actualFixedFiveKernel, H]
    field_simp [conservativeA_pos.ne', ht.ne']
    <;> ring
  simpa only [Rat.cast_ofNat, Rat.cast_mul, heq] using hquot

/-- Correct one-sided interpretation of the original fixed-five tail.
This is not asserted to enclose the actual upper kernel from both sides. -/
theorem actualUpperKernel_le_sourceFixedFiveKernel_hi {n : ℕ} (hn : 0 < n)
    {tI : I80} {t delta : ℝ} (htI : tI.Contains t) (ht : 0 < t)
    (hden : 0 < ((I80.point (5 * conservativeA)).mul tI).lo)
    (hs5 : 5 ≤ delta / (conservativeA : ℝ)) :
    actualUpperKernel t delta ≤ ((sourceFixedFiveKernel n tI).decodeHi : ℝ) := by
  have hcap := sourceFixedFiveKernel_contains_cap hn htI ht hden
  have hu : upper (delta / (conservativeA : ℝ)) ≤ upper 5 :=
    upper_antitone (by norm_num) (by change 2 ≤ delta / (conservativeA : ℝ); linarith)
      hs5
  have hmul := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 4)
  have hkernel := div_le_div_of_nonneg_right hmul
    (mul_nonneg conservativeA_pos.le ht.le)
  exact hkernel.trans hcap.2

end
end ImbalancedChen.P2HistoricJTableLowerClamp

