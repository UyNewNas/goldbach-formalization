import ImbalancedChen.Certificates.P2HistoricJTableInterpreter
import ImbalancedChen.P2HistoricLogCallerGuards
import ImbalancedChen.ActualThirdOriginalLocalCurvature

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-25.

The literal JTable in certify_conservative_chen.py (SHA256
67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e)
already has a directed Darboux interpreter. This module identifies its
integral with the GENUINE normalized upper factor, using H_sub and the
actual logarithmic first strip of the normalized lower factor. It also
discharges the interpreter's interval-log contract with the historical
Q80 log_point endpoint wrapper. No table endpoint, curvature, target
integral enclosure, or log enclosure is supplied as a caller premise.

The Q80 table is distinct from the 112-bit coupled table and the
P=2^160 / W=2^224 log backends. No numerical producer or checker was run.
-/

namespace ImbalancedChen.P2HistoricJTableActualUpper

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open Certificates.P2HistoricJTableInterpreter

/-- The source's logarithmic integrand is exactly the genuine normalized
lower factor throughout the complete delayed interval used by JTable. -/
theorem q_eq_actual_lower {v : ℝ} (hv : v ∈ Icc (2 : ℝ) 4) :
    q v = lower v := by
  exact (lower_eq_log hv.1 hv.2).symm

/-- The original J(s), on its documented domain, is H(s)-1 for the genuine
coupled sieve functions. This is derived from the source DDE, not assumed. -/
theorem J_eq_actual_H_sub_one {s : ℝ} (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    J s = H s - 1 := by
  have hrec := H_sub (x := (3 : ℝ)) (y := s) (by norm_num) hs3
  have h3 : H (3 : ℝ) = 1 := H_eq_one (by norm_num) (by norm_num)
  rw [h3, intervalIntegral.integral_comp_sub_right] at hrec
  have hstart : (3 : ℝ) - 1 = 2 := by norm_num
  rw [hstart] at hrec
  have heq : (∫ v in (2 : ℝ)..(s - 1), lower v) = J s := by
    unfold J
    simp only [intervalIntegral.integral_of_le (by linarith : (2 : ℝ) ≤ s - 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    exact (q_eq_actual_lower ⟨hv.1.le, by linarith [hv.2]⟩).symm
  exact (hrec.trans heq).symm

/-- Exact original upper-factor formula on the full JTable domain. -/
theorem actual_upper_eq_one_add_J_div {s : ℝ} (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    upper s = (1 + J s) / s := by
  rw [J_eq_actual_H_sub_one hs3 hs5]
  dsimp [H]
  field_simp [show s ≠ 0 by linarith]
  <;> ring

/-- Literal log(I80) has the full interval contract used by original
JTable construction; positivity of the rounded lower endpoint is the
producer's own primitive division/log guard. -/
theorem source_interval_log_contract :
    LogContract Certificates.P2HistoricLogCallerGuards.logInterval := by
  intro x v hlo _hv hx
  exact Certificates.P2HistoricLogCallerGuards.logInterval_contains hx hlo

/-- The exact source lookup, retaining every prefix floor, ceiling and
both clamped integer indices. -/
def sourceLookup (n : ℕ) (s : I80) : I80 :=
  lookup Certificates.P2HistoricLogCallerGuards.logInterval n s

/-- The actual source lookup encloses the genuine upper NUMERATOR minus
one, including fixed-point outward rounding beyond the endpoint five. -/
theorem sourceLookup_contains_actual_H {n : ℕ} (hn : 0 < n)
    {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hs3 : 3 ≤ s) :
    (sourceLookup n sI).Contains (H (min s 5) - 1) := by
  have hmin3 : 3 ≤ min s 5 := le_min hs3 (by norm_num)
  have hmin5 : min s 5 ≤ 5 := min_le_right _ _
  have h := lookup_contains Certificates.P2HistoricLogCallerGuards.logInterval
    source_interval_log_contract hn hsI hs3
  rw [J_eq_actual_H_sub_one hmin3 hmin5] at h
  exact h

/-- Literal original expression (1+J(s))/s, preserving the historical
four-corner signed integer division operation. -/
def sourceUpper (n : ℕ) (s : I80) : I80 :=
  historicalDiv ((I80.point 1).add (sourceLookup n s)) s

theorem sourceUpper_contains_actual_upper {n : ℕ} (hn : 0 < n)
    {sI : I80} {s : ℝ} (hsI : sI.Contains s) (hlo : 0 < sI.lo)
    (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    (sourceUpper n sI).Contains (upper s) := by
  have hJ := lookup_contains_original_domain
    Certificates.P2HistoricLogCallerGuards.logInterval source_interval_log_contract
    hn hsI ⟨hs3, hs5⟩
  have hnum := I80.add_contains (I80.point_contains 1) hJ
  have hquot := historicalDiv_contains hnum hsI hlo
  simp only [Rat.cast_one] at hquot
  rw [← actual_upper_eq_one_add_J_div hs3 hs5] at hquot
  exact hquot

/-- A true source rational query in [3,5] supplies its own primitive guard;
no caller theorem about its rounded endpoints is needed. -/
theorem sourceUpper_point_contains_actual_upper {n : ℕ} (hn : 0 < n)
    (s : ℚ) (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    (sourceUpper n (I80.point s)).Contains (upper (s : ℝ)) := by
  apply sourceUpper_contains_actual_upper hn (I80.point_contains s)
  · exact Certificates.P2HistoricLogCallerGuards.point_lo_pos_of_one_le s
      (by linarith)
  · exact_mod_cast hs3
  · exact_mod_cast hs5

/-- The producer's conservative tail uses the actual upper factor at
five. Its enclosure is still an upper bound beyond five by the genuine
source monotonicity, rather than by extending the J formula past its domain. -/
theorem sourceUpper_at_five_bounds_tail {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs5 : 5 ≤ s) :
    upper s ≤ ((sourceUpper n (I80.point 5)).decodeHi : ℝ) := by
  have he := sourceUpper_point_contains_actual_upper hn (5 : ℚ)
    (by norm_num) (by norm_num)
  have hm : upper s ≤ upper 5 :=
    upper_antitone (by norm_num) (by change 2 ≤ s; linarith) hs5
  exact hm.trans (by simpa only [Rat.cast_ofNat] using he.2)

end
end ImbalancedChen.P2HistoricJTableActualUpper

