import ImbalancedChen.P2OriginalW2CandidateIntegerABI
import ImbalancedChen.Certificates.RationalLogCertificate

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_PROOF_CREDIT, 2026-10-25.

Original W1 ABI from certify_finite_step_table.py and its literal
certify_lower_k_finite_table.py recalibration, retained by
certify_expanded_w2_joint_table.py. This is the original exact rational
48-term lower logarithm and one downward baseline increment, followed by
base+oldH[point_index]+sum(oldh[j]*weight//Q). There is no division by five
in W1. All candidates use old; only max retention and the touched-cell
test inspect the mutable next table.

No uniform product-K1 theorem, enhanced-family W1 licence, seed licence,
concrete 70-action bank or h248/h430 numeric result is asserted.
-/

namespace ImbalancedChen.P2OriginalW1CandidateIntegerABI

noncomputable section

open P2SimultaneousTableSourceOnly P2OriginalW2CandidateIntegerABI
open Certificates

def logLower48 (x : ℚ) : ℚ := logSeriesLower x 48

/-- The exact original lower polynomial has actual logarithm semantics;
no checked-log or logarithm-bound premise is supplied by the caller. -/
theorem logLower48_le_log (x : ℚ) (hx : 1 ≤ x) :
    (logLower48 x : ℝ) ≤ Real.log (x : ℝ) := by
  let c : RationalLogCertificate :=
    ⟨x, 48, logSeriesLower x 48, logSeriesUpper x 48⟩
  have hv : c.Valid := ⟨hx, le_rfl, le_rfl⟩
  have hc : c.check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using hv
  exact (RationalLogCertificate.check_sound c hc).1

def sourceC : ℚ := 70893 / 125000
def sourceDelta : ℚ := 681 / 100 - 67633 / 10000

def recalibrationMass (s s0 : ℚ) : ℚ :=
  sourceC * ((s0+s)*logLower48 (s0/s)-2*(s0-s))

/-- Actual lower-cost mass in the recalibration source, with its original
positive multiplier and its exact 48-term rational expression. -/
theorem recalibrationMass_le_actual (s s0 : ℚ)
    (hs : 0 < s) (horder : s ≤ s0) :
    (recalibrationMass s s0 : ℝ) ≤
      (sourceC : ℝ) * (((s0+s : ℚ) : ℝ) * Real.log ((s0/s : ℚ) : ℝ) -
        ((2*(s0-s) : ℚ) : ℝ)) := by
  have hr : 1 ≤ s0/s := (le_div_iff₀ hs).2 (by simpa using horder)
  have hsum : (0 : ℝ) ≤ ((s0+s : ℚ) : ℝ) := by
    have hq : (0 : ℚ) ≤ s0+s := by linarith
    exact_mod_cast hq
  have hc : (0 : ℝ) ≤ (sourceC : ℝ) := by norm_num [sourceC]
  have hl := logLower48_le_log (s0/s) hr
  simp only [recalibrationMass, Rat.cast_mul, Rat.cast_sub]
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hl hsum) _) hc

/-- Literal inc=floor(Q*(K0-K1)*mass/8), followed by old_base+inc. -/
def baselineIncrement (s s0 : ℚ) : ℤ :=
  ⌊(q : ℚ) * sourceDelta * recalibrationMass s s0 / 8⌋

def recalibratedBase (oldBase : ℤ) (s s0 : ℚ) : ℤ :=
  oldBase + baselineIncrement s s0

theorem baselineIncrement_error (s s0 : ℚ) :
    0 ≤ sourceDelta * recalibrationMass s s0 / 8 -
        (baselineIncrement s s0 : ℚ) / q ∧
      sourceDelta * recalibrationMass s s0 / 8 -
        (baselineIncrement s s0 : ℚ) / q < 1 / q := by
  let r : ℚ := (q : ℚ) * sourceDelta * recalibrationMass s s0 / 8
  have hl : 0 ≤ r - (⌊r⌋ : ℚ) := sub_nonneg.mpr (Int.floor_le r)
  have hu : r - (⌊r⌋ : ℚ) < 1 := by
    have h := Int.lt_floor_add_one r
    linarith
  have he : sourceDelta * recalibrationMass s s0 / 8 -
      (baselineIncrement s s0 : ℚ) / q = (r-(⌊r⌋ : ℚ))/q := by
    dsimp only [r, baselineIncrement]
    field_simp [q_rat_pos.ne']
    <;> ring
  rw [he]
  exact ⟨div_nonneg hl q_rat_pos.le,
    (div_lt_div_iff_of_pos_right q_rat_pos).2 hu⟩

structure Action where
  oldBase : ℤ
  s : ℚ
  s0 : ℚ
  pointIndex : Fin 200
  feedback : List WeightRow
  targets : List (Fin 200)

def Action.base (a : Action) : ℤ := recalibratedBase a.oldBase a.s a.s0

def Action.Valid (a : Action) : Prop := ∀ r ∈ a.feedback, r.Valid

def candidate (old : Table) (a : Action) : ℤ :=
  a.base + old true a.pointIndex + weightedSum old false a.feedback

def candidateIdeal (old : Table) (a : Action) : ℚ :=
  ((a.base : ℚ) + old true a.pointIndex + weightedIdeal old false a.feedback) / q

/-- W1 has exactly the per-product losses, with no final //5 loss. -/
theorem candidate_error (old : Table) (a : Action) :
    0 ≤ candidateIdeal old a - (candidate old a : ℚ) / q ∧
      candidateIdeal old a - (candidate old a : ℚ) / q ≤
        (a.feedback.length : ℚ) / q := by
  have h := weightedSum_error old false a.feedback
  have he : candidateIdeal old a - (candidate old a : ℚ) / q =
      (weightedIdeal old false a.feedback-(weightedSum old false a.feedback : ℚ))/q := by
    simp only [candidateIdeal, candidate, Int.cast_add]
    ring
  rw [he]
  exact ⟨div_nonneg h.1 q_rat_pos.le,
    (div_le_div_iff_of_pos_right q_rat_pos).2 h.2⟩

def fullIdeal (old : Table) (a : Action) : ℚ :=
  (a.oldBase : ℚ)/q + sourceDelta*recalibrationMass a.s a.s0/8 +
    (old true a.pointIndex : ℚ)/q + weightedIdeal old false a.feedback/q

/-- Both original rounding layers are counted: the cost recalibration
floor and each feedback product floor. No regrouped single floor is used. -/
theorem full_candidate_error (old : Table) (a : Action) :
    0 ≤ fullIdeal old a - (candidate old a : ℚ)/q ∧
      fullIdeal old a - (candidate old a : ℚ)/q <
        ((a.feedback.length : ℚ)+1)/q := by
  have hb := baselineIncrement_error a.s a.s0
  have hc := candidate_error old a
  have he : fullIdeal old a - (candidate old a : ℚ)/q =
      (sourceDelta*recalibrationMass a.s a.s0/8-
        (baselineIncrement a.s a.s0 : ℚ)/q) +
      (candidateIdeal old a-(candidate old a : ℚ)/q) := by
    simp only [fullIdeal, candidateIdeal, Action.base, recalibratedBase, Int.cast_add]
    ring
  rw [he]
  constructor
  · exact add_nonneg hb.1 hc.1
  · have hu := add_lt_add_of_lt_of_le hb.2 hc.2
    have halg : (1 : ℚ)/q+(a.feedback.length : ℚ)/q =
        ((a.feedback.length : ℚ)+1)/q := by ring
    rw [halg] at hu
    exact hu

theorem candidate_mono {X Y : Table} (hXY : Below X Y) (a : Action)
    (ha : a.Valid) : candidate X a ≤ candidate Y a := by
  exact add_le_add (add_le_add_left (hXY true a.pointIndex) a.base)
    (weightedSum_mono hXY false a.feedback ha)

def apply (old current : Table) (a : Action) : Table := fun side i =>
  if side = true ∧ i ∈ a.targets then max (current side i) (candidate old a)
  else current side i

/-- Literal original touched-cell predicate: inspect current, read old. -/
def touched (old current : Table) (a : Action) (i : Fin 200) : Prop :=
  i ∈ a.targets ∧ candidate old a > current true i

theorem apply_improves_iff_touched (old current : Table) (a : Action) (i : Fin 200) :
    current true i < apply old current a true i ↔ touched old current a i := by
  by_cases hi : i ∈ a.targets <;> simp [apply, touched, hi]

theorem apply_lower_unchanged (old current : Table) (a : Action) (i : Fin 200) :
    apply old current a false i = current false i := by simp [apply]

theorem apply_retains (old current : Table) (a : Action) :
    Below current (apply old current a) := by
  intro side i
  simp only [apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

end

end ImbalancedChen.P2OriginalW1CandidateIntegerABI
