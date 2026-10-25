import ImbalancedChen.P2SimultaneousTableIteration
import Mathlib.Data.Rat.Floor

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_PROOF_CREDIT, 2026-10-25.

Literal arithmetic of `w2_candidate` and its immutable-old-table application
in certify_expanded_w2_joint_table.py, SHA256
1d6d504bd1f676bd99ce35e332f32987dccd10a1221d268e4728fab3bd4f8f9e.
The original ABI uses Q80, signed integer //, every product rounded before
addition, and exactly one final //5. Grouped weight rows are flattened only
after retaining their order. Upper coefficient endpoints are checked data
but are not substituted for the lower endpoints used by this producer.

This supplies integer arithmetic and lawful array reads, not an analytic
W2 action licence. The 70 W1/3 old W2/33 added W2 actions and positive seed
still need their original enhanced-family analytic suppliers. No numerical
h248/h430 table or selected improvement event is replayed or asserted here.
The paired P160/W224 96-term logarithm and P4A positive256 ln32 interpreter
are different backends and are not identified by this module.
-/

namespace ImbalancedChen.P2OriginalW2CandidateIntegerABI

noncomputable section

open P2SimultaneousTableSourceOnly P2TableActionSourceOnly

def q : ℤ := (tableQ : ℤ)

theorem q_pos : 0 < q := by exact_mod_cast tableQ_pos
theorem q_rat_pos : (0 : ℚ) < q := by exact_mod_cast q_pos

/-- A source index has already passed `0 <= j < 200`. -/
structure WeightRow where
  index : Fin 200
  lower : ℤ
  upper : ℤ

def WeightRow.Valid (r : WeightRow) : Prop := 0 ≤ r.lower ∧ r.lower ≤ r.upper

structure PointRow where
  index : Fin 200
  multiplicity : ℤ

def PointRow.Valid (r : PointRow) : Prop := 0 < r.multiplicity

/-- The unused upper endpoint is preserved in the data ABI. -/
structure Action where
  base : ℤ
  points : List PointRow
  negativeRows : List (List WeightRow)
  pairRows : List (List WeightRow)
  targets : List (Fin 200)

def Action.Valid (a : Action) : Prop :=
  (∀ r ∈ a.points, r.Valid) ∧
  (∀ r ∈ a.negativeRows.flatten, r.Valid) ∧
  (∀ r ∈ a.pairRows.flatten, r.Valid)

theorem lawful_read (X : Table) (side : Bool) (i : Fin 200) :
    read X side i.val = X side i := by
  simp only [read, dif_pos i.isLt]

def pointSum (X : Table) : List PointRow → ℤ
  | [] => 0
  | r :: rs => X true r.index * r.multiplicity + pointSum X rs

def weightedSum (X : Table) (side : Bool) : List WeightRow → ℤ
  | [] => 0
  | r :: rs => X side r.index * r.lower / q + weightedSum X side rs

def weightedIdeal (X : Table) (side : Bool) : List WeightRow → ℚ
  | [] => 0
  | r :: rs => (X side r.index : ℚ) * r.lower / q + weightedIdeal X side rs

/-- The exact source total, before the single final division by five. -/
def total (old : Table) (a : Action) : ℤ :=
  pointSum old a.points + weightedSum old false a.negativeRows.flatten +
    weightedSum old true a.pairRows.flatten

def totalIdeal (old : Table) (a : Action) : ℚ :=
  (pointSum old a.points : ℚ) + weightedIdeal old false a.negativeRows.flatten +
    weightedIdeal old true a.pairRows.flatten

def candidate (old : Table) (a : Action) : ℤ := a.base + total old a / 5

def candidateIdeal (old : Table) (a : Action) : ℚ :=
  ((a.base : ℚ) + totalIdeal old a / 5) / q

def floorCount (a : Action) : ℕ := a.negativeRows.flatten.length + a.pairRows.flatten.length

/-- This includes negative numerators: Python // is Euclidean floor here. -/
theorem quotient_error (n d : ℤ) (hd : 0 < d) :
    0 ≤ (n : ℚ) / d - (n / d : ℤ) ∧
      (n : ℚ) / d - (n / d : ℤ) < 1 := by
  have hf : ⌊(n : ℚ) / (d : ℚ)⌋ = n / d := by
    have hdZ : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
    have hdQ : (d.toNat : ℚ) = (d : ℚ) := by exact_mod_cast hdZ
    have h := Rat.floor_intCast_div_natCast n d.toNat
    rw [hdQ, hdZ] at h
    exact h
  have hl := Int.floor_le ((n : ℚ) / d)
  have hu := Int.lt_floor_add_one ((n : ℚ) / d)
  rw [hf] at hl hu
  constructor <;> linarith

/-- Each original per-product floor loses less than one integer unit.
The weak sum bound also handles the empty list, without a fake strict bound. -/
theorem weightedSum_error (X : Table) (side : Bool) (rs : List WeightRow) :
    0 ≤ weightedIdeal X side rs - (weightedSum X side rs : ℚ) ∧
      weightedIdeal X side rs - (weightedSum X side rs : ℚ) ≤ rs.length := by
  induction rs with
  | nil => simp [weightedIdeal, weightedSum]
  | cons r rs ih =>
    have h := quotient_error (X side r.index * r.lower) q q_pos
    simp only [Int.cast_mul] at h
    simp only [weightedIdeal, weightedSum, Int.cast_add, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    constructor <;> linarith [h.1, h.2.le, ih.1, ih.2]

theorem total_error (old : Table) (a : Action) :
    0 ≤ totalIdeal old a - (total old a : ℚ) ∧
      totalIdeal old a - (total old a : ℚ) ≤ floorCount a := by
  have hn := weightedSum_error old false a.negativeRows.flatten
  have hp := weightedSum_error old true a.pairRows.flatten
  simp only [totalIdeal, total, floorCount, Int.cast_add, Nat.cast_add]
  constructor <;> linarith [hn.1, hn.2, hp.1, hp.2]

/-- True signed rounding error for the literal original candidate, with no
assumption on the sign of the base, old entries, or the resulting candidate. -/
theorem candidate_error (old : Table) (a : Action) :
    0 ≤ candidateIdeal old a - (candidate old a : ℚ) / q ∧
      candidateIdeal old a - (candidate old a : ℚ) / q <
        ((floorCount a : ℚ) + 5) / (5 * q) := by
  have ht := total_error old a
  have hf := quotient_error (total old a) 5 (by norm_num)
  have he0 : 0 ≤ totalIdeal old a / 5 - (total old a / 5 : ℤ) := by linarith
  have he1 : totalIdeal old a / 5 - (total old a / 5 : ℤ) <
      (floorCount a : ℚ) / 5 + 1 := by linarith
  have hid : candidateIdeal old a - (candidate old a : ℚ) / q =
      (totalIdeal old a / 5 - (total old a / 5 : ℤ)) / q := by
    simp only [candidateIdeal, candidate, Int.cast_add]
    ring
  rw [hid]
  refine ⟨div_nonneg he0 q_rat_pos.le, ?_⟩
  calc
    _ < ((floorCount a : ℚ) / 5 + 1) / q :=
      (div_lt_div_iff_of_pos_right q_rat_pos).2 he1
    _ = _ := by ring

theorem pointSum_mono {X Y : Table} (hXY : Below X Y) (rs : List PointRow)
    (hr : ∀ r ∈ rs, r.Valid) : pointSum X rs ≤ pointSum Y rs := by
  revert hr
  induction rs with
  | nil => intro hr; exact le_rfl
  | cons r rs ih =>
    intro hr
    have hm := mul_le_mul_of_nonneg_right (hXY true r.index)
      (hr r (by simp)).le
    exact add_le_add hm (ih (by intro s hs; exact hr s (by simp [hs])))

theorem weightedSum_mono {X Y : Table} (hXY : Below X Y) (side : Bool)
    (rs : List WeightRow) (hr : ∀ r ∈ rs, r.Valid) :
    weightedSum X side rs ≤ weightedSum Y side rs := by
  revert hr
  induction rs with
  | nil => intro hr; exact le_rfl
  | cons r rs ih =>
    intro hr
    have hm := mul_le_mul_of_nonneg_right (hXY side r.index)
      (hr r (by simp)).1
    exact add_le_add (Int.ediv_le_ediv q_pos hm)
      (ih (by intro s hs; exact hr s (by simp [hs])))

theorem candidate_mono {X Y : Table} (hXY : Below X Y) (a : Action)
    (ha : a.Valid) : candidate X a ≤ candidate Y a := by
  have htotal : total X a ≤ total Y a :=
    add_le_add (add_le_add (pointSum_mono hXY a.points ha.1)
      (weightedSum_mono hXY false a.negativeRows.flatten ha.2.1))
      (weightedSum_mono hXY true a.pairRows.flatten ha.2.2)
  exact add_le_add_left (Int.ediv_le_ediv (by norm_num : (0 : ℤ) < 5) htotal) a.base

/-- Processing the bank reads `old`, while only retention reads `current`.
This is the original one_round W2 update, not a sequential feedback rule. -/
def apply (old current : Table) (a : Action) : Table := fun side i =>
  if side = true ∧ i ∈ a.targets then max (current side i) (candidate old a)
  else current side i

theorem apply_lower_unchanged (old current : Table) (a : Action) (i : Fin 200) :
    apply old current a false i = current false i := by simp [apply]

theorem apply_retains (old current : Table) (a : Action) :
    Below current (apply old current a) := by
  intro side i
  simp only [apply]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem apply_upper_improves_iff (old current : Table) (a : Action) (i : Fin 200) :
    current true i < apply old current a true i ↔
      i ∈ a.targets ∧ current true i < candidate old a := by
  by_cases hi : i ∈ a.targets <;> simp [apply, hi]

end

end ImbalancedChen.P2OriginalW2CandidateIntegerABI
