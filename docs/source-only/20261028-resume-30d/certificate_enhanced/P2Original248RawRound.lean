import ImbalancedChen.P2OriginalW1CandidateIntegerABI

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.
Exact integer ABI of certify_expanded_w2_joint_table.one_round.
The old table is fixed across ordinary tails and every W1/W2 action.
Only max-retention reads the mutable current table. The lower side is
changed only by the original old-H Buchstab tail. No W1/W2 semantic
licence, seed soundness or terminal table value is assumed here.
-/
namespace ImbalancedChen.P2Original248RawRound

open P2SimultaneousTableSourceOnly
open P2OriginalW2CandidateIntegerABI
open scoped BigOperators

/-- Exactly the W1 fields consumed by the downstream original one_round.
The literal recalibrated base is retained rather than silently recomputed. -/
structure W1Row where
  base : ℤ
  pointIndex : Fin 200
  feedback : List WeightRow
  targets : List (Fin 200)

def w1Candidate (old : Table) (a : W1Row) : ℤ :=
  a.base + old true a.pointIndex + weightedSum old false a.feedback

def applyW1 (old current : Table) (a : W1Row) : Table := fun side i =>
  if side = true ∧ i ∈ a.targets then max (current side i) (w1Candidate old a)
  else current side i

def suffix (weights : ℕ → ℤ) (old : Table) (side : Bool) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (200-k),
    read old side (k+j) * weights (k+j) / (P2TableActionSourceOnly.tableQ:ℤ)

def ordinaryFrame (weights : ℕ → ℤ) (old : Table) : Table := fun side i =>
  if 50 ≤ i.val then
    max (old side i) (suffix weights old (!side)
      (if side then max 50 (i.val-49) else i.val-49))
  else old side i

def runW1 (old current : Table) (bank : List W1Row) : Table :=
  bank.foldl (applyW1 old) current

def runW2 (old current : Table) (bank : List P2OriginalW2CandidateIntegerABI.Action) : Table :=
  bank.foldl (P2OriginalW2CandidateIntegerABI.apply old) current

def oneRound (weights : ℕ → ℤ) (w1 : List W1Row) (w2 : List P2OriginalW2CandidateIntegerABI.Action)
    (old : Table) : Table :=
  runW2 old (runW1 old (ordinaryFrame weights old) w1) w2

def iterate (weights : ℕ → ℤ) (w1 : List W1Row) (w2 : List P2OriginalW2CandidateIntegerABI.Action)
    (seed : Table) : ℕ → Table
  | 0 => seed
  | n+1 => oneRound weights w1 w2 (iterate weights w1 w2 seed n)

theorem applyW1_lower_unchanged (old current : Table) (a : W1Row) (i : Fin 200) :
    applyW1 old current a false i = current false i := by simp [applyW1]

theorem runW1_lower_unchanged (old current : Table) (bank : List W1Row)
    (i : Fin 200) : runW1 old current bank false i = current false i := by
  induction bank generalizing current with
  | nil => rfl
  | cons a bank ih =>
    simpa only [runW1,List.foldl_cons,applyW1_lower_unchanged] using
      ih (applyW1 old current a)

theorem runW2_lower_unchanged (old current : Table) (bank : List P2OriginalW2CandidateIntegerABI.Action)
    (i : Fin 200) : runW2 old current bank false i = current false i := by
  induction bank generalizing current with
  | nil => rfl
  | cons a bank ih =>
    simpa only [runW2,List.foldl_cons,
      P2OriginalW2CandidateIntegerABI.apply_lower_unchanged] using
      ih (P2OriginalW2CandidateIntegerABI.apply old current a)

/-- This is the original retained h update after ALL106 upper actions,
with precisely the preceding generation's H array on the right. -/
theorem oneRound_lower (weights : ℕ → ℤ) (w1 : List W1Row)
    (w2 : List P2OriginalW2CandidateIntegerABI.Action) (old : Table) (i : Fin 200) (hi : 50 ≤ i.val) :
    oneRound weights w1 w2 old false i =
      max (old false i) (suffix weights old true (i.val-49)) := by
  rw [oneRound,runW2_lower_unchanged,runW1_lower_unchanged]
  simp only [ordinaryFrame,hi,if_true,Bool.not_false,Bool.false_eq_true,if_false]

theorem oneRound_low_lower_unchanged (weights : ℕ → ℤ) (w1 : List W1Row)
    (w2 : List P2OriginalW2CandidateIntegerABI.Action) (old : Table) (i : Fin 200) (hi : i.val < 50) :
    oneRound weights w1 w2 old false i = old false i := by
  rw [oneRound,runW2_lower_unchanged,runW1_lower_unchanged]
  simp only [ordinaryFrame,not_le.mpr hi,if_false]

/-- Exact finite arithmetic history: a lower entry is retained or receives
one old-H suffix from one of the preceding generations. No W1/W2 result
is read sequentially within that generation. -/
theorem lower_history_max (weights : ℕ → ℤ) (w1 : List W1Row)
    (w2 : List P2OriginalW2CandidateIntegerABI.Action) (seed : Table) (i : Fin 200) (hi : 50 ≤ i.val) (n : ℕ) :
    iterate weights w1 w2 seed n false i =
      (List.range n).foldl (fun cur r => max cur
        (suffix weights (iterate weights w1 w2 seed r) true (i.val-49)))
        (seed false i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate,oneRound_lower weights w1 w2 _ i hi,ih,
      List.range_succ,List.foldl_append]
    rfl

end ImbalancedChen.P2Original248RawRound
