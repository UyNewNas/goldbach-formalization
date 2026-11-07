import ImbalancedChen.OriginalFifthRawStreamingOwner

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

A literal finite primitive guard bank for one ORIGINAL selected fifth mesh
cell. It contains both affine pieces of every original fourth/fifth raw
candidate, the selected raw-Q3 Gamma seed, all pairwise piece differences,
and every projected fourth raw-box face. Original positions, including
duplicates, index the bank. Strict AND weak sign bits distinguish equality
from either open side. No argmax, owner region, or atom winner is assumed.
The bank is fixed from e, mesh, cell and raw records before N.
-/

namespace ImbalancedChen.OriginalFifthLiteralAffineSignBank20261026b

noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1ActualVariableFourthFifthCellTestLimit
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)
abbrev CandidateKey (records4 : List FourthWireRow) (records5 : List FifthWireRow) :=
  Unit ⊕ (Fin records4.length ⊕ Fin records5.length)

def seedKey {records4 : List FourthWireRow} {records5 : List FifthWireRow} :
    CandidateKey records4 records5 := Sum.inl ()
def fourthKey {records4 : List FourthWireRow} {records5 : List FifthWireRow}
    (k : Fin records4.length) : CandidateKey records4 records5 := Sum.inr (Sum.inl k)
def fifthKey {records4 : List FourthWireRow} {records5 : List FifthWireRow}
    (k : Fin records5.length) : CandidateKey records4 records5 := Sum.inr (Sum.inr k)

/-- The common buffer is subtracted after the minimum. The seed pieces
are Gamma+2e, so its buffered value is exactly the genuine selected seed. -/
def affinePiece (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (c : CandidateKey records4 records5)
    (side : Bool) (t : Point5) : ℝ :=
  match c with
  | .inl _ => selectedSeed e m j + 2 * (e : ℝ)
  | .inr (.inl k) =>
    let s := ∑ q ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 k).selected,
      firstFour t q
    if side then 57 / 64 - (3 / 2 : ℝ) * s else (1 + s) / 2
  | .inr (.inr k) =>
    let s := ∑ q ∈ (rawRowAt records5 m j k).selected, t q
    if side then 57 / 64 - (3 / 2 : ℝ) * s else (1 + s) / 2

def literalValue (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (c : CandidateKey records4 records5) (t : Point5) : ℝ :=
  min (affinePiece records4 records5 e m j c false t)
    (affinePiece records4 records5 e m j c true t) - 2 * (e : ℝ)

theorem literal_seed (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (t : Point5) :
    literalValue records4 records5 e m j seedKey t = selectedSeed e m j := by
  simp [literalValue, affinePiece, seedKey]

theorem literal_fourth (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (k : Fin records4.length) (t : Point5) :
    literalValue records4 records5 e m j (fourthKey k) t =
      (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 k).bufferedCandidate (e : ℝ) (firstFour t) := by
  rw [ProducerRow.bufferedCandidate_eq, VariableEnvelope.v_eq_min]
  rfl

theorem literal_fifth (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (k : Fin records5.length) (t : Point5) :
    literalValue records4 records5 e m j (fifthKey k) t =
      candidate (e : ℝ) (rawRowAt records5 m j k).selected t := rfl

theorem continuous_affinePiece (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (c : CandidateKey records4 records5) (side : Bool) :
    Continuous (affinePiece records4 records5 e m j c side) := by
  rcases c with _ | k | k
  · exact continuous_const
  · have hs : Continuous (fun t : Point5 =>
        ∑ q ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 k).selected, firstFour t q) := by
      apply continuous_finset_sum
      intro q _hq
      exact (continuous_apply q).comp firstFour.continuous
    cases side <;> simp only [affinePiece, Bool.false_eq_true, if_false, if_true] <;> fun_prop
  · have hs : Continuous (fun t : Point5 => ∑ q ∈ (rawRowAt records5 m j k).selected, t q) := by
      fun_prop
    cases side <;> simp only [affinePiece, Bool.false_eq_true, if_false, if_true] <;> fun_prop

abbrev GuardKey (records4 : List FourthWireRow) (records5 : List FifthWireRow) :=
  (CandidateKey records4 records5 × Bool × CandidateKey records4 records5 × Bool) ⊕
    (Fin records4.length × Fin 4 × Bool)

def guardValue (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (g : GuardKey records4 records5) (t : Point5) : ℝ :=
  match g with
  | .inl (a, sa, b, sb) =>
    affinePiece records4 records5 e m j a sa t - affinePiece records4 records5 e m j b sb t
  | .inr (k, q, upper) =>
    if upper then firstFour t q - (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 k).upper q
    else (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 k).lower q - firstFour t q

theorem continuous_guardValue (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (g : GuardKey records4 records5) :
    Continuous (guardValue records4 records5 e m j g) := by
  rcases g with ⟨a, sa, b, sb⟩ | ⟨k, q, upper⟩
  · exact (continuous_affinePiece records4 records5 e m j a sa).sub
      (continuous_affinePiece records4 records5 e m j b sb)
  · have hq : Continuous (fun t : Point5 => firstFour t q) :=
      (continuous_apply q).comp firstFour.continuous
    cases upper <;> simp only [guardValue, Bool.false_eq_true, if_false, if_true] <;> fun_prop

/-- (true,true), (false,true), (false,false) are the negative, zero and
positive signs. The unused (true,false) fiber is empty. -/
def primitiveWord (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (t : Point5) : GuardKey records4 records5 → Bool × Bool :=
  fun g => (decide (guardValue records4 records5 e m j g t < 0),
    decide (guardValue records4 records5 e m j g t ≤ 0))

abbrev SignWord (records4 : List FourthWireRow) (records5 : List FifthWireRow) :=
  GuardKey records4 records5 → Bool × Bool

def signAtom (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5) : Set Point5 :=
  {t | primitiveWord records4 records5 e m j t = s}

theorem mem_actual_signAtom (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (t : Point5) :
    t ∈ signAtom records4 records5 e m j (primitiveWord records4 records5 e m j t) := rfl

theorem signAtom_disjoint (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) {s u : SignWord records4 records5} (hsu : s ≠ u) :
    Disjoint (signAtom records4 records5 e m j s) (signAtom records4 records5 e m j u) := by
  apply Set.disjoint_left.mpr
  intro t hs hu
  exact hsu (hs.symm.trans hu)

theorem atom_guard_lt_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s) (g : GuardKey records4 records5) :
    guardValue records4 records5 e m j g t < 0 ↔ guardValue records4 records5 e m j g u < 0 := by
  have heq := congrArg Prod.fst (congrFun (ht.trans hu.symm) g)
  have hiff : (primitiveWord records4 records5 e m j t g).1 = true ↔
      (primitiveWord records4 records5 e m j u g).1 = true := by rw [heq]
  simpa only [primitiveWord, decide_eq_true_eq] using hiff

theorem atom_guard_le_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s) (g : GuardKey records4 records5) :
    guardValue records4 records5 e m j g t ≤ 0 ↔ guardValue records4 records5 e m j g u ≤ 0 := by
  have heq := congrArg Prod.snd (congrFun (ht.trans hu.symm) g)
  have hiff : (primitiveWord records4 records5 e m j t g).2 = true ↔
      (primitiveWord records4 records5 e m j u g).2 = true := by rw [heq]
  simpa only [primitiveWord, decide_eq_true_eq] using hiff

theorem atom_guard_zero_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s) (g : GuardKey records4 records5) :
    guardValue records4 records5 e m j g t = 0 ↔ guardValue records4 records5 e m j g u = 0 := by
  have hw := atom_guard_le_iff records4 records5 e m j s ht hu g
  have hs := atom_guard_lt_iff records4 records5 e m j s ht hu g
  constructor
  · intro hz
    exact le_antisymm (hw.mp hz.le)
      (le_of_not_gt (fun hneg => (not_lt_of_ge hz.ge) (hs.mpr hneg)))
  · intro hz
    exact le_antisymm (hw.mpr hz.le)
      (le_of_not_gt (fun hneg => (not_lt_of_ge hz.ge) (hs.mp hneg)))

theorem atom_piece_le_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s)
    (a b : CandidateKey records4 records5) (sa sb : Bool) :
    affinePiece records4 records5 e m j a sa t ≤ affinePiece records4 records5 e m j b sb t ↔
      affinePiece records4 records5 e m j a sa u ≤ affinePiece records4 records5 e m j b sb u := by
  simpa only [guardValue, sub_nonpos] using
    atom_guard_le_iff records4 records5 e m j s ht hu (Sum.inl (a, sa, b, sb))

theorem atom_piece_lt_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s)
    (a b : CandidateKey records4 records5) (sa sb : Bool) :
    affinePiece records4 records5 e m j a sa t < affinePiece records4 records5 e m j b sb t ↔
      affinePiece records4 records5 e m j a sa u < affinePiece records4 records5 e m j b sb u := by
  simpa only [guardValue, sub_neg] using
    atom_guard_lt_iff records4 records5 e m j s ht hu (Sum.inl (a, sa, b, sb))

/-- Both pieces are compared. Thus the atom derives all tent comparisons
without presupposing an active affine branch or a winning raw row. -/
theorem atom_literal_le_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s) (a b : CandidateKey records4 records5) :
    literalValue records4 records5 e m j a t ≤ literalValue records4 records5 e m j b t ↔
      literalValue records4 records5 e m j a u ≤ literalValue records4 records5 e m j b u := by
  simp only [literalValue, sub_le_sub_iff_right, le_min_iff, min_le_iff]
  rw [atom_piece_le_iff records4 records5 e m j s ht hu a b false false,
    atom_piece_le_iff records4 records5 e m j s ht hu a b true false,
    atom_piece_le_iff records4 records5 e m j s ht hu a b false true,
    atom_piece_le_iff records4 records5 e m j s ht hu a b true true]

theorem atom_literal_lt_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s) (a b : CandidateKey records4 records5) :
    literalValue records4 records5 e m j a t < literalValue records4 records5 e m j b t ↔
      literalValue records4 records5 e m j a u < literalValue records4 records5 e m j b u := by
  simp only [literalValue, sub_lt_sub_iff_right, lt_min_iff, min_lt_iff]
  rw [atom_piece_lt_iff records4 records5 e m j s ht hu a b false false,
    atom_piece_lt_iff records4 records5 e m j s ht hu a b true false,
    atom_piece_lt_iff records4 records5 e m j s ht hu a b false true,
    atom_piece_lt_iff records4 records5 e m j s ht hu a b true true]

/-- Closed lower and upper box faces are preserved exactly, including
equality walls; no claim of nullity or deletion of boundary atoms is used. -/
theorem atom_fourth_box_iff (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (s : SignWord records4 records5)
    {t u : Point5} (ht : t ∈ signAtom records4 records5 e m j s)
    (hu : u ∈ signAtom records4 records5 e m j s) (k : Fin records4.length) :
    firstFour t ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 k).box ↔
      firstFour u ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 k).box := by
  have hlo (q : Fin 4) := atom_guard_le_iff records4 records5 e m j s ht hu (Sum.inr (k, q, false))
  have hhi (q : Fin 4) := atom_guard_le_iff records4 records5 e m j s ht hu (Sum.inr (k, q, true))
  simp only [guardValue, Bool.false_eq_true, if_false, if_true, sub_nonpos] at hlo hhi
  exact ⟨fun h => ⟨fun q => (hlo q).mp (h.1 q), fun q => (hhi q).mp (h.2 q)⟩,
    fun h => ⟨fun q => (hlo q).mpr (h.1 q), fun q => (hhi q).mpr (h.2 q)⟩⟩

end
end ImbalancedChen.OriginalFifthLiteralAffineSignBank20261026b
