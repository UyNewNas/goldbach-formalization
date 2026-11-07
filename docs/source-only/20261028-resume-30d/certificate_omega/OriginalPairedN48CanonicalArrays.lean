import ImbalancedChen.OriginalPairedN48DirectQuerySoundness

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Canonical arrays for the literal r.Omega(8192) recipe in the original n48
wrapper.  The base script's standalone default Omega()=4096 is not used.
Only previously written entries are read by a delayed update.  A prefix
construction therefore preserves exactly the preallocated Python recipe.

The two remaining guards are PURE FINITE ARITHMETIC.  Their proposed closed
proof terms are separate.  Neither array generation nor a checker is run.
No identity with a historical serialized byte stream is asserted.
-/

namespace ImbalancedChen.OriginalPairedN48CanonicalArrays

noncomputable section

open OriginalN48Q112LocalProduct
open OriginalPairedN48OmegaProducerAdapter

/-- The original producer never reads cell/nodes/query during a U update. -/
def nodePayload (u : List Token) : SourceArrays :=
  ⟨u, [], [], 0⟩

def nextU (u : List Token) (i : ℕ) : Token :=
  if i ≤ 2 * mesh then rational 1
  else if i ≤ 3 * mesh then sourceAdd (rational 1) (sourceSmallLog (logArg i))
  else sourceStep (nodePayload u) i

/-- The append order and all exact source operations are retained. -/
def buildU : ℕ → List Token
  | 0 => []
  | n + 1 =>
      let previous := buildU n
      previous ++ [nextU previous n]

theorem buildU_length (n : ℕ) : (buildU n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [buildU, List.length_append, List.length_singleton, ih]

private theorem lookup_append_left {xs ys : List Token} {i : ℕ}
    (hi : i < xs.length) : (xs ++ ys)[i]? = xs[i]? := by
  have hib : i < (xs ++ ys).length := by simp only [List.length_append]; omega
  rw [List.getElem?_eq_getElem hib, List.getElem?_eq_getElem hi]
  exact congrArg some (List.getElem_append_left hi)

/-- Constructing later U entries leaves every earlier exact token intact. -/
theorem buildU_lookup_stable (m n i : ℕ) (hi : i < m) (hmn : m ≤ n) :
    (buildU n)[i]? = (buildU m)[i]? := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    change (buildU n ++ [nextU (buildU n) n])[i]? = (buildU m)[i]?
    rw [lookup_append_left (by rw [buildU_length]; omega)]
    exact ih

theorem buildU_last (i : ℕ) :
    (buildU (i + 1))[i]? = some (nextU (buildU i) i) := by
  change (buildU i ++ [nextU (buildU i) i])[i]? = some (nextU (buildU i) i)
  have hi : i < (buildU i ++ [nextU (buildU i) i]).length := by
    simp only [List.length_append, List.length_singleton, buildU_length]
    omega
  rw [List.getElem?_eq_getElem hi]
  apply congrArg some
  rw [List.getElem_append_right (by rw [buildU_length])]
  simp only [buildU_length, Nat.sub_self, List.getElem_cons_zero]

def canonicalU : List Token := buildU uCount

def canonicalNodePayload : SourceArrays := nodePayload canonicalU

def canonicalCells : List ℤ :=
  (List.range cellCount).map (fun k => sourceCell canonicalNodePayload k)

def canonicalScanPayload : SourceArrays :=
  ⟨canonicalU, canonicalCells, [], 0⟩

def canonicalSourceArrays : SourceArrays :=
  ⟨canonicalU, canonicalCells, [], sourceQueryMax canonicalScanPayload⟩

def canonicalQueryNumerator : ℤ := canonicalSourceArrays.queryMax

theorem canonical_U_length : canonicalSourceArrays.U.length = uCount :=
  buildU_length uCount

theorem canonical_cell_length : canonicalSourceArrays.cell.length = cellCount := by
  simp only [canonicalSourceArrays, canonicalCells, List.length_map, List.length_range]

theorem canonical_Uat_prefix (i j : ℕ) (hi : i ≤ uCount) (hj : j < i) :
    Uat canonicalSourceArrays j = Uat (nodePayload (buildU i)) j := by
  change ((buildU uCount)[j]?).getD ⟨0, 0⟩ = ((buildU i)[j]?).getD ⟨0, 0⟩
  rw [buildU_lookup_stable i uCount j hj hi]

theorem canonical_Uat_next (i : ℕ) (hi : i < uCount) :
    Uat canonicalSourceArrays i = nextU (buildU i) i := by
  change ((buildU uCount)[i]?).getD ⟨0, 0⟩ = nextU (buildU i) i
  rw [buildU_lookup_stable (i + 1) uCount i (by omega) (by omega), buildU_last]
  rfl

theorem sourceStep_eq_of_three (p q : SourceArrays) (i : ℕ)
    (hprev : Uat p (i - 1) = Uat q (i - 1))
    (hleft : Uat p (i - mesh - 1) = Uat q (i - mesh - 1))
    (hright : Uat p (i - mesh) = Uat q (i - mesh)) :
    sourceStep p i = sourceStep q i := by
  dsimp only [sourceStep]
  rw [hprev, hleft, hright]

theorem sourceCell_eq_of_U_eq (p q : SourceArrays) (hu : p.U = q.U) (i : ℕ) :
    sourceCell p i = sourceCell q i := by
  simp only [sourceCell, pointUpper, Uat, hu]

/-- The constructed canonical U has the literal original row equation,
with delayed nodes retested against the exact current source array. -/
theorem canonical_U_rows (i : Fin uCount) :
    Uat canonicalSourceArrays i.val =
      if i.val ≤ 2 * mesh then rational 1
      else if i.val ≤ 3 * mesh then sourceAdd (rational 1) (sourceSmallLog (logArg i.val))
      else sourceStep canonicalSourceArrays i.val := by
  rw [canonical_Uat_next i.val i.isLt]
  unfold nextU
  split_ifs with hfirst hsecond
  · rfl
  · rfl
  · have hm : 0 < mesh := by norm_num [mesh]
    apply sourceStep_eq_of_three
    · exact (canonical_Uat_prefix i.val (i.val - 1) i.isLt.le (by omega)).symm
    · exact (canonical_Uat_prefix i.val (i.val - mesh - 1) i.isLt.le (by omega)).symm
    · exact (canonical_Uat_prefix i.val (i.val - mesh) i.isLt.le (by omega)).symm

/-- The original canonical cell list contains EXACT sourceCell tokens,
without copying a generic rectangle-checker or recalculated envelope. -/
theorem canonical_cell_rows (i : Fin cellCount) :
    cellAt canonicalSourceArrays i.val = sourceCell canonicalSourceArrays i.val := by
  have hi : i.val < canonicalCells.length := by
    simp only [canonicalCells, List.length_map, List.length_range]
    exact i.isLt
  have he : canonicalCells[i.val]? = some (sourceCell canonicalNodePayload i.val) := by
    rw [List.getElem?_eq_getElem hi]
    apply congrArg some
    simp only [canonicalCells, List.getElem_map, List.getElem_range]
  change (canonicalCells[i.val]?).getD 0 = sourceCell canonicalSourceArrays i.val
  rw [he]
  exact sourceCell_eq_of_U_eq canonicalNodePayload canonicalSourceArrays rfl i.val

private theorem foldl_max_nonneg (xs : List ℤ) (a : ℤ) (ha : 0 ≤ a) :
    0 ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih (max a x) (ha.trans (le_max_left a x))

theorem canonical_query_equation :
    canonicalSourceArrays.queryMax = sourceQueryMax canonicalSourceArrays := rfl

theorem canonical_query_nonneg : 0 ≤ canonicalSourceArrays.queryMax :=
  foldl_max_nonneg _ 0 le_rfl

/-- The first finite guard is exactly the producer's positive divisor
integer test for its initial logarithm strip.  No omega value occurs. -/
def CanonicalLogGuards : Prop :=
  ∀ i : Fin uCount, 2 * mesh < i.val → i.val ≤ 3 * mesh →
    0 < (sourceSub (rational 1)
      (sourceMul (rational (logX (logArg i.val)))
        (rational (logX (logArg i.val))))).lo

/-- The other finite guard is the original integer cell sign. -/
def CanonicalCellSigns : Prop :=
  ∀ i : Fin cellCount, 0 ≤ sourceCell canonicalSourceArrays i.val

instance : Decidable CanonicalLogGuards := by
  unfold CanonicalLogGuards
  infer_instance

instance : Decidable CanonicalCellSigns := by
  unfold CanonicalCellSigns
  infer_instance

def canonicalArithmeticGuardCheck : Bool := decide (CanonicalLogGuards ∧ CanonicalCellSigns)

/-- All other clauses of SourceProducerValid are proved structurally,
leaving exactly the two original finite arithmetic guard obligations. -/
theorem canonical_valid_of_arithmetic_guards
    (hlog : CanonicalLogGuards) (hcells : CanonicalCellSigns) :
    SourceProducerValid canonicalSourceArrays := by
  refine ⟨canonical_U_length, canonical_cell_length, canonical_query_equation,
    canonical_query_nonneg, hlog, canonical_U_rows, ?_⟩
  intro i
  exact ⟨canonical_cell_rows i, by rw [canonical_cell_rows i]; exact hcells i⟩

theorem canonical_guard_check_sound (h : canonicalArithmeticGuardCheck = true) :
    SourceProducerValid canonicalSourceArrays :=
  (fun hh => canonical_valid_of_arithmetic_guards hh.1 hh.2)
    (of_decide_eq_true (show decide (CanonicalLogGuards ∧ CanonicalCellSigns) = true from h))

/-- Nodes are only an unused compatibility field, not a Python output.
The original three payload fields have a unique literal recipe. -/
def CanonicalPayloadMatches (p : SourceArrays) : Prop :=
  p.U = canonicalSourceArrays.U ∧ p.cell = canonicalSourceArrays.cell ∧
    p.queryMax = canonicalSourceArrays.queryMax

theorem original_producer_payload_unique (p : SourceArrays) (hp : SourceProducerValid p) :
    CanonicalPayloadMatches p := by
  have hrows := hp.2.2.2.2.2.1
  have hcrows := hp.2.2.2.2.2.2
  have hUat : ∀ i : ℕ, i < uCount → Uat p i = Uat canonicalSourceArrays i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hic
      have hpRow := hrows ⟨i, hic⟩
      have hcRow := canonical_U_rows ⟨i, hic⟩
      simp only [Fin.val_mk] at hpRow hcRow
      rw [hpRow, hcRow]
      split_ifs with hfirst hsecond
      · rfl
      · rfl
      · have hm : 0 < mesh := by norm_num [mesh]
        apply sourceStep_eq_of_three
        · exact ih (i - 1) (by omega) (by omega)
        · exact ih (i - mesh - 1) (by omega) (by omega)
        · exact ih (i - mesh) (by omega) (by omega)
  have hU : p.U = canonicalSourceArrays.U := by
    apply List.ext_getElem
    · exact hp.1.trans canonical_U_length.symm
    · intro i hip hic
      have hi : i < uCount := by rw [← hp.1]; exact hip
      have h := hUat i hi
      simpa only [Uat, List.getElem?_eq_getElem hip,
        List.getElem?_eq_getElem hic, Option.getD_some] using h
  have hcell : p.cell = canonicalSourceArrays.cell := by
    apply List.ext_getElem
    · exact hp.2.1.trans canonical_cell_length.symm
    · intro i hip hic
      have hi : i < cellCount := by rw [← hp.2.1]; exact hip
      have hpCell := (hcrows ⟨i, hi⟩).1
      have hcCell := canonical_cell_rows ⟨i, hi⟩
      simp only [Fin.val_mk] at hpCell hcCell
      have he : cellAt p i = cellAt canonicalSourceArrays i :=
        hpCell.trans ((sourceCell_eq_of_U_eq p canonicalSourceArrays hU i).trans hcCell.symm)
      simpa only [cellAt, List.getElem?_eq_getElem hip,
        List.getElem?_eq_getElem hic, Option.getD_some] using he
  refine ⟨hU, hcell, ?_⟩
  rw [hp.2.2.1, canonical_query_equation]
  simp only [sourceQueryMax, hcell]

end
end ImbalancedChen.OriginalPairedN48CanonicalArrays
