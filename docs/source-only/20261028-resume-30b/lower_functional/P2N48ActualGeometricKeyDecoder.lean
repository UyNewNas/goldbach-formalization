import ImbalancedChen.P2N48SelectedFunctionalRemainder

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The original producer rectangles(48, "U11full") enumerates ix first,
then combinations_with_replacement(range(48), 3) in lexicographic
ascending order and reverses the small tuple into (iy, iz, iw).
The 249900 low-band rows precede its high band; each ix has 19600
small triples. The finite rank below records precisely this source order.

Two CLOSED kernel-decision proof commands bind the literal extracted
rows to that decoder and check strict adjacency of their original source
ordinals. These commands have NOT been executed. No decision result or
successful compilation is being reported by the author.

The remaining proofs derive geometric-key injectivity and instantiate
the prior exact row-plus-uncovered-cost identities. Neither the old Q80
row cost nor the uncovered domain's upper certificate is supplied here.
-/

namespace ImbalancedChen.P2N48ActualGeometricKeyDecoder

noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder
open OriginalPairedN48ArchiveData

abbrev GeometricKey := Fin 2 × Fin 48 × Fin 48 × Fin 48 × Fin 48

/-- Lexicographic rank of the original ascending triple (iw, iz, iy).
The first sum counts earlier iw blocks; the second counts earlier iz
blocks inside this iw; the last term counts the final iy positions.
Tied indices are present, exactly as in combinations_with_replacement. -/
def tripleLexRank (iy iz iw : Fin 48) : ℕ :=
  (∑ w ∈ Finset.range iw.val, Nat.choose (49 - w) 2) +
    (∑ z ∈ Finset.Ico iw.val iz.val, 48 - z) +
      (iy.val - iz.val)

/-- Zero-based source ordinal of an original high-band n48 key.
The actual row check below also requires term=1 and weakly ordered
small indices; this decoder is not licensed on an arbitrary low key. -/
def highOrdinalOfKey (k : GeometricKey) : ℕ :=
  249900 + 19600 * k.2.1.val +
    tripleLexRank k.2.2.1 k.2.2.2.1 k.2.2.2.2

def HighRowDecoded (r : SourceRow) : Prop :=
  r.term.val = 1 ∧ r.iw.val ≤ r.iz.val ∧ r.iz.val ≤ r.iy.val ∧
    r.ordinal = highOrdinalOfKey (rowKey r)

instance (r : SourceRow) : Decidable (HighRowDecoded r) :=
  inferInstanceAs (Decidable (r.term.val = 1 ∧ r.iw.val ≤ r.iz.val ∧
    r.iz.val ≤ r.iy.val ∧ r.ordinal = highOrdinalOfKey (rowKey r)))

/-- This predicate scans the actual source rows, with no aggregate-floor,
interval or numerical approximation involved. -/
def highDecoderCheck (rows : List SourceRow) : Bool :=
  rows.all (fun r => decide (HighRowDecoded r))

/-- Only adjacent source ordinals are compared. Transitivity below derives
the all-pairs property; no quadratic all-pairs numerical check is needed. -/
def adjacentOrdinalCheck : List SourceRow → Bool
  | [] => true
  | [_] => true
  | r :: s :: rows => decide (r.ordinal < s.ordinal) &&
      adjacentOrdinalCheck (s :: rows)

/-- CLOSED FINITE PROOF SOURCE, NOT EXECUTED. This checks the exact
archived row literals against the original source-rank formula. -/
theorem rawSelectedRows_highDecoderCheck :
    highDecoderCheck rawSelectedRows = true := by
  decide +kernel

/-- CLOSED FINITE PROOF SOURCE, NOT EXECUTED. Literal source ordinals
must remain in strict original enumeration order after the crop. -/
theorem rawSelectedRows_adjacentOrdinalCheck :
    adjacentOrdinalCheck rawSelectedRows = true := by
  decide +kernel

theorem decoded_of_mem_rawSelectedRows (r : SourceRow)
    (hr : r ∈ rawSelectedRows) : HighRowDecoded r := by
  have h := List.all_eq_true.mp rawSelectedRows_highDecoderCheck r hr
  exact of_decide_eq_true h

private theorem pairwise_ordinals_of_adjacent (rows : List SourceRow)
    (h : adjacentOrdinalCheck rows = true) :
    rows.Pairwise (fun r s => r.ordinal < s.ordinal) := by
  revert h
  induction rows with
  | nil =>
      intro h
      exact List.Pairwise.nil
  | cons r rows ih =>
      intro h
      cases rows with
      | nil => simp
      | cons s rows =>
          have hsplit : decide (r.ordinal < s.ordinal) = true ∧
              adjacentOrdinalCheck (s :: rows) = true := by
            simpa only [adjacentOrdinalCheck, Bool.and_eq_true] using h
          have hrs : r.ordinal < s.ordinal := of_decide_eq_true hsplit.1
          have htail := ih hsplit.2
          apply List.pairwise_cons.mpr
          refine ⟨?_, htail⟩
          intro t ht
          rcases List.mem_cons.mp ht with hts | htrows
          · simpa only [hts] using hrs
          · exact hrs.trans ((List.pairwise_cons.mp htail).1 t htrows)

private theorem ordinal_injective_of_pairwise (rows : List SourceRow)
    (hrows : rows.Pairwise (fun r s => r.ordinal < s.ordinal)) :
    ∀ r ∈ rows, ∀ s ∈ rows, r.ordinal = s.ordinal → r = s := by
  revert hrows
  induction rows with
  | nil =>
      intro hrows
      simp
  | cons a rows ih =>
      intro hrows
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hrows
      intro r hr s hs heq
      rcases List.mem_cons.mp hr with hra | hrtail
      · subst r
        rcases List.mem_cons.mp hs with hsa | hstail
        · exact hsa.symm
        · exact False.elim ((ne_of_lt (hhead s hstail)) heq)
      · rcases List.mem_cons.mp hs with hsa | hstail
        · subst s
          exact False.elim ((ne_of_lt (hhead r hrtail)) heq.symm)
        · exact ih htail r hrtail s hstail heq

/-- Unlike ordinal NoDup by itself, this proof uses the checked original
rank relation: equal geometric keys force equal original ordinals. -/
theorem rawSelectedRows_rowKey_injective (r s : SourceRow)
    (hr : r ∈ rawSelectedRows) (hs : s ∈ rawSelectedRows)
    (hkey : rowKey r = rowKey s) : r = s := by
  have hdr := decoded_of_mem_rawSelectedRows r hr
  have hds := decoded_of_mem_rawSelectedRows s hs
  have hord : r.ordinal = s.ordinal := by
    calc
      r.ordinal = highOrdinalOfKey (rowKey r) := hdr.2.2.2
      _ = highOrdinalOfKey (rowKey s) := congrArg highOrdinalOfKey hkey
      _ = s.ordinal := hds.2.2.2.symm
  exact ordinal_injective_of_pairwise rawSelectedRows
    (pairwise_ordinals_of_adjacent rawSelectedRows rawSelectedRows_adjacentOrdinalCheck)
    r hr s hs hord

/-- The actual method-zero crop inherits the proved geometric ownership;
there is no new row selection and no assumption hkeys at the consumer. -/
theorem actualRetainedRows_distinctGeometricKeys :
    DistinctGeometricKeys actualRetainedRows := by
  intro r hr s hs hkey
  exact rawSelectedRows_rowKey_injective r s
    (actualRetainedRows_policy r hr).1
    (actualRetainedRows_policy s hs).1 hkey

/-- The first batch's exact whole-domain identity now has its ACTUAL
archive geometric ownership supplied by the two closed finite proofs. -/
theorem actual_selected_coefficient_eq_rows_add_uncovered :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient =
      (∑ r ∈ actualRetainedRows,
        parentCost ImbalancedChen.currentK (selectedParent r actualMask)) +
          uncoveredCost actualRetainedRows :=
  actualSelectedCoefficient_eq_rows_add_uncovered actualRetainedRows
    actualRetainedRows_distinctGeometricKeys

/-- Only the original row mass and switched/Q80 certificates remain as
inputs to this recost; uncoveredCost is kept explicitly in the full term. -/
theorem actual_selected_functional_upper_with_decoded_keys
    (hMass : ∀ r ∈ actualRetainedRows,
      massLower r ≤ parentUnweightedMass (fullParent r))
    (hOld : ∀ r ∈ actualRetainedRows,
      r.method = 0 → r.ordinal ∉ rawPriorityOrdinals.toFinset →
        anchorK * parentSwitchedMass (fullParent r) ≤
          savedParent r (parentUnweightedMass (fullParent r))) :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient ≤
      (∑ r ∈ actualRetainedRows,
        savedParent r (parentUnweightedMass (fullParent r))) -
      (∑ r ∈ actualRetainedRows, rowGainLower r) + uncoveredCost actualRetainedRows :=
  actual_selected_functional_upper_with_remainder
    actualRetainedRows_distinctGeometricKeys hMass hOld

end
end ImbalancedChen.P2N48ActualGeometricKeyDecoder
