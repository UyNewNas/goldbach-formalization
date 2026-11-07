"""Generate Lean proof text only. Does not read or evaluate archive payloads."""
from pathlib import Path

here = Path(__file__).resolve().parent
header = '''import ImbalancedChen.P5OriginalTaylorRationalData
import ImbalancedChen.P5FullStoredParentSameOwnerBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
72 closed finite bodies pair the original 143 typed blocks with the
independent 72 stored old/new blocks IN THEIR ORIGINAL ORDER.  Each
body covers 4096 original parents, except the final 1817.  They reconstruct
the original rational Taylor expression independently of the saved floor.
All bodies are UNEVALUATED.  No integral licence, oldfloor hypothesis,
new axiom, or numerical-replay output is a premise of the exports below.
-/
namespace ImbalancedChen.P5OriginalStoredOldArchiveBinding
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthTypedArchiveShape P5SubdivisionStoredParentTypes
open P5FullStoredParentSameOwnerBinding P5OriginalParentJensenRawFields
open P5OriginalTaylorRationalData

def RowBinding (raw : FifthWireRow) (saved : StoredParent) : Prop :=
  0 ≤ originalParentJensenFloorZ raw ∧
  saved.oldQ80 = max (originalParentJensenFloorZ raw) (availableTaylorFloorZ raw)

instance (raw : FifthWireRow) (saved : StoredParent) : Decidable (RowBinding raw saved) := by
  unfold RowBinding
  infer_instance

'''
blocks=[]
raws=[]
for b in range(72):
    a=f'Data.P1HistoricalFifthSavedDataBlock{2*b:03d}.rows.toList'
    if 2*b+1<143:
        a=f'({a} ++ Data.P1HistoricalFifthSavedDataBlock{2*b+1:03d}.rows.toList)'
    raws.append(a)
    blocks.append(f'''set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem block{b:03d}_stored_old_binding :
    List.Forall₂ RowBinding
      {a}
      Data.P5SubdivisionStoredBlock{b:03d}.rows.toList := by
  decide

''')
aggregate='''theorem all_original_stored_old_bindings :
    List.Forall₂ RowBinding
      Data.P1HistoricalFifthSavedTableData.rows.toList
      P5SubdivisionStoredParentArchive.rows.toList := by
  rw [rows_toList_order, block_order]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [P5SubdivisionStoredParentArchive.rows, Array.toList_append]
  have h := '''
expression='block071_stored_old_binding'
for b in reversed(range(71)):
    expression=f'(block{b:03d}_stored_old_binding.append {expression})'
aggregate+=expression+'''
  simpa only [List.append_assoc] using h

/-- Positional extraction preserves source multiplicity and does not use
row-value equality or a Finset deduplication. -/
private theorem forall₂_get {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (n : ℕ) (hx : n < xs.length) (hy : n < ys.length) :
    R xs[n] ys[n] := by
  induction h generalizing n with
  | nil => simp at hx
  | @cons x y xs ys hxy htail ih =>
      cases n with
      | zero => exact hxy
      | succ n => exact ih n (by simpa using hx) (by simpa using hy)

theorem original_stored_old_binding (i : ArchiveIndex) :
    0 ≤ originalParentJensenFloorZ (archiveRow i) ∧
    (storedAt i).oldQ80 = max (originalParentJensenFloorZ (archiveRow i))
      (availableTaylorFloorZ (archiveRow i)) := by
  have hy : i.val < P5SubdivisionStoredParentArchive.rows.toList.length := by
    simpa only [Array.length_toList, P5SubdivisionStoredParentArchive.rows_size]
      using archiveIndex_lt i
  have h := forall₂_get all_original_stored_old_bindings i.val i.isLt hy
  simpa only [RowBinding, archiveRow, storedAt, Array.getElem_toList] using h

/-- Exact old saved numerator, before division by the unchanged Q80 scale. -/
theorem original_stored_old_eq_max (i : ArchiveIndex) :
    (storedAt i).oldQ80 = max (originalParentJensenFloorZ (archiveRow i))
      (availableTaylorFloorZ (archiveRow i)) := (original_stored_old_binding i).2

/-- The strict Taylor branch supplies its ACTUAL primitive source data.
No caller supplies BranchFacts, ranges, midpoint values or a floor licence. -/
theorem strict_stored_taylor_available (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    available (archiveRow i) := by
  by_contra hn
  have h := original_stored_old_eq_max i
  rw [availableTaylorFloorZ, if_neg hn,
    max_eq_left (original_stored_old_binding i).1] at h
  omega

theorem strict_stored_taylor_primitive_facts (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    TaylorFiniteFacts (archiveRow i) := (strict_stored_taylor_available i hstrict).1

theorem strict_stored_taylor_branchFacts (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    P5OriginalTaylorAffineBranchBinding.BranchFacts (archiveRow i)
      (newSide (archiveRow i)) (oldSides (archiveRow i)) (selected (archiveRow i)) :=
  available_branchFacts _ (strict_stored_taylor_available i hstrict)

/-- When the saved old branch is Taylor, its numerator is the floor of
the independent original rational bound, rather than an invented defect. -/
theorem strict_stored_old_eq_original_taylor_floor (i : ArchiveIndex)
    (hstrict : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80) :
    (storedAt i).oldQ80 = taylorFloorZ (archiveRow i) := by
  have ha := strict_stored_taylor_available i hstrict
  have h := original_stored_old_eq_max i
  rw [availableTaylorFloorZ, if_pos ha] at h
  have hj : originalParentJensenFloorZ (archiveRow i) < taylorFloorZ (archiveRow i) := by
    by_contra hn
    rw [max_eq_left (le_of_not_gt hn)] at h
    omega
  simpa only [max_eq_right hj.le] using h

end ImbalancedChen.P5OriginalStoredOldArchiveBinding
'''
(here/'P5OriginalStoredOldArchiveBinding.lean').write_text(
    header+''.join(blocks)+aggregate,encoding='utf-8',newline='\n')
print('Wrote source text; 72 finite bodies remain UNEVALUATED.')
