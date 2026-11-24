import ImbalancedChen.P4AOriginalNewFifthArchiveData
import ImbalancedChen.P4AOriginalNewFifthBoxIntegral
import ImbalancedChen.P5OriginalHistoryGapCorner

/-! Numeric tests read only actual original row fields. One third component
must beat the H3 test throughout the box. The two selected fifth tent
planes must beat every support gate. The integral comparison is proved
separately from these rational checks. -/
namespace ImbalancedChen.P4AOriginalNewFifthArchive
open P4AOriginalNewFifthArchiveData P4AOriginalNewFifthArchiveReader
open P4AOriginalNewFifthBoxIntegral
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthCorrelatedRawBoxGates
open scoped BigOperators

def Geometry (r : FifthWireRow) : Prop :=
  (∀ i, 0 ≤ r.lo i) ∧ (∀ i, 1/50 ≤ r.lower i) ∧ r.upper 0 ≤ 39/200 ∧
    (∀ j : Fin 4, r.upper j.succ ≤ r.lower j.castSucc) ∧
    17 ≤ r.mask ∧ r.mask ≤ 31 ∧ 0 < r.ratioB ∧ 0 < r.vertexGapSum ∧
    correlatedRawBoxGateCheck 0 r = true ∧ 1/1600 ≤ gateMarginQ 0 r ∧
    1/1600 ≤ P5OriginalHistoryGapCorner.rawThirdGapQ r

instance (r : FifthWireRow) : Decidable (Geometry r) := by
  unfold Geometry
  infer_instance

def CheckRow (g : ℕ) (x : ℕ × ℕ) : Prop :=
  (wire x).grid = (g : ℤ) ∧ saved? x = some (saved x) ∧ 0 < saved x ∧
    Geometry (wire x) ∧ RowFacts (wire x) (saved x)

instance (g : ℕ) (x : ℕ × ℕ) : Decidable (CheckRow g x) := by unfold CheckRow; infer_instance

def Checked (b : BlockIndex) : Prop :=
  (block b).cellsHeader = expectedHeader (count b) false ∧
  (block b).floorsHeader = expectedHeader (count b) true ∧
  (block b).words.size = count b ∧ (block b).words.total saved = floorSum b ∧
  (block b).words.all (fun x => decide (CheckRow (grid b) x)) = true

instance (b : BlockIndex) : Decidable (Checked b) := by unfold Checked; infer_instance


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0000 : Checked (false,0) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0001 : Checked (false,1) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0002 : Checked (false,2) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0003 : Checked (false,3) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0004 : Checked (false,4) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0005 : Checked (false,5) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0006 : Checked (false,6) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0007 : Checked (false,7) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0008 : Checked (false,8) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0009 : Checked (false,9) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0010 : Checked (false,10) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0011 : Checked (false,11) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0012 : Checked (false,12) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0013 : Checked (false,13) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0014 : Checked (false,14) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0015 : Checked (false,15) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0016 : Checked (false,16) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0017 : Checked (false,17) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0018 : Checked (false,18) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0019 : Checked (false,19) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0020 : Checked (false,20) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0021 : Checked (false,21) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0022 : Checked (false,22) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0023 : Checked (false,23) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0024 : Checked (false,24) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0025 : Checked (false,25) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0026 : Checked (false,26) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0027 : Checked (false,27) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0028 : Checked (false,28) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0029 : Checked (false,29) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0030 : Checked (false,30) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0031 : Checked (false,31) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0032 : Checked (false,32) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0033 : Checked (false,33) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0034 : Checked (false,34) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0035 : Checked (false,35) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0036 : Checked (false,36) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0037 : Checked (false,37) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0038 : Checked (false,38) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0039 : Checked (false,39) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0040 : Checked (false,40) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0041 : Checked (false,41) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0042 : Checked (false,42) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0043 : Checked (false,43) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0044 : Checked (false,44) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0045 : Checked (false,45) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyC0046 : Checked (false,46) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0000 : Checked (true,0) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0001 : Checked (true,1) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0002 : Checked (true,2) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0003 : Checked (true,3) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0004 : Checked (true,4) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0005 : Checked (true,5) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0006 : Checked (true,6) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0007 : Checked (true,7) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0008 : Checked (true,8) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0009 : Checked (true,9) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0010 : Checked (true,10) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0011 : Checked (true,11) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0012 : Checked (true,12) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0013 : Checked (true,13) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0014 : Checked (true,14) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0015 : Checked (true,15) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0016 : Checked (true,16) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0017 : Checked (true,17) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0018 : Checked (true,18) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0019 : Checked (true,19) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0020 : Checked (true,20) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0021 : Checked (true,21) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0022 : Checked (true,22) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0023 : Checked (true,23) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0024 : Checked (true,24) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0025 : Checked (true,25) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0026 : Checked (true,26) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0027 : Checked (true,27) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0028 : Checked (true,28) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0029 : Checked (true,29) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0030 : Checked (true,30) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0031 : Checked (true,31) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0032 : Checked (true,32) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0033 : Checked (true,33) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0034 : Checked (true,34) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0035 : Checked (true,35) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0036 : Checked (true,36) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0037 : Checked (true,37) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0038 : Checked (true,38) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0039 : Checked (true,39) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0040 : Checked (true,40) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0041 : Checked (true,41) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0042 : Checked (true,42) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0043 : Checked (true,43) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0044 : Checked (true,44) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0045 : Checked (true,45) := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bodyF0046 : Checked (true,46) := by decide

theorem all_blocks (b : BlockIndex) : Checked b := by
  rcases b with ⟨fine,k⟩
  cases fine
  · fin_cases k
    · exact bodyC0000
    · exact bodyC0001
    · exact bodyC0002
    · exact bodyC0003
    · exact bodyC0004
    · exact bodyC0005
    · exact bodyC0006
    · exact bodyC0007
    · exact bodyC0008
    · exact bodyC0009
    · exact bodyC0010
    · exact bodyC0011
    · exact bodyC0012
    · exact bodyC0013
    · exact bodyC0014
    · exact bodyC0015
    · exact bodyC0016
    · exact bodyC0017
    · exact bodyC0018
    · exact bodyC0019
    · exact bodyC0020
    · exact bodyC0021
    · exact bodyC0022
    · exact bodyC0023
    · exact bodyC0024
    · exact bodyC0025
    · exact bodyC0026
    · exact bodyC0027
    · exact bodyC0028
    · exact bodyC0029
    · exact bodyC0030
    · exact bodyC0031
    · exact bodyC0032
    · exact bodyC0033
    · exact bodyC0034
    · exact bodyC0035
    · exact bodyC0036
    · exact bodyC0037
    · exact bodyC0038
    · exact bodyC0039
    · exact bodyC0040
    · exact bodyC0041
    · exact bodyC0042
    · exact bodyC0043
    · exact bodyC0044
    · exact bodyC0045
    · exact bodyC0046
  · fin_cases k
    · exact bodyF0000
    · exact bodyF0001
    · exact bodyF0002
    · exact bodyF0003
    · exact bodyF0004
    · exact bodyF0005
    · exact bodyF0006
    · exact bodyF0007
    · exact bodyF0008
    · exact bodyF0009
    · exact bodyF0010
    · exact bodyF0011
    · exact bodyF0012
    · exact bodyF0013
    · exact bodyF0014
    · exact bodyF0015
    · exact bodyF0016
    · exact bodyF0017
    · exact bodyF0018
    · exact bodyF0019
    · exact bodyF0020
    · exact bodyF0021
    · exact bodyF0022
    · exact bodyF0023
    · exact bodyF0024
    · exact bodyF0025
    · exact bodyF0026
    · exact bodyF0027
    · exact bodyF0028
    · exact bodyF0029
    · exact bodyF0030
    · exact bodyF0031
    · exact bodyF0032
    · exact bodyF0033
    · exact bodyF0034
    · exact bodyF0035
    · exact bodyF0036
    · exact bodyF0037
    · exact bodyF0038
    · exact bodyF0039
    · exact bodyF0040
    · exact bodyF0041
    · exact bodyF0042
    · exact bodyF0043
    · exact bodyF0044
    · exact bodyF0045
    · exact bodyF0046

theorem position_checks (i : Position) : CheckRow (grid i.1) (packed i) :=
  of_decide_eq_true ((block i.1).words.all_spec _ (all_blocks i.1).2.2.2.2 _
    (List.getElem_mem i.2.isLt))

theorem geometry (i : Position) : Geometry (rawRow i) := (position_checks i).2.2.2.1
theorem facts (i : Position) : RowFacts (rawRow i) (floorNumerator i) := (position_checks i).2.2.2.2
theorem row_grid (i : Position) : (rawRow i).grid = (grid i.1 : ℤ) := (position_checks i).1

private theorem indexed_list_sum {α : Type*} [AddCommMonoid α] (xs : List (ℕ × ℕ))
    (f : ℕ × ℕ → α) : (∑ i : Fin xs.length, f xs[i.val]) = (xs.map f).sum := by
  rw [← List.sum_ofFn]
  have h : List.ofFn (fun i : Fin xs.length => xs[i.val]) = xs := List.ofFn_getElem
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (fun ys : List (ℕ × ℕ) => (ys.map f).sum) h

theorem block_floor_sum (b : BlockIndex) :
    (∑ j : Fin (block b).words.list.length, floorNumerator ⟨b,j⟩) = floorSum b := by
  change (∑ j : Fin _, saved (block b).words.list[j.val]) = _
  rw [indexed_list_sum, Words.sum_list]
  exact (all_blocks b).2.2.2.1

set_option maxRecDepth 32768 in
theorem exact_counts : (∑ k : Fin 47, count (false,k)) = 43236 ∧
    (∑ k : Fin 47, count (true,k)) = 1720184 := by decide

set_option maxRecDepth 32768 in
theorem original_block_totals : (∑ b : BlockIndex, floorSum b) = 1648717268323516459667 := by decide

theorem original_sum_Q80 : (∑ i : Position, floorNumerator i) = 1648717268323516459667 := by
  rw [Fintype.sum_sigma]
  simpa only [block_floor_sum] using original_block_totals

noncomputable section
open MeasureTheory
open P1OriginalFifthActualB13IntegralError (positiveKernel)

def literalIntegral (i : Position) : ℝ := ∫ t in (rawRow i).originalBox, positiveKernel (rawRow i) 0 t

/-- Exact G3 from every position in the 94 actual arrays. Each
summand is the physical-coordinate integral on that position's box,
before transferring to the mesh and its signed arithmetic mean. -/
theorem original_floor_le_full_sum :
    (1648717268323516459667 : ℝ)/2^80 ≤ ∑ i : Position, literalIntegral i := by
  calc
    (1648717268323516459667 : ℝ)/2^80 = (∑ i : Position, (floorNumerator i : ℝ))/2^80 := by
      exact congrArg (fun z : ℝ => z / 2^80)
        (by exact_mod_cast original_sum_Q80.symm)
    _ = ∑ i : Position, (floorNumerator i : ℝ)/2^80 := Finset.sum_div _ _ _
    _ ≤ ∑ i : Position, literalIntegral i := Finset.sum_le_sum (fun i _ =>
      saved_floor_le_literal_integral (rawRow i) (floorNumerator i) (facts i))

end
end ImbalancedChen.P4AOriginalNewFifthArchive
