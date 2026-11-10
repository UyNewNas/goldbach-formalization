import ImbalancedChen.P4AOriginalNewFifthArchiveData
import ImbalancedChen.P4AOriginalNewFifthExclusion
import ImbalancedChen.P4AOriginalFull87CompleteSixthBound

/-! The common fourth history plus the old and disjoint new fifth owners.
Each added row carries its own archived selected mask and an actual decoded
mesh label. It passes both original support tests and both own-first tests.
All fields preceding the fifth level remain definitionally the original ones. -/
namespace ImbalancedChen.P4AOriginalNewFifthUnion
noncomputable section
open scoped Classical BigOperators
open P4AOriginalNewFifthArchiveData
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P1OriginalFifthAdoptedOwnerBank (adoptedOwners adoptedOwners_original_decoded adoptedOwners_selected_buffer)
open P1OriginalCoarseFifthContinuation (selectedFifthCells mem_selectedFifthCells)
open P1OriginalVariableFifthContinuation (FifthRow Label5 eligible gateCheck candidate)
open P1OriginalVariableFourthContinuation (finiteMax finiteMax_row_le finiteMax_le finiteMax_seed_le)
open P5OriginalCommonRefinedConstructor (OriginalData exponent4 exponent5 actualParent5)

abbrev original := P4AOriginalCompleteSixthChronology.data

def rowAt (i : Position) (q : ℕ) (j : Label5 (refinedMesh q)) : FifthRow (refinedMesh q) :=
  ⟨j, maskSlots 5 (rawRow i).mask.toNat⟩

def owners (i : Position) (e : ℚ) (q : ℕ) (a : ℝ) : Finset (Label5 (refinedMesh q)) :=
  (adoptedOwners (rawRow i) e q ((e : ℝ)/20) a).filter (fun j =>
    gateCheck 0 (refinedMesh q) (rowAt i q j) = true ∧
    gateCheck e (refinedMesh q) (rowAt i q j) = true)

def newLabels (e : ℚ) (q : ℕ) (a : ℝ) : Finset (Label5 (refinedMesh q)) :=
  Finset.univ.biUnion (fun i : Position => owners i e q a)

def newRows (e : ℚ) (q : ℕ) (a : ℝ) : Finset (FifthRow (refinedMesh q)) :=
  Finset.univ.biUnion (fun i : Position => (owners i e q a).image (rowAt i q))

def data (e : ℚ) (q : ℕ) (a : ℝ) : OriginalData :=
  { original e q a with
    J5 := (original e q a).J5 ∪ newLabels e q a
    rows5 := (original e q a).rows5 ∪ newRows e q a }

@[simp] theorem same_fourth (e : ℚ) (q : ℕ) (a N : ℝ) (pre : List ℕ) :
    exponent4 (data e q a) N pre = exponent4 (original e q a) N pre := rfl

theorem rowAt_decodes (i : Position) (e : ℚ) (q : ℕ) (a : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ owners i e q a) :
    rowAt i q j ∈ decodeFifthRows (rawRow i) (refinedMesh q) := by
  obtain ⟨r, hr, hcell⟩ := adoptedOwners_original_decoded _ _ _ _ _ _ (Finset.mem_filter.mp hj).1
  have hmask := decodeFifthRows_selected_eq _ _ r hr
  have heq : r = rowAt i q j := by
    cases r
    simp only [rowAt, FifthRow.mk.injEq] at *
    exact ⟨hcell,hmask⟩
  exact heq ▸ hr

theorem rowAt_eligible (i : Position) (e : ℚ) (q : ℕ) (a : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ owners i e q a)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) j) :
    eligible e ((e : ℝ)/20) (refinedMesh q) a (data e q a).J5 (rowAt i q j) t := by
  have ha := (Finset.mem_filter.mp hj).1
  have hs := (mem_selectedFifthCells _ _ _ _ _ _).mp (adoptedOwners_selected_buffer _ _ _ _ _ _ ha)
  have hJ : j ∈ (data e q a).J5 :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hj⟩)
  exact ⟨(mem_selectedFifthCells _ _ _ _ _ _).mpr ⟨hJ,hs.2⟩, (Finset.mem_filter.mp hj).2.2, ht⟩

/-- Enlarging J5 cannot activate an old row that lacked its original
label. Every source member of the old licensed rows already owns that label. -/
theorem old_row_eligible_iff (e : ℚ) (q : ℕ) (a : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ (original e q a).rows5) (t : Fin 5 → ℝ) :
    eligible e ((e : ℝ)/20) (refinedMesh q) a (data e q a).J5 r t ↔
      eligible e ((e : ℝ)/20) (refinedMesh q) a (original e q a).J5 r t := by
  obtain ⟨i, hi, hcell, _, _⟩ := P1HistoricalFifthCommonPolicyInputs.full_archive_licensed_rows_source
    P5OriginalFourthFifthSourceInputs.originalRows4 P5OriginalFourthFifthSourceInputs.originalAdmission4
    e q ((e : ℝ)/20) a r hr
  have hJ : r.cell ∈ (original e q a).J5 := Finset.mem_biUnion.mpr ⟨i,hi,hcell⟩
  have hJ' : r.cell ∈ (data e q a).J5 := Finset.mem_union_left _ hJ
  simp only [eligible, mem_selectedFifthCells, hJ, hJ', true_and]

/-- For every history the actual new maximum contains the entire old
maximum, including its own fourth ancestor. This compares exponents. -/
theorem original_le_union (e : ℚ) (q : ℕ) (a N : ℝ) (pre : List ℕ) :
    exponent5 (original e q a) N pre ≤ exponent5 (data e q a) N pre := by
  by_cases h : pre.length = 5
  · rw [exponent5, if_pos h, exponent5, if_pos h, same_fourth]
    apply finiteMax_le
    · exact finiteMax_seed_le _ _ _ _
    · intro r hr he
      exact finiteMax_row_le _ _ _ _ r (Finset.mem_union_left _ hr)
        ((old_row_eligible_iff e q a r hr _).mpr he)
  · simp only [exponent5, if_neg h, same_fourth, le_refl]

theorem new_candidate_le_union (i : Position) (e : ℚ) (q : ℕ) (a N : ℝ)
    (pre : List ℕ) (h5 : pre.length = 5) (j : Label5 (refinedMesh q))
    (hj : j ∈ owners i e q a)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) j) :
    P1OriginalFifthRawBoxSelectorEquivalence.rawCandidate (e : ℝ) (rawRow i)
      (primeHistoryLogCoordinates N 5 pre) ≤ exponent5 (data e q a) N pre := by
  have hr : rowAt i q j ∈ (data e q a).rows5 := Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩)
  rw [exponent5, if_pos h5, P1OriginalFifthRawBoxSelectorEquivalence.rawCandidate_eq_candidate]
  exact finiteMax_row_le _ _ _ _ (rowAt i q j) hr (rowAt_eligible i e q a j hj _ ht)

theorem union_eq_original_off_new (e : ℚ) (q : ℕ) (a N : ℝ) (pre : List ℕ)
    (hout : ∀ i : Position, primeHistoryLogCoordinates N 5 pre ∉ (rawRow i).originalBox) :
    exponent5 (data e q a) N pre = exponent5 (original e q a) N pre := by
  refine le_antisymm ?_ (original_le_union e q a N pre)
  by_cases h : pre.length = 5
  · rw [exponent5, if_pos h, exponent5, if_pos h, same_fourth]
    apply finiteMax_le
    · exact finiteMax_seed_le _ _ _ _
    · intro r hr he
      rcases Finset.mem_union.mp hr with hr | hn
      · exact finiteMax_row_le _ _ _ _ r hr ((old_row_eligible_iff e q a r hr _).mp he)
      · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hn
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact False.elim (hout i (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes i e q a j hj)
          _ he.2.2).2.2.2)
  · simp only [exponent5, if_neg h, same_fourth, le_refl]

/-- The existing all-subset bound is generic in J5 and rows5.
It holds for this actual union at all 87 original source positions. -/
theorem union_fifth_le_original_comparison (e : ℚ) (q : ℕ) (a N : ℝ) (he : 0 ≤ e)
    (pre : List ℕ) (hlen : pre.length = 8) (c : P4AOriginalFull87SourceDictionary.Cell)
    (h : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (hs : P1ThirdFallbackSupport.supported ((original e q a).e : ℝ) (original e q a).chi
      (original e q a).m (original e q a).omega N (rosserAncestor 3 pre)) :
    actualParent5 (data e q a) N (rosserAncestor 6 pre) ≤
      P4AOriginalFull87SourceDictionary.comparison c (primeHistoryLogCoordinates N 8 pre) :=
  P4AOriginalFull87CompleteSixthBound.supported_fifth_le_comparison
    (data e q a) N he pre hlen c h hs

end
end ImbalancedChen.P4AOriginalNewFifthUnion

