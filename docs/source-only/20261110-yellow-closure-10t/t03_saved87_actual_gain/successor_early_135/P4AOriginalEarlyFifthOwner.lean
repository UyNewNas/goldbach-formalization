import ImbalancedChen.P4AOriginalEarlyFourthAlignedOwner
import ImbalancedChen.P4AOriginalNewFifthMean
import ImbalancedChen.P4AOriginalOrderedFifthOwner

namespace ImbalancedChen.P4AOriginalEarlyFifthOwner
noncomputable section
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P1HistoricalFifthIndexedOwnerArchive (archiveRow licensedIndex_geometry)
open P1HistoricalFifthCommonPolicyInputs (full_archive_licensed_rows_source)
open P5OriginalFourthFifthSourceInputs (originalRows4 originalAdmission4)
open P4AOriginalNewFifthUnion (data rowAt_decodes old_row_eligible_iff)
open P4AOriginalNewFifthArchiveData P4AOriginalNewFifthArchive
open P1OriginalVariableFifthContinuation (FifthRow eligible)
open P4AOriginalOrderedThirdFullPolicy (current prior root_on_old_owner)
open P4AOriginalOrderedSixthStages (orderedFifth)
open P4AOriginalFull87DataPolicy (fifthPolicy)

/-- The actual old and new row banks both have a positive lower edge
in every coordinate. This bound is independent of the historical cutoff. -/
theorem eligible_coordinate_floor (e : ℚ) (q : ℕ) (a : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r∈(data e q a).rows5) (t : Fin 5→ℝ)
    (he : eligible e ((e:ℝ)/20) (refinedMesh q) a (data e q a).J5 r t) :
    ∀ i, 1/400≤t i := by
  rcases Finset.mem_union.mp hr with old | new
  · obtain ⟨i,hi,_,_,hd⟩ := full_archive_licensed_rows_source originalRows4 originalAdmission4
      e q ((e:ℝ)/20) a r old
    have hg := licensedIndex_geometry i hi
    have hb := (decodeFifthRows_source_geometry (archiveRow i) _ r hd t he.2.2).2.2.2
    intro j
    apply le_trans _ (hb j).1
    have H : (1:ℚ) ≤ ((archiveRow i).lo j:ℚ) := by exact_mod_cast hg.2.2.1 j
    have hQ : (1:ℚ)/400 ≤ (archiveRow i).lower j := by
      unfold FifthWireRow.lower
      rw [hg.1]
      simpa only [Int.cast_ofNat] using div_le_div_of_nonneg_right H (by norm_num : (0:ℚ)≤400)
    exact_mod_cast hQ
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp new
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have hb := (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes i e q a j hj) t he.2.2).2.2.2
    intro l
    have hR : (1/50:ℝ)≤((rawRow i).lower l:ℝ) := by exact_mod_cast (geometry i).2.1 l
    exact (by norm_num : (1/400:ℝ)≤1/50).trans (hR.trans (hb l).1)

/-- Whole ordered third owner, complete protected old-plus-new fifth
decision, and all five compact coordinates for the same target word. -/
theorem actual_eligible_owner (n : ℕ) {e : ℚ} (he : 0≤(e:ℝ)) (q : ℕ)
    {a omega N : ℝ} (hwa : omega≤a) (hN : 1<N) (p : List ℕ) (hl : p.length=5)
    (hp : ∀ x∈p,0<x) (r : FifthRow (refinedMesh q)) (hr : r∈(data e q a).rows5)
    (H : eligible e ((e:ℝ)/20) (refinedMesh q) a (data e q a).J5 r
      (primeHistoryLogCoordinates N 5 p)) :
    let d := data e q a
    let t := primeHistoryLogCoordinates N 5 p
    t 0<VariableEnvelope.mu ∧ (∀ i,1/400≤t i) ∧
      current d omega N p=prior d N p ∧
      ∀ b,orderedFifth n d omega N b p=fifthPolicy n d N b p := by
  exact ⟨P4AOriginalNewFifthMean.eligible_first_lt_mu e q a r hr _ H,
    eligible_coordinate_floor e q a r hr _ H,
    root_on_old_owner he hN.le hwa (P4AOrderedThirdFifthOwnersAndTail.fifth_owner
      (d:=data e q a) hN hl hp H),fun b => P4AOriginalOrderedFifthOwner.fifth_on_owner n
      (data e q a) he hN.le hwa (P4AOrderedThirdFifthOwnersAndTail.fifth_owner hN hl hp H) b⟩

end
end ImbalancedChen.P4AOriginalEarlyFifthOwner
