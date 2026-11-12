import ImbalancedChen.P4AOriginalSavedSixthOwnCaps
import ImbalancedChen.P4AOriginalOrderedThirdFullPolicy

/-! Arithmetic admission of each literal saved sixth row, with the fifth
parent evaluated in its own bank. The historical owner is read at its actual
third ancestor. Grid and square facts come from the original 632104 rows. -/
namespace ImbalancedChen.P1OriginalSavedRowsActualAdmission
noncomputable section
open scoped Classical
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalSavedSixthHistoricalOwner
open P4AOriginalSavedSixthArchive (Row oldUpper endpoint)
open P4AOriginalSavedSixthPlanes (box)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalNewFifthCoverage (Schedule)
open P4AOriginalSavedSixthPrimeMean (bounds)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4AOriginalFull87HistoryCore (width)

/-- The aligned historical label and its level do not depend on the rough
cutoff once its actual third prime passes it. The original saved boxes have
third coordinate at least 1/50; the original schedule allows a ≤ 1/100. -/
theorem row_owner (i : Row) {e : ℚ} {q : ℕ} (hs : Schedule e q 0)
    {a : ℝ} (ha : a ≤ 1/100) {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ)
    (hp : ∀ j, 0 < p j) (ht : actualPrimeTupleLog N p ∈ box i) :
    Owner (P4AOriginalCompleteSixthChronology.data e q a) N p ∧
    Owner (P4AOriginalNewFifthUnion.data e q a) N p := by
  let d := P4AOriginalCompleteSixthChronology.data e q a
  let d0 := P4AOriginalNewFifthUnion.data e q 0
  have h0 : Owner d0 N p := actual_owner i hs hN p hp ht
  obtain ⟨j,hj,hcell⟩ := mesh_owner i hs ht
  rw [← triple_log] at hcell
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have hrough : (N:ℝ)^a ≤ (p 2:ℝ) := by
    rw [← actualPrimeTupleLog_rpow hN p hp 2]
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    linarith only [ha,(bounds i ht 2).1]
  have hsup : P1ThirdFallbackSupport.supported (e:ℝ) ((e:ℝ)/20)
      (refinedMesh q) a (N:ℝ) (rosserAncestor 3 (pre p)) := by
    rw [ancestor_three]
    exact (P1ThirdFallbackSupport.supported_triple _ _ _ _ _ _ _ _).mpr
      ⟨hrough,j,hj,hcell⟩
  have hsup0 : P1ThirdFallbackSupport.supported (e:ℝ) ((e:ℝ)/20)
      (refinedMesh q) 0 (N:ℝ) (rosserAncestor 3 (pre p)) := h0.active.2
  have hseed : originalSeed d (N:ℝ) (pre p) = originalSeed d0 (N:ℝ) (pre p) := by
    change P1CoarseFirstCubeFallbackMargin.effectiveExponent (e:ℝ) ((e:ℝ)/20)
        (refinedMesh q) a (N:ℝ) (rosserAncestor 3 (pre p)) =
      P1CoarseFirstCubeFallbackMargin.effectiveExponent (e:ℝ) ((e:ℝ)/20)
        (refinedMesh q) 0 (N:ℝ) (rosserAncestor 3 (pre p))
    simp only [P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hsup,if_pos hsup0]
  have hs' := third_eq_seed d N p (ordered i ht).2.2.2
  have hr : root d N p = root d0 N p := hs'.trans (hseed.trans h0.seed.symm)
  have hd : Owner d N p := ⟨⟨h0.active.1,hsup⟩,h0.stop,hs',
    hr.symm ▸ h0.initial,hr.symm ▸ h0.first,hr.symm ▸ h0.third,hr.symm ▸ h0.fifth,hr.symm ▸ h0.upper⟩
  exact ⟨hd,⟨hd.active,hd.stop,hd.seed,hd.initial,hd.first,hd.third,hd.fifth,hd.upper⟩⟩

private theorem accepted_of_source {d : OriginalData} (i : Row) (he : 0 ≤ d.e)
    {N : ℕ} (p : Fin 6 → ℕ) (ht : actualPrimeTupleLog N p ∈ box i)
    (hg : oldUpper i (actualPrimeTupleLog N p) < endpoint i (actualPrimeTupleLog N p))
    (hist : Owner d N p) (n : ℕ) (hn : 4*width n < 1/1600) :
    P4AOriginalFull87DataPolicy.Accepted n d (N:ℝ) (pre p) (.saved i) := by
  have hl : lambda3 d (N:ℝ) (pre p) = root d N p :=
    (lambda3_ancestor d (N:ℝ) 4 (by decide) (pre p)).symm
  have hsrc := (P4AOriginalSavedSixthSourceGates.source_iff i _).mpr ⟨ht,hg⟩
  have hparent := P4AOriginalSavedSixthOwnCaps.raw_parent_upper i he p ht hist
  have h3 := hist.third
  have h5 := hist.fifth
  change P4AOriginalFull87DataPolicy.savedEligible d (N:ℝ) i (pre p) ∧ _ ∧ _
  unfold P4AOriginalFull87DataPolicy.savedEligible
  dsimp only
  rw [pre_log N p,hl]
  exact ⟨⟨pre_len p,hsrc,by linarith,by linarith,hparent⟩,
    P4AOriginalSavedSixthSourceGates.quantized_all_gates i ht n hn⟩

/-- The original record, its own literal mask, and the current fifth parent
are checked at the integer tuple. Equality of the comparison gives no update.
Both the original P1 bank and the union bank occur explicitly. -/
theorem original_and_union_admission (i : Row) {e : ℚ} {q : ℕ}
    (hs : Schedule e q 0) {a : ℝ} (ha : a ≤ 1/100) {N : ℕ} (hN : 1 < N)
    (p : Fin 6 → ℕ) (hp : ∀ j, 0 < p j) (n : ℕ) (hn : 4*width n < 1/1600) :
    let t := actualPrimeTupleLog N p
    let new := P4AOriginalNewFifthUnion.data e q a
    (P4AOriginalSixthLicensedFilter.Accepted n e q a (N:ℝ) (pre p) (.saved i) ↔
      t∈box i ∧ oldUpper i t < endpoint i t) ∧
    (P4AOriginalFull87DataPolicy.Accepted n new (N:ℝ) (pre p) (.saved i) ↔
      t∈box i ∧ oldUpper i t < endpoint i t) := by
  dsimp only
  have hf (d : OriginalData) (h : P4AOriginalFull87DataPolicy.Accepted n d (N:ℝ) (pre p) (.saved i)) :
      actualPrimeTupleLog N p ∈ box i ∧ oldUpper i (actualPrimeTupleLog N p) < endpoint i (actualPrimeTupleLog N p) := by
    apply (P4AOriginalSavedSixthSourceGates.source_iff i _).mp
    rw [← pre_log N p]
    exact h.1.2.1
  constructor
  · constructor
    · exact fun h => hf (P4AOriginalCompleteSixthChronology.data e q a) h
    · rintro ⟨ht,hg⟩
      exact accepted_of_source (d := P4AOriginalCompleteSixthChronology.data e q a)
        i hs.1 p ht hg (row_owner i hs ha hN p hp ht).1 n hn
  · constructor
    · exact hf _
    · rintro ⟨ht,hg⟩
      exact accepted_of_source (d := P4AOriginalNewFifthUnion.data e q a)
        i hs.1 p ht hg (row_owner i hs ha hN p hp ht).2 n hn

/-- Ordered-third semantics at the final rough cutoff. A passing saved row
itself supplies the old historical owner needed to move between the trees. -/
theorem ordered_admission (i : Row) {e : ℚ} {q : ℕ} (hs : Schedule e q 0)
    {a ω : ℝ} (ha : a ≤ 1/100) (hw : ω ≤ a) {N : ℕ} (hN : 1 < N)
    (p : Fin 6 → ℕ) (hp : ∀ j, 0 < p j) (n : ℕ) (hn : 4*width n < 1/1600) :
    let d := P4AOriginalNewFifthUnion.data e q a
    let t := actualPrimeTupleLog N p
    P4AOriginalOrderedThirdFullPolicy.accepted
      (P4AOriginalOrderedThirdFullPolicy.current d ω (N:ℝ) (pre p)) d (N:ℝ) n (pre p) (.saved i) ↔
      t∈box i ∧ oldUpper i t < endpoint i t := by
  let d := P4AOriginalNewFifthUnion.data e q a
  dsimp only
  constructor
  · intro h
    have hs' : P4AOriginalSavedSixthArchive.Source i (primeHistoryLogCoordinates (N:ℝ) 6 (pre p)) :=
      h.1.2.1
    rw [pre_log] at hs'
    exact (P4AOriginalSavedSixthSourceGates.source_iff i _).mp hs'
  · intro h
    have ho := (row_owner i hs ha hN p hp h.1).2
    have he : (0:ℝ) ≤ d.e := by exact_mod_cast hs.1
    have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN.le
    rw [P4AOriginalOrderedThirdFullPolicy.root_on_old_owner he hNr hw ho.active.2]
    unfold P4AOriginalOrderedThirdFullPolicy.accepted
    dsimp only
    rw [P4AOriginalOrderedThirdFullPolicy.eligible_prior]
    exact (original_and_union_admission i hs ha hN p hp n hn).2.mpr h

end
end ImbalancedChen.P1OriginalSavedRowsActualAdmission
