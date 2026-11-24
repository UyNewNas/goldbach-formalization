import ImbalancedChen.P4AOriginalSavedSixthHistoricalOwner
import ImbalancedChen.P4AOriginalSavedSixthActualAdmission

/-! The original fifth majorant covers all actual old and new rows. The
finite saved cap is squeezed between its actual inherited cutoff and its
own rounded endpoint on every positive component of the G4 bank. -/
namespace ImbalancedChen.P4AOriginalSavedSixthOwnCaps
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P1OriginalVariableFourthContinuation P1GuardFrozenFiniteCapAlgebra
open P4AOriginalSavedSixthHistoricalOwner
open P4AOriginalSavedSixthSigned (pre old)
open P4AOriginalSavedSixthStage (level accepted_lower fifth_le_level)
open P4AOriginalFull87DataPolicy (active level5Exponent cap5 cap5_eq_protect Accepted)
open P4AOriginalSavedSixthArchive (Row endpoint oldUpper)
open P4AOriginalSavedSixthPlanes (box)
open P4AOriginalSavedSixthSourceGates (source_iff quantized_all_gates)
open P4AOriginalSavedSixthPrimeMean (bounds ordered6)
open P4AOriginalSavedSixthIntegral (box_disjoint residual_ceiling)
open P4AOriginalFull87HistoryCore (width)

private theorem ancestor_tent (i : Row) {N : ℕ} (p : Fin 6 → ℕ)
    (ht : actualPrimeTupleLog N p ∈ box i) (k : ℕ) (hk : k≤5) (I : Finset (Fin k)) :
    v (∑ j ∈ I,primeHistoryLogCoordinates (N:ℝ) k (rosserAncestor k (pre p)) j) ≤
      oldUpper i (actualPrimeTupleLog N p) := by
  let emb : Fin k ↪ Fin 5 := ⟨fun j => j.castLE hk,by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩
  have he : (∑ j ∈ I,primeHistoryLogCoordinates (N:ℝ) k (rosserAncestor k (pre p)) j) =
      ∑ j ∈ I.map emb,actualPrimeTupleLog N p j.castSucc := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    rw [primeHistoryLogCoordinates_ancestor (N:ℝ) (pre_len p) (by omega : k≤6) j,pre_log]
  rw [he]
  exact P4AOriginalSavedSixthActualAdmission.saved_all_subsets_le i _ ((bounds i ht 2).2.le.trans
    (by norm_num [mu])) _

theorem raw_parent_upper (i : Row) {d : OriginalData} {N : ℕ} (he : 0≤d.e) (p : Fin 6 → ℕ)
    (ht : actualPrimeTupleLog N p ∈ box i) (hist : Owner d N p) :
    actualParent5 d (N:ℝ) (pre p) ≤ oldUpper i (actualPrimeTupleLog N p) := by
  have heR : (0:ℝ)≤d.e := by exact_mod_cast he
  have h4 : exponent4 d (N:ℝ) (rosserAncestor 4 (pre p)) ≤ oldUpper i (actualPrimeTupleLog N p) := by
    rw [exponent4,if_pos (show (rosserAncestor 4 (pre p)).length=4 by simp [pre_len])]
    apply finiteMax_le
    · exact hist.upper.trans (P4AOriginalSavedSixthActualAdmission.six_le_saved i _
        ((bounds i ht 2).2.le.trans (by norm_num [mu])))
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      linarith only [heR,ancestor_tent i p ht 4 (by decide) r.selected]
  change exponent5 _ _ (rosserAncestor 5 (pre p)) ≤ _
  rw [exponent5,if_pos (show (rosserAncestor 5 (pre p)).length=5 by simp [pre_len]),
    rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le _ _ _ _ _ h4
  intro r _ _
  rw [P1OriginalVariableFifthContinuation.candidate,P1OriginalVariableFifthContinuation.envelope_eq_v]
  linarith only [heR,ancestor_tent i p ht 5 (by decide) r.selected]

theorem on_positive (i : Row) {d : OriginalData} {N : ℕ} (he : 0≤d.e) (p : Fin 6 → ℕ)
    (ht : actualPrimeTupleLog N p ∈ box i) (hg : oldUpper i (actualPrimeTupleLog N p)<
      endpoint i (actualPrimeTupleLog N p)) (hist : Owner d N p) (n : ℕ) (hn : 4*width n<1/1600) :
    let t := actualPrimeTupleLog N p
    let P := old n d (N:ℝ) (pre p)
    let M := level n d (N:ℝ) (pre p)
    root d N p ≤ P ∧ P ≤ oldUpper i t ∧ P≤M ∧ M≤endpoint i t ∧
      endpoint i t-2*width n < M ∧ t 5 < P-Certificates.P2OriginalSixthElevenLogSemantics.S6 t ∧ M-Certificates.P2OriginalSixthElevenLogSemantics.S6 t ≤ 3*t 5 := by
  let t := actualPrimeTupleLog N p
  let h := pre p
  have ha := hist.active
  have ha5 := (P4AOriginalFull87DataPolicy.active_ancestor d (N:ℝ) 5 (by decide) h).mpr ha
  have hsrc := (source_iff i _).mpr ⟨ht,hg⟩
  have hparent := raw_parent_upper i he p ht hist
  have hl : lambda3 d (N:ℝ) h = root d N p := (lambda3_ancestor d (N:ℝ) 4 (by decide) h).symm
  have hrawbase : root d N p ≤ actualParent5 d (N:ℝ) h := by
    have hh := lambda3_le_exponent5 d (N:ℝ) (rosserAncestor 5 h)
    simpa only [lambda3_ancestor _ _ 5 (by decide),hl] using hh
  have hseed : originalSeed d (N:ℝ) (rosserAncestor 5 h) = root d N p := by
    rw [P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 5 (by decide)]
    exact hist.seed.symm
  have hf := hist.first
  have hpos : (0:ℝ) ≤ root d N p := by linarith only [hf,(bounds i ht 0).1]
  have hrawc : actualParent5 d (N:ℝ) h ≤ cap := (hparent.trans hg.le).trans (v_le_cap _)
  have hp := protect_error n (root d N p) (actualParent5 d (N:ℝ) h) hpos hrawbase hrawc
  have hold : old n d (N:ℝ) h = protect n (root d N p) (actualParent5 d (N:ℝ) h) := by
    rw [old,level5Exponent,if_pos ha5,cap5_eq_protect,hseed]; rfl
  have hc := quantized_all_gates i ht n hn
  have hacc : Accepted n d (N:ℝ) h (.saved i) := by
    have h3 := hist.third
    have h5 := hist.fifth
    change P4AOriginalFull87DataPolicy.savedEligible d (N:ℝ) i h ∧ _ ∧ _
    unfold P4AOriginalFull87DataPolicy.savedEligible
    dsimp only
    rw [show primeHistoryLogCoordinates (N:ℝ) 6 h=t from pre_log N p,hl]
    exact ⟨⟨pre_len p,hsrc,by linarith,by linarith,hparent⟩,hc⟩
  have hr := accepted_lower n d (N:ℝ) h i ha hacc
  have htR : primeHistoryLogCoordinates (N:ℝ) 6 h=t := pre_log N p
  rw [htR] at hr
  have hent : 0≤endpoint i t := hpos.trans (hrawbase.trans (hparent.trans hg.le))
  have hrounded := rounded_error n (endpoint i t) hent (v_le_cap _)
  have ho : old n d (N:ℝ) h ≤ oldUpper i t := by rw [hold]; exact hp.2.2.trans hparent
  have hcap : level n d (N:ℝ) h ≤ endpoint i t := by
    rw [level,if_pos ha]
    apply finiteMax_le
    · change cap5 n d (N:ℝ) (rosserAncestor 5 h) ≤ _
      have hh := ho.trans hg.le
      simpa only [old,level5Exponent,if_pos ha5] using hh
    · intro k _ hk
      have hs : P4AOriginalSavedSixthArchive.Source k (primeHistoryLogCoordinates (N:ℝ) 6 h) := hk.1.2.1
      rw [htR] at hs ⊢
      have hki : k=i := by
        by_contra hne
        exact Set.disjoint_left.mp (box_disjoint hne) ((source_iff k t).mp hs).1 ht
      subst k
      exact hrounded.2.2
  have hfloor : root d N p≤old n d (N:ℝ) h := by rw [hold]; exact hp.1
  have h5 := hist.fifth
  have hord := (ordered6 i ht (by decide : (4:Fin 6)<5)).le
  have hres : t 5 < old n d (N:ℝ) h-Certificates.P2OriginalSixthElevenLogSemantics.S6 t := by
    dsimp only [Certificates.P2OriginalSixthElevenLogSemantics.S6,Certificates.P2OriginalSixthElevenLogSemantics.S5,Certificates.P2OriginalSixthElevenLogSemantics.H5] at h5 ⊢
    linarith only [h5,hfloor,hord]
  exact ⟨hfloor,ho,fifth_le_level n d _ h,hcap,hrounded.1.trans_le hr,hres,
    (sub_le_sub_right hcap _).trans (residual_ceiling i ht).2.2⟩

end
end ImbalancedChen.P4AOriginalSavedSixthOwnCaps
