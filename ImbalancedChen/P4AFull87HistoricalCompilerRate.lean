import ImbalancedChen.P4AFull87NativeAdmissionFamilies

/-! Discharge the changed-set containment for the actual licensed tree on
the existing historical suffix. All native program signature disagreements
are charged, with no refinement of the original tag. -/
namespace ImbalancedChen.P4AFull87HistoricalCompilerRate
noncomputable section
open scoped Classical BigOperators
open P4AFull87CompilerCapRead P4AFull87CompilerChangedPartition P4AFull87HistoricalChangedSupport
open P4AFull87NativeAdmissionFamilies P4AFull87NativeThirdProgram P4AFull87ActualAffineDeletion
open P4AFull87OrdinaryAdmissionDeletion P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport
open P2CanonicalWallFullResidualPayment P4AUpperTaggedFrozenAdmissionCatalogue
open P4AOriginalCompleteSixthChronology (data currentSixthExponent)
open P4AOriginalFull87FiniteParentPolicy (active active_ancestor)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87LicensedSixthPolicy (policy sixthPolicy eighthContinuation level6Exponent)

theorem selected_on_ancestor (delta : ℝ) (n : ℕ) (N : ℝ) (h : List ℕ)
    (r : ℕ) (hr : 8 ≤ r) (hl : r ≤ h.length) :
    selectedCap delta n N (rosserAncestor r h) = selectedCap delta n N (rosserAncestor 8 h) := by
  have h1 : 8 ≤ (rosserAncestor r h).length := by simp [Nat.min_eq_left hl,hr]
  have h2 : 8 ≤ (rosserAncestor 8 h).length := by simp [Nat.min_eq_left (hr.trans hl)]
  simp only [selectedCap,P4AOriginalFull87SourceDispatch.ownerAtPrefix,
    P4AOriginalFull87SourceDispatch.point8,if_pos h1,if_pos h2,
    rosserAncestor_nested 8 r hr,rosserAncestor_nested 8 8 le_rfl]

private theorem late_keep (P : Parameters) (N r d : ℕ) (hr : 6 < r)
    (hl : r ≤ d.primeFactorsList.length) (hn : P.read N r d=none)
    (ha : ¬active P.e P.q P.om (N:ℝ) d.primeFactorsList) :
    P.keep N (rosserAncestor r d.primeFactorsList) = decide (ordinaryRosserPrefixAdmissible
      false ((N:ℝ)^(currentSixthExponent P.e P.q P.om (N:ℝ) (rosserAncestor 6 d.primeFactorsList)))
      (rosserAncestor r d.primeFactorsList)) := by
  have h6 := not_le.mpr hr
  have h4 : ¬r≤4 := by omega
  have hs : ¬active P.e P.q P.om (N:ℝ) (rosserAncestor 6 d.primeFactorsList) :=
    fun h => ha ((active_ancestor _ _ _ _ 6 (by omega) _).mp h)
  have hlen : (rosserAncestor r d.primeFactorsList).length=r := by simp [Nat.min_eq_left hl]
  have base : sixthPolicy P.n P.e P.q P.om (N:ℝ) false (rosserAncestor r d.primeFactorsList) =
    decide (ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^(currentSixthExponent P.e P.q P.om (N:ℝ) (rosserAncestor 6 d.primeFactorsList)))
      (rosserAncestor r d.primeFactorsList)) := by
    simp [sixthPolicy,firstExitDepthSplicePolicy,hlen,h6,frozenParityRosserPolicy,ancestorFrozenPolicy,
      level6Exponent,rosserAncestor_nested 6 r hr.le,hs,ordinaryParityRosserPolicy,oddFirstExitPolicy]
  by_cases h8 : r≤8
  · simpa only [Parameters.keep,policy,firstExitDepthSplicePolicy,hlen,if_pos h8] using base
  · have hnone : selectedCap P.delta P.n (N:ℝ) (rosserAncestor 8 d.primeFactorsList)=none := by
      cases he : selectedCap P.delta P.n (N:ℝ) (rosserAncestor 8 d.primeFactorsList) with
      | none => rfl
      | some a => simp [Parameters.read,atRank,h4,h6,h8,readStage,he] at hn
    simpa only [Parameters.keep,policy,firstExitDepthSplicePolicy,hlen,if_neg h8,
      eighthContinuation,selected_on_ancestor P.delta P.n (N:ℝ) _ r (by omega) hl,hnone] using base

abbrev nativeProgram (P : Parameters) := complete (data P.e P.q P.om)
abbrev count (P : Parameters) := Fintype.card (Family (nativeProgram P) P.caps)

theorem changed_seen (P : Parameters) (he : 0 ≤ P.e) (hdelta : 0 < P.delta)
    (N cap : ℕ) (hN : 2 ≤ N) (omega v tau : ℝ)
    (hw : 0 < omega) (hv : omega ≤ v) (ht : 0 < tau) {d : ℕ}
    (hd : d ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hc : changed (P.keep N) (P.tags N (suffix P N)) N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau d) :
    Seen (nativeProgram P) P.caps N cap (J0 omega) omega v tau d := by
  let tags := P.tags N (suffix P N)
  have hJ := P4AFull87LicensedPhysicalSupport.changed_rank_lt P he hdelta tags N cap hN
    omega ((N:ℝ)^v) tau hw hd hc
  have hn : 1<N := by omega
  rcases changed_in_catalogue_or_inherited P hdelta N cap hN (suffix P N) omega v tau hw hd hc
    with hcat | hrem
  · obtain ⟨r,_,hr,a,ha,f,hf,hflip⟩ := (Finset.mem_filter.mp hcat).2
    have hrf : r.val ≤ f.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hf]; exact hr
    rw [reversed_prefix d r.val hr,reversed_prefix f r.val hrf] at hflip
    exact constant_seen _ _ N cap _ hn omega v tau hw hv ht tags hd hf hr (hr.trans hJ.le) ha hflip
  · obtain ⟨f,hf,k,hk,hlate,had,haf,hdiff⟩ := inherited_late_inactive P hdelta N cap _ _ tau hrem
    let r := k+1
    have hr : r ≤ d.primeFactorsList.length := hk
    have hrf : r ≤ f.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hf]; exact hr
    have heq := reads_eq_of_tag_eq hdelta P.n P.e P.q P.om (N:ℝ) (suffix P N)
      (cell_frozen_tag _ _ _ _ _ _ hf)
    cases hread : P.read N r d with
    | some a =>
      have hf' : P.read N r f = some a := (congrArg (atRank r) heq).trans hread
      have ha := atRank_mem hdelta P.n P.e P.q P.om (N:ℝ) _ r hread
      apply constant_seen _ _ N cap _ hn omega v tau hw hv ht tags hd hf hr (hr.trans hJ.le) ha
      intro h
      exact hdiff ((policy_at_read _ _ _ _ _ _ _ r hr hread).trans
        ((congrArg (fun q : Prop => decide q) (propext h)).trans (policy_at_read _ _ _ _ _ _ _ r hrf hf').symm))
    | none =>
      have hf' : P.read N r f = none := (congrArg (atRank r) heq).trans hread
      have hnative (x : ℕ) (hx : x ∈ universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
          (hrx : r ≤ x.primeFactorsList.length) :
          (nativeProgram P).eval (coords N 6 x.primeFactorsList.reverse) =
          currentSixthExponent P.e P.q P.om (N:ℝ) (rosserAncestor 6 x.primeFactorsList) := by
        rw [data_complete_on_modulus _ N cap x hn omega v hx (by omega)]
        exact P4AOriginalFull87DataPolicy.old_afterLater _ _ _ _ _ 8
      apply native_seen _ _ N cap _ hn omega v tau hw hv ht tags hd hf hlate.le hr (hr.trans hJ.le)
      rw [hnative d hd hr,hnative f (Finset.mem_filter.mp hf).1 hrf]
      intro h
      exact hdiff ((late_keep P N r d hlate hr hread had).trans
        ((congrArg (fun q : Prop => decide q) (propext h)).trans (late_keep P N r f hlate hrf hf' haf).symm))

/-- Explicit pre-roughness coefficient of the actual changed-modulus mass.
The 1/log N term includes moving endpoints and every erased-divisor tail.
No residual or wall-cover hypothesis. -/
theorem exists_actual_rate (P : Parameters) (he : 0 ≤ P.e) (hdelta : 0 < P.delta) :
    ∃ K E : ℝ, 1 < K ∧ 1 < E ∧ ∀ B : ℝ, 0 ≤ B →
    ∀ N cap : ℕ, 2 ≤ N → Even N → ∀ omega v tau : ℝ, 0 < omega → omega ≤ v → v ≤ 1 →
    0 < tau → 3 ≤ (N:ℝ)^omega → E ≤ omega*Real.log (N:ℝ) →
    (B/omega)*changedMass (P.keep N) (P.tags N (suffix P N)) N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau ≤
      ((count P : ℝ)*150*B*tau+(count P : ℝ)*10*B*K/Real.log (N:ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,hh⟩ := P4AFull87FiniteWallRate.exists_finite_rate
    (ι := Family (nativeProgram P) P.caps)
  refine ⟨K,E,hK,hE,?_⟩
  intro B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog
  apply hh B hB N cap (by omega) hEven omega v tau hw hv hv1 ht.le h3 hlog
    (bank (nativeProgram P) P.caps N (J0 omega))
  intro d hd
  obtain ⟨hU,hc⟩ := Finset.mem_filter.mp hd
  exact changed_seen P he hdelta N cap hN omega v tau hw hv ht hU hc

end
end ImbalancedChen.P4AFull87HistoricalCompilerRate
