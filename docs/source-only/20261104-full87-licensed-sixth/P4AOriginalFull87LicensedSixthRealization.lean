import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import ImbalancedChen.P4AOriginalFull87AllRankBoxedProvenance

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The new filtered-sixth tree has a NEW occurrence list. Source members are
constructed by direct admission, including the unsafe-margin complement.
Only the additional sixth action is suppressed when its rounded licence
fails; the real finite fifth predecessor remains. Original coarse choices,
third tags, eighth owner and target-deleted arithmetic carrier are kept.
External analytic inputs are documented, not proved or assumed anew here.
-/
namespace ImbalancedChen.P4AOriginalFull87LicensedSixthRealization
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalSixthLicensedFilter
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87TrimOmission (totalOmitted)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap finiteCap_licensed)
open P4AOriginalFull87ActionLicenseIntegration (SourceSupply)
open P4AOriginalFourthFifthUniformActionLicense (ArchiveLicenses)
open P4AOriginalFull87SixthMarginIntegration (SixthLicenses)
open P4AOriginalSixthCommonMargin (safe8 totalSixthOmitted)
open P4AOriginalFull87AllRankBoxedProvenance (allOmitted LowerWinnerSupply)
open P4AOriginalFull87BoxedWinner (WinnerSupply SavedSourceSupply)

/-- The actual owned list of the new tree. The ORIGINAL source selector is
retained. No Finset conversion or multiplicity assertion is hidden here. -/
def states (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 8 (policy delta n e q om (N : ℝ)) weight [] true 1
    (roughPrimeUniverse N enumerationCap w z)).filter fun s =>
      decide (ownerAtPrefix (N : ℝ) s.selectedPrefix = some c ∧
        point8 (N : ℝ) s.selectedPrefix ∈ trim c delta)

/-- Construct the state, THEN use the actual frontier invariants to read
its sign, mass and suffix. No global old/new frontier equality is needed. -/
theorem canonical_mem_states_of_history (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N enumerationCap : ℕ)
    (he : 0 ≤ e) (hN : 1 < (N : ℝ)) (w z : ℝ)
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ)^mu ≤ z) (hzcap : z ≤ (enumerationCap : ℝ))
    (weight : ℕ → ℝ) (p : Fin 8 → ℕ)
    (hp : ∀ i, (p i).Prime) (hdelete : ∀ i, ¬p i ∣ N)
    (c : Cell) (ht : point (N : ℝ) p ∈ trim c delta)
    (hr : RealizedHistory e q om (N : ℝ) (pre p) c) :
    canonicalState N enumerationCap w weight p ∈
      states delta n e q om N enumerationCap w z weight c := by
  let P := policy delta n e q om (N : ℝ)
  have hs := trim_subset_source c hd ht
  have hpos : ∀ i, 0 < p i := fun i => (hp i).pos
  have hord := source_strictAnti (N : ℝ) hN p hpos c hs
  have hbounds := P4AOriginalFull87PolicyReverseAdmission.source_carrier_bounds
    (N : ℝ) hN p hpos c hs w z hw hz
  have hcarrier : ∀ r ∈ pre p, r.Prime ∧ ¬r ∣ N ∧ w ≤ (r : ℝ) ∧ (r : ℝ) < z := by
    intro r hmem
    rw [pre_ofFn] at hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hmem)
    exact ⟨hp i, hdelete i, (hbounds i).1, (hbounds i).2⟩
  have hvalid := validSelection_of_history delta n e q om (N : ℝ) he hN p hp c hs hr
  obtain ⟨s, hstate, hpre⟩ := P1ActualFrontierReverseAdmission.valid_prime_history_reaches_frontier
    P weight N enumerationCap w z hzcap (pre p) (pre_pairwise p hord) hcarrier hvalid
  rw [pre_length] at hstate
  have hsign : s.positive = true := by
    have h := mem_firstExitDepthFrontier_positive_eq_evenListLength 8 P weight
      (roughPrimeUniverse N enumerationCap w z) s hstate
    simpa [hpre, pre, evenListLength] using h
  have hmass : s.mass = ((pre p).map weight).prod := by
    simpa only [hpre] using mem_firstExitDepthFrontier_mass_eq_selected_prod
      8 P weight (roughPrimeUniverse N enumerationCap w z) s hstate
  obtain ⟨r, tail, hsel, _hmem, hrem⟩ := mem_firstExitDepthFrontier_remaining_eq_filter
    8 (by decide) P weight (roughPrimeUniverse N enumerationCap w z)
    (roughPrimeUniverse_pairwise_gt N enumerationCap w z) s hstate
  have hrp : r = p 7 := by
    have h := congrArg (fun xs : List ℕ => xs.headD 0) (hpre.symm.trans hsel)
    simpa only [pre, List.headD_cons] using h.symm
  have hremaining : s.remaining = roughPrimeUniverse N enumerationCap w (p 7 : ℝ) := by
    rw [hrem, hrp]
    exact roughPrimeUniverse_filter_lt_eq N enumerationCap w z (p 7) (hbounds 7).2.le
  have heq : s = canonicalState N enumerationCap w weight p := by
    cases s with
    | mk selectedPrefix positive mass remaining =>
        dsimp only at hpre hsign hmass hremaining
        subst selectedPrefix
        subst positive
        subst mass
        subst remaining
        rfl
  rw [heq] at hstate
  apply List.mem_filter.mpr
  refine ⟨hstate, decide_eq_true ⟨?_, ?_⟩⟩
  · exact (P4AOriginalFull87SourceDispatch.ownerAtPrefix_rank_eight
      (N : ℝ) (pre p) (pre_length p) c).mpr hs
  · change point8 (N : ℝ) (pre p) ∈ trim c delta
    rw [P4AOriginalFull87FiniteEighthPolicy.point8_at_eight _ _ (pre_length p)]
    exact ht

/-- New-state membership and actual cap bounds, not a renamed old list.
The safe equality compares only the same own-sixth cap, not whole trees. -/
def FilteredSourceSupply (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℕ, 1 < (N : ℝ) → ∀ p : Fin 8 → ℕ,
    (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
    ∀ c : Cell, point (N : ℝ) p ∈ trim c (width r) →
      RealizedHistory e q om (N : ℝ) (pre p) c ∧
      cap5 n e q om (N : ℝ) (rosserAncestor 5 (pre p)) ≤
        licensedCap n e q om (N : ℝ) (rosserAncestor 6 (pre p)) ∧
      licensedCap n e q om (N : ℝ) (rosserAncestor 6 (pre p)) ≤
        cap6 n e q om (N : ℝ) (rosserAncestor 6 (pre p)) ∧
      licensedCap n e q om (N : ℝ) (rosserAncestor 6 (pre p)) ∈
        (alphabet n e q).image (fun x : ℚ => (x : ℝ)) ∧
      licensedCap n e q om (N : ℝ) (rosserAncestor 6 (pre p)) + width r / 2 <
        (finiteCap n c (point (N : ℝ) p) : ℝ) ∧
      (point (N : ℝ) p ∈ safe8 (width s) →
        licensedCap n e q om (N : ℝ) (rosserAncestor 6 (pre p)) =
          cap6 n e q om (N : ℝ) (rosserAncestor 6 (pre p))) ∧
      (∀ enumerationCap : ℕ, ∀ w z : ℝ,
        w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
        (N : ℝ)^mu ≤ z → z ≤ (enumerationCap : ℝ) → ∀ weight : ℕ → ℝ,
        canonicalState N enumerationCap w weight p ∈
          states (width r) n e q om N enumerationCap w z weight c)

/-- The old SourceSupply is an internal supplier at this intermediate
conversion. The public theorem below derives it; it is not a new axiom. -/
theorem filteredSourceSupply_of_original (s r n m : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (he : 0 ≤ e) (hn : 4 * width n < width r)
    (hold : SourceSupply r n m e q om) (h6 : SixthLicenses s n e q om) :
    FilteredSourceSupply s r n e q om := by
  intro N hN p hp hdelete c ht
  obtain ⟨hr,hb,_hlookup,_hbox,_holdMember⟩ := hold N hN p hp hdelete c ht
  have hs := trim_subset_source c (width_pos r) ht
  have hup := licensedCap_le_old n e q om (N : ℝ) (rosserAncestor 6 (pre p))
  have hparent : cap6 n e q om (N : ℝ) (rosserAncestor 6 (pre p)) ≤
      comparison c (point (N : ℝ) p) := hb.2.2.2.2.1
  have h8 := finiteCap_licensed n (width_pos r) hn ht
  refine ⟨hr,?_,hup,licensedCap_mem_alphabet n e q om (N : ℝ) _,?_,?_,?_⟩
  · simpa only [rosserAncestor_nested 5 6 (by decide)] using
      fifth_le_licensedCap n e q om (N : ℝ) (rosserAncestor 6 (pre p))
  · exact (add_le_add_right (hup.trans hparent) (width r / 2)).trans_lt h8.2.1
  · intro hsafe
    apply eq_old_of_all_accepted
    intro a ha
    have hl := (h6 (N : ℝ) (pre p) (pre_length p) c hs hsafe).1 a ha
    exact ⟨ha,hl.1,hl.2.2⟩
  · intro enumerationCap w z hw hz hzcap weight
    exact canonical_mem_states_of_history (width r) (width_pos r) n e q om N
      enumerationCap he hN w z hw hz hzcap weight p hp hdelete c ht hr

/-- The old certificate bundle is kept explicitly attached to the OLD
finite-parent tree. The new output is separate. No old box/tag identity is
silently transported to a changed cap on the unsafe complement. -/
theorem exists_shared_licensed_sixth_schedule
    (epsilonSource epsilonBox epsilonSixth : ℝ)
    (hSource : 0 < epsilonSource) (hBox : 0 < epsilonBox)
    (hSixth : 0 < epsilonSixth) :
    ∃ s r : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalSixthOmitted s (fun _ _ => (1 : ℝ)) < epsilonSixth ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilonSource ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ 1 / 100 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ArchiveLicenses n e q om ∧ SixthLicenses s n e q om ∧
        ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
          allOmitted n e q om m (fun _ _ => (1 : ℝ)) < epsilonBox ∧
          SourceSupply r n m e q om ∧ WinnerSupply s n m e q om ∧
          SavedSourceSupply r e q om ∧ LowerWinnerSupply n m e q om ∧
          FilteredSourceSupply s r n e q om := by
  obtain ⟨s,r,e0,he0,hemax,hsixth,hsource,hchoose⟩ :=
    P4AOriginalFull87AllRankBoxedProvenance.exists_shared_all_rank_winner_schedule
      epsilonSource epsilonBox epsilonSixth hSource hBox hSixth
  obtain ⟨nTrim,hnTrim⟩ :=
    P4AOriginalFull87FiniteEighthCap.exists_uniform_cap_resolution (width r) (width_pos r)
  refine ⟨s,r,e0,he0,hemax,hsixth,hsource,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq⟩ := hchoose e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨nOld,hnOld⟩ := hq q hqq om hom
  refine ⟨max nOld nTrim,?_⟩
  intro n hn
  obtain ⟨ha,h6,m0,hm0⟩ := hnOld n ((le_max_left _ _).trans hn)
  have hn8 := hnTrim n ((le_max_right _ _).trans hn)
  refine ⟨ha,h6,m0,?_⟩
  intro m hm
  obtain ⟨hmass,hold,hwin,hsaved,hlower⟩ := hm0 m hm
  exact ⟨hmass,hold,hwin,hsaved,hlower,
    filteredSourceSupply_of_original s r n m e q om he.le hn8 hold h6⟩

end
end ImbalancedChen.P4AOriginalFull87LicensedSixthRealization
