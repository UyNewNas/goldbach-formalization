import ImbalancedChen.P4AOriginalFull87FiniteParentPolicy
import ImbalancedChen.P4AOriginalFull87FiniteEighthRealization

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The public terminal chooses one original e/q history schedule and one
rounding index for ranks 4,5,6,8. Original source membership and all history
facts are supplied internally. Actual states are constructed in the NEW
finite-parent companion, not transported through a false global frontier
equality. Only an omitted Euclidean-volume budget is inherited here.
-/
namespace ImbalancedChen.P4AOriginalFull87FiniteParentRealization
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalFull87FiniteParentPolicy
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87TrimOmission (totalOmitted)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)

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

/-- Same pre-N schedule and SAME n at all four ranks. No public support,
raw/finite parent bound, owner, validity or frontier licence is supplied.
The raw current in every stage guard remains the unchanged original one.
The omission budget is VOLUME ONLY, not either analytical reserve. -/
theorem exists_shared_finite_parent_schedule (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ r n0 : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalOmitted r (fun _ _ => (1 : ℝ)) < epsilon ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ n : ℕ, n0 ≤ n →
      ∀ om : ℝ, om ≤ 1 / 100 → ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ p : Fin 8 → ℕ, (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
      ∀ c : Cell, point (N : ℝ) p ∈ trim c (width r) →
        RealizedHistory e q om (N : ℝ) (pre p) c ∧
        ParentBounds n e q om (N : ℝ) (pre p) c ∧
        (cap4 n e q om (N : ℝ) (rosserAncestor 4 (pre p)) ∈
          (alphabet n e q).image (fun a => (a : ℝ))) ∧
        (cap5 n e q om (N : ℝ) (rosserAncestor 5 (pre p)) ∈
          (alphabet n e q).image (fun a => (a : ℝ))) ∧
        (cap6 n e q om (N : ℝ) (rosserAncestor 6 (pre p)) ∈
          (alphabet n e q).image (fun a => (a : ℝ))) ∧
        finiteCap n c (point (N : ℝ) p) ∈ P4AOriginalFull87FiniteEighthCap.alphabet n ∧
        cap6 n e q om (N : ℝ) (rosserAncestor 6 (pre p)) + width r / 2 <
          (finiteCap n c (point (N : ℝ) p) : ℝ) ∧
        (∀ j, prefixSquareExpr (point (N : ℝ) p) j + width r / 2 <
          (finiteCap n c (point (N : ℝ) p) : ℝ)) ∧
        (∀ j ∉ selected c, selectedSquareExpr (selected c) (point (N : ℝ) p) j + width r / 2 <
          (finiteCap n c (point (N : ℝ) p) : ℝ)) ∧
        (finiteCap n c (point (N : ℝ) p) : ℝ) + width n <
          v (∑ j ∈ selected c, point (N : ℝ) p j) ∧
        (∀ enumerationCap : ℕ, ∀ w z : ℝ, w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
          (N : ℝ)^mu ≤ z → z ≤ (enumerationCap : ℝ) → ∀ weight : ℕ → ℝ,
          canonicalState N enumerationCap w weight p ∈
            states (width r) n e q om N enumerationCap w z weight c) := by
  obtain ⟨r, n0, e0, he0, hemax, hvolume, hchoose⟩ :=
    P4AOriginalFull87FiniteEighthRealization.exists_shared_finite_eighth_schedule epsilon hepsilon
  refine ⟨r, n0, e0, he0, hemax, hvolume, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hq⟩ := hchoose e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hqq n hn om hom N hN p hp hdelete c ht
  obtain ⟨hr, halpha8, hgain8, hfull, hselected, hlicense, _hcap8, _holdMember⟩ :=
    hq q hqq n hn om hom N hN p hp hdelete c ht
  have hs := trim_subset_source c (width_pos r) ht
  have hb := parent_bounds_of_history n e q om (N : ℝ) (pre p) (pre_length p) c hs hr
  have h6le : cap6 n e q om (N : ℝ) (rosserAncestor 6 (pre p)) ≤
      P4AOriginalCompleteSixthChronology.currentSixthExponent e q om (N : ℝ)
        (rosserAncestor 6 (pre p)) := by
    obtain ⟨_, _, _, _, _, _, _, h6error⟩ := hb
    exact h6error.2
  refine ⟨hr, hb,
    (caps_mem_alphabet n e q om (N : ℝ) (rosserAncestor 4 (pre p))).1,
    (caps_mem_alphabet n e q om (N : ℝ) (rosserAncestor 5 (pre p))).2.1,
    (caps_mem_alphabet n e q om (N : ℝ) (rosserAncestor 6 (pre p))).2.2,
    halpha8, (add_le_add_right h6le (width r / 2)).trans_lt hgain8,
    hfull, hselected, hlicense, ?_⟩
  intro enumerationCap w z hw hz hzcap weight
  exact canonical_mem_states_of_history (width r) (width_pos r) n e q om N enumerationCap
    he.le hN w z hw hz hzcap weight p hp hdelete c ht hr

end
end ImbalancedChen.P4AOriginalFull87FiniteParentRealization
