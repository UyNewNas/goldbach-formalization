import ImbalancedChen.P4AOriginalFull87PolicyReverseAdmission

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.
The public schedule terminal has NO realized-history, valid-selection or
frontier premise. It constructs those facts from the preceding common
mesh theorem, the original Source rows and the literal arithmetic carrier.
The returned state keeps the exact sign, local weight product and suffix.
No count asymptotic, numerical saving or buffered-compiler reserve follows.
-/
namespace ImbalancedChen.P4AOriginalFull87ActualSourceMembership
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87HistoryCore
open P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87ActualCommonHistory
open P4AOriginalFull87PolicyReverseAdmission
open P4AOriginalCompleteSixthChronology

/-- Original owned states are a FILTER of the actual occurrence list.
No Finset quotient, arbitrary support set or replacement carrier is used. -/
def sourceStates (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z : ℝ) (weight : ℕ → ℝ) (c : Cell) : List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 8
    (P4AOriginalFull87CompleteSixthDispatch.policy e q omega (N : ℝ))
    weight [] true 1 (roughPrimeUniverse N cap w z)).filter fun state =>
      decide (P4AOriginalFull87SourceDispatch.ownerAtPrefix (N : ℝ)
        state.selectedPrefix = some c)

/-- The state forced by the actual decreasing prime scan. The prime at
slot7 is the last selected one; the remainder is its original strict suffix. -/
def canonicalState (N cap : ℕ) (w : ℝ) (weight : ℕ → ℝ) (p : Fin 8 → ℕ) :
    FirstExitDepthState ℕ :=
  ⟨pre p, true, ((pre p).map weight).prod, roughPrimeUniverse N cap w (p 7 : ℝ)⟩

theorem sourceStates_eq_complete_sixth_filter
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z : ℝ) (weight : ℕ → ℝ) (c : Cell) :
    sourceStates e q omega N cap w z weight c =
      (firstExitDepthFrontier 8 (currentSixthPolicy e q omega (N : ℝ))
        weight [] true 1 (roughPrimeUniverse N cap w z)).filter (fun state =>
          decide (P4AOriginalFull87SourceDispatch.ownerAtPrefix (N : ℝ)
            state.selectedPrefix = some c)) := by
  unfold sourceStates
  rw [P4AOriginalFull87CompleteSixthDispatch.policy_frontier]

/-- This intermediate conversion accepts actual history inequalities, but
never assumes a selected state. The public terminal below supplies the
history internally and therefore removes this intermediate premise. -/
theorem canonical_mem_frontier_of_history
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (he : 0 ≤ e) (hN : 1 < (N : ℝ)) (w z : ℝ)
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ)^mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (weight : ℕ → ℝ) (p : Fin 8 → ℕ)
    (hp : ∀ i, (p i).Prime) (hdelete : ∀ i, ¬p i ∣ N)
    (c : Cell) (hs : Source c (point (N : ℝ) p))
    (hr : RealizedHistory e q omega (N : ℝ) (pre p) c) :
    canonicalState N cap w weight p ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87CompleteSixthDispatch.policy e q omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
  let P := P4AOriginalFull87CompleteSixthDispatch.policy e q omega (N : ℝ)
  have hpos : ∀ i, 0 < p i := fun i => (hp i).pos
  have hord := source_strictAnti (N : ℝ) hN p hpos c hs
  have hbounds := source_carrier_bounds (N : ℝ) hN p hpos c hs w z hw hz
  have hcarrier : ∀ r ∈ pre p, r.Prime ∧ ¬r ∣ N ∧ w ≤ (r : ℝ) ∧ (r : ℝ) < z := by
    intro r hrmem
    rw [pre_ofFn] at hrmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hrmem)
    exact ⟨hp i, hdelete i, (hbounds i).1, (hbounds i).2⟩
  have hvalid := validSelection_of_realized_history e q omega (N : ℝ)
    he hN p hp c hs hr
  obtain ⟨state, hstate, hpre⟩ :=
    P1ActualFrontierReverseAdmission.valid_prime_history_reaches_frontier
      P weight N cap w z hzcap (pre p) (pre_pairwise p hord) hcarrier hvalid
  rw [pre_length] at hstate
  have hsign : state.positive = true := by
    have h := mem_firstExitDepthFrontier_positive_eq_evenListLength 8 P weight
      (roughPrimeUniverse N cap w z) state hstate
    simpa [hpre, pre, evenListLength] using h
  have hmass : state.mass = ((pre p).map weight).prod := by
    simpa only [hpre] using mem_firstExitDepthFrontier_mass_eq_selected_prod
      8 P weight (roughPrimeUniverse N cap w z) state hstate
  obtain ⟨r, tail, hsel, _hmem, hrem⟩ :=
    mem_firstExitDepthFrontier_remaining_eq_filter 8 (by decide) P weight
      (roughPrimeUniverse N cap w z) (roughPrimeUniverse_pairwise_gt N cap w z)
      state hstate
  have hrp : r = p 7 := by
    have h := congrArg (fun xs : List ℕ => xs.headD 0) (hpre.symm.trans hsel)
    simpa only [pre, List.headD_cons] using h.symm
  have hremaining : state.remaining = roughPrimeUniverse N cap w (p 7 : ℝ) := by
    rw [hrem, hrp]
    exact roughPrimeUniverse_filter_lt_eq N cap w z (p 7) (hbounds 7).2.le
  have heq : state = canonicalState N cap w weight p := by
    cases state with
    | mk selectedPrefix positive mass remaining =>
        dsimp only at hpre hsign hmass hremaining
        subst selectedPrefix
        subst positive
        subst mass
        subst remaining
        rfl
  rwa [heq] at hstate

/-- Actual original owner membership, now in the genuine occurrence list. -/
theorem canonical_mem_sourceStates_of_history
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (he : 0 ≤ e) (hN : 1 < (N : ℝ)) (w z : ℝ)
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ)^mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (weight : ℕ → ℝ) (p : Fin 8 → ℕ)
    (hp : ∀ i, (p i).Prime) (hdelete : ∀ i, ¬p i ∣ N)
    (c : Cell) (hs : Source c (point (N : ℝ) p))
    (hr : RealizedHistory e q omega (N : ℝ) (pre p) c) :
    canonicalState N cap w weight p ∈ sourceStates e q omega N cap w z weight c := by
  apply List.mem_filter.mpr
  refine ⟨canonical_mem_frontier_of_history e q omega N cap he hN w z hw hz hzcap
    weight p hp hdelete c hs hr, ?_⟩
  apply decide_eq_true
  exact (P4AOriginalFull87SourceDispatch.ownerAtPrefix_rank_eight
    (N : ℝ) (pre p) (pre_length p) c).mpr hs

/-- Cofinal original mesh choices, before omega, N, the tuple, the source
label, the presieve, and the full local weight. No frontier/history licence
is an input. The original precision ceiling remains available downstream. -/
theorem exists_cofinal_original_source_membership (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ omega : ℝ, omega ≤ 1 / 100 → ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ p : Fin 8 → ℕ, (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
      ∀ c : Cell, Source c (point (N : ℝ) p) → point (N : ℝ) p ∈ core delta →
      RealizedHistory e q omega (N : ℝ) (pre p) c ∧
      (∀ cap : ℕ, ∀ w z : ℝ, w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
        (N : ℝ)^mu ≤ z → z ≤ (cap : ℝ) → ∀ weight : ℕ → ℝ,
        canonicalState N cap w weight p ∈ sourceStates e q omega N cap w z weight c) := by
  obtain ⟨eh, heh, hchoose⟩ := exists_original_common_history delta hdelta
  refine ⟨min eh (11 / 64000), lt_min heh (by norm_num), min_le_right _ _, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hhistory⟩ := hchoose e he (hee.trans_le (min_le_left _ _))
  refine ⟨q0, hq0, ?_⟩
  intro q hq omega homega N hN p hp hdelete c hs ht
  have hpos : ∀ r ∈ pre p, 0 < r := by
    intro r hmem
    rw [pre_ofFn] at hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hmem)
    exact (hp i).pos
  have hr := hhistory q hq omega homega (N : ℝ) hN (pre p)
    (pre_length p) hpos c hs ht
  refine ⟨hr, ?_⟩
  intro cap w z hw hz hzcap weight
  exact canonical_mem_sourceStates_of_history e q omega N cap he.le hN w z hw hz hzcap
    weight p hp hdelete c hs hr

/-- An actual rational precision and grid, not an uninstantiated mesh
licence. Existence precedes every arithmetic parameter. -/
theorem exists_concrete_original_source_membership (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < e ∧ (e : ℝ) ≤ 11 / 64000 ∧ 0 < q ∧
      ∀ omega : ℝ, omega ≤ 1 / 100 → ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ p : Fin 8 → ℕ, (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) →
      ∀ c : Cell, Source c (point (N : ℝ) p) → point (N : ℝ) p ∈ core delta →
      RealizedHistory e q omega (N : ℝ) (pre p) c ∧
      (∀ cap : ℕ, ∀ w z : ℝ, w ≤ (N : ℝ) ^ (53 / 13824 : ℝ) →
        (N : ℝ)^mu ≤ z → z ≤ (cap : ℝ) → ∀ weight : ℕ → ℝ,
        canonicalState N cap w weight p ∈ sourceStates e q omega N cap w z weight c) := by
  obtain ⟨e0, he0, hebound, hchoose⟩ := exists_cofinal_original_source_membership delta hdelta
  obtain ⟨e, heR, hee⟩ := exists_rat_btwn he0
  have he : (0 : ℚ) < e := by exact_mod_cast heR
  obtain ⟨q0, hq0, hq⟩ := hchoose e he hee
  exact ⟨e, q0, he, hee.le.trans hebound, hq0, hq q0 le_rfl⟩

end
end ImbalancedChen.P4AOriginalFull87ActualSourceMembership
