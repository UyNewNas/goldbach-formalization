import ImbalancedChen.P4AOriginalFull87RankNineActualLevelOrder
import ImbalancedChen.P4AOriginalFull87ActualCommonHistory
import ImbalancedChen.FirstExitFrontierInvariants
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: extend the original, pre-N common-history supplier from an
arbitrary positive, source-and-core eight-prime word to EVERY genuine
owned, filtered-sixth eighth-frontier occurrence. The same original
source, trim, owner, target-deleted rough carrier, frozen levels and
full87 list are retained. No new licence is assumed for a state.

Unlike the predecessor's statewise conditional rank-nine theorem, the
final result has NO caller-supplied RealizedHistory premise. The one
precision/mesh schedule is fixed before omega,N,n,carrier,cell,state.
No asymptotic number-theory input or reserve payment is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87AllOwnedRealizedHistory
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87SourceDictionary (Cell Source)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87StrictActionTrim
  (trim trim_subset_source trim_subset_core)
open P4AOriginalFull87ActualCommonHistory
  (RealizedHistory exists_original_common_history)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy)
open P4AOriginalFull87OwnedEighthSource
  (frontier states_eq_owner_filter retainedOwner retainedOwner_some_iff)
open P4AOriginalFull87ActualEighthCarrier (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87RankNineActualLevelOrder
  (owned_actual_frozen_parent_lt_cap owned_actual_rankNine_cross_iff_forward)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87RankNinePrimeCrossover
  (rankNineThresholdCrosses rankNineChoiceThreshold)

/-- Each prime in an actually reached owned eighth state is a member
of the ORIGINAL target-deleted, capped, descending rough-prime carrier.
It is not a fresh prime population selected for the comparison. -/
theorem owned_eighth_history_primes_and_deletion
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N enumerationCap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    ∀ p ∈ s.selectedPrefix, p.Prime ∧ ¬ p ∣ N := by
  have hfront : s ∈ frontier n e q om N enumerationCap w z := by
    have h := hs
    rw [states_eq_owner_filter] at h
    exact (List.mem_filter.mp h).1
  have hsub : s.selectedPrefix.reverse <+
      roughPrimeUniverse N enumerationCap w z :=
    mem_firstExitDepthFrontier_selected_reverse_sublist
      8 (sixthPolicy n e q om (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
      (roughPrimeUniverse N enumerationCap w z) s hfront
  intro p hp
  have hrev : p ∈ s.selectedPrefix.reverse := by simpa using hp
  have hcarrier : p ∈ roughPrimeUniverse N enumerationCap w z :=
    hsub.subset hrev
  exact ⟨mem_roughPrimeUniverse_prime hcarrier,
    mem_roughPrimeUniverse_not_dvd hcarrier⟩

/-- One common original choice of rational precision and the actual
historical mesh supplies RealizedHistory at EVERY owned occurrence.
Membership, positivity, the source row and the compact core are
obtained from the literal NEW filtered-sixth frontier/owner/trim.

In particular, none of these is introduced as a premise, field,
external input, or an abstract equivalent of the required conclusion.
The quantifier order fixes e and q before omega, N, n, cap, w, z,
source cell and ALL occurrence multiplicities. -/
theorem exists_shared_history_for_all_owned_eighth_states (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ (1 / 100 : ℝ) →
      ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ n enumerationCap : ℕ, ∀ w z : ℝ, ∀ c : Cell,
      ∀ s : FirstExitDepthState ℕ,
        s ∈ states (width r) n e q om N enumerationCap w z
          (fun _ : ℕ => (1 : ℝ)) c →
        RealizedHistory e q om (N : ℝ) s.selectedPrefix c := by
  obtain ⟨e0, he0, hchoice⟩ :=
    exists_original_common_history (width r) (width_pos r)
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hhistory⟩ := hchoice e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hq om hom N hN n enumerationCap w z c s hs
  have hlen : s.selectedPrefix.length = 8 :=
    (owned87_eighth_state_exact_carrier
      (width r) n e q om N enumerationCap w z c s hs).1
  have hpositive : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (owned_eighth_history_primes_and_deletion
      r n e q om N enumerationCap w z c s hs p hp).1.pos
  have hfiltered : s ∈
      (frontier n e q om N enumerationCap w z).filter (fun t =>
        decide (retainedOwner (width r) (N : ℝ)
          t.selectedPrefix = some c)) := by
    simpa only [states_eq_owner_filter] using hs
  have howner : retainedOwner (width r) (N : ℝ)
      s.selectedPrefix = some c :=
    of_decide_eq_true (List.mem_filter.mp hfiltered).2
  have htrim : point8 (N : ℝ) s.selectedPrefix ∈ trim c (width r) :=
    ((retainedOwner_some_iff (width r) (N : ℝ)
      s.selectedPrefix c).mp howner).2
  have ht : primeHistoryLogCoordinates (N : ℝ) 8
      s.selectedPrefix ∈ trim c (width r) := by
    simpa only [point8,
      rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using htrim
  have hsource : Source c
      (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) :=
    trim_subset_source c (width_pos r) ht
  have hcore : primeHistoryLogCoordinates (N : ℝ) 8
      s.selectedPrefix ∈ P4AOriginalFull87HistoryCore.core (width r) :=
    trim_subset_core c (width r) ht
  exact hhistory q hq om hom (N : ℝ) hN
    s.selectedPrefix hlen hpositive c hsource hcore

/-- Application to the original parent/cap ninth-prime comparison:
the result no longer requires a state-specific RealizedHistory argument.
The two real levels and threshold use that SAME original state.

The condition 4*width n < width r is the original rounding resolution;
it is NOT an invented schedule licence or a paid reserve. -/
theorem exists_shared_forward_rankNine_for_all_owned_states
    (r n : ℕ) (hn : 4 * width n < width r) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ (1 / 100 : ℝ) →
      ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ enumerationCap : ℕ, ∀ w z : ℝ, ∀ c : Cell,
      ∀ s : FirstExitDepthState ℕ,
        s ∈ states (width r) n e q om N enumerationCap w z
          (fun _ : ℕ => (1 : ℝ)) c →
        actualFrozenPost8Level n e q om N c s true <
          actualFrozenPost8Level n e q om N c s false ∧
        (∀ p : ℕ,
          rankNineThresholdCrosses n e q om N c s p ↔
            actualFrozenPost8Level n e q om N c s true ≤
              rankNineChoiceThreshold s.selectedPrefix p ∧
            rankNineChoiceThreshold s.selectedPrefix p <
              actualFrozenPost8Level n e q om N c s false) := by
  obtain ⟨e0, he0, hchoose⟩ :=
    exists_shared_history_for_all_owned_eighth_states r
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hh⟩ := hchoose e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hq om hom N hN enumerationCap w z c s hs
  have hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c :=
    hh q hq om hom N hN n enumerationCap w z c s hs
  exact ⟨owned_actual_frozen_parent_lt_cap
      r n e q om N enumerationCap hN hn w z c s hs hr,
    fun p => owned_actual_rankNine_cross_iff_forward
      r n e q om N enumerationCap hN hn w z c s hs hr p⟩

end
end ImbalancedChen.P4AOriginalFull87AllOwnedRealizedHistory
