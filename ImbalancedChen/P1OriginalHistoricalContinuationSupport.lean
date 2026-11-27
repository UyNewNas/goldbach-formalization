import ImbalancedChen.P1OriginalHistoricalOwnerUniqueness
import ImbalancedChen.P2LowerCanonicalRetainedTrace

/-!
Actual common exits and their literal valid continuations recover the original
retained-support difference. No rough-mask equation is a reconstruction premise.
This does not yet identify Cartesian atoms or estimate a signed medium sum.
-/
namespace ImbalancedChen.P1OriginalHistoricalContinuationSupport
noncomputable section
open Classical

/-- Reconstruct the SAME full selected word from the actual exit recursion.
All earlier common selections passed both original policies; the admitting
policy passes the exit test and the rejecting policy fails it. -/
theorem exit_continuation_word {α : Type*}
    (allowing rejecting : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hs : state ∈ p1SignedExitStates (p1CommonAdmissionPolicy allowing rejecting)
      h pre positive mass carrier)
    (ha : allowing state.positive state.selectedPrefix = true)
    (tail : List α) (ht : List.Sublist tail state.remaining)
    (hv : FirstExitValidSelection allowing state.selectedPrefix state.positive tail) :
    ∃ chosen : List α, List.Sublist chosen carrier ∧
      chosen.reverse ++ pre = tail.reverse ++ state.selectedPrefix ∧
      FirstExitValidSelection allowing pre positive chosen ∧
      ¬FirstExitValidSelection rejecting pre positive chosen := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hs
  | cons p ps ih =>
    by_cases hp : p1CommonAdmissionPolicy allowing rejecting (!positive) (p :: pre) = true
    · rw [p1SignedExitStates, if_pos hp, List.mem_append] at hs
      rcases hs with hskip | hselect
      · obtain ⟨chosen, hc, he, hallow, hreject⟩ := ih pre positive mass hskip
        exact ⟨chosen, hc.cons p, he, hallow, hreject⟩
      · obtain ⟨chosen, hc, he, hallow, hreject⟩ :=
          ih (p :: pre) (!positive) (mass * h p) hselect
        have hboth := Bool.and_eq_true_iff.mp hp
        refine ⟨p :: chosen, hc.cons_cons p, ?_, ⟨hboth.1, hallow⟩, ?_⟩
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using he
        · exact fun hh => hreject hh.2
    · rw [p1SignedExitStates, if_neg hp, List.mem_append] at hs
      rcases hs with hskip | hexit
      · obtain ⟨chosen, hc, he, hallow, hreject⟩ := ih pre positive mass hskip
        exact ⟨chosen, hc.cons p, he, hallow, hreject⟩
      · simp only [List.mem_singleton] at hexit
        subst state
        have hr : rejecting (!positive) (p :: pre) ≠ true := by
          intro hh
          exact hp (by simp [p1CommonAdmissionPolicy, ha, hh])
        refine ⟨p :: tail, ht.cons_cons p, ?_, ⟨ha, hv⟩, ?_⟩
        · simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
        · exact fun hh => hr hh.1

/-- Prime-word uniqueness is reused from the accepted original P2 API.
It rules out a different rejecting retained representation of the SAME b. -/
theorem fixed_rough_support_of_exit_continuation
    (allowing rejecting : List ℕ → Bool) (N cap b : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ p1SignedExitStates
      (p1CommonAdmissionPolicy (oddFirstExitPolicy allowing) (oddFirstExitPolicy rejecting))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (ha : oddFirstExitPolicy allowing state.positive state.selectedPrefix = true)
    (tail : List ℕ) (hp : b = state.selectedPrefix.prod * tail.prod)
    (ht : List.Sublist tail state.remaining)
    (hv : FirstExitValidSelection (oddFirstExitPolicy allowing)
      state.selectedPrefix state.positive tail) :
    b ∈ fixedRoughSupport allowing N cap w z ∧
      b ∉ fixedRoughSupport rejecting N cap w z := by
  obtain ⟨chosen, hc, he, hallow, hreject⟩ := exit_continuation_word
    (oddFirstExitPolicy allowing) (oddFirstExitPolicy rejecting) (fun _ => 1)
    [] (roughPrimeUniverse N cap w z) true 1 state hs ha tail ht hv
  have hword : chosen = state.selectedPrefix.reverse ++ tail := by
    simpa only [List.append_nil, List.reverse_reverse, List.reverse_append] using
      congrArg List.reverse he
  have hprod : chosen.prod = b := by
    rw [hword, List.prod_append, List.prod_reverse, ← hp]
  constructor
  · exact (mem_firstExitRetainedModuli_iff_validSelection
      (oddFirstExitPolicy allowing) (roughPrimeUniverse N cap w z) b).mpr
        ⟨chosen, hc, hallow, hprod⟩
  · intro hb
    obtain ⟨other, ho, hr, hop⟩ := (mem_firstExitRetainedModuli_iff_validSelection
      (oddFirstExitPolicy rejecting) (roughPrimeUniverse N cap w z) b).mp hb
    have hsame : other = chosen :=
      (P2LowerCanonicalRetainedTrace.actual_chosen_eq_canonical N cap w z other ho hop).trans
        (P2LowerCanonicalRetainedTrace.actual_chosen_eq_canonical N cap w z chosen hc hprod).symm
    exact hreject (hsame ▸ hr)

open P1OriginalHistoricalResidualCarrier
  (RealizedRoughContinuation fixed_rough_modulus_realized_continuation)

theorem realized_continuation_iff_support_difference
    (allowing rejecting : List ℕ → Bool) (N cap b : ℕ) (w z : ℝ) :
    RealizedRoughContinuation allowing rejecting N cap w z b ↔
      b ∈ fixedRoughSupport allowing N cap w z ∧
        b ∉ fixedRoughSupport rejecting N cap w z := by
  constructor
  · rintro ⟨state, hs, hpos, ha, _, tail, hp, _, ht, hv⟩
    exact fixed_rough_support_of_exit_continuation allowing rejecting N cap b w z state hs
      (by simpa only [oddFirstExitPolicy, hpos, Bool.false_or] using ha) tail hp ht hv
  · rintro ⟨ha, hr⟩
    exact fixed_rough_modulus_realized_continuation allowing rejecting N cap b w z ha hr

open P1OriginalHistoricalRoughOwnerPartition (Realizes changedRough fibre)
open P1OriginalHistoricalCoefficientDictionary (roughMaskDelta commonRoughSupport)

/-- The mask and changed-support membership follow from the actual tests and
the literal admitting continuation, rather than being assumed. -/
theorem realizes_of_actual_continuation
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ) (b : ℕ)
    (hs : state ∈ p1SignedExitStates
      (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (hpos : state.positive = false)
    (hdiff : old state.selectedPrefix ≠ fresh state.selectedPrefix)
    (tail : List ℕ) (hp : b = state.selectedPrefix.prod * tail.prod)
    (ht : List.Sublist tail state.remaining)
    (hv : (old state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy old)
          state.selectedPrefix state.positive tail) ∨
      (fresh state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy fresh)
          state.selectedPrefix state.positive tail)) :
    Realizes old fresh N cap w z state b ∧ b ∈ changedRough old fresh N cap w z := by
  have hpre : List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z) := by
    have hall := P1OriginalHistoricalCanonicalOwnerWord.selected_remaining_sublist
      _ (fun _ => 1) [] (roughPrimeUniverse N cap w z) true 1 state hs
    simp only [List.reverse_nil, List.nil_append] at hall
    exact (List.sublist_append_left _ _).trans hall
  have hmask : roughMaskDelta old fresh N cap w z b =
      (if fresh state.selectedPrefix = true then 1 else -1) := by
    rcases hv with ⟨ha, hv⟩ | ⟨ha, hv⟩
    · have hf : fresh state.selectedPrefix = false := by
        cases hh : fresh state.selectedPrefix <;> simp_all
      obtain ⟨ho, hn⟩ := fixed_rough_support_of_exit_continuation old fresh N cap b w z state hs
        (by simpa only [oddFirstExitPolicy, hpos, Bool.false_or] using ha) tail hp ht hv
      simp [roughMaskDelta, ho, hn, hf]
    · have hswap : p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh) =
          p1CommonAdmissionPolicy (oddFirstExitPolicy fresh) (oddFirstExitPolicy old) := by
        funext positive pre
        simp only [p1CommonAdmissionPolicy, Bool.and_comm]
      obtain ⟨hf, hn⟩ := fixed_rough_support_of_exit_continuation fresh old N cap b w z state
        (hswap ▸ hs) (by simpa only [oddFirstExitPolicy, hpos, Bool.false_or] using ha) tail hp ht hv
      simp [roughMaskDelta, hf, hn, ha]
  have hnonzero : roughMaskDelta old fresh N cap w z b ≠ 0 := by
    rw [hmask]
    split <;> norm_num
  have hcommon : b ∈ commonRoughSupport old fresh N cap w z := by
    by_contra hn
    simp only [commonRoughSupport, Finset.mem_union, not_or] at hn
    exact hnonzero (by simp [roughMaskDelta, hn.1, hn.2])
  exact ⟨⟨hs, hpos, hdiff, hmask, hpre, tail, hp, ht, hv⟩,
    Finset.mem_filter.mpr ⟨hcommon, hnonzero⟩⟩

/-- An exact fibre test with no owner choice, rough-mask equation or
changedRough premise. The actual common path and SAME valid tail remain. -/
theorem fibre_iff_actual_continuation
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ) (b : ℕ) :
    b ∈ fibre old fresh N cap w z state ↔
      state ∈ p1SignedExitStates
        (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      state.positive = false ∧ old state.selectedPrefix ≠ fresh state.selectedPrefix ∧
      ∃ tail : List ℕ, b = state.selectedPrefix.prod * tail.prod ∧
        List.Sublist tail state.remaining ∧
        ((old state.selectedPrefix = true ∧
          FirstExitValidSelection (oddFirstExitPolicy old)
            state.selectedPrefix state.positive tail) ∨
         (fresh state.selectedPrefix = true ∧
          FirstExitValidSelection (oddFirstExitPolicy fresh)
            state.selectedPrefix state.positive tail)) := by
  rw [P1OriginalHistoricalOwnerUniqueness.fibre_iff_realizes]
  constructor
  · rintro ⟨_, hs, hpos, hd, _, _, ht⟩
    exact ⟨hs, hpos, hd, ht⟩
  · rintro ⟨hs, hpos, hd, tail, hp, ht, hv⟩
    exact (realizes_of_actual_continuation old fresh N cap w z state b hs hpos hd tail hp ht hv).symm

end
end ImbalancedChen.P1OriginalHistoricalContinuationSupport
