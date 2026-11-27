import ImbalancedChen.P1OriginalHistoricalFirstDisagreement

/-!
# The literal residual carrier after the first differing admission

Strengthen the accepted first-disagreement induction by retaining the actual
unprocessed chosen tail and its valid continuation. A prime-factor-divisibility
witness alone does not expose this ordering information. No analytic bound or
free-tensor identity is assumed here.
-/

namespace ImbalancedChen.P1OriginalHistoricalResidualCarrier

noncomputable section
open Classical

/-- The selected tail is a sublist of the recorded remaining carrier and is
valid for the admitting policy, not an arbitrary collection of divisor primes. -/
theorem valid_selection_first_disagreement_tail
    (allowing rejecting : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    {chosen carrier : List ℕ} (hsub : List.Sublist chosen carrier)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (hallow : FirstExitValidSelection allowing pre positive chosen)
    (hreject : ¬FirstExitValidSelection rejecting pre positive chosen) :
    ∃ state ∈ p1SignedExitStates (p1CommonAdmissionPolicy allowing rejecting)
        h pre positive mass carrier,
      allowing state.positive state.selectedPrefix = true ∧
      rejecting state.positive state.selectedPrefix = false ∧
      ∃ tail : List ℕ,
        chosen.reverse ++ pre = tail.reverse ++ state.selectedPrefix ∧
        List.Sublist tail state.remaining ∧
        FirstExitValidSelection allowing state.selectedPrefix state.positive tail := by
  induction hsub generalizing pre positive mass with
  | slnil => exact False.elim (hreject trivial)
  | cons p hsub ih =>
      obtain ⟨state, hs, ha, hr, tail, heq, ht, hv⟩ := ih pre positive mass hallow hreject
      refine ⟨state, ?_, ha, hr, tail, heq, ht, hv⟩
      rw [p1SignedExitStates]
      exact List.mem_append_left _ hs
  | @cons_cons chosenTail carrierTail p hsub ih =>
      obtain ⟨ha, htail⟩ := hallow
      by_cases hr : rejecting (!positive) (p :: pre) = true
      · have hn : ¬FirstExitValidSelection rejecting (p :: pre) (!positive) chosenTail :=
          fun hv => hreject ⟨hr, hv⟩
        obtain ⟨state, hs, ha', hr', tail, heq, ht, hv⟩ :=
          ih (p :: pre) (!positive) (mass * h p) htail hn
        refine ⟨state, ?_, ha', hr', tail, ?_, ht, hv⟩
        · have hc : p1CommonAdmissionPolicy allowing rejecting (!positive) (p :: pre) = true := by
            simp [p1CommonAdmissionPolicy, ha, hr]
          rw [p1SignedExitStates, if_pos hc]
          exact List.mem_append_right _ hs
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq
      · have hrfalse : rejecting (!positive) (p :: pre) = false := by
          cases hb : rejecting (!positive) (p :: pre) <;> simp_all
        let state : FirstExitDepthState ℕ :=
          { selectedPrefix := p :: pre, positive := !positive,
            mass := mass * h p, remaining := carrierTail }
        refine ⟨state, ?_, ha, hrfalse, chosenTail, ?_, hsub, htail⟩
        · have hc : p1CommonAdmissionPolicy allowing rejecting (!positive) (p :: pre) ≠ true := by
            simp [p1CommonAdmissionPolicy, ha, hrfalse]
          rw [p1SignedExitStates, if_neg hc]
          exact List.mem_append_right _ (by simp [state])
        · simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          rfl

/-- A genuinely changed retained modulus factors into the literal first
disagreement prefix and a valid ordered selection in its actual residual carrier. -/
theorem retained_modulus_first_disagreement_factorization
    (allowing rejecting : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (b : ℕ)
    (hb : b ∈ firstExitRetainedModuli allowing carrier)
    (hn : b ∉ firstExitRetainedModuli rejecting carrier) :
    ∃ state ∈ p1SignedExitStates (p1CommonAdmissionPolicy allowing rejecting)
        h [] true 1 carrier,
      allowing state.positive state.selectedPrefix = true ∧
      rejecting state.positive state.selectedPrefix = false ∧
      ∃ tail : List ℕ,
        b = state.selectedPrefix.prod * tail.prod ∧
        List.Sublist state.selectedPrefix.reverse carrier ∧
        List.Sublist tail state.remaining ∧
        FirstExitValidSelection allowing state.selectedPrefix state.positive tail := by
  obtain ⟨chosen, hsub, hv, hp⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection allowing carrier b).mp hb
  have hnvalid : ¬FirstExitValidSelection rejecting [] true chosen := by
    intro hv'
    exact hn ((mem_firstExitRetainedModuli_iff_validSelection rejecting carrier b).mpr
      ⟨chosen, hsub, hv', hp⟩)
  obtain ⟨state, hs, ha, hr, tail, heq, ht, hv'⟩ :=
    valid_selection_first_disagreement_tail allowing rejecting h hsub [] true 1 hv hnvalid
  have hchosen : chosen = state.selectedPrefix.reverse ++ tail := by
    have hh := congrArg List.reverse heq
    simpa only [List.append_nil, List.reverse_reverse, List.reverse_append] using hh
  have hprefix : List.Sublist state.selectedPrefix.reverse carrier := by
    rw [hchosen] at hsub
    exact (List.sublist_append_left _ _).trans hsub
  refine ⟨state, hs, ha, hr, tail, ?_, hprefix, ht, hv'⟩
  rw [← hp, hchosen, List.prod_append, List.prod_reverse]

/-- A physical rough modulus with its literal admitting continuation. The
orientation records which original policy admits and which rejects. -/
def RealizedRoughContinuation (allowing rejecting : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (b : ℕ) : Prop :=
  ∃ state ∈ p1SignedExitStates
      (p1CommonAdmissionPolicy (oddFirstExitPolicy allowing) (oddFirstExitPolicy rejecting))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z),
    state.positive = false ∧ allowing state.selectedPrefix = true ∧
    rejecting state.selectedPrefix = false ∧
    ∃ tail : List ℕ,
      b = state.selectedPrefix.prod * tail.prod ∧
      List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z) ∧
      List.Sublist tail state.remaining ∧
      FirstExitValidSelection (oddFirstExitPolicy allowing)
        state.selectedPrefix state.positive tail

theorem fixed_rough_modulus_realized_continuation
    (allowing rejecting : List ℕ → Bool) (N cap b : ℕ) (w z : ℝ)
    (hb : b ∈ fixedRoughSupport allowing N cap w z)
    (hn : b ∉ fixedRoughSupport rejecting N cap w z) :
    RealizedRoughContinuation allowing rejecting N cap w z b := by
  change b ∈ firstExitRetainedModuli (oddFirstExitPolicy allowing)
    (roughPrimeUniverse N cap w z) at hb
  change b ∉ firstExitRetainedModuli (oddFirstExitPolicy rejecting)
    (roughPrimeUniverse N cap w z) at hn
  obtain ⟨state, hs, ha, hr, tail, hp, hpre, ht, hv⟩ :=
    retained_modulus_first_disagreement_factorization
      (oddFirstExitPolicy allowing) (oddFirstExitPolicy rejecting)
      (fun _ => 1) (roughPrimeUniverse N cap w z) b hb hn
  have hodd : state.positive = false := by
    cases hh : state.positive <;> simp_all [oddFirstExitPolicy]
  refine ⟨state, hs, hodd, ?_, ?_, tail, hp, hpre, ht, hv⟩
  · simpa only [oddFirstExitPolicy, hodd, Bool.false_or] using ha
  · simpa only [oddFirstExitPolicy, hodd, Bool.false_or] using hr

/-- The actual signed historical coefficient supplies both the small factor
and the ordered residual rough selection. The two disjuncts retain the exact
fresh-only / old-only orientation; the attached coefficient is not exchanged. -/
theorem nonzero_has_realized_rough_continuation
    (old fresh : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ)
    (hd : P1Full87TrueDPolicyDelta.trueDDeltaRho old fresh N cap w z L d ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ P1OriginalHistoricalCoefficientDictionary.commonRoughSupport
        old fresh N cap w z,
        a * b = d ∧
        (RealizedRoughContinuation fresh old N cap w z b ∨
          RealizedRoughContinuation old fresh N cap w z b) := by
  obtain ⟨a, ha, b, hb, hab, hchange⟩ :=
    P1OriginalHistoricalFirstDisagreement.nonzero_has_changed_rough_factor
      old fresh N cap d w z L hd
  refine ⟨a, ha, b, hb, hab, ?_⟩
  by_cases hf : b ∈ fixedRoughSupport fresh N cap w z
  · by_cases ho : b ∈ fixedRoughSupport old N cap w z
    · exact False.elim (hchange (by
        simp [P1OriginalHistoricalCoefficientDictionary.roughMaskDelta, hf, ho]))
    · exact Or.inl (fixed_rough_modulus_realized_continuation fresh old N cap b w z hf ho)
  · have ho : b ∈ fixedRoughSupport old N cap w z := by
      by_contra hn
      exact hchange (by
        simp [P1OriginalHistoricalCoefficientDictionary.roughMaskDelta, hf, hn])
    exact Or.inr (fixed_rough_modulus_realized_continuation old fresh N cap b w z ho hf)

end
end ImbalancedChen.P1OriginalHistoricalResidualCarrier
