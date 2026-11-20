import ImbalancedChen.OriginalFourthRoughCutoffStateLicense
import ImbalancedChen.ActualUpperPolicyFiniteBridge

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Sharp dynamic-Q support for the ORIGINAL fourth physical coefficient.
The small factor, rough factor, sign-dependent small Rosser weight and
native original policy remain the exact actualSmallRoughRho factors.
The rough factor's prime-factor rank constructs a genuine physical rough
frontier. At rank at least four its strict modulus bound is the attained
original owned Q, rather than only the global Theta ceiling.

The full physical modulus is strictly below smallLevel times that SAME Q.
Low-rank branches, including the empty rough factor, are retained as a
separate exact alternative. No independent beta is factored out, and no
final coefficient support or analytic distribution bound is assumed.
-/

namespace ImbalancedChen.OriginalFourthPhysicalOwnedModulusSupport20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFourthSuccessorTransition20261026b
open OriginalFourthRoughCutoffStateLicense20261026b
open Part3.ActualAttachedRoughFrontier

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega : ℝ)
  (licensed : ProducerRow → Prop)

/-- The actual same-Q ordinary license supplies the pinned native full
square support on the original chronological prime list. This is a
conclusion on real source states, not a factorization-support premise. -/
theorem actual_owned_frontier_dwell
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z : ℝ) (weight : ℕ → ℝ)
    (rank : ℕ) (hrank : 4 ≤ rank) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    actualDwellSupport
      (producerFrozenLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed
        state.selectedPrefix) state.selectedPrefix.reverse := by
  have hadmissible := actual_rough_frontier_owned_admissible records e chi m omega licensed
    N cap hN w z weight rank hrank state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse N cap w z) state hstate
  apply Part3.ActualCompactAllRankSupport.upper_set_dwell_support state.selectedPrefix.reverse
    (fun p hp => mem_roughPrimeUniverse_prime (hsub.subset hp))
    ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
  simpa only [List.toFinset_reverse] using hadmissible.2

/-- The actual retained rough factor supplies its own history and cap.
The inclusive physical cutoff w is kept throughout. -/
theorem actual_retained_rough_ownedQ
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z : ℝ) (b : ℕ)
    (hb : b ∈ firstExitRetainedModuli
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      (roughPrimeUniverse N cap w z))
    (hrank : 4 ≤ ArithmeticFunction.cardFactors b) :
    ∃ state ∈ firstExitDepthFrontier (ArithmeticFunction.cardFactors b)
        (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z),
      state.selectedPrefix.prod = b ∧
      ordinaryRosserPrefixAdmissible false
        (producerFrozenLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed
          state.selectedPrefix) state.selectedPrefix ∧
      (b : ℝ) < producerFrozenLevel4 e chi m omega (N : ℝ)
        (fourthFamily records) licensed state.selectedPrefix := by
  obtain ⟨chosen, hsub, hvalid, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      (roughPrimeUniverse N cap w z) b).mp hb
  have hprime : ∀ p ∈ chosen, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset hp)
  have hfactorRank : ArithmeticFunction.cardFactors b = chosen.length := by
    rw [← hprod]
    exact cardFactors_list_prod_eq_length_of_primes chosen hprime
  obtain ⟨state, hstateRaw, hselected⟩ := valid_selection_frontier_witness
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    (fun _ => 1) hsub [] true 1 hvalid
  have hstate : state ∈ firstExitDepthFrontier (ArithmeticFunction.cardFactors b)
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only [List.length_nil, zero_add, hfactorRank] using hstateRaw
  have hstateProd : state.selectedPrefix.prod = b := by
    simpa only [hselected, List.append_nil, List.prod_reverse] using hprod
  have hadmissible := actual_rough_frontier_owned_admissible records e chi m omega licensed
    N cap hN w z (fun _ => 1) (ArithmeticFunction.cardFactors b) hrank state hstate
  refine ⟨state, hstate, hstateProd, hadmissible, ?_⟩
  rw [← hstateProd]
  exact hadmissible.1

/-- Exact physical source decomposition with a sharp owned-Q bound on
every high-rank branch. The low-rank alternative is never discarded. -/
theorem actual_nonzero_physical_ownedQ_support
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (q : ℕ)
    (hq : actualSmallRoughRho
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed false)
      N cap w z L q ≠ 0) :
    ∃ a b : ℕ, a ∈ actualSmallRosserSupport N cap w ∧ (a : ℝ) < L ∧
      q = a * b ∧
      fixedRoughCoefficient
        (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed false)
        N cap w z b ≠ 0 ∧
      (ArithmeticFunction.cardFactors b < 4 ∨
        ∃ state ∈ firstExitDepthFrontier (ArithmeticFunction.cardFactors b)
            (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
            (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z),
          state.selectedPrefix.prod = b ∧
          ordinaryRosserPrefixAdmissible false
            (producerFrozenLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed
              state.selectedPrefix) state.selectedPrefix ∧
          (q : ℝ) < L * producerFrozenLevel4 e chi m omega (N : ℝ)
            (fourthFamily records) licensed state.selectedPrefix) := by
  obtain ⟨a, ha, b, hb, hprod, haL, hbne⟩ := actualSmallRoughRho_ne_zero_factors
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed false)
    N cap w z L hq
  refine ⟨a, b, ha, haL, hprod, hbne, ?_⟩
  by_cases hrank : 4 ≤ ArithmeticFunction.cardFactors b
  · have hbret : b ∈ firstExitRetainedModuli
        (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
        (roughPrimeUniverse N cap w z) := by
      rw [← UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
        (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
        (fun pre => OriginalFourthSuccessorTransition20261026b.policy_even
          records e chi m omega (N : ℝ) licensed pre) N cap w z]
      exact hb
    obtain ⟨state, hstate, hstateProd, hadmissible, hbQ⟩ :=
      actual_retained_rough_ownedQ records e chi m omega licensed N cap hN w z b hbret hrank
    apply Or.inr
    refine ⟨state, hstate, hstateProd, hadmissible, ?_⟩
    have hL : 0 < L := lt_of_le_of_lt (Nat.cast_nonneg a) haL
    rw [hprod, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg b)).trans_lt
      (mul_lt_mul_of_pos_left hbQ hL)
  · exact Or.inl (by omega)

end
end ImbalancedChen.OriginalFourthPhysicalOwnedModulusSupport20261026b
