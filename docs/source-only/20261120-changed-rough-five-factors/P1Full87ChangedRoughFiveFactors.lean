import ImbalancedChen.P1Full87ChangedRoughCausalWitness
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous actual RAW/LICENSED rough-carrier disagreement witness has a
selected rank > 4, but this alone does not yet give an arithmetic bound
on the modulus. On the literal nodup decreasing rough-prime universe, the
selected history is a *distinct* subset of b.primeFactors. Hence any
genuinely changed rough modulus has at least FIVE distinct prime factors.

This is a one-sided support obstruction, not a rank-eight ownership
certificate and not an analytic estimate. Rank five or later first
disagreements need not belong to any of the 87 eighth owner cells.
The original two policies, their common history, and the small-prime
beta density remain completely unchanged.
-/

namespace ImbalancedChen.P1Full87ChangedRoughFiveFactors

noncomputable section
open Classical
open scoped BigOperators

/-- A selected history of length >= 5 in the original nodup rough carrier
forces at least five *distinct* prime factors of its original modulus.
This uses the literal selected list, not a deduplicated owner list. -/
private theorem primeFactor_card_ge_five_of_history
    (carrier : List ℕ) (b : ℕ) (state : FirstExitDepthState ℕ)
    (hnodup : carrier.Nodup)
    (hsub : state.selectedPrefix.reverse <+ carrier)
    (hfactor : ∀ p ∈ state.selectedPrefix, p ∈ b.primeFactors)
    (hlate : 4 < state.selectedPrefix.length) :
    5 ≤ b.primeFactors.card := by
  classical
  have hrev : state.selectedPrefix.reverse.Nodup := hnodup.sublist hsub
  have hselected : state.selectedPrefix.Nodup := by
    simpa using hrev
  have hsubset : state.selectedPrefix.toFinset ⊆ b.primeFactors := by
    intro p hp
    exact hfactor p (List.mem_toFinset.mp hp)
  have hcard : state.selectedPrefix.toFinset.card ≤ b.primeFactors.card :=
    Finset.card_le_card hsubset
  have hlen :
      state.selectedPrefix.toFinset.card = state.selectedPrefix.length :=
    List.toFinset_card_of_nodup hselected
  omega

/-- No rough modulus with at most four distinct prime factors can occur
in the actual RAW/LICENSED *symmetric difference*. This is an exact
fixed-N support exclusion, with no number-theoretic distribution input. -/
theorem actual_full87_changed_rough_ge_five_primeFactors
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap b : ℕ) (w z : ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    b ∈
      (fixedRoughSupport (S false) N cap w z \
       fixedRoughSupport (R false) N cap w z) ∪
      (fixedRoughSupport (R false) N cap w z \
       fixedRoughSupport (S false) N cap w z) →
    5 ≤ b.primeFactors.card := by
  dsimp only
  intro hb
  obtain ⟨state, _hstate, _hodd, hlate, _hchange, hsub, hfactor⟩ :=
    P1Full87ChangedRoughCausalWitness.actual_full87_changed_rough_has_late_causal_witness
      delta n e q om N cap b w z hb
  exact primeFactor_card_ge_five_of_history
    (roughPrimeUniverse N cap w z) b state
    (roughPrimeUniverse_nodup N cap w z) hsub hfactor hlate

/-- The same genuine first-disagreement witness also has ODD selected
parity, not merely a length greater than four. It follows from the sign
invariant of the *same* common-exit recursion, not from the geometry of
any rank-eight cell. Thus possible first different tests are at ranks
5, 7, 9, ... (without asserting they all occur). -/
theorem actual_full87_changed_rough_has_odd_disagreement
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap b : ℕ) (w z : ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    b ∈
      (fixedRoughSupport (S false) N cap w z \
       fixedRoughSupport (R false) N cap w z) ∪
      (fixedRoughSupport (R false) N cap w z \
       fixedRoughSupport (S false) N cap w z) →
    ∃ state ∈
        p1SignedExitStates
          (p1CommonAdmissionPolicy (oddFirstExitPolicy (R false))
            (oddFirstExitPolicy (S false)))
          (fun _ : ℕ => (1 : ℝ)) [] true 1
          (roughPrimeUniverse N cap w z),
      evenListLength state.selectedPrefix = false ∧
      4 < state.selectedPrefix.length ∧
      (R false) state.selectedPrefix ≠ (S false) state.selectedPrefix ∧
      state.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z ∧
      ∀ p ∈ state.selectedPrefix, p ∈ b.primeFactors := by
  dsimp only
  intro hb
  obtain ⟨state, hstate, hodd, hlate, hchange, hsub, hfactor⟩ :=
    P1Full87ChangedRoughCausalWitness.actual_full87_changed_rough_has_late_causal_witness
      delta n e q om N cap b w z hb
  have hparity : state.positive = evenListLength state.selectedPrefix :=
    (p1_mem_exitStates_sign_mass
      (p1CommonAdmissionPolicy
        (oddFirstExitPolicy
          (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false))
        (oddFirstExitPolicy
          (P4AOriginalFull87LicensedSixthPolicy.policy
            delta n e q om (N : ℝ) false)))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1
      (by rfl) (by simp) state hstate).1
  refine ⟨state, hstate, ?_, hlate, hchange, hsub, hfactor⟩
  exact hparity.symm.trans hodd

/-- Operational density consequence: the two REAL physical coefficient
densities differ only on rough moduli with at least five distinct prime
factors. Both ORIGINAL supports retain their own signed contributions;
no high-factor term is replaced by an unrelated sieve bound. -/
theorem actual_full87_true_d_density_only_ge_five_primeFactors
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let F := fixedRoughSupport (S false) N cap w z
    let O := fixedRoughSupport (R false) N cap w z
    physicalDensitySum
      (P1Full87TrueDPolicyDelta.trueDDeltaSupport
        (R false) (S false) N cap w z)
      (P1Full87TrueDPolicyDelta.trueDDeltaRho
        (R false) (S false) N cap w z L) =
      (∑ b ∈ (F \ O).filter (fun b => 5 ≤ b.primeFactors.card),
        P1Full87TrueDRoughSymmDiffDensity.commonRoughDensityTerm
          N cap w L b) -
      (∑ b ∈ (O \ F).filter (fun b => 5 ≤ b.primeFactors.card),
        P1Full87TrueDRoughSymmDiffDensity.commonRoughDensityTerm
          N cap w L b) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let F := fixedRoughSupport (S false) N cap w z
  let O := fixedRoughSupport (R false) N cap w z
  have hF : (F \ O).filter (fun b => 5 ≤ b.primeFactors.card) = F \ O := by
    apply Finset.filter_eq_self.mpr
    intro b hb
    exact actual_full87_changed_rough_ge_five_primeFactors
      delta n e q om N cap b w z (Finset.mem_union.mpr
        (Or.inl (by simpa only [F, O] using hb)))
  have hO : (O \ F).filter (fun b => 5 ≤ b.primeFactors.card) = O \ F := by
    apply Finset.filter_eq_self.mpr
    intro b hb
    exact actual_full87_changed_rough_ge_five_primeFactors
      delta n e q om N cap b w z (Finset.mem_union.mpr
        (Or.inr (by simpa only [F, O] using hb)))
  have hprior :=
    P1Full87TrueDRoughSymmDiffDensity.actual_full87_true_d_density_eq_changed_rough
      delta n e q om N cap w z L
  dsimp only at hprior
  simpa only [F, O, hF, hO] using hprior

end
end ImbalancedChen.P1Full87ChangedRoughFiveFactors
