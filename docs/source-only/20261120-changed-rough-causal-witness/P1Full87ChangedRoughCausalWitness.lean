import ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport
import ImbalancedChen.P1Full87TrueDRoughSymmDiffDensity
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous physical-density identity isolates S_LICENSED \\ S_RAW and
S_RAW \\ S_LICENSED as *rough* modulus supports. A changed rough modulus
cannot be assigned an arbitrary geometric owner: it must first supply a
real causal policy disagreement reached by the SAME decreasing rough-prime
carrier.

Reuse the existing P1 first-disagreement theorem, rather than reimplementing
its one-occurrence traversal. Then apply the actual full87 policy equality
through rank four. The witness has odd sign, selected rank >= 5, and every
selected prime divides the original changed rough modulus. This is a precise
support obstruction to a false direct 87-cell ownership assertion, NOT yet a
bijection with changed/tagged/BOTH/rank9 cells, nor an H_N saving.
-/

namespace ImbalancedChen.P1Full87ChangedRoughCausalWitness

noncomputable section
open Classical
open scoped BigOperators

/-- One changed rough carrier yields a first genuine odd admission divergence.
The generic P1 coefficient-difference witness keeps its selected-prime
factor history; the rank bound follows from equality of the two *actual*
policy predicates through the common early ancestor. -/
private theorem changed_rough_first_late_disagreement
    (old fresh : List ℕ → Bool) (N cap b : ℕ) (w z : ℝ)
    (hfour : ∀ pre : List ℕ, pre.length ≤ 4 → old pre = fresh pre)
    (hb : b ∈
      (fixedRoughSupport fresh N cap w z \\
       fixedRoughSupport old N cap w z) ∪
      (fixedRoughSupport old N cap w z \\
       fixedRoughSupport fresh N cap w z)) :
    ∃ state ∈
        p1SignedExitStates
          (p1CommonAdmissionPolicy (oddFirstExitPolicy old)
            (oddFirstExitPolicy fresh))
          (fun _ : ℕ => (1 : ℝ)) [] true 1 (roughPrimeUniverse N cap w z),
      state.positive = false ∧
      4 < state.selectedPrefix.length ∧
      old state.selectedPrefix ≠ fresh state.selectedPrefix ∧
      state.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z ∧
      ∀ p ∈ state.selectedPrefix, p ∈ b.primeFactors := by
  classical
  let carrier := roughPrimeUniverse N cap w z
  have hsupport : b ∈
      (firstExitRetainedModuli (oddFirstExitPolicy fresh) carrier \\
       firstExitRetainedModuli (oddFirstExitPolicy old) carrier) ∪
      (firstExitRetainedModuli (oddFirstExitPolicy old) carrier \\
       firstExitRetainedModuli (oddFirstExitPolicy fresh) carrier) := by
    change b ∈
      (firstExitRetainedModuli (oddFirstExitPolicy fresh) carrier \\
       firstExitRetainedModuli (oddFirstExitPolicy old) carrier) ∪
      (firstExitRetainedModuli (oddFirstExitPolicy old) carrier \\
       firstExitRetainedModuli (oddFirstExitPolicy fresh) carrier) at hb
    exact hb
  have hnonzero :
      p1PolicyCoefficientDifference
        (oddFirstExitPolicy old) (oddFirstExitPolicy fresh) carrier b ≠ 0 :=
    (p1_policyCoefficientDifference_ne_zero_iff_mem_symmDifference
      (oddFirstExitPolicy old) (oddFirstExitPolicy fresh)
      carrier (roughPrimeUniverse_nodup N cap w z)
      (fun p hp => mem_roughPrimeUniverse_prime hp) b).2 hsupport
  obtain ⟨state, hstate, hchange, hsub, hfactor⟩ :=
    p1_coefficientDifference_ne_zero_firstDisagreement
      (oddFirstExitPolicy old) (oddFirstExitPolicy fresh)
      (fun _ : ℕ => (1 : ℝ)) carrier
      (roughPrimeUniverse_nodup N cap w z)
      (fun p hp => mem_roughPrimeUniverse_prime hp) b hnonzero
  have hodd : state.positive = false := by
    cases hp : state.positive with
    | false => rfl
    | true =>
        exfalso
        apply hchange
        simp [oddFirstExitPolicy, hp]
  have hreal : old state.selectedPrefix ≠ fresh state.selectedPrefix := by
    simpa [oddFirstExitPolicy, hodd] using hchange
  have hlate : 4 < state.selectedPrefix.length := by
    by_contra hnot
    exact hreal (hfour state.selectedPrefix (Nat.le_of_not_gt hnot))
  exact ⟨state, hstate, hodd, hlate, hreal, hsub, hfactor⟩

/-- The ACTUAL complete-sixth RAW versus LICENSED full87 source policies,
on the SAME rough-prime universe used by the density ledger. A changed
rough modulus necessarily contains an actual selected odd disagreement
of rank at least five among its prime factors. This witness is not
silently assigned to an eighth owner cell. -/
theorem actual_full87_changed_rough_has_late_causal_witness
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap b : ℕ) (w z : ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    b ∈
      (fixedRoughSupport (S false) N cap w z \\
       fixedRoughSupport (R false) N cap w z) ∪
      (fixedRoughSupport (R false) N cap w z \\
       fixedRoughSupport (S false) N cap w z) →
    ∃ state ∈
        p1SignedExitStates
          (p1CommonAdmissionPolicy (oddFirstExitPolicy (R false))
            (oddFirstExitPolicy (S false)))
          (fun _ : ℕ => (1 : ℝ)) [] true 1 (roughPrimeUniverse N cap w z),
      state.positive = false ∧
      4 < state.selectedPrefix.length ∧
      (R false) state.selectedPrefix ≠ (S false) state.selectedPrefix ∧
      state.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z ∧
      ∀ p ∈ state.selectedPrefix, p ∈ b.primeFactors := by
  dsimp only
  intro hb
  apply changed_rough_first_late_disagreement
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ) false)
    N cap b w z ?_ hb
  intro pre hlen
  exact (P4AOriginalFull87LicensedSixthPolicy.through_four_eq_raw
    delta n e q om (N : ℝ) false pre hlen).symm

end
end ImbalancedChen.P1Full87ChangedRoughCausalWitness
