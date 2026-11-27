import ImbalancedChen.P1OriginalHistoricalCoefficientDictionary
import ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport

/-!
# First-disagreement witnesses for the actual attached historical coefficient

SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original physical coefficient can be nonzero only when its unique rough
factor is retained by exactly one policy. The existing common-tree witness
then locates an actual first different admission. Its primes divide this same
complete physical modulus, even after the small Rosser factor is attached.

This supplies provenance of a nonzero historical summand. It does not select
whole-atom groups, remove squarefreeness, or estimate the medium discrepancy.
The original signed attachment and the fresh-minus-old policy order remain.
-/

namespace ImbalancedChen.P1OriginalHistoricalFirstDisagreement

noncomputable section
open Classical
open P1Full87TrueDPolicyDelta
  (trueDDeltaSupport trueDDeltaRho trueDDeltaRho_zero_outside
    trueDDeltaSupport_squarefree)
open P1OriginalHistoricalCoefficientDictionary
  (commonRoughSupport roughMaskDelta trueDDeltaSupport_eq_smallRoughModuli
    trueDDeltaRho_mul)

private theorem physical_mem_of_nonzero
    (old fresh : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ)
    (hd : trueDDeltaRho old fresh N cap w z L d ≠ 0) :
    d ∈ trueDDeltaSupport old fresh N cap w z := by
  by_contra hnot
  exact hd (trueDDeltaRho_zero_outside old fresh N cap w z L hnot)

/-- The existing actual attachment identity forces a genuine rough-mask
change; neither small Rosser member is swapped when the policy changes. -/
theorem nonzero_has_changed_rough_factor
    (old fresh : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ)
    (hd : trueDDeltaRho old fresh N cap w z L d ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ commonRoughSupport old fresh N cap w z,
        a * b = d ∧ roughMaskDelta old fresh N cap w z b ≠ 0 := by
  have hmem := physical_mem_of_nonzero old fresh N cap d w z L hd
  rw [trueDDeltaSupport_eq_smallRoughModuli, smallRoughModuli] at hmem
  obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hmem
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  refine ⟨a, ha, b, hb, heq, ?_⟩
  intro hz
  apply hd
  rw [← heq, trueDDeltaRho_mul old fresh N cap w z L ha hb, hz, zero_mul]

private theorem rough_change_gives_generic_difference
    (old fresh : List ℕ → Bool) (N cap b : ℕ) (w z : ℝ)
    (hb : roughMaskDelta old fresh N cap w z b ≠ 0) :
    p1PolicyCoefficientDifference (oddFirstExitPolicy old)
      (oddFirstExitPolicy fresh) (roughPrimeUniverse N cap w z) b ≠ 0 := by
  apply (p1_policyCoefficientDifference_ne_zero_iff_mem_symmDifference
    (oddFirstExitPolicy old) (oddFirstExitPolicy fresh)
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) b).mpr
  change b ∈ (fixedRoughSupport fresh N cap w z \ fixedRoughSupport old N cap w z) ∪
    (fixedRoughSupport old N cap w z \ fixedRoughSupport fresh N cap w z)
  by_cases hf : b ∈ fixedRoughSupport fresh N cap w z <;>
    by_cases ho : b ∈ fixedRoughSupport old N cap w z <;>
    simp_all [roughMaskDelta]

/-- An actual nonzero complete-modulus coefficient has an original common
tree first-disagreement witness on its unique rough factor. The witness is
at an odd admission, uses the same target-deleted rough universe, and every
prime in its literal stored history is a prime factor of the complete d. -/
theorem nonzero_has_actual_first_disagreement
    (old fresh : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ)
    (h : ℕ → ℝ) (hd : trueDDeltaRho old fresh N cap w z L d ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ commonRoughSupport old fresh N cap w z,
        a * b = d ∧
        ∃ state ∈ p1SignedExitStates
          (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
          h [] true 1 (roughPrimeUniverse N cap w z),
          state.positive = false ∧
          old state.selectedPrefix ≠ fresh state.selectedPrefix ∧
          List.Sublist state.selectedPrefix.reverse (roughPrimeUniverse N cap w z) ∧
          ∀ p ∈ state.selectedPrefix, p ∈ d.primeFactors := by
  obtain ⟨a, ha, b, hb, hab, hchange⟩ :=
    nonzero_has_changed_rough_factor old fresh N cap d w z L hd
  obtain ⟨state, hstate, hneq, hsub, hfactor⟩ :=
    p1_coefficientDifference_ne_zero_firstDisagreement
      (oddFirstExitPolicy old) (oddFirstExitPolicy fresh) h
      (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
      (fun _ hp => mem_roughPrimeUniverse_prime hp) b
      (rough_change_gives_generic_difference old fresh N cap b w z hchange)
  have hodd : state.positive = false := by
    cases hp : state.positive <;> simp_all [oddFirstExitPolicy]
  have hpolicy : old state.selectedPrefix ≠ fresh state.selectedPrefix := by
    simpa only [oddFirstExitPolicy, hodd, Bool.false_or] using hneq
  have hbd : b ∣ d := ⟨a, by simpa only [Nat.mul_comm] using hab.symm⟩
  have hd0 : d ≠ 0 :=
    (trueDDeltaSupport_squarefree old fresh N cap w z
      (physical_mem_of_nonzero old fresh N cap d w z L hd)).ne_zero
  refine ⟨a, ha, b, hb, hab, state, hstate, hodd, hpolicy, hsub, ?_⟩
  intro p hp
  obtain ⟨hpp, hpb, _⟩ := Nat.mem_primeFactors.mp (hfactor p hp)
  exact Nat.mem_primeFactors.mpr ⟨hpp, hpb.trans hbd, hd0⟩

end

end ImbalancedChen.P1OriginalHistoricalFirstDisagreement
