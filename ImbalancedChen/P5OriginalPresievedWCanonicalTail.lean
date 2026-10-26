import ImbalancedChen.P5OriginalPresievedRoughPrimeSlots
import ImbalancedChen.P5OriginalPresievedActiveDeltaFactors
import ImbalancedChen.P5ZU1011OriginalW16ActiveNativeFactors

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Canonical presieved rough slots are literally the original native residual
prime list. The existing odd-cubic native support supplier then gives the
real D-well tail used by W completion. No rank/fine-box construction or
new well-support hypothesis is introduced.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedWCanonicalTail

noncomputable section
open OriginalOrdinaryCommonBetaModel OriginalPresievedRoughPrimeSlots
open OriginalPresievedActiveDeltaFactors
open U1011OriginalFifteenJointSelectedSupport (residualPrimes actual_plus_residual_well)

/-- Two actual distinct decreasing prime lists of the same squarefree
rough divisor coincide literally. No permutation is substituted into W. -/
theorem canonical_slots_eq_native_residual {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    canonicalSlots N cap w Z d = residualPrimes d := by
  have hsf := fixedRoughSupport_squarefree (ordinaryRetainOdd L) N cap w Z hd
  have hcanonical := (List.toFinset_sort (r := (· ≥ ·))
    (canonicalSlots_nodup N cap w Z d)).mpr
    ((canonicalSlots_descending N cap w Z d).imp (fun h => h.le))
  rw [canonicalSlots_toFinset hd] at hcanonical
  have hresidual := (List.toFinset_sort (r := (· ≥ ·)) hsf.nodup_primeFactorsList.reverse).mpr
    (Nat.primeFactorsList_sorted d).reverse.pairwise
  change (residualPrimes d).toFinset.sort (· ≥ ·) = residualPrimes d at hresidual
  rw [residualPrimes, List.toFinset_reverse, Nat.toFinset_factors] at hresidual
  exact hcanonical.symm.trans hresidual

/-- The ACTUAL presieved rough support supplies D-well support for its
canonical slots through unchanged original native odd-cubic tests. -/
theorem canonical_rough_tail_well {N cap d : ℕ} {w Z L : ℝ}
    (hL : 1 < L) (hwZ : w ≤ Z)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    actualDwellSupport L (canonicalSlots N cap w Z d) := by
  have hnative := ordinary_rough_supported_native_active hL hwZ hd
  have hwell := actual_plus_residual_well hnative
  rw [← canonical_slots_eq_native_residual hd] at hwell
  exact hwell

/-- W completion receives the same ordered natural tail, with actual
product d and strict prime ceiling. The beta integer never enters it. -/
theorem canonical_rough_tail_data {N cap d : ℕ} {w Z L : ℝ}
    (hL : 1 < L) (hwZ : w ≤ Z)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    actualDwellSupport L (canonicalSlots N cap w Z d) ∧
      (canonicalSlots N cap w Z d).prod = d ∧
      ∀ p ∈ canonicalSlots N cap w Z d, Nat.Prime p ∧ (p : ℝ) < Z := by
  refine ⟨canonical_rough_tail_well hL hwZ hd, canonicalSlots_prod hd, ?_⟩
  intro p hp
  exact ⟨(canonicalSlots_prime_data hp).1, (canonicalSlots_prime_data hp).2.2.2⟩

end
end ImbalancedChen.P5Z.OriginalPresievedWCanonicalTail
