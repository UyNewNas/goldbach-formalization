import ImbalancedChen.P3HBEvenRoughTarget
import ImbalancedChen.P3ActualOriginalMarkedPrimeNoDiagonal
import ImbalancedChen.P3ActualWeightedFineSameRho

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2--4: the EXACT complete-product=N diagonal
of a mixed original fine-MARKED-prime word and original strictly rough
HB integer word.

If the original marked word is nonempty, each prime comes from the
real actualPrimeFineLabelFinset N tau alphabet, so its product cannot
divide N. If it is empty, its product is one; the residual HB integer
equals even N, and the actual rough projector annihilates every
ordered HB occurrence when 2 <= z.

The last result retains the real complete marked*HB product, original
positional multiplicities, +3,-3,+1 signs, arbitrary complex labelled
weight W, and the SAME physical q and integer rho in the literal
congruence-minus-exact-coprime-mean fineKernel. No W regularity,
arithmetic saving, causal compiler admission or external input is
claimed. An arbitrary even outside marked integer (not from the
original fine-prime alphabet) is NOT covered.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalMarkedFineTarget

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBEvenRoughTarget
open ImbalancedChen.P3ActualOriginalMarkedPrimeNoDiagonal
open ImbalancedChen.P3ActualWeightedFineSameRho

/-- Every actual full-product=N mixed occurrence is zero. The original
fine marked prime alphabet is essential in the nonempty branch. -/
theorem original_marked_fine_rough_occurrence_target_zero
    (N n j : ℕ) (tau z y : ℝ)
    (word marked hb : List ℕ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hm : marked ∈
      actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) word)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n)
    (hfull : marked.prod * hb.prod = N) :
    roughTupleWeight z y (roles j) hb = 0 := by
  have hhbprod : hb.prod = n :=
    (factorTuples_spec (2 * (j + 1)) n hb hhb).2.1
  by_cases hword : word = []
  · have hmarked : marked = [] := by
      simpa [hword, actualPrimeSlotBox] using hm
    have hn : n = N := by
      simpa [hmarked, hhbprod] using hfull
    subst n
    exact literal_occurrence_target_zero z y j N hz hN hb hhb
  · have hnot : ¬ marked.prod ∣ N :=
      original_prime_box_product_not_dvd
        N tau word marked hm hword
    exact (hnot ⟨hb.prod, hfull.symm⟩).elim

/-- The literal complete marked product, not merely the HB residual,
is tested against N in the same physical kernel. Empty and repeated
label occurrences remain in their original finite sources. -/
def originalMarkedFineRoughTargetTerm
    (N n j q : ℕ) (tau z y : ℝ)
    (word : List ℕ) (W : List ℕ × List ℕ → ℂ) : ℂ :=
  ∑ t ∈
    ((actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) word).product
      (factorTuples (2 * (j + 1)) n)).filter
        (fun t => t.1.prod * t.2.prod = N),
    W t * roughTupleWeight z y (roles j) t.2 *
      ((fineKernel N q (t.1.prod * t.2.prod) : ℝ) : ℂ)

/-- Zero for each actual original signed HB occurrence at ANY physical
modulus, including its exact coprime mean and Lean's q=0 convention. -/
theorem originalMarkedFineRoughTargetTerm_zero
    (N n j q : ℕ) (tau z y : ℝ)
    (word : List ℕ) (W : List ℕ × List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    originalMarkedFineRoughTargetTerm N n j q tau z y word W = 0 := by
  unfold originalMarkedFineRoughTargetTerm
  apply Finset.sum_eq_zero
  intro t ht
  obtain ⟨hpair, hfull⟩ := Finset.mem_filter.mp ht
  obtain ⟨hm, hhb⟩ := Finset.mem_product.mp hpair
  have hzero := original_marked_fine_rough_occurrence_target_zero
    N n j tau z y word t.1 t.2 hz hN hm hhb hfull
  rw [hzero]
  simp

/-- The ACTUAL +3,-3,+1 rough-HB order-three diagonal is zero after
the complete SAME integer-rho and physical-Q sum. This is an exact
source-local cancellation, NOT a PP or shifted-moment estimate. -/
theorem original_marked_fine_rough_three_same_rho_target_zero
    (N n : ℕ) (tau z y : ℝ)
    (word : List ℕ) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          originalMarkedFineRoughTargetTerm N n j q tau z y word W) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hj :
      (∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          originalMarkedFineRoughTargetTerm N n j q tau z y word W) = 0 := by
    apply Finset.sum_eq_zero
    intro j hjmem
    rw [originalMarkedFineRoughTargetTerm_zero
      N n j q tau z y word W hz hN]
    simp
  rw [hj]
  simp

end
end ImbalancedChen.P3HBOriginalMarkedFineTarget
