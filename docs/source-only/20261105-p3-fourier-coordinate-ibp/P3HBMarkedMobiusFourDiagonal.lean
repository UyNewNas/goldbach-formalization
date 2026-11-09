import ImbalancedChen.P3HBExternalEvenMarkedDiagonal
import ImbalancedChen.P3ActualMarkedResidualExactProduct
import ImbalancedChen.P3ActualWeightedFineSameRho
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree

/-!
P3.6: a genuine squarefree-versus-even-marked distinction for the
COMPLETE-product=T diagonal in sources which literally retain the
original full-product Mobius factor moebius (r * n).

The previous arbitrary-marked HB lemma proved only that a surviving
rough-HB diagonal must have EVEN outside marked product. It did NOT
make that even-marked exception zero. A different, genuinely original
arithmetic factor supplies an additional restriction: if 4 | T, then
the original complete-product Mobius coefficient itself is zero.

This applies to actual markedResidualKernel, actual weightedSortedPP,
and to the literal rough-HB occurrence only when the complete-product
Mobius factor is *present*. It does NOT assert that every HB word, every
marked carrier, or the final causal compiler retains that factor.

In particular T=30, marked=[2], rough residual 15, z=2 is NOT
excluded by the present argument: T is squarefree and mu(T) != 0.
Thus T congruent to 2 mod 4 remains an unpaid diagonal family.
Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2--4. SOURCE_ONLY/UNCOMPILED/KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBMarkedMobiusFourDiagonal

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualMarkedResidualExactProduct
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- A concrete 2-primary square obstruction, from the real global
Mobius arithmetic function. This is not a premise about a PP error. -/
theorem complete_mobius_zero_of_four_dvd (T : ℕ) (h4 : 4 ∣ T) :
    ArithmeticFunction.moebius T = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  have hno := (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two
  have h22 : 2 * 2 ∣ T := by
    simpa only [show (2 : ℕ) * 2 = 4 by norm_num] using h4
  exact hno h22

/-- In the ACTUAL existing marked residual kernel, mu(r*n) is evaluated
on the complete physical product, not on the HB residual alone.
The exact target fibre vanishes for 4 | T at EVERY q, without making a
coprimality or signed-rho cancellation assumption. -/
theorem markedResidualKernel_target_zero_of_four_dvd
    (r T q n : ℕ) (hfull : r * n = T) (h4 : 4 ∣ T) :
    markedResidualKernel r T q n = 0 := by
  unfold markedResidualKernel
  rw [hfull, complete_mobius_zero_of_four_dvd T h4]
  simp

/-- The original actual sorted prime source keeps its tuple-dependent W
and the original outside integer r in mu(r * product). The target
contribution is zero for 4 | T under the same physical q/rho, including
the exact coprime mean. Non-target source terms are not affected. -/
theorem weightedSortedPP_target_zero_of_four_dvd
    (N : ℕ) (tau : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ) (h4 : 4 ∣ T) :
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N tau blocks).filter
          (fun ps => r * ps.prod = T),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps * fineKernel T q (r * ps.prod)) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hinner :
      (∑ ps ∈ (actualPrimeFineLabelSortedTuples N tau blocks).filter
          (fun ps => r * ps.prod = T),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps * fineKernel T q (r * ps.prod)) = 0 := by
    apply Finset.sum_eq_zero
    intro ps hps
    have hfull : r * ps.prod = T := (Finset.mem_filter.mp hps).2
    rw [hfull, complete_mobius_zero_of_four_dvd T h4]
    simp
  simp [hinner]

/-- For the original integer rough-HB positions and arbitrary OUTSIDE
marked integer labels, this is exactly the existing full-product Mobius
markedResidualKernel, multiplied by the real literal rough HB weight.
It is intentionally a separate subfamily from arbitrary markedRoughTargetAtQ
which has no global Mobius factor. -/
def mobiusMarkedRoughTargetAtQ
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ))
    (W : List ℕ × List ℕ → ℂ) : ℂ :=
  ∑ marked ∈ M,
    ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
        (fun hb => marked.prod * hb.prod = N),
      W (marked, hb) * roughTupleWeight z y (roles j) hb *
        markedResidualKernel marked.prod N q hb.prod

/-- No positivity, no roughness cutoff and no extra marked alphabet
are needed on the mu-weighted diagonal when 4 | N. This statement does
NOT erase the unweighted exceptional family of the predecessor. -/
theorem mobiusMarkedRoughTargetAtQ_zero_of_four_dvd
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ))
    (W : List ℕ × List ℕ → ℂ) (h4 : 4 ∣ N) :
    mobiusMarkedRoughTargetAtQ N n j q z y M W = 0 := by
  unfold mobiusMarkedRoughTargetAtQ
  apply Finset.sum_eq_zero
  intro marked hm
  apply Finset.sum_eq_zero
  intro hb hhb
  have hfull : marked.prod * hb.prod = N :=
    (Finset.mem_filter.mp hhb).2
  rw [markedResidualKernel_target_zero_of_four_dvd
    marked.prod N q hb.prod hfull h4]
  simp

/-- The actual +3,-3,+1 ordered HB signs and the SAME physical Q and
integer rho preserve the exact vanishing in this only-if-global-mu
subfamily. No large-N PP or divisor moment is inferred. -/
theorem mobius_marked_rough_three_same_rho_target_zero_four_dvd
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ))
    (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (h4 : 4 ∣ N) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughTargetAtQ N n j q z y M W) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hj :
      (∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughTargetAtQ N n j q z y M W) = 0 := by
    apply Finset.sum_eq_zero
    intro j hjmem
    rw [mobiusMarkedRoughTargetAtQ_zero_of_four_dvd
      N n j q z y M W h4]
    simp
  simp [hj]

end
end ImbalancedChen.P3HBMarkedMobiusFourDiagonal
