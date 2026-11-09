import ImbalancedChen.P3HBMarkedMobiusFourDiagonal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
P3.6: the actual complete-product Mobius kernel and strict rough-HB
marking leave ONLY squarefree, even-outside-marked exceptions at an
even exact target. This genuinely strengthens the earlier 4 | N result:
N = 18 (2 mod 4) is not squarefree, so its full-product Mobius target
vanishes although the old four-divisibility argument does not apply.

Every equality uses the existing markedResidualKernel, original ordered
factorTuples, roughTupleWeight, labelled W, literal +3,-3,+1 HB signs,
and the SAME physical Q and integer rho. This is still a restricted
subfamily: unweighted markedRoughTargetAtQ and unknown final compiler
branches cannot be discarded. No off-target error, analytic saving or
geometric source admission is proved. SOURCE_ONLY / UNCOMPILED.
Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion sections 2-4.
-/

namespace ImbalancedChen.P3HBMarkedMobiusSquarefreeDiagonal

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBMarkedMobiusFourDiagonal
open ImbalancedChen.P3HBExternalEvenMarkedDiagonal
open ImbalancedChen.P3ActualMarkedResidualExactProduct
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- Exact target kernel vanishes for EVERY non-squarefree target, not
merely those divisible by four. This is a property of the genuine
complete-product Mobius factor, with no restrictions on physical q. -/
theorem markedResidualKernel_target_zero_of_nonsquarefree
    (r N q n : ℕ) (hfull : r * n = N)
    (hbad : ¬ Squarefree N) :
    markedResidualKernel r N q n = 0 := by
  unfold markedResidualKernel
  rw [hfull, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbad]
  simp

/-- The actual sorted fine-prime source also retains the full-product
Mobius; its target fibre is zero for any non-squarefree T. -/
theorem weightedSortedPP_target_zero_of_nonsquarefree
    (N : ℕ) (tau : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ) (hbad : ¬ Squarefree T) :
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
    rw [hfull, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbad]
    simp
  simp [hinner]

/-- The original ordered marked/rough HB subfamily, if its ACTUAL
global Mobius factor is present, has no non-squarefree target fibre. -/
theorem mobiusMarkedRoughTargetAtQ_zero_of_nonsquarefree
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (hbad : ¬ Squarefree N) :
    mobiusMarkedRoughTargetAtQ N n j q z y M W = 0 := by
  unfold mobiusMarkedRoughTargetAtQ
  apply Finset.sum_eq_zero
  intro marked hm
  apply Finset.sum_eq_zero
  intro hb hhb
  have hfull : marked.prod * hb.prod = N :=
    (Finset.mem_filter.mp hhb).2
  rw [markedResidualKernel_target_zero_of_nonsquarefree
    marked.prod N q hb.prod hfull hbad]
  simp

/-- For EVEN target and genuine strict rough HB cutoff, the
Mobius-weighted original family still restricts EXACTLY to even outside
marked integers; the global Mobius does not permit dropping the
squarefree even-marked remainder. -/
theorem mobiusMarkedRoughTargetAtQ_eq_even_marked
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    mobiusMarkedRoughTargetAtQ N n j q z y M W =
      mobiusMarkedRoughTargetAtQ N n j q z y
        (M.filter (fun marked => 2 ∣ marked.prod)) W := by
  classical
  unfold mobiusMarkedRoughTargetAtQ
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro marked hm
  by_cases heven : 2 ∣ marked.prod
  · simp [heven]
  · have hzero :
        (∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
            (fun hb => marked.prod * hb.prod = N),
          W (marked, hb) * roughTupleWeight z y (roles j) hb *
            markedResidualKernel marked.prod N q hb.prod) = 0 := by
      apply Finset.sum_eq_zero
      intro hb hhbmem
      obtain ⟨hhb, hfull⟩ := Finset.mem_filter.mp hhbmem
      have hw := odd_marked_target_occurrence_zero
        N n j z y marked hb hz hN hhb hfull heven
      rw [hw]
      simp
    simp [heven, hzero]

/-- No target occurrence with a nonzero product of the original rough
word and full-product Mobius kernel can avoid BOTH restrictions. -/
theorem surviving_mobius_target_requires_squarefree_even_marked
    (N n j q : ℕ) (z y : ℝ) (marked hb : List ℕ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n)
    (hfull : marked.prod * hb.prod = N)
    (hsurvive :
      roughTupleWeight z y (roles j) hb *
        markedResidualKernel marked.prod N q hb.prod ≠ (0 : ℂ)) :
    Squarefree N ∧ 2 ∣ marked.prod := by
  have hsquare : Squarefree N := by
    by_contra hbad
    have hkernel :
        markedResidualKernel marked.prod N q hb.prod = 0 :=
      markedResidualKernel_target_zero_of_nonsquarefree
        marked.prod N q hb.prod hfull hbad
    exact hsurvive (by simp [hkernel])
  have hrough : roughTupleWeight z y (roles j) hb ≠ 0 := by
    intro hw
    exact hsurvive (by simp [hw])
  exact ⟨hsquare, surviving_target_requires_even_marked
    N n j z y marked hb hz hN hhb hfull hrough⟩

/-- Genuine same-Q, same-INTEGER-rho order-three target ledger.
If N is squarefree, only even outside marked products remain.
Otherwise all full-product-Mobius terms vanish. Neither branch asserts
a bound for the unweighted external marked diagonal. -/
theorem signed_three_mobius_target_eq_squarefree_even_marked
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughTargetAtQ N n j q z y M W) =
      if Squarefree N then
        (∑ q ∈ Q, (rho q : ℂ) *
          ∑ j ∈ Finset.range 3,
            (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
              mobiusMarkedRoughTargetAtQ N n j q z y
                (M.filter (fun marked => 2 ∣ marked.prod)) W)
      else 0 := by
  classical
  by_cases hsquare : Squarefree N
  · rw [if_pos hsquare]
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mobiusMarkedRoughTargetAtQ_eq_even_marked
      N n j q z y M W hz hN]
  · rw [if_neg hsquare]
    apply Finset.sum_eq_zero
    intro q hq
    have hj :
        (∑ j ∈ Finset.range 3,
          (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
            mobiusMarkedRoughTargetAtQ N n j q z y M W) = 0 := by
      apply Finset.sum_eq_zero
      intro j hjmem
      rw [mobiusMarkedRoughTargetAtQ_zero_of_nonsquarefree
        N n j q z y M W hsquare]
      simp
    simp [hj]

end
end ImbalancedChen.P3HBMarkedMobiusSquarefreeDiagonal
