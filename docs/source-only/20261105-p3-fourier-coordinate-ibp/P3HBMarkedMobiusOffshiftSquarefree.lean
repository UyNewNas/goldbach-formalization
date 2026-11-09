import ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
P3.6 — complete-product squarefree restriction for the ORIGINAL marked /
strict rough-HB off-target ledger, retaining the actual signed physical rho.

This is a new genuine arithmetic restriction on the predecessor's *nonzero*
complete-product shifted-divisor response. It uses the global Mobius which
is present in the explicitly qualified original markedResidualKernel source.
No extra filter is inserted into the original coefficient or into PP:
the squarefree filter is proved equal to the unrestricted original sum.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED. This is not a shifted-divisor
moment, not an estimate for arbitrary causal W_T, and not a PP saving.
Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2–4, original complete b != N shift and (F).
-/

namespace ImbalancedChen.P3HBMarkedMobiusOffshiftSquarefree

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualMarkedResidualExactProduct
open ImbalancedChen.P3HBMarkedMobiusPhysicalDiagonalFactor
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- Genuine full-product Mobius vanishes on any nonsquarefree
marked/HB product; the physical coprime mean and q are unrestricted. -/
theorem markedResidualKernel_zero_of_nonsquarefree
    (r N q n : ℕ) (hbad : ¬ Squarefree (r * n)) :
    markedResidualKernel r N q n = 0 := by
  unfold markedResidualKernel
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbad]
  simp

/-- The previous original labelled occurrence is identically zero
unless its entire marked-times-HB physical product is squarefree. -/
theorem offMarkedOccurrence_zero_of_nonsquarefree
    (j : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (marked hb : List ℕ)
    (hbad : ¬ Squarefree (marked.prod * hb.prod)) :
    offMarkedOccurrence j z y W marked hb = 0 := by
  unfold offMarkedOccurrence
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hbad]
  simp

/-- A surviving full-product-Mobius occurrence really has pairwise
coprime marked and HB products and EACH of those products is squarefree.
This follows from the pinned Nat.squarefree_mul_iff, not from a new
coefficient-class hypothesis. No HB label or repeated position is erased. -/
theorem offMarkedOccurrence_nonzero_coprime
    (j : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (marked hb : List ℕ)
    (h : offMarkedOccurrence j z y W marked hb ≠ 0) :
    Squarefree (marked.prod * hb.prod) ∧
    Nat.Coprime marked.prod hb.prod ∧
    Squarefree marked.prod ∧ Squarefree hb.prod := by
  have hsq : Squarefree (marked.prod * hb.prod) := by
    by_contra hbad
    exact h (offMarkedOccurrence_zero_of_nonsquarefree
      j z y W marked hb hbad)
  rcases (Nat.squarefree_mul_iff.mp hsq) with ⟨hcop, hmarked, hhb⟩
  exact ⟨hsq, hcop, hmarked, hhb⟩

/-- The actual off-target complete-shift occurrence mass admits an
EXACT squarefree restriction. The nonzero shift is selected first, so
no divisors-at-zero term is introduced. The identical physical signed
rho-response stays attached to each original ordered HB occurrence. -/
theorem offMarkedResponse_sum_eq_squarefree
    (N n j : ℕ) (z y : ℝ)
    (marked : List ℕ) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
        (fun hb => marked.prod * hb.prod ≠ N),
      offMarkedOccurrence j z y W marked hb *
        offMarkedPhysicalResponse marked.prod N hb.prod Q rho) =
    (∑ hb ∈ ((factorTuples (2 * (j + 1)) n).filter
        (fun hb => marked.prod * hb.prod ≠ N)).filter
        (fun hb => Squarefree (marked.prod * hb.prod)),
      offMarkedOccurrence j z y W marked hb *
        offMarkedPhysicalResponse marked.prod N hb.prod Q rho) := by
  classical
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro hb hhb
  by_cases hs : Squarefree (marked.prod * hb.prod)
  · simp [hs]
  · have hz := offMarkedOccurrence_zero_of_nonsquarefree
      j z y W marked hb hs
    simp [hs, hz]

/-- Full original SAME-rho, +3,-3,+1 signed marked/rough HB ledger:
the target product remains separately factored; the nonzero-shift
arithmetic response now runs EXACTLY over squarefree complete physical
products, hence disjoint marked/HB prime factors. This is finite algebra,
not the needed near-linear shifted-divisor or Fourier/H error bound. -/
theorem signed_three_full_squarefree_off_same_rho
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughFullAtQ N n j q z y M W) =
    ((((ArithmeticFunction.moebius N : ℝ) : ℂ) *
        physicalRhoTargetKernel N Q rho) *
          hbThreeTargetMass N n z y M W) +
      (∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          (∑ marked ∈ M,
            ∑ hb ∈ ((factorTuples (2 * (j + 1)) n).filter
                (fun hb => marked.prod * hb.prod ≠ N)).filter
                (fun hb => Squarefree (marked.prod * hb.prod)),
              offMarkedOccurrence j z y W marked hb *
                offMarkedPhysicalResponse marked.prod N hb.prod Q rho)) := by
  rw [signed_three_full_target_and_off_same_rho]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro marked hm
  exact offMarkedResponse_sum_eq_squarefree N n j z y marked W Q rho

end
end ImbalancedChen.P3HBMarkedMobiusOffshiftSquarefree
