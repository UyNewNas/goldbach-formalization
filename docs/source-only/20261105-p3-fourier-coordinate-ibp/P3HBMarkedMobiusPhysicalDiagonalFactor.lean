import ImbalancedChen.P3HBMarkedMobiusSquarefreeDiagonal
import Mathlib.Tactic

/-!
P3.6 — exact same-rho physical factor of the remaining full-product
marked/rough HB target diagonal. SOURCE_ONLY / UNCOMPILED.

At complete product N, the actual markedResidualKernel is the same
mu(N)*fineKernel N q N for EACH original ordered HB and outside marked
label. It can be factored AFTER the complete physical q sum, with all
integer rho signs, +3,-3,+1 HB terms, and literal primitive coprime mean.

Only the genuine subfamily with mu(complete product) is considered.
The surviving squarefree-even-marked target mass is NOT bounded here;
there is no admission of arbitrary W_T or final causal compiler.
Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2–4, especially §4 (F).
-/

namespace ImbalancedChen.P3HBMarkedMobiusPhysicalDiagonalFactor

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBMarkedMobiusFourDiagonal
open ImbalancedChen.P3HBMarkedMobiusSquarefreeDiagonal
open ImbalancedChen.P3ActualMarkedResidualExactProduct
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- Original physical Q and signed integer rho. Keeping fineKernel at
the EXACT complete product retains the true coprime mean for every q. -/
def physicalRhoTargetKernel
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ) : ℂ :=
  ∑ q ∈ Q, (rho q : ℂ) * ((fineKernel N q N : ℝ) : ℂ)

/-- The labelled ordered HB target mass. Neither the marked labels nor
HB tuple positions are collapsed to the value of their product. -/
def hbTargetMass
    (N n j : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ) : ℂ :=
  ∑ marked ∈ M,
    ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
        (fun hb => marked.prod * hb.prod = N),
      W (marked, hb) * roughTupleWeight z y (roles j) hb

/-- The original 3,-3,+1 signed order-three HB mass, prior to physical
modulus evaluation. -/
def hbThreeTargetMass
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3,
    (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
      hbTargetMass N n j z y M W

/-- Unlike the earlier coprime-only factor lemma, this equality imposes
no (N,q)=1 assumption, and does not replace the exact mean. -/
theorem markedResidualKernel_target_without_coprime
    (r N q n : ℕ) (hfull : r * n = N) :
    markedResidualKernel r N q n =
      ((ArithmeticFunction.moebius N : ℝ) : ℂ) *
        ((fineKernel N q N : ℝ) : ℂ) := by
  unfold markedResidualKernel
  rw [hfull]

/-- The same q-dependent actual full-product kernel factors out of all
original outside marked labels and all ordered HB occurrences. -/
theorem mobiusMarkedRoughTargetAtQ_exact_factor
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ) :
    mobiusMarkedRoughTargetAtQ N n j q z y M W =
      (((ArithmeticFunction.moebius N : ℝ) : ℂ) *
        ((fineKernel N q N : ℝ) : ℂ)) *
          hbTargetMass N n j z y M W := by
  classical
  unfold mobiusMarkedRoughTargetAtQ hbTargetMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro marked hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro hb hhb
  have hfull : marked.prod * hb.prod = N :=
    (Finset.mem_filter.mp hhb).2
  rw [markedResidualKernel_target_without_coprime
    marked.prod N q hb.prod hfull]
  ring

/-- Entire signed physical q/j ledger, with one unchanged integer rho.
This is a finite factorization, NOT a bound for either of its factors. -/
theorem signed_three_mobius_target_exact_factor
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughTargetAtQ N n j q z y M W) =
      (((ArithmeticFunction.moebius N : ℝ) : ℂ) *
        physicalRhoTargetKernel N Q rho) *
          hbThreeTargetMass N n z y M W := by
  classical
  have hq (q : ℕ) :
      (∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughTargetAtQ N n j q z y M W) =
        (((ArithmeticFunction.moebius N : ℝ) : ℂ) *
          ((fineKernel N q N : ℝ) : ℂ)) *
            hbThreeTargetMass N n z y M W := by
    unfold hbThreeTargetMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mobiusMarkedRoughTargetAtQ_exact_factor]
    ring
  calc
    _ = ∑ q ∈ Q, (rho q : ℂ) *
        ((((ArithmeticFunction.moebius N : ℝ) : ℂ) *
            ((fineKernel N q N : ℝ) : ℂ)) *
              hbThreeTargetMass N n z y M W) := by
          apply Finset.sum_congr rfl
          intro q hqmem
          rw [hq q]
    _ = (∑ q ∈ Q,
          (((ArithmeticFunction.moebius N : ℝ) : ℂ) *
            ((rho q : ℂ) * ((fineKernel N q N : ℝ) : ℂ))) *
              hbThreeTargetMass N n z y M W) := by
          apply Finset.sum_congr rfl
          intro q hqmem
          ring
    _ = (((ArithmeticFunction.moebius N : ℝ) : ℂ) *
          physicalRhoTargetKernel N Q rho) *
            hbThreeTargetMass N n z y M W := by
          rw [Finset.sum_mul]
          unfold physicalRhoTargetKernel
          rw [Finset.mul_sum]

/-- When N is even and z>=2, the entire signed physical response is
supported on EVEN outside marked products. This uses the previous real
strict rough projector proof, and does NOT discard that remainder. -/
theorem signed_three_mobius_target_even_marked_exact_factor
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ)) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          mobiusMarkedRoughTargetAtQ N n j q z y M W) =
      (((ArithmeticFunction.moebius N : ℝ) : ℂ) *
        physicalRhoTargetKernel N Q rho) *
          hbThreeTargetMass N n z y
            (M.filter (fun marked => 2 ∣ marked.prod)) W := by
  calc
    _ = (∑ q ∈ Q, (rho q : ℂ) *
        ∑ j ∈ Finset.range 3,
          (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
            mobiusMarkedRoughTargetAtQ N n j q z y
              (M.filter (fun marked => 2 ∣ marked.prod)) W) := by
          apply Finset.sum_congr rfl
          intro q hq
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [mobiusMarkedRoughTargetAtQ_eq_even_marked
            N n j q z y M W hz hN]
    _ = _ := signed_three_mobius_target_exact_factor
      N n z y (M.filter (fun marked => 2 ∣ marked.prod)) W Q rho

/-- Only when the actual physical moduli satisfy (N,q)=1 can the
genuine exact mean be rewritten as 1-1/phi(q). -/
theorem physicalRhoTargetKernel_coprime
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hcop : ∀ q ∈ Q, Nat.Coprime N q) :
    physicalRhoTargetKernel N Q rho =
      ∑ q ∈ Q, (rho q : ℂ) *
        (((1 : ℝ) - (Nat.totient q : ℝ)⁻¹) : ℂ) := by
  unfold physicalRhoTargetKernel
  apply Finset.sum_congr rfl
  intro q hq
  rw [fineKernel_exact N q (hcop q hq)]

end
end ImbalancedChen.P3HBMarkedMobiusPhysicalDiagonalFactor
