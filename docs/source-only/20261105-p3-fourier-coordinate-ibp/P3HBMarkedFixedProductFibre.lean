import ImbalancedChen.P3HBMarkedMobiusOffshiftSquarefree
import Mathlib.Tactic

/-!
P3.6 — genuine fixed-HB-product arithmetic fibre reduction.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The ORIGINAL factorTuples k n carrier has hb.prod = n on every labelled
ordered occurrence. Therefore the complete physical shift, its global
Mobius support, and the signed same-rho physical response are constant
across that fibre; only the actual occurrence W and rough HB coefficient
remain inside the ordered-label sum. This is not a distribution estimate.
Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2–4, original full-product shift and (F).
-/

namespace ImbalancedChen.P3HBMarkedFixedProductFibre

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBMarkedMobiusPhysicalDiagonalFactor
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
open ImbalancedChen.P3HBMarkedMobiusOffshiftSquarefree
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords

/-- Keep the exact original ordered HB labels and the actual complex
W(marked,hb), with no positional quotient or fabricated coefficient. -/
def originalHBFixedOccurrenceMass
    (n j : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (marked : List ℕ) : ℂ :=
  ∑ hb ∈ factorTuples (2 * (j + 1)) n,
    offMarkedOccurrence j z y W marked hb

/-- Exact original HB factor-fibre product, including the zero/empty cases
allowed by the literal factorTuples carrier. -/
theorem full_product_on_original_hb_fibre
    (n j : ℕ) (marked hb : List ℕ)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n) :
    marked.prod * hb.prod = marked.prod * n := by
  rw [(factorTuples_spec (2 * (j + 1)) n hb hhb).2.1]

/-- The original off-target + global-Mobius squarefree HB sum is exactly
ONE original complete-product shifted physical response times its entire
ordered HB occurrence mass, or zero when the marked fibre is ineligible.
This retains the SAME physical Q and signed integer rho. -/
theorem squarefree_offshift_hb_fibre
    (N n j : ℕ) (z y : ℝ)
    (marked : List ℕ) (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    (∑ hb ∈ ((factorTuples (2 * (j + 1)) n).filter
        (fun hb => marked.prod * hb.prod ≠ N)).filter
        (fun hb => Squarefree (marked.prod * hb.prod)),
      offMarkedOccurrence j z y W marked hb *
        offMarkedPhysicalResponse marked.prod N hb.prod Q rho) =
      (if marked.prod * n ≠ N ∧ Squarefree (marked.prod * n)
       then originalHBFixedOccurrenceMass n j z y W marked *
          offMarkedPhysicalResponse marked.prod N n Q rho
       else 0) := by
  classical
  calc
    _ = ∑ hb ∈ factorTuples (2 * (j + 1)) n,
          if marked.prod * hb.prod ≠ N ∧ Squarefree (marked.prod * hb.prod)
          then offMarkedOccurrence j z y W marked hb *
            offMarkedPhysicalResponse marked.prod N hb.prod Q rho
          else 0 := by
            rw [Finset.filter_filter, Finset.sum_filter]
    _ = ∑ hb ∈ factorTuples (2 * (j + 1)) n,
          if marked.prod * n ≠ N ∧ Squarefree (marked.prod * n)
          then offMarkedOccurrence j z y W marked hb *
            offMarkedPhysicalResponse marked.prod N n Q rho
          else 0 := by
            apply Finset.sum_congr rfl
            intro hb hhb
            have hp : hb.prod = n :=
              (factorTuples_spec (2 * (j + 1)) n hb hhb).2.1
            rw [hp]
    _ = _ := by
          by_cases h : marked.prod * n ≠ N ∧ Squarefree (marked.prod * n)
          · simp only [if_pos h]
            unfold originalHBFixedOccurrenceMass
            rw [Finset.sum_mul]
          · simp [h]

/-- Physical q never sees a separate HB positional shift inside the
admissible fibre. This is an EXACT finite arithmetic assembly, not a
claim of a weighted shifted-divisor moment or of uniform PP saving. -/
theorem signed_three_full_fixed_fibres_same_rho
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
            if marked.prod * n ≠ N ∧ Squarefree (marked.prod * n)
            then originalHBFixedOccurrenceMass n j z y W marked *
              offMarkedPhysicalResponse marked.prod N n Q rho
            else 0)) := by
  rw [signed_three_full_squarefree_off_same_rho]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro marked hm
  exact squarefree_offshift_hb_fibre N n j z y marked W Q rho

end ImbalancedChen.P3HBMarkedFixedProductFibre
