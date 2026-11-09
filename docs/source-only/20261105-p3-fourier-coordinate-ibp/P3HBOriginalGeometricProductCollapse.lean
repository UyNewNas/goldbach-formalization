import ImbalancedChen.P3HBMarkedFixedProductFibre
import ImbalancedChen.P5ActualRoughHeathBrownWords
import Mathlib.Tactic

/-!
P3.6 — exact ORIGINAL three-term HB cancellation for coherent group geometry.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The fixed-product absolute bound separately costs log(n)*tau(n)^(2*(j+1)).
If the geometric factor depends only on the ORIGINAL group product, the
+3,-3,+1 terms recombine BEFORE absolute values, using the production
actual_rough_order_three_identity at the CLOSED real cube n <= y^3.
The real strict rough cutoff, full-product global Mobius, original ordered
labels and exact physical signed response remain unchanged.

The original HB rectangle-localized Fourier modes need not be coherent
with group products; this covers the complete group fibre BEFORE such
localization. No all-source causal compiler or PP saving is claimed.
Pinned paper: 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2,4 (HB),(F), eq:current-HB/eq:current-PP.
-/

namespace ImbalancedChen.P3HBOriginalGeometricProductCollapse

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
open ImbalancedChen.P3HBMarkedFixedProductFibre

/-- Actual original group geometry pulled back along its integer product;
no artificial independent HB-label weights are assumed. -/
def productGeometry (G : List ℕ → ℕ → ℂ) :
    List ℕ × List ℕ → ℂ := fun a => G a.1 a.2.prod

/-- The original geometry and global Mobius are constant on each literal
ordered factorTuples fibre. The HB occurrence weights remain distinct. -/
theorem original_fixed_mass_product_geometry
    (n j : ℕ) (z y : ℝ) (G : List ℕ → ℕ → ℂ)
    (marked : List ℕ) :
    originalHBFixedOccurrenceMass n j z y (productGeometry G) marked =
      (G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (∑ hb ∈ factorTuples (2 * (j + 1)) n,
            roughTupleWeight z y (roles j) hb) := by
  classical
  unfold originalHBFixedOccurrenceMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro hb hhb
  have hprod : hb.prod = n :=
    (factorTuples_spec (2 * (j + 1)) n hb hhb).2.1
  simp only [offMarkedOccurrence, productGeometry, hprod]
  ring

/-- True signed +3,-3,+1 HB cancellation before absolute values. For
coherent geometry this is the exact original rough-filtered von Mangoldt
rather than a divisor-power absolute mass bound. -/
theorem signed_three_product_geometry_collapse
    (n : ℕ) (z y : ℝ) (G : List ℕ → ℕ → ℂ)
    (marked : List ℕ) (hz : 0 ≤ z) (hy : 0 ≤ y)
    (hcube : (n : ℝ) ≤ y ^ 3) :
    (∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        originalHBFixedOccurrenceMass n j z y (productGeometry G) marked) =
      (G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n) := by
  classical
  calc
    _ = ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          ((G marked n *
            (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
            (∑ hb ∈ factorTuples (2 * (j + 1)) n,
              roughTupleWeight z y (roles j) hb)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [original_fixed_mass_product_geometry]
    _ = (G marked n *
          (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (∑ j ∈ Finset.range 3,
            ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
              ∑ hb ∈ factorTuples (2 * (j + 1)) n,
                roughTupleWeight z y (roles j) hb) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by
        rw [← actual_rough_order_three_identity hz hy hcube]

/-- One unchanged integer rho and physical Q multiply the signed HB
collapse. The full marked*HB shift is nonzero, squarefree, and retained
inside the exact divisor-minus-coprime-mean response. This is an exact
finite reduction, NOT a distribution estimate. -/
theorem signed_three_product_geometry_offshift_same_rho
    (N n : ℕ) (z y : ℝ) (G : List ℕ → ℕ → ℂ)
    (marked : List ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hz : 0 ≤ z) (hy : 0 ≤ y)
    (hcube : (n : ℝ) ≤ y ^ 3)
    (hoff : marked.prod * n ≠ N)
    (hsquarefree : Squarefree (marked.prod * n)) :
    (∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        (∑ hb ∈ ((factorTuples (2 * (j + 1)) n).filter
          (fun hb => marked.prod * hb.prod ≠ N)).filter
          (fun hb => Squarefree (marked.prod * hb.prod)),
          offMarkedOccurrence j z y (productGeometry G) marked hb *
            offMarkedPhysicalResponse marked.prod N hb.prod Q rho)) =
      ((G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          roughOneSlot z n)) *
          offMarkedPhysicalResponse marked.prod N n Q rho := by
  classical
  calc
    _ = ∑ j ∈ Finset.range 3,
          ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
            (originalHBFixedOccurrenceMass n j z y
              (productGeometry G) marked *
              offMarkedPhysicalResponse marked.prod N n Q rho) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [squarefree_offshift_hb_fibre]
        have hcond : marked.prod * n ≠ N ∧
            Squarefree (marked.prod * n) := ⟨hoff, hsquarefree⟩
        simp only [if_pos hcond]
    _ = (∑ j ∈ Finset.range 3,
          ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
            originalHBFixedOccurrenceMass n j z y
              (productGeometry G) marked) *
          offMarkedPhysicalResponse marked.prod N n Q rho := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by
        rw [signed_three_product_geometry_collapse n z y G marked hz hy hcube]

end ImbalancedChen.P3HBOriginalGeometricProductCollapse
