import ImbalancedChen.P3HBOriginalGeometricProductCollapse
import ImbalancedChen.P3HBMarkedFixedProductMassBound
import Mathlib.Tactic

/-!
P3.6 — actual original HB geometric localization defect, exact physical rho.
SOURCE_ONLY, UNCOMPILED, KERNEL_UNVERIFIED.
Pinned manuscript 9731290e8f53cffda44129906cde6a965eaa869b, PP §§2,4.
Pinned Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
An arbitrary original positional W is NOT assumed coherent after HB rectangles.
The genuine defect is retained and bounded; no PP saving is asserted.
-/

namespace ImbalancedChen.P3HBGeometryDefectBudget

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
open ImbalancedChen.P3HBMarkedFixedProductFibre
open ImbalancedChen.P3HBMarkedFixedProductMassBound
open ImbalancedChen.P3HBOriginalGeometricProductCollapse

/-- Literal original tuple-dependent geometry minus the group-product lift. -/
def geometryDefect (W : List ℕ × List ℕ → ℂ)
    (G : List ℕ → ℕ → ℂ) : List ℕ × List ℕ → ℂ :=
  fun a => W a - productGeometry G a

/-- No HB label, position, rough factor or global Mobius is changed. -/
theorem original_fixed_mass_geometry_split
    (n j : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (G : List ℕ → ℕ → ℂ) (marked : List ℕ) :
    originalHBFixedOccurrenceMass n j z y W marked =
      originalHBFixedOccurrenceMass n j z y (productGeometry G) marked +
      originalHBFixedOccurrenceMass n j z y (geometryDefect W G) marked := by
  classical
  unfold originalHBFixedOccurrenceMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro hb hhb
  unfold offMarkedOccurrence geometryDefect
  ring

/-- The genuine signed +3,-3,+1 HB collapse, with explicit localized error.
The rough threshold is strict and the cube n<=y^3 is closed. -/
theorem signed_three_geometry_split
    (n : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (G : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3) :
    (∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        originalHBFixedOccurrenceMass n j z y W marked) =
      (G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n) +
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (geometryDefect W G) marked) := by
  classical
  calc
    _ = ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          (originalHBFixedOccurrenceMass n j z y (productGeometry G) marked +
            originalHBFixedOccurrenceMass n j z y (geometryDefect W G) marked) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [original_fixed_mass_geometry_split]
    _ = (∑ j ∈ Finset.range 3,
          ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
            originalHBFixedOccurrenceMass n j z y (productGeometry G) marked) +
        (∑ j ∈ Finset.range 3,
          ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
            originalHBFixedOccurrenceMass n j z y (geometryDefect W G) marked) := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ = _ := by
        rw [signed_three_product_geometry_collapse n z y G marked hz hy hcube]

/-- Non-circular actual pointwise defect bound on all original ordered slots.
This invokes the ORIGINAL literal rough-HB mass, not an assumed PP error. -/
theorem geometry_defect_fixed_mass_norm_le
    (n j : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (G : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (delta : ℝ) (hn : n ≠ 0) (hz : 0 ≤ z) (hdelta : 0 ≤ delta)
    (hW : ∀ hb ∈ factorTuples (2 * (j + 1)) n,
      ‖W (marked, hb) - G marked n‖ ≤ delta) :
    ‖originalHBFixedOccurrenceMass n j z y
        (geometryDefect W G) marked‖ ≤
      delta * Real.log (n : ℝ) *
        ((n.divisors.card : ℝ) ^ (2 * (j + 1))) := by
  have hdef : ∀ hb ∈ factorTuples (2 * (j + 1)) n,
      ‖geometryDefect W G (marked, hb)‖ ≤ delta := by
    intro hb hhb
    have hp : hb.prod = n :=
      (factorTuples_spec (2 * (j + 1)) n hb hhb).2.1
    simpa [geometryDefect, productGeometry, hp] using hW hb hhb
  exact originalHBFixedOccurrenceMass_norm_le_tau n j z y
    (geometryDefect W G) marked delta hn hdelta hdef hz

/-- Pay localization for all actual ordered 2,4,6-slot HB fibres, keeping
the literal +3,-3,+1 coefficients before the modulus response. -/
theorem signed_three_geometry_defect_norm_le
    (n : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (G : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (delta : ℝ) (hn : n ≠ 0) (hz : 0 ≤ z) (hdelta : 0 ≤ delta)
    (hW : ∀ j ∈ Finset.range 3, ∀ hb ∈ factorTuples (2 * (j + 1)) n,
      ‖W (marked, hb) - G marked n‖ ≤ delta) :
    ‖∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        originalHBFixedOccurrenceMass n j z y
          (geometryDefect W G) marked‖ ≤
      ∑ j ∈ Finset.range 3,
        ‖((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ))‖ *
          (delta * Real.log (n : ℝ) *
            ((n.divisors.card : ℝ) ^ (2 * (j + 1)))) := by
  calc
    _ ≤ ∑ j ∈ Finset.range 3,
        ‖((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (geometryDefect W G) marked‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range 3,
        ‖((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ))‖ *
          ‖originalHBFixedOccurrenceMass n j z y
            (geometryDefect W G) marked‖ := by
        simp only [norm_mul]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (geometry_defect_fixed_mass_norm_le n j z y W G marked
            delta hn hz hdelta (hW j hj)) (norm_nonneg _)

/-- Same original physical Q and integer rho off-target error, retaining
the complete marked*HB product and the exact coprime mean. In particular,
NO separate absolute value is taken per q. This lemma does NOT prove an
actual uniform delta for the localized W_T family. -/
theorem same_rho_offshift_geometry_defect_norm_le
    (N n : ℕ) (z y : ℝ) (W : List ℕ × List ℕ → ℂ)
    (G : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (delta : ℝ)
    (hn : n ≠ 0) (hz : 0 ≤ z) (hy : 0 ≤ y)
    (hcube : (n : ℝ) ≤ y ^ 3)
    (hoff : marked.prod * n ≠ N)
    (hdelta : 0 ≤ delta)
    (hW : ∀ j ∈ Finset.range 3, ∀ hb ∈ factorTuples (2 * (j + 1)) n,
      ‖W (marked, hb) - G marked n‖ ≤ delta) :
    ‖((∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y W marked) *
            offMarkedPhysicalResponse marked.prod N n Q rho) -
      (((G marked n *
          (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              roughOneSlot z n)) *
                offMarkedPhysicalResponse marked.prod N n Q rho)‖ ≤
      (∑ j ∈ Finset.range 3,
        ‖((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ))‖ *
          (delta * Real.log (n : ℝ) *
            ((n.divisors.card : ℝ) ^ (2 * (j + 1))))) *
        ‖offMarkedPhysicalResponse marked.prod N n Q rho‖ := by
  have hid := signed_three_geometry_split n z y W G marked hz hy hcube
  have hnorm := signed_three_geometry_defect_norm_le
    n z y W G marked delta hn hz hdelta hW
  calc
    _ = ‖(∑ j ∈ Finset.range 3,
          ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
            originalHBFixedOccurrenceMass n j z y
              (geometryDefect W G) marked) *
                offMarkedPhysicalResponse marked.prod N n Q rho‖ := by
        rw [hid]
        congr 1
        ring
    _ = ‖∑ j ∈ Finset.range 3,
          ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
            originalHBFixedOccurrenceMass n j z y
              (geometryDefect W G) marked‖ *
          ‖offMarkedPhysicalResponse marked.prod N n Q rho‖ := norm_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

end ImbalancedChen.P3HBGeometryDefectBudget
