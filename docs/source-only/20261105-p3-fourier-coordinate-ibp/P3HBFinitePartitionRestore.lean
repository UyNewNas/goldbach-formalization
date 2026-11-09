import ImbalancedChen.P3HBGeometryDefectBudget
import Mathlib.Tactic

/-!
P3.6 — reconstruct the original signed HB fibre *after summing a complete
finite family of positional geometric partition pieces*.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Manuscript pin: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b
prime-product completion §2 (exact HB and retained rectangles) and §4 (F).
Mathlib pin: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Individual HB-rectangle cutoffs are NOT product coherent. Their complete
pointwise sum can nevertheless be exactly one on the original occurrence
fibre. This restores the signed 3,-3,1 cancellation only AFTER summing all
those pieces. The pointwise partition identity on the NONZERO original geometric support
for the ACTUAL selected rectangles is still an independent internal obligation.
No Fourier tail or analytic PP saving is claimed here.
-/

namespace ImbalancedChen.P3HBFinitePartitionRestore

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho
open ImbalancedChen.P3HBMarkedFixedProductFibre
open ImbalancedChen.P3HBOriginalGeometricProductCollapse

/-- Original group-product geometry times a literal positional partition
piece. Labels (including repeated arithmetic occurrences) are not merged. -/
def partitionPiece {ι : Type*} (G : List ℕ → ℕ → ℂ)
    (cut : ι → List ℕ → List ℕ → ℂ) (label : ι) :
    List ℕ × List ℕ → ℂ :=
  fun a => productGeometry G a * cut label a.1 a.2

/-- If the original labelled HB rectangle cutoffs sum to exactly one on
the ORIGINAL factorTuples fibre, its original weighted occurrence sum is
recovered without taking norms or dropping the original full-product mu. -/
theorem fixed_fibre_partition_restores
    {ι : Type*} (labels : Finset ι)
    (n j : ℕ) (z y : ℝ) (G : List ℕ → ℕ → ℂ)
    (cut : ι → List ℕ → List ℕ → ℂ) (marked : List ℕ)
    (hpartition : ∀ hb ∈ factorTuples (2 * (j + 1)) n,
       G marked n ≠ 0 →
       ∑ label ∈ labels, cut label marked hb = (1 : ℂ)) :
    (∑ label ∈ labels,
      originalHBFixedOccurrenceMass n j z y
        (partitionPiece G cut label) marked) =
      originalHBFixedOccurrenceMass n j z y (productGeometry G) marked := by
  classical
  unfold originalHBFixedOccurrenceMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro hb hhb
  have hprod : hb.prod = n :=
    (factorTuples_spec (2 * (j + 1)) n hb hhb).2.1
  have hcut : (∑ label ∈ labels,
       partitionPiece G cut label (marked, hb)) = G marked n := by
    simp only [partitionPiece, productGeometry, Prod.fst, Prod.snd, hprod]
    by_cases hg : G marked n = 0
    · simp [hg]
    · rw [← Finset.mul_sum, hpartition hb hhb hg]
      ring
  calc
    (∑ label ∈ labels,
      offMarkedOccurrence j z y (partitionPiece G cut label) marked hb) =
      (∑ label ∈ labels, partitionPiece G cut label (marked, hb)) *
        (roughTupleWeight z y (roles j) hb *
          (((ArithmeticFunction.moebius (marked.prod * hb.prod) : ℝ) : ℂ))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro label hlabel
        simp only [offMarkedOccurrence]
        ring
    _ = offMarkedOccurrence j z y (productGeometry G) marked hb := by
      rw [hcut]
      simp only [offMarkedOccurrence, productGeometry, hprod]
      ring

/-- The original 3,-3,1 rough-HB identity is recovered AFTER the entire
finite positional partition, not separately on each rectangle. This is an
exact finite partition-of-unity argument; no smooth-derivative estimate or
new distribution hypothesis is introduced. -/
theorem signed_three_partition_restores
    {ι : Type*} (labels : Finset ι)
    (n : ℕ) (z y : ℝ) (G : List ℕ → ℕ → ℂ)
    (cut : ι → List ℕ → List ℕ → ℂ) (marked : List ℕ)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3)
    (hpartition : ∀ j ∈ Finset.range 3,
      ∀ hb ∈ factorTuples (2 * (j + 1)) n,
        G marked n ≠ 0 →
        ∑ label ∈ labels, cut label marked hb = (1 : ℂ)) :
    (∑ label ∈ labels,
      ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece G cut label) marked) =
      (G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n) := by
  classical
  calc
    _ = ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          (∑ label ∈ labels,
            originalHBFixedOccurrenceMass n j z y
              (partitionPiece G cut label) marked) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y (productGeometry G) marked := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [fixed_fibre_partition_restores labels n j z y G cut marked
            (hpartition j hj)]
    _ = _ := signed_three_product_geometry_collapse
      n z y G marked hz hy hcube

/-- SAME integer rho and full physical modulus family Q. Summing actual
positional pieces before the complete off-target physical response restores
the original signed cancellation with its exact coprime mean. It does NOT
justify estimating every rectangle separately without paying its error. -/
theorem same_rho_offshift_partition_restores
    {ι : Type*} (labels : Finset ι)
    (N n : ℕ) (z y : ℝ) (G : List ℕ → ℕ → ℂ)
    (cut : ι → List ℕ → List ℕ → ℂ) (marked : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3)
    (_hoff : marked.prod * n ≠ N)
    (hpartition : ∀ j ∈ Finset.range 3,
      ∀ hb ∈ factorTuples (2 * (j + 1)) n,
        G marked n ≠ 0 →
        ∑ label ∈ labels, cut label marked hb = (1 : ℂ)) :
    (∑ label ∈ labels,
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece G cut label) marked) *
        offMarkedPhysicalResponse marked.prod N n Q rho) =
      ((G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n)) *
        offMarkedPhysicalResponse marked.prod N n Q rho := by
  classical
  calc
    _ = (∑ label ∈ labels,
          ∑ j ∈ Finset.range 3,
            ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
              originalHBFixedOccurrenceMass n j z y
                (partitionPiece G cut label) marked) *
          offMarkedPhysicalResponse marked.prod N n Q rho := by
          rw [Finset.sum_mul]
    _ = _ := by
          rw [signed_three_partition_restores labels n z y G cut marked
            hz hy hcube hpartition]

end ImbalancedChen.P3HBFinitePartitionRestore
