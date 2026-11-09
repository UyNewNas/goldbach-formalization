import ImbalancedChen.P3HBRetainedDyadicUpperSupport
import Mathlib.Tactic

/-!
P3.6 — original HB rank-adaptive pruning of genuine six-position dyadic
rectangles, combined with the previously verified-in-source group upper
support. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt §2,
including original 2/4/6-slot HB, dyadic psi and R/128 lower endpoint.
Mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

This packet pays the ACTUAL dummy-slot geometry: positions beyond the
original factorTuples length are literal units. Their dyadic indices cannot
be nonzero on support. The finite set of retained labels now depends on
the actual HB rank 2/4/6, without deleting any live original occurrence,
merging source labels, or replacing the physical Q/rho.

Also derive the strict LOWER original group window R/2 < n from its
literal chi(n/R)-chi(2n/R); this is NOT YET the full manuscript R/128
rectangle-product estimate. All full Fourier/H and arithmetic savings stay open.
-/

namespace ImbalancedChen.P3HBRankAdaptiveRetainedSupport

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P3HBFinitePartitionRestore
open ImbalancedChen.P3HBDyadicTensorPartition
open ImbalancedChen.P3HBRetainedDyadicUpperSupport
open ImbalancedChen.P3HBMarkedFixedProductFibre
open ImbalancedChen.P3HBOriginalGeometricProductCollapse
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho

/-- The lower endpoint of the genuine original group smooth cutoff is
STRICT: nonzero psi(n/R) forces R/2 < n, even at n = R/2.
It uses only the actual lower chi plateau, not a guessed sharp wall. -/
theorem original_group_dyadic_lower_window
    (chi : ℝ → ℂ) (x R : ℝ) (hR : 0 < R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hgroup : chi (x / R) - chi (2 * x / R) ≠ 0) :
    R / 2 < x := by
  by_contra h
  have hx : x ≤ R / 2 := le_of_not_gt h
  have hleft : x / R ≤ 1 :=
    (div_le_iff₀ hR).2 (by linarith)
  have hright : 2 * x / R ≤ 1 :=
    (div_le_iff₀ hR).2 (by linarith)
  apply hgroup
  rw [hsmall _ hleft, hsmall _ hright]
  ring

/-- A concrete rank-adaptive subset of the previously upper-pruned
six-axis box. Beyond the actual HB rank r, unit-padded axes may have
a nonzero dyadic factor only at bases 2^j < 2, i.e. index j=0.
The definition uses the actual dyadic scales, not an invented PP mask. -/
def rankUpperRetainedLabels (J r : ℕ) (R : ℝ) :
    Finset (Fin 6 → ℕ) :=
  (upperRetainedLabels J R).filter
    (fun label => ∀ i : Fin 6,
      r ≤ i.val → (2 : ℝ) ^ (label i) < 2)

/-- An omitted dummy-coordinate label has zero REAL original dyadic
tensor factor: factorTuples_spec supplies hb.length = r, so getD is 1. -/
theorem omitted_padding_label_zero
    (chi : ℝ → ℂ) (J r n : ℕ) (R : ℝ)
    (marked hb : List ℕ) (label : Fin 6 → ℕ)
    (hhb : hb ∈ factorTuples r n)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hupper : label ∈ upperRetainedLabels J R)
    (homit : label ∉ rankUpperRetainedLabels J r R) :
    hbDyadicCut chi label marked hb = 0 := by
  classical
  have hnot : ¬ ∀ i : Fin 6,
      r ≤ i.val → (2 : ℝ) ^ (label i) < 2 := by
    intro hp
    apply homit
    exact Finset.mem_filter.mpr ⟨hupper, hp⟩
  push_neg at hnot
  obtain ⟨i, hpad, hscale⟩ := hnot
  have hlen : hb.length = r :=
    (factorTuples_spec r n hb hhb).1
  have hget : hb.getD i.val 1 = 1 := by
    rw [List.getD_eq_default hb 1 (by omega)]
  have hscale' : 2 * (hb.getD i.val 1 : ℝ) ≤
      (2 : ℝ) ^ (label i) := by
    simpa [hget] using hscale
  exact hbDyadicCut_zero_of_high_scale
    chi label marked hb i hsmall hscale'

/-- Each actual r-slot ordered HB fibre still has total dyadic mass one
after BOTH upper geometric pruning and padding-aware rank pruning.
This is not merely an abstract partition-of-unity premise. -/
theorem factorTuple_rank_upper_retained_partition
    (chi : ℝ → ℂ) (J r n : ℕ) (R : ℝ)
    (marked hb : List ℕ)
    (hhb : hb ∈ factorTuples r n)
    (hn : 1 ≤ n) (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hwindow : (n : ℝ) ≤ 2 * R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    (∑ label ∈ rankUpperRetainedLabels J r R,
      hbDyadicCut chi label marked hb) = 1 := by
  classical
  have hupper := factorTuple_upper_retained_partition
    chi J r n R marked hb hhb hn hnJ hwindow hsmall hlarge
  calc
    (∑ label ∈ rankUpperRetainedLabels J r R,
      hbDyadicCut chi label marked hb) =
      ∑ label ∈ upperRetainedLabels J R,
        hbDyadicCut chi label marked hb := by
        simp only [rankUpperRetainedLabels, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro label hlabel
        by_cases hp : ∀ i : Fin 6,
            r ≤ i.val → (2 : ℝ) ^ (label i) < 2
        · simp [hp]
        · have homit : label ∉ rankUpperRetainedLabels J r R := by
            intro hh
            exact hp (Finset.mem_filter.mp hh).2
          have hzero := omitted_padding_label_zero
            chi J r n R marked hb label hhb hsmall hlabel homit
          simp [hp, hzero]
    _ = 1 := hupper

/-- ACTUAL rank-specific original +3,-3,+1 restoration. For j=0,1,2,
the summation over labels is taken in the correct original 2,4,6 slots
BEFORE the j sum; no single-rectangle HB cancellation is claimed. -/
theorem original_group_rank_upper_signed_restoration
    (chi : ℝ → ℂ) (J n : ℕ) (R z y : ℝ)
    (H : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (hR : 0 < R) (hn : 1 ≤ n)
    (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3) :
    (∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        (∑ label ∈ rankUpperRetainedLabels J (2 * (j + 1)) R,
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece (groupDyadicGeometry chi R H)
              (hbDyadicCut chi) label) marked)) =
      (groupDyadicGeometry chi R H marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n) := by
  classical
  calc
    _ = ∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        originalHBFixedOccurrenceMass n j z y
          (productGeometry (groupDyadicGeometry chi R H)) marked := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [fixed_fibre_partition_restores
          (rankUpperRetainedLabels J (2 * (j + 1)) R)
          n j z y (groupDyadicGeometry chi R H)
          (hbDyadicCut chi) marked]
        intro hb hhb hg
        have hgroup : chi ((n : ℝ) / R) -
            chi (2 * (n : ℝ) / R) ≠ 0 := by
          intro hzero
          apply hg
          simp [groupDyadicGeometry, hzero]
        have hwindow : (n : ℝ) ≤ 2 * R :=
          le_of_lt (original_group_dyadic_upper_window
            chi (n : ℝ) R hR hlarge hgroup)
        exact factorTuple_rank_upper_retained_partition
          chi J (2 * (j + 1)) n R marked hb hhb hn hnJ
          hwindow hsmall hlarge
    _ = _ := signed_three_product_geometry_collapse
      n z y (groupDyadicGeometry chi R H) marked hz hy hcube

/-- Original physical signed rho and Q remain OUTSIDE the complete
rank-adaptive 2/4/6 HB sum, with the exact coprime mean and complete
marked.prod*n shift, before taking any absolute values. -/
theorem original_group_rank_upper_offshift_same_rho
    (chi : ℝ → ℂ) (J N n : ℕ) (R z y : ℝ)
    (H : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hR : 0 < R) (hn : 1 ≤ n)
    (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3)
    (_hoff : marked.prod * n ≠ N) :
    (∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        (∑ label ∈ rankUpperRetainedLabels J (2 * (j + 1)) R,
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece (groupDyadicGeometry chi R H)
              (hbDyadicCut chi) label) marked) *
          offMarkedPhysicalResponse marked.prod N n Q rho)) =
      ((groupDyadicGeometry chi R H marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n)) *
        offMarkedPhysicalResponse marked.prod N n Q rho := by
  classical
  calc
    _ = (∑ j ∈ Finset.range 3,
      ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
        (∑ label ∈ rankUpperRetainedLabels J (2 * (j + 1)) R,
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece (groupDyadicGeometry chi R H)
              (hbDyadicCut chi) label) marked)) *
      offMarkedPhysicalResponse marked.prod N n Q rho := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_mul]
        ring
    _ = _ := by
      rw [original_group_rank_upper_signed_restoration
        chi J n R z y H marked hR hn hnJ hsmall hlarge hz hy hcube]

end ImbalancedChen.P3HBRankAdaptiveRetainedSupport
