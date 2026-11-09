import ImbalancedChen.P3HBDyadicTensorPartition
import Mathlib.Tactic

/-!
P3.6 — support-safe pruning of the full original six-slot HB dyadic grid.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Manuscript: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (psi and retained HB rectangles) and §4 (F).
Mathlib pin: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Unlike the preceding FULL grid theorem, this packet removes a CONCRETE
set of dyadic rectangles: any label with a coordinate base 2^j >= 4R
is identically zero on an original HB fibre of complete product n <= 2R.
The upper support n < 2R follows directly for the manuscript's literal
group cutoff psi(n/R) = chi(n/R) - chi(2n/R) when it is nonzero.

This is only a safe OVER-retention of genuine geometric support; it does
not identify the manuscript's final selected rectangle list or pay Fourier
or shifted-divisor discrepancy. No source words or rho are changed.
-/

namespace ImbalancedChen.P3HBRetainedDyadicUpperSupport

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P3HBFinitePartitionRestore
open ImbalancedChen.P3HBDyadicTensorPartition
open ImbalancedChen.P3HBMarkedFixedProductFibre
open ImbalancedChen.P3HBOriginalGeometricProductCollapse
open ImbalancedChen.P3HBMarkedMobiusOffshiftSameRho

/-- If the dyadic base already dominates 2*x, BOTH terms in the actual
difference cutoff are on chi's lower plateau. No monotonicity or
nonnegativity hypothesis is used. The endpoint is closed. -/
theorem dyadicPiece_zero_of_high_scale (chi : ℝ → ℂ)
    (x : ℝ) (j : ℕ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hx : 0 ≤ x) (hscale : 2 * x ≤ (2 : ℝ) ^ j) :
    dyadicPiece chi x j = 0 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hxsmall : x ≤ (2 : ℝ) ^ j := by linarith
  have hleft : x / (2 : ℝ) ^ j ≤ 1 :=
    (div_le_iff₀ hp).2 hxsmall
  have hright : 2 * x / (2 : ℝ) ^ j ≤ 1 :=
    (div_le_iff₀ hp).2 hscale
  unfold dyadicPiece
  rw [hsmall _ hleft, hsmall _ hright]
  ring

/-- A single zero factor kills the genuine ordered six-slot tensor cut.
This also applies to padded unit slots, with no merging of equal labels. -/
theorem hbDyadicCut_zero_of_high_scale (chi : ℝ → ℂ)
    (label : Fin 6 → ℕ) (marked hb : List ℕ) (i : Fin 6)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hscale : 2 * (hb.getD i.val 1 : ℝ) ≤
      (2 : ℝ) ^ (label i)) :
    hbDyadicCut chi label marked hb = 0 := by
  unfold hbDyadicCut
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply dyadicPiece_zero_of_high_scale chi _ _ hsmall
  · exact Nat.cast_nonneg _
  · exact hscale

/-- A concrete finite subset of the same six-coordinate labels: discard
any dyadic rectangle whose one coordinate base is >= 4R. Unlike a
hypothetical "selected" predicate, this is an explicit geometric test. -/
def upperRetainedLabels (J : ℕ) (R : ℝ) : Finset (Fin 6 → ℕ) :=
  (dyadicLabels J).filter
    (fun label => ∀ i : Fin 6, (2 : ℝ) ^ (label i) < 4 * R)

/-- Every omitted full-grid label is identically zero on an ORIGINAL
ordered positive factorTuples fibre with complete product n <= 2R.
The bound on each slot comes from factorTuples_spec, not a newly assumed
rectangle/PP property. -/
theorem omitted_upper_label_zero
    (chi : ℝ → ℂ) (J r n : ℕ) (R : ℝ)
    (marked hb : List ℕ) (label : Fin 6 → ℕ)
    (hhb : hb ∈ factorTuples r n) (hn : 1 ≤ n)
    (hwindow : (n : ℝ) ≤ 2 * R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hgrid : label ∈ dyadicLabels J)
    (homit : label ∉ upperRetainedLabels J R) :
    hbDyadicCut chi label marked hb = 0 := by
  classical
  have hnot : ¬ ∀ i : Fin 6, (2 : ℝ) ^ (label i) < 4 * R := by
    intro h
    apply homit
    exact Finset.mem_filter.mpr ⟨hgrid, h⟩
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hbase : 4 * R ≤ (2 : ℝ) ^ (label i) := le_of_not_gt hi
  have hslot := (factorTuple_getD_bounds hhb hn i).2
  have hslotR : (hb.getD i.val 1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hslot
  have hscale : 2 * (hb.getD i.val 1 : ℝ) ≤
      (2 : ℝ) ^ (label i) := by
    linarith
  exact hbDyadicCut_zero_of_high_scale
    chi label marked hb i hsmall hscale

/-- The explicitly pruned grid, not just an abstract partition interface,
still sums to one over each original ordered HB fibre. This genuinely
removes zero rectangles from the previously complete canonical grid. -/
theorem factorTuple_upper_retained_partition
    (chi : ℝ → ℂ) (J r n : ℕ) (R : ℝ)
    (marked hb : List ℕ)
    (hhb : hb ∈ factorTuples r n)
    (hn : 1 ≤ n) (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hwindow : (n : ℝ) ≤ 2 * R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    (∑ label ∈ upperRetainedLabels J R,
      hbDyadicCut chi label marked hb) = 1 := by
  classical
  have hfull := factorTuple_dyadic_partition_marked
    chi J r n marked hb hhb hn hnJ hsmall hlarge
  calc
    (∑ label ∈ upperRetainedLabels J R,
      hbDyadicCut chi label marked hb) =
      ∑ label ∈ dyadicLabels J, hbDyadicCut chi label marked hb := by
        simp only [upperRetainedLabels, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro label hlabel
        by_cases hkeep : ∀ i : Fin 6,
            (2 : ℝ) ^ (label i) < 4 * R
        · simp [hkeep]
        · have homit : label ∉ upperRetainedLabels J R := by
            intro hh
            exact hkeep (Finset.mem_filter.mp hh).2
          have hzero := omitted_upper_label_zero
            chi J r n R marked hb label hhb hn hwindow
            hsmall hlabel homit
          simp [hkeep, hzero]
    _ = 1 := hfull

/-- The literal ORIGINAL group dyadic cutoff gives a strict upper window,
including the endpoint: psi(n/R) nonzero implies n < 2R. -/
theorem original_group_dyadic_upper_window
    (chi : ℝ → ℂ) (x R : ℝ) (hR : 0 < R)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hgroup : chi (x / R) - chi (2 * x / R) ≠ 0) :
    x < 2 * R := by
  by_contra h
  have hx : 2 * R ≤ x := le_of_not_gt h
  have hleft : 2 ≤ x / R := (le_div_iff₀ hR).2 hx
  have hright : 2 ≤ 2 * x / R := (le_div_iff₀ hR).2 (by linarith)
  apply hgroup
  rw [hlarge _ hleft, hlarge _ hright]
  ring

/-- Original product-type geometry with its literal whole-group psi(n/R),
as opposed to an invented target-dependent geometric support selector. -/
def groupDyadicGeometry (chi : ℝ → ℂ) (R : ℝ)
    (H : List ℕ → ℕ → ℂ) : List ℕ → ℕ → ℂ :=
  fun marked n => H marked n *
    (chi ((n : ℝ) / R) - chi (2 * (n : ℝ) / R))

/-- On the nonzero support of the ORIGINAL smooth group cutoff, every
dropped upper-impossible rectangle is zero. Thus the original 3,-3,+1
identity is restored using a STRICT subset of the full canonical grid.
The geometry H remains arbitrary and no PP estimate is assumed. -/
theorem original_group_upper_retained_signed_restoration
    (chi : ℝ → ℂ) (J n : ℕ) (R z y : ℝ)
    (H : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (hR : 0 < R) (hn : 1 ≤ n)
    (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3) :
    (∑ label ∈ upperRetainedLabels J R,
      ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece (groupDyadicGeometry chi R H)
              (hbDyadicCut chi) label) marked) =
      (groupDyadicGeometry chi R H marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n) := by
  apply signed_three_partition_restores
    (upperRetainedLabels J R) n z y
    (groupDyadicGeometry chi R H) (hbDyadicCut chi)
    marked hz hy hcube
  intro j hj hb hhb hg
  have hgroup : chi ((n : ℝ) / R) -
      chi (2 * (n : ℝ) / R) ≠ 0 := by
    intro hzero
    apply hg
    simp [groupDyadicGeometry, hzero]
  have hwindow : (n : ℝ) ≤ 2 * R :=
    le_of_lt (original_group_dyadic_upper_window
      chi (n : ℝ) R hR hlarge hgroup)
  exact factorTuple_upper_retained_partition chi J
    (2 * (j + 1)) n R marked hb hhb hn hnJ
    hwindow hsmall hlarge

/-- The same original integer rho and physical Q response is factored
only AFTER the complete retained-label sum. The complete physical
product marked.prod*n, exact coprime mean, strict offshift and original
HB position multiplicities are untouched. -/
theorem original_group_upper_retained_offshift_same_rho
    (chi : ℝ → ℂ) (J N n : ℕ) (R z y : ℝ)
    (H : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hR : 0 < R) (hn : 1 ≤ n)
    (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3)
    (hoff : marked.prod * n ≠ N) :
    (∑ label ∈ upperRetainedLabels J R,
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece (groupDyadicGeometry chi R H)
              (hbDyadicCut chi) label) marked) *
        offMarkedPhysicalResponse marked.prod N n Q rho) =
      ((groupDyadicGeometry chi R H marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n)) *
        offMarkedPhysicalResponse marked.prod N n Q rho := by
  rw [← Finset.sum_mul]
  rw [original_group_upper_retained_signed_restoration
    chi J n R z y H marked hR hn hnJ hsmall hlarge hz hy hcube]

end ImbalancedChen.P3HBRetainedDyadicUpperSupport
