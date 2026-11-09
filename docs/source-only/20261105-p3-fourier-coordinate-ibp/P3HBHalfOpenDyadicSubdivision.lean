import ImbalancedChen.P3HBDyadicRectangleEndpointAudit
import Mathlib.Tactic

/-!
P3.6 — literal HB dyadic support: a finite HALF-OPEN ratio-two
subdivision of each six-axis coarse psi rectangle.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Frozen paper: chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (HB rectangular lower endpoints, (S)).
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Each original psi_j(x) has support (2^(j-1), 2^(j+1)).
We split it at the genuine base 2^j, assigning equality to the
upper half. Each resulting HALF-OPEN support box has upper/lower
endpoint ratio exactly two, and their sum restores the original
ordered six-coordinate tensor without deleting labels or multiplicity.

IMPORTANT: This is an exact FINITE ARITHMETIC support partition;
the indicator at x=2^j is discontinuous. It does NOT establish the
smooth C-infinity refinement or mixed Fourier bounds demanded by the
manuscript. Do not feed the individual sharp pieces to (F), and do
not mark (S) closed from this source alone. The separately recorded
padded factorTuples product bridge is still an explicit algebraic
premise in the R/128 lemma below.
-/

namespace ImbalancedChen.P3HBHalfOpenDyadicSubdivision
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3HBDyadicTensorPartition
open ImbalancedChen.P3HBRankAdaptiveRetainedSupport
open ImbalancedChen.P3HBDyadicRectangleEndpointAudit
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords

/-- The actual half-open membership of each of the SIX ordered slots.
The inequality is strict on the lower half: x = 2^j belongs to the
upper half. Unused HB positions remain genuine unit-padded slots. -/
def hbHalfMask (label : Fin 6 → ℕ) (hb : List ℕ) : Fin 6 → Bool :=
  fun i => decide (((hb.getD i.val 1 : ℕ) : ℝ) <
    (2 : ℝ) ^ (label i))

/-- Preserve the original tensor verbatim on the unique matching mask.
No sharp cutoff is silently differentiated: this is an arithmetic
support decomposition only. -/
def hbHalfCut (chi : ℝ → ℂ) (label : Fin 6 → ℕ)
    (side : Fin 6 → Bool) (marked hb : List ℕ) : ℂ :=
  if side = hbHalfMask label hb then hbDyadicCut chi label marked hb else 0

/-- The actual lower endpoint on one of the two half-open subboxes. -/
def hbHalfLower (label : Fin 6 → ℕ) (side : Fin 6 → Bool)
    (i : Fin 6) : ℝ :=
  if side i then (2 : ℝ) ^ (label i) / 2
  else (2 : ℝ) ^ (label i)

/-- Exactly one mask contributes to each genuine ordered original
HB tensor: no factor is duplicated and no coefficient is discarded. -/
theorem hbHalfCut_sum (chi : ℝ → ℂ) (label : Fin 6 → ℕ)
    (marked hb : List ℕ) :
    (∑ side : Fin 6 → Bool, hbHalfCut chi label side marked hb) =
      hbDyadicCut chi label marked hb := by
  classical
  simp [hbHalfCut]

/-- Nonzero refined mass forces the TRUE physical half-open mask,
and the original unmodified dyadic tensor must itself be nonzero. -/
theorem hbHalfCut_live_mask (chi : ℝ → ℂ) (label : Fin 6 → ℕ)
    (side : Fin 6 → Bool) (marked hb : List ℕ)
    (hlive : hbHalfCut chi label side marked hb ≠ 0) :
    side = hbHalfMask label hb ∧
      hbDyadicCut chi label marked hb ≠ 0 := by
  by_cases h : side = hbHalfMask label hb
  · refine ⟨h, ?_⟩
    simpa [hbHalfCut, h] using hlive
  · have hz : hbHalfCut chi label side marked hb = 0 := by
      simp [hbHalfCut, h]
    exact False.elim (hlive hz)

/-- Every nonzero refined slot belongs to its actual half-open box:
lower_i <= x_i < 2 * lower_i.  In the LOWER half the stricter
lower_i < x_i also holds. This uses literal psi plateau values,
NOT a guessed smoothing or a target distribution hypothesis. -/
theorem hbHalfCut_live_box (chi : ℝ → ℂ)
    (label : Fin 6 → ℕ) (side : Fin 6 → Bool)
    (marked hb : List ℕ) (i : Fin 6)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hlive : hbHalfCut chi label side marked hb ≠ 0) :
    hbHalfLower label side i ≤ ((hb.getD i.val 1 : ℕ) : ℝ) ∧
      ((hb.getD i.val 1 : ℕ) : ℝ) <
        2 * hbHalfLower label side i := by
  obtain ⟨hside, htensor⟩ :=
    hbHalfCut_live_mask chi label side marked hb hlive
  have hhigh :
      ((hb.getD i.val 1 : ℕ) : ℝ) <
        2 * (2 : ℝ) ^ (label i) :=
    hb_tensor_live_coordinate_upper chi label marked hb hlarge htensor i
  have hlow : (2 : ℝ) ^ (label i) <
      2 * ((hb.getD i.val 1 : ℕ) : ℝ) := by
    by_contra h
    have hzero := hbDyadicCut_zero_of_high_scale
      chi label marked hb i hsmall (le_of_not_gt h)
    exact htensor hzero
  by_cases hx : ((hb.getD i.val 1 : ℕ) : ℝ) <
      (2 : ℝ) ^ (label i)
  · have hs : side i = true := by
      rw [hside]
      simp [hbHalfMask, hx]
    constructor
    · simp only [hbHalfLower, if_pos hs]
      linarith
    · simp only [hbHalfLower, if_pos hs]
      linarith
  · have hs : side i = false := by
      rw [hside]
      simp [hbHalfMask, hx]
    constructor
    · simp only [hbHalfLower, if_neg (by simp [hs])]
      exact le_of_not_gt hx
    · simp only [hbHalfLower, if_neg (by simp [hs])]
      exact hhigh

/-- The R/128 geometry is VALID on every LIVE ratio-two half-open
subbox, with the precise original group psi and its strict R/2
lower window. The only algebraic extra premise, hphysical, is
the six-position padded ordered HB product identity. -/
theorem hbHalfCut_live_R128 (chi : ℝ → ℂ)
    (label : Fin 6 → ℕ) (side : Fin 6 → Bool)
    (marked hb : List ℕ) (n : ℕ) (R : ℝ)
    (hR : 0 < R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hgroup : chi ((n : ℝ) / R) - chi (2 * (n : ℝ) / R) ≠ 0)
    (hlive : hbHalfCut chi label side marked hb ≠ 0)
    (hphysical : (∏ i : Fin 6,
      ((hb.getD i.val 1 : ℕ) : ℝ)) = (n : ℝ)) :
    R / 128 < ∏ i : Fin 6, hbHalfLower label side i := by
  have hgroupLow : R / 2 < (n : ℝ) :=
    original_group_dyadic_lower_window
      chi (n : ℝ) R hR hsmall hgroup
  apply refined_two_to_one_R128_lower_envelope
    (fun i : Fin 6 => ((hb.getD i.val 1 : ℕ) : ℝ))
    (hbHalfLower label side) R
  · intro i
    exact Nat.cast_nonneg _
  · intro i
    exact (hbHalfCut_live_box chi label side marked hb i
      hsmall hlarge hlive).2.le
  · simpa only [hphysical] using hgroupLow

/-- Refining every already rank-and-upper-retained original label
recovers the exact ORIGINAL tensor sum, not a replacement source. -/
theorem rank_retained_half_sum (chi : ℝ → ℂ)
    (J r : ℕ) (R : ℝ) (marked hb : List ℕ) :
    (∑ label ∈ rankUpperRetainedLabels J r R,
      ∑ side : Fin 6 → Bool, hbHalfCut chi label side marked hb) =
    ∑ label ∈ rankUpperRetainedLabels J r R,
      hbDyadicCut chi label marked hb := by
  apply Finset.sum_congr rfl
  intro label _
  exact hbHalfCut_sum chi label marked hb

/-- Genuine factorTuples r n retain a finite exact partition
after HALF-OPEN subdivision of all original kept rectangles.
This is an identity of integer occurrence coefficients, not a
claim of C-infinity geometry or Fourier admissibility. -/
theorem factorTuple_rank_half_partition (chi : ℝ → ℂ)
    (J r n : ℕ) (R : ℝ) (marked hb : List ℕ)
    (hhb : hb ∈ factorTuples r n)
    (hn : 1 ≤ n) (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hwindow : (n : ℝ) ≤ 2 * R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    (∑ label ∈ rankUpperRetainedLabels J r R,
      ∑ side : Fin 6 → Bool,
        hbHalfCut chi label side marked hb) = 1 := by
  rw [rank_retained_half_sum]
  exact factorTuple_rank_upper_retained_partition
    chi J r n R marked hb hhb hn hnJ hwindow hsmall hlarge

end ImbalancedChen.P3HBHalfOpenDyadicSubdivision
