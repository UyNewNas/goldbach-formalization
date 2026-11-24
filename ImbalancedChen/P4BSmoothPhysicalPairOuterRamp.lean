import ImbalancedChen.P4BSmoothGateUpperStep
import ImbalancedChen.P4BPhysicalProductOuterRamp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Genuine smooth physical pair outer ramp and its continuous profile

YELLOW / SOURCE-ONLY / UNCOMPILED DRAFT.

Both project imports are future normal module names of sibling drafts.
The first three gates use their original normalized logarithmic margins;
only the upper-product gate is scaled by log N. The discrete prime-tuple
weight is exactly evaluation of an all-space smooth profile on Fin 2 -> R.
Every ContDiff order n in Nat-infinity is covered, including infinity.
No derivative-size bound, P3 geometric licence or distribution estimate
is asserted merely from this qualitative smoothness.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry

/-- The actual four-wall smooth weight, with a physical upper-product
shell of multiplicative width exp(width). -/
def smoothPhysicalPairOuterRamp (b : ℝ) (N : ℕ) (T width : ℝ)
    (t : Fin 2 → Fin (N + 1)) : ℝ :=
  ∏ i : Fin 4, smoothGateUpperStep width (physicalPairMargins b N T t i)

/-- The same affine physical margins, now on the full continuous plane.
N, T and b are fixed parameters; no logarithm of a varying coordinate
occurs in this continuous function. -/
def smoothPhysicalProfileMargin (b : ℝ) (N : ℕ) (T : ℝ)
    (v : Fin 2 → ℝ) (i : Fin 4) : ℝ :=
  physicalProductWallScale N i *
    actualPairMargins b (Real.log T / Real.log (N : ℝ)) v i

/-- A genuinely smooth profile on all of Fin 2 -> R, not just a function
on a finite discrete carrier. -/
def smoothPhysicalProfile (b : ℝ) (N : ℕ) (T width : ℝ)
    (v : Fin 2 → ℝ) : ℝ :=
  ∏ i : Fin 4, smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v i)

theorem smoothPhysicalPairOuterRamp_eq_profile (b : ℝ) (N : ℕ) (T width : ℝ)
    (t : Fin 2 → Fin (N + 1)) :
    smoothPhysicalPairOuterRamp b N T width t =
      smoothPhysicalProfile b N T width (logPoint N t) := by
  rfl

/-- Every affine margin is smooth at every order on the full plane.
This does not require log N to be nonzero, as it is only a parameter. -/
theorem contDiff_smoothPhysicalProfileMargin (b : ℝ) (N : ℕ) (T : ℝ)
    (i : Fin 4) {n : ℕ∞} :
    ContDiff ℝ n (fun v : Fin 2 → ℝ => smoothPhysicalProfileMargin b N T v i) := by
  have hx : ContDiff ℝ n (fun v : Fin 2 → ℝ => v 0) := contDiff_apply ℝ ℝ 0
  have hy : ContDiff ℝ n (fun v : Fin 2 → ℝ => v 1) := contDiff_apply ℝ ℝ 1
  have hm : ContDiff ℝ n (fun v : Fin 2 → ℝ =>
      actualPairMargins b (Real.log T / Real.log (N : ℝ)) v i) := by
    fin_cases i
    · change ContDiff ℝ n (fun v : Fin 2 → ℝ => v 1 - v 0)
      exact hy.sub hx
    · change ContDiff ℝ n (fun v : Fin 2 → ℝ => v 0 - b * v 1)
      exact hx.sub (contDiff_const.mul hy)
    · change ContDiff ℝ n (fun v : Fin 2 → ℝ =>
        v 0 + v 1 - Real.log T / Real.log (N : ℝ))
      exact (hx.add hy).sub contDiff_const
    · change ContDiff ℝ n (fun v : Fin 2 → ℝ => 1 - v 0 - v 1)
      exact (contDiff_const.sub hx).sub hy
  exact contDiff_const.mul hm

/-- All-space smoothness of the actual continuous profile, at every
finite or infinite differentiability order. No support or size hypothesis
is smuggled into this qualitative statement. -/
theorem contDiff_smoothPhysicalProfile (b : ℝ) (N : ℕ) (T width : ℝ)
    {n : ℕ∞} : ContDiff ℝ n (smoothPhysicalProfile b N T width) := by
  unfold smoothPhysicalProfile
  apply contDiff_prod
  intro i hi
  exact (contDiff_smoothGateUpperStep width).comp
    (contDiff_smoothPhysicalProfileMargin b N T i)

theorem smoothPhysicalProfile_bounds (b : ℝ) (N : ℕ) (T width : ℝ)
    (v : Fin 2 → ℝ) :
    0 ≤ smoothPhysicalProfile b N T width v ∧
      smoothPhysicalProfile b N T width v ≤ 1 := by
  exact finite_gate_ramp_product_bounds (Finset.univ : Finset (Fin 4))
    (fun i => smoothGateUpperStep width (smoothPhysicalProfileMargin b N T v i))
    (fun i _ => smoothGateUpperStep_bounds width _)

theorem smoothPhysicalPairOuterRamp_bounds (b : ℝ) (N : ℕ) (T width : ℝ)
    (t : Fin 2 → Fin (N + 1)) :
    0 ≤ smoothPhysicalPairOuterRamp b N T width t ∧
      smoothPhysicalPairOuterRamp b N T width t ≤ 1 := by
  rw [smoothPhysicalPairOuterRamp_eq_profile]
  exact smoothPhysicalProfile_bounds b N T width (logPoint N t)

/-- Exact equality to one on the original mixed-wall region, including
the closed order and product boundaries. -/
theorem smoothPhysicalPairOuterRamp_eq_one_of_affineRegion
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hwidth : 0 < width)
    {t : Fin 2 → Fin (N + 1)}
    (hv : affineRegion b (Real.log T / Real.log (N : ℝ)) (logPoint N t)) :
    smoothPhysicalPairOuterRamp b N T width t = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply smoothGateUpperStep_eq_one hwidth
  exact mul_nonneg (physicalProductWallScale_pos hN i).le
    (actualPairMargins_nonneg_of_affineRegion hv i)

/-- The genuine actual W is majorized on its original labelled prime
carrier. The three closed walls and one strict wall are used exactly. -/
theorem actual_W_le_smoothPhysicalPairOuterRamp
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hwidth : 0 < width) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    W b N T t ≤ smoothPhysicalPairOuterRamp b N T width t := by
  rw [W_eq_affineIndicator hN hT ht]
  by_cases hv : affineRegion b (Real.log T / Real.log (N : ℝ)) (logPoint N t)
  · simpa only [if_pos hv,
      smoothPhysicalPairOuterRamp_eq_one_of_affineRegion hN hwidth hv] using
      (le_refl (1 : ℝ))
  · rw [if_neg hv]
    exact (smoothPhysicalPairOuterRamp_bounds b N T width t).1

/-- Nonzero smooth weight forces every physical margin strictly above
-width. Equality at the expanded boundary gives a zero factor. -/
theorem smoothPhysicalPairOuterRamp_nonzero_margin_support
    {b T width : ℝ} {N : ℕ} (hwidth : 0 < width)
    {t : Fin 2 → Fin (N + 1)}
    (hnonzero : smoothPhysicalPairOuterRamp b N T width t ≠ 0) :
    ∀ i : Fin 4, -width < physicalPairMargins b N T t i := by
  intro i
  apply smoothGateUpperStep_nonzero_support hwidth
  intro hzero
  apply hnonzero
  exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-- The first three margins are the unchanged normalized gates needed
by the existing actual factor-roughness argument. -/
theorem smoothPhysicalPairOuterRamp_nonzero_original_margin_support
    {b T width : ℝ} {N : ℕ} (hwidth : 0 < width)
    {t : Fin 2 → Fin (N + 1)}
    (hnonzero : smoothPhysicalPairOuterRamp b N T width t ≠ 0)
    {i : Fin 4} (hi : i ≠ 3) :
    -width < actualPairMargins b (Real.log T / Real.log (N : ℝ))
      (logPoint N t) i := by
  have hs := smoothPhysicalPairOuterRamp_nonzero_margin_support hwidth hnonzero i
  rw [physicalPairMargins_eq_original_of_ne_upper b T N t hi] at hs
  exact hs

/-- The actual physical product support is strictly below exp(width)*N.
It is not enlarged to N^(1+width). Prime squares are included. -/
theorem smoothPhysicalPairOuterRamp_nonzero_product_lt_exp_mul_N
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hwidth : 0 < width)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hnonzero : smoothPhysicalPairOuterRamp b N T width t ≠ 0) :
    (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) < Real.exp width * (N : ℝ) := by
  have hgap := smoothPhysicalPairOuterRamp_nonzero_margin_support hwidth hnonzero 3
  rw [physicalPairMargins_upper_eq_log_gap b T hN t] at hgap
  obtain ⟨hr, hq⟩ := labelled_prime_pair_pos ht
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN
  rw [Nat.cast_mul]
  apply (Real.log_lt_log_iff (mul_pos hr hq)
    (mul_pos (Real.exp_pos width) hNpos)).mp
  rw [Real.log_mul hr.ne' hq.ne',
    Real.log_mul (Real.exp_pos width).ne' hNpos.ne', Real.log_exp]
  linarith only [hgap]

theorem smoothPhysicalPairOuterRamp_eq_zero_of_exp_mul_N_le_product
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hwidth : 0 < width)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hfar : Real.exp width * (N : ℝ) ≤
      (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ)) :
    smoothPhysicalPairOuterRamp b N T width t = 0 := by
  by_contra hn
  exact (not_lt_of_ge hfar)
    (smoothPhysicalPairOuterRamp_nonzero_product_lt_exp_mul_N hN hwidth ht hn)

/-- The closed four-wall enclosure of the continuous profile.  Its
upper-product wall includes the expanded endpoint, as topological support
must, even though every nonzero value has strict support. -/
def smoothPhysicalProfileClosedWalls (b : ℝ) (N : ℕ) (T width : ℝ) :
    Set (Fin 2 → ℝ) :=
  {v | ∀ i : Fin 4, -width ≤ smoothPhysicalProfileMargin b N T v i}

theorem isClosed_smoothPhysicalProfileClosedWalls
    (b : ℝ) (N : ℕ) (T width : ℝ) :
    IsClosed (smoothPhysicalProfileClosedWalls b N T width) := by
  change IsClosed (⋂ i : Fin 4,
    (fun v : Fin 2 → ℝ => smoothPhysicalProfileMargin b N T v i) ⁻¹' Ici (-width))
  apply isClosed_iInter
  intro i
  exact isClosed_Ici.preimage
    (contDiff_smoothPhysicalProfileMargin b N T i (n := 0)).continuous

theorem smoothPhysicalProfile_support_subset_closedWalls
    {b T width : ℝ} {N : ℕ} (hwidth : 0 < width) :
    Function.support (smoothPhysicalProfile b N T width) ⊆
      smoothPhysicalProfileClosedWalls b N T width := by
  intro v hv i
  change smoothPhysicalProfile b N T width v ≠ 0 at hv
  by_contra hbad
  have hmargin : smoothPhysicalProfileMargin b N T v i ≤ -width :=
    (lt_of_not_ge hbad).le
  have hzero : smoothPhysicalProfile b N T width v = 0 := by
    unfold smoothPhysicalProfile
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (smoothGateUpperStep_eq_zero hwidth hmargin)
  exact hv hzero

/-- Closed support control for the genuine continuous smooth packet.
This does not infer a P3 packet licence or any derivative-size bound. -/
theorem smoothPhysicalProfile_tsupport_subset_closedWalls
    {b T width : ℝ} {N : ℕ} (hwidth : 0 < width) :
    tsupport (smoothPhysicalProfile b N T width) ⊆
      smoothPhysicalProfileClosedWalls b N T width := by
  exact closure_minimal
    (smoothPhysicalProfile_support_subset_closedWalls hwidth)
    (isClosed_smoothPhysicalProfileClosedWalls b N T width)

/-- In normalized log coordinates the closed product wall has precisely
the physical logarithmic width. The original wall is included. -/
theorem smoothPhysicalProfile_tsupport_upper_product_wall
    {b T width : ℝ} {N : ℕ} (hwidth : 0 < width)
    {v : Fin 2 → ℝ} (hv : v ∈ tsupport (smoothPhysicalProfile b N T width)) :
    Real.log (N : ℝ) * (v 0 + v 1) ≤ Real.log (N : ℝ) + width := by
  have h := (smoothPhysicalProfile_tsupport_subset_closedWalls hwidth hv) (3 : Fin 4)
  change -width ≤ Real.log (N : ℝ) * (1 - v 0 - v 1) at h
  nlinarith only [h]

end

end ImbalancedChen.P4B
