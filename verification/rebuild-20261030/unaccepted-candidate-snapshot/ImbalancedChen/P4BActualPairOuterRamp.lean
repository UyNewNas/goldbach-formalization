import ImbalancedChen.P4BLabelledLogGeometry
import ImbalancedChen.P4BOuterRampBoundaryUnion

/-!
# P4B: the actual three-closed / one-strict pair outer ramp

YELLOW / SOURCE ONLY / UNCOMPILED.

The imports are future normal module names of sibling source-only drafts.
The exact source has three closed walls and one strict badness wall.  Its
indicator is never identified with an all-strict intersection.  An all-strict
indicator is used only as a lower bound when applying the finite strip union
inequality.  All boundary strips below are literal arithmetic finite filters.
No small strip estimate, derivative bound, P3 licence or SW result is claimed.
-/

namespace ImbalancedChen.P4B

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry

/-- Order, strict badness, lower cutoff, upper product, in that order. -/
def actualPairMargins (b lower : ℝ) (v : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![v 1 - v 0, v 0 - b * v 1, v 0 + v 1 - lower, 1 - v 0 - v 1]

/-- Four explicit scalar outer ramps at the exact normalized margins. -/
def fourWallOuterWeight (b lower delta : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ∏ i : Fin 4, logGateOuterRamp delta (actualPairMargins b lower v i)

/-- The actual mixed region implies nonnegative margins at all four walls.
Only the badness margin is necessarily strictly positive. -/
theorem actualPairMargins_nonneg_of_affineRegion
    {b lower : ℝ} {v : Fin 2 → ℝ} (hv : affineRegion b lower v) :
    ∀ i : Fin 4, 0 ≤ actualPairMargins b lower v i := by
  obtain ⟨horder, hbad, hlower, hupper⟩ := hv
  intro i
  fin_cases i <;> simp [actualPairMargins] <;> linarith

/-- The all-strict intersection is contained in the actual mixed region.
This is an implication, not an equality of the source indicators. -/
theorem affineRegion_of_all_strict_actualPairMargins
    {b lower : ℝ} {v : Fin 2 → ℝ}
    (hstrict : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      0 < actualPairMargins b lower v i) :
    affineRegion b lower v := by
  have h0 := hstrict 0 (Finset.mem_univ 0)
  have h1 := hstrict 1 (Finset.mem_univ 1)
  have h2 := hstrict 2 (Finset.mem_univ 2)
  have h3 := hstrict 3 (Finset.mem_univ 3)
  simp [actualPairMargins] at h0 h1 h2 h3
  unfold affineRegion
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The all-strict indicator is below the exact three-closed / one-strict
indicator, including points on any ordering or product wall. -/
theorem allStrictMargins_indicator_le_actual_affineIndicator
    (b lower : ℝ) (v : Fin 2 → ℝ) :
    (if ∀ i ∈ (Finset.univ : Finset (Fin 4)),
        0 < actualPairMargins b lower v i then (1 : ℝ) else 0) ≤
      (if affineRegion b lower v then (1 : ℝ) else 0) := by
  classical
  by_cases hstrict : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      0 < actualPairMargins b lower v i
  · have hv := affineRegion_of_all_strict_actualPairMargins hstrict
    simp only [if_pos hstrict, if_pos hv, le_refl]
  · rw [if_neg hstrict]
    split_ifs <;> norm_num

/-- All four ramps equal one on the exact source, including its three
closed boundaries. -/
theorem fourWallOuterWeight_eq_one_of_affineRegion
    {b lower delta : ℝ} (hdelta : 0 < delta) {v : Fin 2 → ℝ}
    (hv : affineRegion b lower v) :
    fourWallOuterWeight b lower delta v = 1 := by
  exact Finset.prod_eq_one (fun i _ =>
    logGateOuterRamp_eq_one hdelta (actualPairMargins_nonneg_of_affineRegion hv i))

theorem fourWallOuterWeight_bounds (b lower delta : ℝ) (v : Fin 2 → ℝ) :
    0 ≤ fourWallOuterWeight b lower delta v ∧
      fourWallOuterWeight b lower delta v ≤ 1 := by
  exact finite_gate_ramp_product_bounds (Finset.univ : Finset (Fin 4))
    (fun i => logGateOuterRamp delta (actualPairMargins b lower v i))
    (fun i _ => logGateOuterRamp_bounds delta _)

/-- Explicit actual labelled-pair outer weight. The original lower cutoff
T, cap N, ordering and strict power wall are all present. -/
def actualPairOuterRamp (b : ℝ) (N : ℕ) (T delta : ℝ)
    (t : Fin 2 → Fin (N + 1)) : ℝ :=
  fourWallOuterWeight b (Real.log T / Real.log (N : ℝ)) delta (logPoint N t)

/-- Literal arithmetic tuples in the i-th one-sided boundary strip.
The zero wall is included, and the expanded outer endpoint is strict. -/
def actualPairArithmeticStrip (b : ℝ) (N : ℕ) (T delta : ℝ) (i : Fin 4) :
    Finset (Fin 2 → Fin (N + 1)) :=
  (labelledPrimeTuples 2 N).filter (fun t =>
    -delta < actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i ∧
      actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i ≤ 0)

/-- The exact W is dominated on the genuine labelled prime carrier.
This uses its exact mixed-wall dictionary, rather than an all-strict source. -/
theorem actual_W_le_pairOuterRamp
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    W b N T t ≤ actualPairOuterRamp b N T delta t := by
  rw [W_eq_affineIndicator hN hT ht]
  by_cases hv : affineRegion b (Real.log T / Real.log (N : ℝ)) (logPoint N t)
  · simpa only [if_pos hv, actualPairOuterRamp,
      fourWallOuterWeight_eq_one_of_affineRegion hdelta hv] using (le_refl (1 : ℝ))
  · rw [if_neg hv]
    exact (fourWallOuterWeight_bounds b _ delta (logPoint N t)).1

/-- Actual surplus is nonnegative, retaining the original W exactly. -/
theorem actual_pairOuterRamp_surplus_nonneg
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    0 ≤ actualPairOuterRamp b N T delta t - W b N T t := by
  exact sub_nonneg.mpr (actual_W_le_pairOuterRamp hN hT hdelta ht)

/-- The exact surplus over actual W is paid by all four literal strip
indicators. Closed original order/product endpoints are preserved by W. -/
theorem actual_pairOuterRamp_sub_W_le_arithmetic_strip_indicators
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    actualPairOuterRamp b N T delta t - W b N T t ≤
      ∑ i : Fin 4,
        if -delta < actualPairMargins b (Real.log T / Real.log (N : ℝ))
            (logPoint N t) i ∧
          actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i ≤ 0
        then (1 : ℝ) else 0 := by
  rw [W_eq_affineIndicator hN hT ht]
  have hind := allStrictMargins_indicator_le_actual_affineIndicator
    b (Real.log T / Real.log (N : ℝ)) (logPoint N t)
  have hunion := logGateOuterRamp_product_surplus_le_strip_union
    (Finset.univ : Finset (Fin 4))
    (actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t)) hdelta
  exact (sub_le_sub_left hind _).trans (by
    simpa only [actualPairOuterRamp, fourWallOuterWeight, Finset.mem_univ, true_implies] using hunion)

/-- Genuine labelled W has exactly the actual source cardinality as mass;
there is no factor two, tuple multiplicity or surrogate normalization. -/
theorem sum_actual_labelled_W_eq_source_card (b : ℝ) (N : ℕ) (T : ℝ) :
    (∑ t ∈ labelledPrimeTuples 2 N, W b N T t) =
      ((realHalfProductSource b N T).card : ℝ) := by
  simpa using sum_labelled_W_eq_source b N T (fun _ => (1 : ℝ))

/-- Final finite actual-object bridge: the full positive outer tuple mass
costs actual source.card plus the four actual arithmetic strip cardinalities.
The strip counts remain explicit external arithmetic quantities. -/
theorem sum_actual_pairOuterRamp_le_source_card_add_arithmetic_strip_cards
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) :
    (∑ t ∈ labelledPrimeTuples 2 N, actualPairOuterRamp b N T delta t) ≤
      ((realHalfProductSource b N T).card : ℝ) +
        ∑ i : Fin 4, ((actualPairArithmeticStrip b N T delta i).card : ℝ) := by
  have hstrips :
      (∑ t ∈ labelledPrimeTuples 2 N, ∑ i : Fin 4,
        if -delta < actualPairMargins b (Real.log T / Real.log (N : ℝ))
            (logPoint N t) i ∧
          actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i ≤ 0
        then (1 : ℝ) else 0) =
      ∑ i : Fin 4, ((actualPairArithmeticStrip b N T delta i).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [actualPairArithmeticStrip, ← Finset.sum_filter]
    simp
  calc
    (∑ t ∈ labelledPrimeTuples 2 N, actualPairOuterRamp b N T delta t) ≤
        ∑ t ∈ labelledPrimeTuples 2 N, (W b N T t +
          ∑ i : Fin 4,
            if -delta < actualPairMargins b (Real.log T / Real.log (N : ℝ))
                (logPoint N t) i ∧
              actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i ≤ 0
            then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      have hpoint := actual_pairOuterRamp_sub_W_le_arithmetic_strip_indicators
        (b := b) hN hT hdelta ht
      linarith only [hpoint]
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_actual_labelled_W_eq_source_card, hstrips]

end
end ImbalancedChen.P4B