import ImbalancedChen.P4BActualPairOuterRamp

/-!
# P4B: physical product shell with a fixed logarithmic width

YELLOW / SOURCE ONLY / UNCOMPILED.

This future-import draft retains the older normalized-wall finite result.
It positively rescales only the upper product margin by log N. Thus a fixed
ramp width delta expands the product cap to exp(delta)*N, with a strict
outer endpoint for nonzero weight. It does not expand the cap to N^(1+delta).
All arithmetic strip counts remain explicit; no shell smallness, derivative
bound, P3 licence or Siegel--Walfisz estimate is claimed.
-/

namespace ImbalancedChen.P4B

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry

/-- Positive rescaling preserves a closed gate exactly. -/
theorem positive_scale_nonneg_iff {s x : ℝ} (hs : 0 < s) :
    0 ≤ s * x ↔ 0 ≤ x := by
  constructor
  · intro h
    by_contra hx
    have hnegative := mul_neg_of_pos_of_neg hs (lt_of_not_ge hx)
    linarith only [h, hnegative]
  · intro hx
    exact mul_nonneg hs.le hx

/-- Positive rescaling preserves a strict gate exactly. -/
theorem positive_scale_pos_iff {s x : ℝ} (hs : 0 < s) :
    0 < s * x ↔ 0 < x := by
  constructor
  · intro h
    by_contra hx
    have hnonpositive := mul_nonpos_of_nonneg_of_nonpos hs.le (le_of_not_gt hx)
    linarith only [h, hnonpositive]
  · intro hx
    exact mul_pos hs hx

/-- The original mixture of three closed walls and one strict wall. -/
theorem affineRegion_iff_four_margin_signs (b lower : ℝ) (v : Fin 2 → ℝ) :
    affineRegion b lower v ↔
      0 ≤ actualPairMargins b lower v 0 ∧
      0 < actualPairMargins b lower v 1 ∧
      0 ≤ actualPairMargins b lower v 2 ∧
      0 ≤ actualPairMargins b lower v 3 := by
  change (v 0 ≤ v 1 ∧ b * v 1 < v 0 ∧ lower ≤ v 0 + v 1 ∧ v 0 + v 1 ≤ 1) ↔
    (0 ≤ v 1 - v 0 ∧ 0 < v 0 - b * v 1 ∧
      0 ≤ v 0 + v 1 - lower ∧ 0 ≤ 1 - v 0 - v 1)
  constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Arbitrary positive scales preserve the exact mixed-wall region. -/
theorem affineRegion_iff_positive_rescaled_margins
    (b lower : ℝ) (v : Fin 2 → ℝ) (scale : Fin 4 → ℝ)
    (hscale : ∀ i, 0 < scale i) :
    affineRegion b lower v ↔
      0 ≤ scale 0 * actualPairMargins b lower v 0 ∧
      0 < scale 1 * actualPairMargins b lower v 1 ∧
      0 ≤ scale 2 * actualPairMargins b lower v 2 ∧
      0 ≤ scale 3 * actualPairMargins b lower v 3 := by
  rw [positive_scale_nonneg_iff (hscale 0), positive_scale_pos_iff (hscale 1),
    positive_scale_nonneg_iff (hscale 2), positive_scale_nonneg_iff (hscale 3)]
  exact affineRegion_iff_four_margin_signs b lower v

/-- Four actual scalar ramps, with a separate scale for each physical wall. -/
def positiveRescaledFourWallWeight (b lower : ℝ) (scale : Fin 4 → ℝ)
    (delta : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  ∏ i : Fin 4, logGateOuterRamp delta (scale i * actualPairMargins b lower v i)

theorem positiveRescaledFourWallWeight_bounds
    (b lower : ℝ) (scale : Fin 4 → ℝ) (delta : ℝ) (v : Fin 2 → ℝ) :
    0 ≤ positiveRescaledFourWallWeight b lower scale delta v ∧
      positiveRescaledFourWallWeight b lower scale delta v ≤ 1 := by
  exact finite_gate_ramp_product_bounds (Finset.univ : Finset (Fin 4))
    (fun i => logGateOuterRamp delta (scale i * actualPairMargins b lower v i))
    (fun i _ => logGateOuterRamp_bounds delta _)

theorem positiveRescaledFourWallWeight_eq_one
    {b lower delta : ℝ} (scale : Fin 4 → ℝ)
    (hscale : ∀ i, 0 < scale i) (hdelta : 0 < delta) {v : Fin 2 → ℝ}
    (hv : affineRegion b lower v) :
    positiveRescaledFourWallWeight b lower scale delta v = 1 := by
  exact Finset.prod_eq_one (fun i _ => logGateOuterRamp_eq_one hdelta
    (mul_nonneg (hscale i).le (actualPairMargins_nonneg_of_affineRegion hv i)))

theorem actual_affineIndicator_le_positiveRescaledFourWallWeight
    (b lower : ℝ) (scale : Fin 4 → ℝ) (hscale : ∀ i, 0 < scale i)
    {delta : ℝ} (hdelta : 0 < delta) (v : Fin 2 → ℝ) :
    (if affineRegion b lower v then (1 : ℝ) else 0) ≤
      positiveRescaledFourWallWeight b lower scale delta v := by
  by_cases hv : affineRegion b lower v
  · simpa only [if_pos hv, positiveRescaledFourWallWeight_eq_one scale hscale hdelta hv]
      using (le_refl (1 : ℝ))
  · rw [if_neg hv]
    exact (positiveRescaledFourWallWeight_bounds b lower scale delta v).1

/-- Generic positive-rescaling union bound, with the actual mixed region. -/
theorem positiveRescaledFourWallWeight_sub_actualIndicator_le_strips
    (b lower : ℝ) (scale : Fin 4 → ℝ) (hscale : ∀ i, 0 < scale i)
    {delta : ℝ} (hdelta : 0 < delta) (v : Fin 2 → ℝ) :
    positiveRescaledFourWallWeight b lower scale delta v -
        (if affineRegion b lower v then (1 : ℝ) else 0) ≤
      ∑ i : Fin 4, if -delta < scale i * actualPairMargins b lower v i ∧
        scale i * actualPairMargins b lower v i ≤ 0 then (1 : ℝ) else 0 := by
  have hstrict :
      (∀ i ∈ (Finset.univ : Finset (Fin 4)),
        0 < scale i * actualPairMargins b lower v i) ↔
      (∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 < actualPairMargins b lower v i) := by
    constructor
    · intro h i hi
      exact (positive_scale_pos_iff (hscale i)).mp (h i hi)
    · intro h i hi
      exact (positive_scale_pos_iff (hscale i)).mpr (h i hi)
  have hind := allStrictMargins_indicator_le_actual_affineIndicator b lower v
  have hunion := logGateOuterRamp_product_surplus_le_strip_union
    (Finset.univ : Finset (Fin 4))
    (fun i => scale i * actualPairMargins b lower v i) hdelta
  rw [hstrict] at hunion
  exact (sub_le_sub_left hind _).trans hunion

/-- Only the upper product wall is changed; its scale is log N. -/
def physicalProductWallScale (N : ℕ) (i : Fin 4) : ℝ :=
  if i = 3 then Real.log (N : ℝ) else 1

theorem physicalProductWallScale_pos {N : ℕ} (hN : (1 : ℝ) < N) :
    ∀ i, 0 < physicalProductWallScale N i := by
  intro i
  by_cases hi : i = 3
  · simpa only [physicalProductWallScale, if_pos hi] using Real.log_pos hN
  · simp only [physicalProductWallScale, if_neg hi, zero_lt_one]

def physicalPairMargins (b : ℝ) (N : ℕ) (T : ℝ)
    (t : Fin 2 → Fin (N + 1)) (i : Fin 4) : ℝ :=
  physicalProductWallScale N i *
    actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i

def physicalPairOuterRamp (b : ℝ) (N : ℕ) (T delta : ℝ)
    (t : Fin 2 → Fin (N + 1)) : ℝ :=
  positiveRescaledFourWallWeight b (Real.log T / Real.log (N : ℝ))
    (physicalProductWallScale N) delta (logPoint N t)

def physicalPairArithmeticStrip (b : ℝ) (N : ℕ) (T delta : ℝ) (i : Fin 4) :
    Finset (Fin 2 → Fin (N + 1)) :=
  (labelledPrimeTuples 2 N).filter (fun t =>
    -delta < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0)

/-- The other three margins are literally unchanged. -/
theorem physicalPairMargins_eq_original_of_ne_upper
    (b T : ℝ) (N : ℕ) (t : Fin 2 → Fin (N + 1)) {i : Fin 4} (hi : i ≠ 3) :
    physicalPairMargins b N T t i =
      actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i := by
  simp only [physicalPairMargins, physicalProductWallScale, if_neg hi, one_mul]

/-- Every physical margin lies inside its expanded gate when the full
actual tuple weight is nonzero. This uses the literal product factors. -/
theorem physicalPairOuterRamp_nonzero_margin_support
    {b T delta : ℝ} {N : ℕ} (hdelta : 0 < delta)
    {t : Fin 2 → Fin (N + 1)} (hnonzero : physicalPairOuterRamp b N T delta t ≠ 0) :
    ∀ i : Fin 4, -delta < physicalPairMargins b N T t i := by
  intro i
  apply logGateOuterRamp_nonzero_support hdelta
  intro hzero
  apply hnonzero
  exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-- In particular the first three normalized margins retain the identical
width delta. This API supplies the actual roughness-transfer geometry. -/
theorem physicalPairOuterRamp_nonzero_original_margin_support
    {b T delta : ℝ} {N : ℕ} (hdelta : 0 < delta)
    {t : Fin 2 → Fin (N + 1)} (hnonzero : physicalPairOuterRamp b N T delta t ≠ 0)
    {i : Fin 4} (hi : i ≠ 3) :
    -delta < actualPairMargins b (Real.log T / Real.log (N : ℝ)) (logPoint N t) i := by
  have hs := physicalPairOuterRamp_nonzero_margin_support hdelta hnonzero i
  rw [physicalPairMargins_eq_original_of_ne_upper b T N t hi] at hs
  exact hs
/-- The rescaled product wall is exactly a physical logarithmic gap. -/
theorem physicalPairMargins_upper_eq_log_gap
    (b T : ℝ) {N : ℕ} (hN : (1 : ℝ) < N) (t : Fin 2 → Fin (N + 1)) :
    physicalPairMargins b N T t 3 =
      Real.log (N : ℝ) - Real.log ((tuplePair t).1 : ℝ) -
        Real.log ((tuplePair t).2 : ℝ) := by
  change Real.log (N : ℝ) *
      (1 - Real.log ((t 0).val : ℝ) / Real.log (N : ℝ) -
        Real.log ((t 1).val : ℝ) / Real.log (N : ℝ)) =
    Real.log (N : ℝ) - Real.log ((t 0).val : ℝ) - Real.log ((t 1).val : ℝ)
  field_simp [ne_of_gt (Real.log_pos hN)] <;> ring

/-- The actual indicator retains exactly three closed and one strict wall
also after the physical product-wall rescaling. -/
theorem actual_W_eq_physical_mixedIndicator
    {b T : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N) :
    W b N T t =
      (if 0 ≤ physicalPairMargins b N T t 0 ∧
          0 < physicalPairMargins b N T t 1 ∧
          0 ≤ physicalPairMargins b N T t 2 ∧
          0 ≤ physicalPairMargins b N T t 3 then (1 : ℝ) else 0) := by
  simpa only [physicalPairMargins,
    affineRegion_iff_positive_rescaled_margins b
      (Real.log T / Real.log (N : ℝ)) (logPoint N t)
      (physicalProductWallScale N) (physicalProductWallScale_pos hN)] using
    (W_eq_affineIndicator hN hT ht)

theorem actual_W_le_physicalPairOuterRamp
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    W b N T t ≤ physicalPairOuterRamp b N T delta t := by
  rw [W_eq_affineIndicator hN hT ht]
  exact actual_affineIndicator_le_positiveRescaledFourWallWeight b _
    (physicalProductWallScale N) (physicalProductWallScale_pos hN) hdelta _

/-- The physical outer surplus is nonnegative on the genuine prime carrier. -/
theorem physicalPairOuterRamp_surplus_nonneg
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    0 ≤ physicalPairOuterRamp b N T delta t - W b N T t := by
  exact sub_nonneg.mpr (actual_W_le_physicalPairOuterRamp hN hT hdelta ht)

/-- Nonzero physical outer weight has the strict physical cap exp(delta)*N.
Equality at this expanded cap is excluded, including for prime squares. -/
theorem physicalPairOuterRamp_nonzero_product_lt_exp_mul_N
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hdelta : 0 < delta)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hnonzero : physicalPairOuterRamp b N T delta t ≠ 0) :
    (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) < Real.exp delta * (N : ℝ) := by
  have hfactor : logGateOuterRamp delta (physicalPairMargins b N T t 3) ≠ 0 := by
    intro hzero
    apply hnonzero
    exact Finset.prod_eq_zero (Finset.mem_univ (3 : Fin 4)) hzero
  have hgap := logGateOuterRamp_nonzero_support hdelta hfactor
  rw [physicalPairMargins_upper_eq_log_gap b T hN t] at hgap
  obtain ⟨hr, hq⟩ := labelled_prime_pair_pos ht
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN
  rw [Nat.cast_mul]
  apply (Real.log_lt_log_iff (mul_pos hr hq)
    (mul_pos (Real.exp_pos delta) hNpos)).mp
  rw [Real.log_mul hr.ne' hq.ne',
    Real.log_mul (Real.exp_pos delta).ne' hNpos.ne', Real.log_exp]
  linarith only [hgap]

/-- At or beyond the expanded physical product cap the weight is zero. -/
theorem physicalPairOuterRamp_eq_zero_of_exp_mul_N_le_product
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hdelta : 0 < delta)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hfar : Real.exp delta * (N : ℝ) ≤
      (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ)) :
    physicalPairOuterRamp b N T delta t = 0 := by
  by_contra hn
  exact (not_lt_of_ge hfar)
    (physicalPairOuterRamp_nonzero_product_lt_exp_mul_N hN hdelta ht hn)

/-- Exact physical arithmetic shell, including the original product cap
and excluding the expanded outer endpoint. No shell count is estimated. -/
theorem physical_upper_margin_strip_iff_product_shell
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N) :
    (-delta < physicalPairMargins b N T t 3 ∧ physicalPairMargins b N T t 3 ≤ 0) ↔
      ((N : ℝ) ≤ (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) ∧
        (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) < Real.exp delta * (N : ℝ)) := by
  obtain ⟨hr, hq⟩ := labelled_prime_pair_pos ht
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN
  have hge :
      (N : ℝ) ≤ (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) ↔
        Real.log (N : ℝ) ≤
          Real.log ((tuplePair t).1 : ℝ) + Real.log ((tuplePair t).2 : ℝ) := by
    rw [Nat.cast_mul, ← Real.log_le_log_iff hNpos (mul_pos hr hq),
      Real.log_mul hr.ne' hq.ne']
  have hless :
      (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) < Real.exp delta * (N : ℝ) ↔
        Real.log ((tuplePair t).1 : ℝ) + Real.log ((tuplePair t).2 : ℝ) <
          delta + Real.log (N : ℝ) := by
    rw [Nat.cast_mul,
      ← Real.log_lt_log_iff (mul_pos hr hq) (mul_pos (Real.exp_pos delta) hNpos),
      Real.log_mul hr.ne' hq.ne',
      Real.log_mul (Real.exp_pos delta).ne' hNpos.ne', Real.log_exp]
  rw [physicalPairMargins_upper_eq_log_gap b T hN t, hge, hless]
  constructor <;> rintro ⟨h0, h1⟩ <;>
    exact ⟨by linarith only [h0, h1], by linarith only [h0, h1]⟩

/-- The actual physical surplus has the same exact finite arithmetic union
payment, now with the physically rescaled upper-product strip. -/
theorem physicalPairOuterRamp_sub_W_le_arithmetic_strips
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    physicalPairOuterRamp b N T delta t - W b N T t ≤
      ∑ i : Fin 4, if -delta < physicalPairMargins b N T t i ∧
        physicalPairMargins b N T t i ≤ 0 then (1 : ℝ) else 0 := by
  rw [W_eq_affineIndicator hN hT ht]
  exact positiveRescaledFourWallWeight_sub_actualIndicator_le_strips b _
    (physicalProductWallScale N) (physicalProductWallScale_pos hN) hdelta _

/-- Literal finite mass bound for the physically localized positive weight.
The complete four-strip arithmetic price remains on the right-hand side. -/
theorem sum_physicalPairOuterRamp_le_source_card_add_arithmetic_strip_cards
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) :
    (∑ t ∈ labelledPrimeTuples 2 N, physicalPairOuterRamp b N T delta t) ≤
      ((realHalfProductSource b N T).card : ℝ) +
        ∑ i : Fin 4, ((physicalPairArithmeticStrip b N T delta i).card : ℝ) := by
  have hstrips :
      (∑ t ∈ labelledPrimeTuples 2 N, ∑ i : Fin 4,
        if -delta < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0
        then (1 : ℝ) else 0) =
      ∑ i : Fin 4, ((physicalPairArithmeticStrip b N T delta i).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [physicalPairArithmeticStrip, ← Finset.sum_filter]
    simp
  calc
    (∑ t ∈ labelledPrimeTuples 2 N, physicalPairOuterRamp b N T delta t) ≤
        ∑ t ∈ labelledPrimeTuples 2 N, (W b N T t +
          ∑ i : Fin 4,
            if -delta < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0
            then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      have hpoint := physicalPairOuterRamp_sub_W_le_arithmetic_strips hN hT hdelta ht
      linarith only [hpoint]
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_actual_labelled_W_eq_source_card, hstrips]

end
end ImbalancedChen.P4B