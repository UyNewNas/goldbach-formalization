import ImbalancedChen.P4BPhysicalProductOuterRamp
import ImbalancedChen.P4BLabelledOuterPushforward

/-!
# P4B jointly supported arithmetic boundary strips

SOURCE-ONLY / YELLOW / UNCOMPILED, 2026-10-24.

The older single-wall strip bound is a valid finite inequality, but does
not retain the other gates and supplies no small arithmetic boundary
budget. Here every strip also requires ALL softened margin inequalities.
Positive residual forces a positive product, which forces this full joint
support. The physical specialization uses the genuine three-closed /
one-strict W and its exact source-cardinality sum. No arithmetic smallness
is claimed for either the old strips or the supported strips.

Imports are future normal module names for source-only companion drafts.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary

/-- A positive finite ramp product forces every original margin into its
strict softened half-space. This is a finite zero-factor argument. -/
theorem softened_margins_of_ramp_product_pos {ι : Type*}
    (I : Finset ι) (G ramp : ι → ℝ) (width : ℝ)
    (hzero : ∀ i ∈ I, G i ≤ -width → ramp i = 0)
    (hprod : 0 < ∏ i ∈ I, ramp i) :
    ∀ i ∈ I, -width < G i := by
  intro i hi
  apply lt_of_not_ge
  intro hfar
  have hz : (∏ j ∈ I, ramp j) = 0 :=
    Finset.prod_eq_zero hi (hzero i hi hfar)
  rw [hz] at hprod
  exact (lt_irrefl 0) hprod

/-- Positive surplus above the strict indicator retains all softened
gates, rather than merely one failed wall. -/
theorem softened_margins_of_positive_ramp_residual {ι : Type*}
    (I : Finset ι) (G ramp : ι → ℝ) (width : ℝ)
    (hzero : ∀ i ∈ I, G i ≤ -width → ramp i = 0)
    (hresidual : 0 < (∏ i ∈ I, ramp i) -
      (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0)) :
    ∀ i ∈ I, -width < G i := by
  have hindicator : 0 ≤ (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hprod : 0 < ∏ i ∈ I, ramp i := by
    linarith only [hresidual, hindicator]
  exact softened_margins_of_ramp_product_pos I G ramp width hzero hprod

/-- Sharp finite union payment with common joint support in every term.
Empty families and both strip endpoints follow the same finite argument. -/
theorem ramp_product_sub_indicator_le_supported_strip_union {ι : Type*}
    (I : Finset ι) (G ramp : ι → ℝ) (width : ℝ)
    (hbound : ∀ i ∈ I, 0 ≤ ramp i ∧ ramp i ≤ 1)
    (hone : ∀ i ∈ I, 0 < G i → ramp i = 1)
    (hzero : ∀ i ∈ I, G i ≤ -width → ramp i = 0) :
    (∏ i ∈ I, ramp i) - (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0) ≤
      ∑ i ∈ I, if (-width < G i ∧ G i ≤ 0) ∧
        (∀ j ∈ I, -width < G j) then (1 : ℝ) else 0 := by
  by_cases hresidual : 0 < (∏ i ∈ I, ramp i) -
      (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0)
  · have hsoft := softened_margins_of_positive_ramp_residual
      I G ramp width hzero hresidual
    have hsupport : (∀ j ∈ I, -width < G j) = True :=
      propext (iff_true_intro hsoft)
    simpa only [hsupport, and_true] using
      ramp_product_sub_strict_indicator_le_strip_union I G ramp width hbound hone hzero
  · apply (le_of_not_gt hresidual).trans
    apply Finset.sum_nonneg
    intro i _hi
    split_ifs <;> norm_num

/-- The genuine public scalar ramp satisfies all generic laws internally. -/
theorem logGateOuterRamp_sub_indicator_le_supported_strip_union {ι : Type*}
    (I : Finset ι) (G : ι → ℝ) {width : ℝ} (hwidth : 0 < width) :
    (∏ i ∈ I, logGateOuterRamp width (G i)) -
      (if ∀ i ∈ I, 0 < G i then (1 : ℝ) else 0) ≤
        ∑ i ∈ I, if (-width < G i ∧ G i ≤ 0) ∧
          (∀ j ∈ I, -width < G j) then (1 : ℝ) else 0 := by
  exact ramp_product_sub_indicator_le_supported_strip_union I G
    (fun i => logGateOuterRamp width (G i)) width
    (fun i _hi => logGateOuterRamp_bounds width (G i))
    (fun i _hi hpos => logGateOuterRamp_eq_one hwidth hpos.le)
    (fun i _hi hfar => logGateOuterRamp_eq_zero hwidth hfar)

/-- Supported physical strips retain the complete actual labelled prime
carrier, one failed physical wall, AND every softened physical margin. -/
def physicalSupportedStrip (width b : ℝ) (N : ℕ)
    (T : ℝ) (i : Fin 4) : Finset (Fin 2 → Fin (N + 1)) :=
  (labelledPrimeTuples 2 N).filter (fun t =>
    (-width < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
      ∀ j : Fin 4, -width < physicalPairMargins b N T t j)

/-- Literal membership API, with no geometric or analytic assumptions. -/
@[simp] theorem mem_physicalSupportedStrip
    (width b : ℝ) (N : ℕ) (T : ℝ) (i : Fin 4)
    (t : Fin 2 → Fin (N + 1)) :
    t ∈ physicalSupportedStrip width b N T i ↔
      t ∈ labelledPrimeTuples 2 N ∧
        (-width < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
          (∀ j : Fin 4, -width < physicalPairMargins b N T t j) := by
  simp only [physicalSupportedStrip, Finset.mem_filter]

/-- Parameter-order alias for the longer arithmetic-strip API. -/
abbrev physicalPairSupportedArithmeticStrip (b : ℝ) (N : ℕ)
    (T delta : ℝ) (i : Fin 4) : Finset (Fin 2 → Fin (N + 1)) :=
  physicalSupportedStrip delta b N T i

/-- The refinement only removes tuples lacking another softened gate. -/
theorem physicalPairSupportedArithmeticStrip_subset_strip
    (b : ℝ) (N : ℕ) (T delta : ℝ) (i : Fin 4) :
    physicalSupportedStrip delta b N T i ⊆
      physicalPairArithmeticStrip b N T delta i := by
  intro t ht
  obtain ⟨htprime, hstrip, _hsoft⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨htprime, hstrip⟩

/-- All-strict physical gates imply the exact mixed-wall W. The reverse
implication is not asserted: three genuine source walls are closed. -/
theorem allStrictPhysicalMargins_indicator_le_W
    {b T : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N) :
    (if ∀ i : Fin 4, 0 < physicalPairMargins b N T t i then (1 : ℝ) else 0) ≤
      W b N T t := by
  rw [actual_W_eq_physical_mixedIndicator hN hT ht]
  by_cases hs : ∀ i : Fin 4, 0 < physicalPairMargins b N T t i
  · have hmixed :
        0 ≤ physicalPairMargins b N T t 0 ∧
        0 < physicalPairMargins b N T t 1 ∧
        0 ≤ physicalPairMargins b N T t 2 ∧
        0 ≤ physicalPairMargins b N T t 3 :=
      ⟨(hs 0).le, hs 1, (hs 2).le, (hs 3).le⟩
    simp only [if_pos hs, if_pos hmixed, le_refl]
  · rw [if_neg hs]
    split_ifs <;> norm_num

/-- Actual mixed-wall physical surplus is paid only on jointly supported
strips. The upper product margin is the physical logarithmic gap. -/
theorem physicalPairOuterRamp_sub_W_le_supported_arithmetic_strips
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    physicalPairOuterRamp b N T delta t - W b N T t ≤
      ∑ i : Fin 4, if
        (-delta < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
          (∀ j : Fin 4, -delta < physicalPairMargins b N T t j)
        then (1 : ℝ) else 0 := by
  have hg := logGateOuterRamp_sub_indicator_le_supported_strip_union
    (Finset.univ : Finset (Fin 4)) (physicalPairMargins b N T t) hdelta
  have hpoint :
      physicalPairOuterRamp b N T delta t -
        (if ∀ i : Fin 4, 0 < physicalPairMargins b N T t i then (1 : ℝ) else 0) ≤
      ∑ i : Fin 4, if
        (-delta < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
          (∀ j : Fin 4, -delta < physicalPairMargins b N T t j)
        then (1 : ℝ) else 0 := by
    convert hg using 1 <;>
      simp -failIfUnchanged only [physicalPairOuterRamp, positiveRescaledFourWallWeight,
        physicalPairMargins, Finset.mem_univ, true_implies]
    · congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact (ite_eq_ite _ _ _).mpr trivial
  exact (sub_le_sub_left (allStrictPhysicalMargins_indicator_le_W hN hT ht)
    (physicalPairOuterRamp b N T delta t)).trans hpoint

/-- Genuine tuple mass, exact W sum, and complete jointly supported strip
counts. This finite inequality alone asserts no boundary smallness. -/
theorem sum_physicalPairOuterRamp_le_source_card_add_supported_strip_cards
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) :
    (∑ t ∈ labelledPrimeTuples 2 N, physicalPairOuterRamp b N T delta t) ≤
      ((realHalfProductSource b N T).card : ℝ) +
        ∑ i : Fin 4, ((physicalSupportedStrip delta b N T i).card : ℝ) := by
  have hstrips :
      (∑ t ∈ labelledPrimeTuples 2 N, ∑ i : Fin 4, if
        (-delta < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
          (∀ j : Fin 4, -delta < physicalPairMargins b N T t j)
        then (1 : ℝ) else 0) =
      ∑ i : Fin 4, ((physicalSupportedStrip delta b N T i).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [physicalSupportedStrip, ← Finset.sum_filter]
    simp
  calc
    (∑ t ∈ labelledPrimeTuples 2 N, physicalPairOuterRamp b N T delta t) ≤
        ∑ t ∈ labelledPrimeTuples 2 N, (W b N T t +
          ∑ i : Fin 4, if
            (-delta < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
              (∀ j : Fin 4, -delta < physicalPairMargins b N T t j)
            then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      have hp := physicalPairOuterRamp_sub_W_le_supported_arithmetic_strips
        (b := b) hN hT hdelta ht
      linarith only [hp]
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_actual_labelled_W_eq_source_card, hstrips]

/-- The genuine full product-fibre pushforward inherits exactly the same
supported strip price; products above N are included in the carrier. -/
theorem physical_productWeight_mass_le_source_card_add_supported_strip_cards
    {b T delta : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta) :
    finiteSourceMass (P4BLabelledOuterPushforward.productCarrier N)
      (P4BLabelledOuterPushforward.productWeight N (physicalPairOuterRamp b N T delta)) ≤
      ((realHalfProductSource b N T).card : ℝ) +
        ∑ i : Fin 4, ((physicalSupportedStrip delta b N T i).card : ℝ) := by
  rw [P4BLabelledOuterPushforward.finiteSourceMass_eq_labelled]
  exact sum_physicalPairOuterRamp_le_source_card_add_supported_strip_cards hN hT hdelta

/-- Arithmetic strip smallness remains a separate explicit input. -/
theorem physicalPairOuterRamp_surplus_paid_by_supported_strips
    {b T delta E : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hdelta : 0 < delta)
    (hpaid : (∑ i : Fin 4,
      ((physicalSupportedStrip delta b N T i).card : ℝ)) ≤ E) :
    (∑ t ∈ labelledPrimeTuples 2 N, physicalPairOuterRamp b N T delta t) ≤
      ((realHalfProductSource b N T).card : ℝ) + E := by
  exact (sum_physicalPairOuterRamp_le_source_card_add_supported_strip_cards
    hN hT hdelta).trans (add_le_add_right hpaid _)

end

end ImbalancedChen.P4B
