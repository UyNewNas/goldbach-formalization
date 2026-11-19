import ImbalancedChen.Part5OriginalH430D8TwoAffineAdditive

/-!
P5.6 / h34. Original singleton-source genuine rational Darboux chains.
Each ordered interval is paid once by the inherited proved
rational_cell_integral_lower. There is no assumed integral lower bound,
additional analytic input or replacement for the original /5 factor.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430EightCellSingletonChain
noncomputable section
open Set MeasureTheory
open scoped Interval
open P2EnhancedSeedSingletonPrimitive
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

def OrderedFrom (a : ℚ) : List ℚ → Prop
  | [] => a ≤ 5/11
  | b :: rest => a ≤ b ∧ OrderedFrom b rest

def endpoint (a : ℚ) : List ℚ → ℚ
  | [] => a
  | b :: rest => endpoint b rest

def cellMass (a b : ℚ) : ℚ := (b-a) * cellLower 2 a b

def chainMass (a : ℚ) : List ℚ → ℚ
  | [] => 0
  | b :: rest => cellMass a b + chainMass b rest

private theorem endpoint_bounds (a : ℚ) (xs : List ℚ)
    (h : OrderedFrom a xs) :
    a ≤ endpoint a xs ∧ endpoint a xs ≤ (5/11 : ℚ) := by
  induction xs generalizing a with
  | nil =>
      change a ≤ (5/11 : ℚ) at h
      simp only [endpoint]
      exact ⟨le_rfl, h⟩
  | cons b rest ih =>
      change a ≤ b ∧ OrderedFrom b rest at h
      obtain ⟨hab, hrest⟩ := h
      obtain ⟨hbEnd, hEndTop⟩ := ih b hrest
      change a ≤ endpoint b rest ∧ endpoint b rest ≤ (5/11 : ℚ)
      exact ⟨hab.trans hbEnd, hEndTop⟩

/-- Genuine interval-integral lower bound for an ordered chain.
The only induction input is geometry, not a numerical target. -/
theorem chain_integral_lower (a : ℚ) (xs : List ℚ)
    (ha : (67/227 : ℚ) ≤ a)
    (hOrder : OrderedFrom a xs) :
    (chainMass a xs : ℝ) ≤
      ∫ u in (a : ℝ)..(endpoint a xs : ℝ), singletonLogKernel u := by
  induction xs generalizing a with
  | nil =>
      simp only [chainMass, endpoint, intervalIntegral.integral_same]
      exact le_refl _
  | cons b rest ih =>
      change a ≤ b ∧ OrderedFrom b rest at hOrder
      obtain ⟨hab, hRest⟩ := hOrder
      obtain ⟨hbEnd, hEndCap⟩ := endpoint_bounds b rest hRest
      have hbCap : b ≤ (5/11 : ℚ) := hbEnd.trans hEndCap
      have hCell := rational_cell_integral_lower 2 a b ha hab hbCap
      change (cellMass a b : ℝ) ≤
        ∫ u in (a : ℝ)..(b : ℝ), singletonLogKernel u at hCell
      have hTail := ih b (ha.trans hab) hRest
      have haR : (0 : ℝ) < (a : ℝ) := by
        have h : (67/227 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        linarith
      have hbR : (0 : ℝ) < (b : ℝ) := by
        have h : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        exact haR.trans_le h
      have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have hbEndR : (b : ℝ) ≤ (endpoint b rest : ℝ) := by
        exact_mod_cast hbEnd
      have hbCapR : (b : ℝ) ≤ (5/11 : ℝ) := by exact_mod_cast hbCap
      have hEndCapR : (endpoint b rest : ℝ) ≤ (5/11 : ℝ) := by
        exact_mod_cast hEndCap
      have hI₁ : IntervalIntegrable singletonLogKernel volume
          (a : ℝ) (b : ℝ) :=
        (continuousOn_singletonLogKernel haR hbCapR).intervalIntegrable_of_Icc habR
      have hI₂ : IntervalIntegrable singletonLogKernel volume
          (b : ℝ) (endpoint b rest : ℝ) :=
        (continuousOn_singletonLogKernel hbR hEndCapR).intervalIntegrable_of_Icc hbEndR
      have hJoin := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
      have hCast : (chainMass a (b :: rest) : ℝ) =
          (cellMass a b : ℝ) + (chainMass b rest : ℝ) := by
        simp only [chainMass, Rat.cast_add]
      change (chainMass a (b :: rest) : ℝ) ≤
        ∫ u in (a : ℝ)..(endpoint b rest : ℝ), singletonLogKernel u
      linarith only [hCell, hTail, hJoin, hCast]

/-- Reconnect the final endpoint with the exact ORIGINAL singleton cap. -/
theorem chain_to_singleton (j : Fin 3) (xs : List ℚ)
    (hOrder : OrderedFrom (67/227) xs)
    (hCap : (endpoint (67/227) xs : ℝ) = cap j) :
    (chainMass (67/227) xs : ℝ) ≤ singletonCoefficient j := by
  have h := chain_integral_lower (67/227) xs (le_refl _) hOrder
  have hExact :
      (∫ u in ((67/227 : ℚ) : ℝ)..
        (endpoint (67/227) xs : ℝ), singletonLogKernel u) =
          singletonCoefficient j := by
    unfold singletonCoefficient
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (literal_bounds j).2.2.1.le]
    simp only [uStar, hCap, Rat.cast_div, Rat.cast_ofNat]
  exact h.trans (le_of_eq hExact)

def knots0 : List ℚ := [5/16, 1/3, 7/20, 3/8, 2/5, 5/12, 7/16, 5/11]
def knots1 : List ℚ := [3/10, 31/100, 63/200, 8/25, 13/40, 33/100, 17/50, 10/29]
def knots2 : List ℚ := [31/100, 13/40, 17/50, 7/20, 3/8, 39/100, 2/5, 25/61]

theorem original_singleton_zero_ge_106_per_1000 :
    (106/1000 : ℝ) ≤ singletonCoefficient (0 : Fin 3) := by
  have hOrder : OrderedFrom (67/227) knots0 := by
    norm_num [OrderedFrom, knots0]
  have hCap : (endpoint (67/227) knots0 : ℝ) = cap (0 : Fin 3) := by
    norm_num [endpoint, knots0, cap]
  have hRat : (106/1000 : ℝ) ≤ (chainMass (67/227) knots0 : ℝ) := by
    norm_num [chainMass, knots0, cellMass, cellLower, rationalArgument,
      logSeriesLower, logParameter, Finset.sum_range_succ]
  exact hRat.trans (chain_to_singleton 0 knots0 hOrder hCap)

theorem original_singleton_one_ge_10_per_1000 :
    (10/1000 : ℝ) ≤ singletonCoefficient (1 : Fin 3) := by
  have hOrder : OrderedFrom (67/227) knots1 := by
    norm_num [OrderedFrom, knots1]
  have hCap : (endpoint (67/227) knots1 : ℝ) = cap (1 : Fin 3) := by
    norm_num [endpoint, knots1, cap]
  have hRat : (10/1000 : ℝ) ≤ (chainMass (67/227) knots1 : ℝ) := by
    norm_num [chainMass, knots1, cellMass, cellLower, rationalArgument,
      logSeriesLower, logParameter, Finset.sum_range_succ]
  exact hRat.trans (chain_to_singleton 1 knots1 hOrder hCap)

theorem original_singleton_two_ge_53_per_1000 :
    (53/1000 : ℝ) ≤ singletonCoefficient (2 : Fin 3) := by
  have hOrder : OrderedFrom (67/227) knots2 := by
    norm_num [OrderedFrom, knots2]
  have hCap : (endpoint (67/227) knots2 : ℝ) = cap (2 : Fin 3) := by
    norm_num [endpoint, knots2, cap]
  have hRat : (53/1000 : ℝ) ≤ (chainMass (67/227) knots2 : ℝ) := by
    norm_num [chainMass, knots2, cellMass, cellLower, rationalArgument,
      logSeriesLower, logParameter, Finset.sum_range_succ]
  exact hRat.trans (chain_to_singleton 2 knots2 hOrder hCap)

/-- Seven genuine original sources, with the literal /5 only once. -/
theorem actual_lambda_ge_544_over_5000 :
    (544/5000 : ℝ) ≤ lambda := by
  have h0 := original_singleton_zero_ge_106_per_1000
  have h1 := original_singleton_one_ge_10_per_1000
  have h2 := original_singleton_two_ge_53_per_1000
  have h5 := Part5OriginalH430FourCellD5Darboux.genuine_four_cell_D5_ge_13_over_100
  have h6 := Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 := Part5OriginalH430D7EightCellRationalLower.genuine_d7_eight_cell_ge_27_per_1000
  have h8 := Part5OriginalH430D8TwoAffineAdditive.genuine_d8_two_affine_ge_108_per_1000
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430EightCellSingletonChain
