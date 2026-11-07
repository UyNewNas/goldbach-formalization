import ImbalancedChen.P1OriginalVariableFourthProfileRegularity
import ImbalancedChen.P1OriginalCoarseFourthCellLimit
import ImbalancedChen.P1OriginalCoarseFourthArithmeticWall

/-!
Source-only positive-cell prime-box limit for the original variable fourth
profile.  The fixed-row maximum below is an extension of the actual producer
profile from ONE cell, not a replacement for the pointwise policy.  The
carrier is the original coarse Q3 sourceRegion: its firstStop, current raw
Gamma third cube, strict order/cube gates, and rough activation are retained
by P1OriginalFourthLimit.tendsto_test_original_sourceRegion.
-/

namespace ImbalancedChen.P1OriginalVariableFourthCellTestLimit

noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open P1FourthNearOneKernel P1FourthFullCellIntegral
open P1OriginalCoarseContinuation P1OriginalFourthLimit P1OriginalFourthIntegral
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthProfileRegularity
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseFourthArithmeticWall

/-- The finite eligible-row maximum extends the actual variable M_I(t)-2e
profile continuously away from this cell.  No row is discarded when its
candidate is below the inherited raw Q3 seed. -/
def fixedCellExponent (e : ℝ) (rows : Finset ProducerRow)
    (E : Finset ProducerRow) (seed : ℝ) (t : Point) : ℝ :=
  fixedMax seed (rows.filter (fun r => r ∈ E))
    (fun r => r.bufferedCandidate e) t

def fixedCellTest (e : ℝ) (rows : Finset ProducerRow)
    (E : Finset ProducerRow) (seed : ℝ) (t : Point) : ℝ :=
  extendedProfile seed t - extendedProfile (fixedCellExponent e rows E seed t) t

theorem continuous_fixedCellExponent (e : ℝ) (rows : Finset ProducerRow)
    (E : Finset ProducerRow) (seed : ℝ) :
    Continuous (fixedCellExponent e rows E seed) := by
  exact continuous_fixedMax seed _ _ (fun r _ =>
    continuous_bufferedCandidate r e)

/-- The max-one extension is used only to make a continuous test on the
ambient positive cube.  On the original admitted cell its value is the
literal fourth PLUS source coefficient. -/
theorem continuousOn_variableExtended (e : ℝ) (rows : Finset ProducerRow)
    (E : Finset ProducerRow) (seed a b : ℝ) (ha : 0 < a) :
    ContinuousOn (fun t : Point =>
      extendedProfile (fixedCellExponent e rows E seed t) t)
        (univ.pi (fun _ : Fin 4 => Icc a b)) := by
  let C : Set Point := univ.pi (fun _ : Fin 4 => Icc a b)
  have hsum : Continuous (fun t : Point => ∑ i, t i) := by fun_prop
  have hlast : Continuous (fun t : Point => t (Fin.last 3)) := by fun_prop
  have hnum : Continuous (fun t : Point =>
      fixedCellExponent e rows E seed t - ∑ i, t i) :=
    (continuous_fixedCellExponent e rows E seed).sub hsum
  have hne : ∀ t ∈ C, t (Fin.last 3) ≠ 0 := by
    intro t ht
    exact (ha.trans_le (ht _ (mem_univ _)).1).ne'
  have hres : ContinuousOn (fun t : Point =>
      (fixedCellExponent e rows E seed t - ∑ i, t i) / t (Fin.last 3)) C :=
    hnum.continuousOn.div hlast.continuousOn hne
  have hclosed : ContinuousOn (fun t : Point =>
      closedUpper (max 1 ((fixedCellExponent e rows E seed t - ∑ i, t i) /
        t (Fin.last 3)))) C :=
    continuousOn_closedUpper.comp (continuousOn_const.sup hres)
      (fun _ _ => le_max_left _ _)
  have hmain : ContinuousOn (fun t : Point =>
      (2 * Real.exp (-Real.eulerMascheroniConstant)) *
        (closedUpper (max 1 ((fixedCellExponent e rows E seed t - ∑ i, t i) /
          t (Fin.last 3))) / t (Fin.last 3))) C :=
    continuousOn_const.mul (hclosed.div hlast.continuousOn hne)
  simpa only [extendedProfile, maxOneNormalized, residual, C] using hmain

theorem continuousOn_fixedCellTest (e : ℝ) (rows : Finset ProducerRow)
    (E : Finset ProducerRow) (seed a b : ℝ) (ha : 0 < a) :
    ContinuousOn (fixedCellTest e rows E seed)
      (univ.pi (fun _ : Fin 4 => Icc a b)) := by
  exact (continuousOn_extendedProfile ha).sub
    (continuousOn_variableExtended e rows E seed a b ha)

/-- Fixed eligibility is asserted on this original mesh source cell alone.
In particular, nothing here asserts continuity across producer box walls. -/
theorem producerProfile4_eq_fixedCellExponent_on_source
    (e : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (E : Finset ProducerRow) (seed : ℝ)
    (C : Set Point)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ C,
      producerEligible licensed r t ↔ r ∈ E)
    {t : Point} (ht : t ∈ C) :
    producerProfile4 e rows licensed seed t =
      fixedCellExponent e rows E seed t := by
  exact profile4_eq_fixed_on_cell seed rows (producerEligible licensed)
    (fun r => r.bufferedCandidate e) C E hfixed ht

/-- The actual selected label supplies the original firstStop/raw-Q3
geometric source, while E records only the producer rows eligible THERE. -/
theorem tendsto_variableFourth_fixed_cell_test
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ sourceRegion e m omega j,
      producerEligible licensed r t ↔ r ∈ E) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceRegion e m omega j).indicator
          (fun t => extendedProfile (oldExponent e m j) t -
            extendedProfile
              (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t)))
      atTop
      (𝓝 (∫ t in truncatedCell e m omega a j,
        (fourthPlusProfileP1 (oldExponent e m j) t -
          fourthPlusProfileP1
            (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t) *
          ∏ i, 1 / t i)) := by
  let seed := oldExponent e m j
  let f := fixedCellTest (e : ℝ) rows E seed
  have hwhole := selected_whole_active e chi m omega J4 j hj
  have htransport := tendsto_test_original_sourceRegion e m omega a ha haRho j
    hwhole f (continuousOn_fixedCellTest (e : ℝ) rows E seed a (19 / 96) ha)
  have hsource : ∀ t ∈ sourceRegion e m omega j,
      producerProfile4 (e : ℝ) rows licensed seed t =
        fixedCellExponent (e : ℝ) rows E seed t := by
    intro t ht
    exact producerProfile4_eq_fixedCellExponent_on_source
      (e : ℝ) rows licensed E seed _ hfixed ht
  have hsum : (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceRegion e m omega j).indicator
        (fun t => extendedProfile seed t -
          extendedProfile (producerProfile4 (e : ℝ) rows licensed seed t) t))) =
      (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceRegion e m omega j).indicator f)) := by
    funext N
    unfold actualPrimeBoxTestSum
    apply Finset.sum_congr rfl
    intro p _
    by_cases ht : actualPrimeTupleLog N p ∈ sourceRegion e m omega j
    · simp only [Set.indicator_of_mem ht, hsource _ ht, f, fixedCellTest]
    · simp only [Set.indicator_of_not_mem ht]
  have hraw : (∫ t in truncatedCell e m omega a j,
      f t * ∏ i, 1 / t i) =
      ∫ t in truncatedCell e m omega a j,
        (fourthPlusProfileP1 seed t -
          fourthPlusProfileP1
            (producerProfile4 (e : ℝ) rows licensed seed t) t) *
          ∏ i, 1 / t i := by
    apply setIntegral_congr_fun (truncatedCell_measurable e m omega a j)
    intro t ht
    have hs : t ∈ sourceRegion e m omega j :=
      (truncatedCell_eq_inter_sourceRegion e m omega a j ▸ ht).2
    have hle : seed ≤ producerProfile4 (e : ℝ) rows licensed seed t :=
      producerProfile4_seed_le (e : ℝ) rows licensed seed t
    simp only [f, fixedCellTest, ← hsource t hs]
    rw [← rawProfile_eq_extended_on_truncated e m omega ha j le_rfl ht,
      ← rawProfile_eq_extended_on_truncated e m omega ha j hle ht]
  rw [hraw] at htransport
  rw [← hsum] at htransport
  simpa only [seed] using htransport

/-- The finite labelled sum has the actual rank-four signed tree coefficient,
the original selected source gate, and the literal Suzuki PLUS factor at
the tuple-dependent fourth exponent. -/
def labelledRawCellSum (e : ℚ) (m : ℕ) (omega a : ℝ)
    (j : FourthCell m) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (N : ℕ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ)),
    signedTupleWeight p *
      (if actualPrimeTupleLog N p ∈ sourceRegion e m omega j then
        fourthPlusProfileP1 (oldExponent e m j) (actualPrimeTupleLog N p) -
          fourthPlusProfileP1
            (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j)
              (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p)
       else 0)

theorem labelledRawCellSum_eq_test (e : ℚ) (m N : ℕ) (omega a : ℝ)
    (ha : 0 < a) (hN : 1 < N) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    labelledRawCellSum e m omega a j rows licensed N =
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceRegion e m omega j).indicator
          (fun t => extendedProfile (oldExponent e m j) t -
            extendedProfile
              (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t)) := by
  unfold labelledRawCellSum actualPrimeBoxTestSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [signedTupleWeight_eq]
  by_cases hs : actualPrimeTupleLog N p ∈ sourceRegion e m omega j
  · have hbox := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
    have ht : actualPrimeTupleLog N p ∈ truncatedCell e m omega a j := by
      rw [truncatedCell_eq_inter_sourceRegion]
      exact ⟨hbox, hs⟩
    have hle : oldExponent e m j ≤
        producerProfile4 (e : ℝ) rows licensed (oldExponent e m j)
          (actualPrimeTupleLog N p) :=
      producerProfile4_seed_le (e : ℝ) rows licensed (oldExponent e m j) _
    simp only [if_pos hs, Set.indicator_of_mem hs]
    rw [rawProfile_eq_extended_on_truncated e m omega ha j le_rfl ht,
      rawProfile_eq_extended_on_truncated e m omega ha j hle ht]
  · simp only [if_neg hs, Set.indicator_of_not_mem hs, mul_zero]

theorem tendsto_labelledRawCellSum
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ sourceRegion e m omega j,
      producerEligible licensed r t ↔ r ∈ E) :
    Tendsto (fun N : ℕ => labelledRawCellSum e m omega a j rows licensed N)
      atTop
      (𝓝 (∫ t in truncatedCell e m omega a j,
        (fourthPlusProfileP1 (oldExponent e m j) t -
          fourthPlusProfileP1
            (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t) *
          ∏ i, 1 / t i)) := by
  have htest := tendsto_variableFourth_fixed_cell_test e chi m omega a ha haRho
    J4 j hj rows licensed E hfixed
  have heq : (fun N : ℕ => labelledRawCellSum e m omega a j rows licensed N) =ᶠ[atTop]
      (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceRegion e m omega j).indicator
          (fun t => extendedProfile (oldExponent e m j) t -
            extendedProfile
              (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t))) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
    exact labelledRawCellSum_eq_test e m N omega a ha hN j rows licensed
  exact htest.congr' heq

end
end ImbalancedChen.P1OriginalVariableFourthCellTestLimit
