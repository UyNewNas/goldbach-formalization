import ImbalancedChen.P1OriginalVariableFourthEligibilityPartition
import ImbalancedChen.P1OriginalCoarseUpperResidualUniformity

/-!
Actual selected original variable-fourth source limits, without a fixed
eligible-row premise or a continuity premise on the producer maximum.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The genuine closed PLUS quotient supplier is uniform over ALL exponents in
a fixed bounded interval. Its proved parameter rectangle pays arithmetic
replacement even across jumps. Separately, the exact finite row-wall atoms
pay the prime-test limit. Every overlapping licensed row and the inherited
original rawQ3 seed participate in the same pointwise maximum.

The positive cutoff remains fixed. The variable-fourth small-prime tail,
unselected-source terms, cutoff removal and the full original policy limit
are OPEN; no such conclusion is an input here.
-/

namespace ImbalancedChen.P1OriginalVariableFourthBoundedSourceLimit
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1FourthFullCellIntegral P1FourthNearOneKernel
open P1OriginalCoarseContinuation P1OriginalFourthLimit P1OriginalFourthIntegral
open P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthCellTestLimit
open P1OriginalVariableFourthSourceLimit
open P1OriginalVariableFourthEligibilityPartition

/-- The existing compact legal quotient rectangle supplies one threshold
for EVERY physical exponent in the interval. No profile continuity enters. -/
theorem exists_tuplePlus_bounded_levels_threshold
    (a b lower upper : ℝ) (ha : 0 < a) (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
      ∀ lambda ∈ Icc lower upper,
        (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p (Fin.last 3) ≤ lambda →
        |fourthTuplePlusResidualP1 N cap lambda p -
          extendedProfile lambda (actualPrimeTupleLog N p)| < eta := by
  let T := HistoricalThirdCoarse.P1OriginalUpperResidual.residualWindow a b upper
  have hT : IsCompact T := HistoricalThirdCoarse.P1OriginalUpperResidual.residualWindow_isCompact a b upper
  have hparam : ∀ q ∈ T, 0 < q.2 ∧ q.2 ≤ q.1 :=
    HistoricalThirdCoarse.P1OriginalUpperResidual.residualWindow_legal a b upper ha
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_closed_quotient_compact_normalized_threshold T hT hparam eta heta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap p hp lambda hlambda hlegal
  have hN1 : 1 < N := by omega
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hx := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
  have hmem : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
      (p (Fin.last 3) : ℝ) lambda ∈ T := by
    apply HistoricalThirdCoarse.P1OriginalUpperResidual.quotientParameters_mem_window
      a b upper N p hpos lambda
    · exact fun i => (ha.trans_le (mem_logPrimeBox.mp hx i).1).le
    · exact (mem_logPrimeBox.mp hx (Fin.last 3)).1
    · exact (mem_logPrimeBox.mp hx (Fin.last 3)).2.le
    · linarith
    · exact hlambda.2
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hy : (0 : ℝ) < p (Fin.last 3) := by exact_mod_cast hpos (Fin.last 3)
  have hh := hbound N hN hEven _ _ lambda hP hy hmem cap
    ((hpi (Fin.last 3)).2.2.2.le.trans hcap)
  have hparams : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
      (p (Fin.last 3) : ℝ) lambda =
        (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p (Fin.last 3)) :=
    HistoricalThirdCoarse.P1OriginalUpperResidual.quotientParameters_eq_tuple N p hpos lambda
  have hu : 0 < actualPrimeTupleLog N p (Fin.last 3) :=
    ha.trans_le (mem_logPrimeBox.mp hx (Fin.last 3)).1
  have hs : 1 ≤ residual lambda (actualPrimeTupleLog N p) := by
    apply (le_div_iff₀ hu).mpr
    dsimp [residual]
    linarith
  have hprofile : extendedProfile lambda (actualPrimeTupleLog N p) =
      (2 * Real.exp (-Real.eulerMascheroniConstant) / actualPrimeTupleLog N p (Fin.last 3)) *
        closedUpper ((lambda - ∑ i, actualPrimeTupleLog N p i) /
          actualPrimeTupleLog N p (Fin.last 3)) := by
    rw [extendedProfile, maxOneNormalized, max_eq_right hs]
    dsimp [residual]
    ring
  rw [hprofile]
  simpa only [fourthTuplePlusResidualP1, hparams] using hh

/-- Arbitrary bounded moving PLUS profiles may jump on row faces. Their
arithmetic replacement error still tends to zero, by uniform compact
quotient control and the proved nonnegative prime mass bound. -/
theorem tendsto_bounded_movingBoxResidualSum_error
    (a b lower upper : ℝ) (ha : 0 < a) (hab : a < b)
    (R : Set Point) (profile : Point → ℝ)
    (hprofile : ∀ t ∈ R, profile t ∈ Icc lower upper)
    (hlegal : ∀ t ∈ R, (∑ i, t i) + t (Fin.last 3) ≤ profile t)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => movingBoxResidualSum N (cap N) a b R profile -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
        (R.indicator (fun t => extendedProfile (profile t) t)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin 4 → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f (N : ℕ) (p : Fin 4 → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then
      fourthTuplePlusResidualP1 N (cap N) (profile (actualPrimeTupleLog N p)) p else 0
  let g (N : ℕ) (p : Fin 4 → ℕ) :=
    R.indicator (fun t => extendedProfile (profile t) t) (actualPrimeTupleLog N p)
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin 4 => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N₀, _, hbound⟩ := exists_tuplePlus_bounded_levels_threshold a b lower upper ha eta heta
    have hNat : ∀ᶠ N in l, N₀ ≤ N := (eventually_ge_atTop N₀).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc p hp
    by_cases hR : actualPrimeTupleLog N p ∈ R
    · simpa only [f, g, if_pos hR, indicator_of_mem hR] using
        hbound N hN hE.2 (cap N) hc p hp (profile (actualPrimeTupleLog N p))
          (hprofile _ hR) (hlegal _ hR)
    · simpa only [f, g, if_neg hR, indicator_of_notMem hR, sub_self, abs_zero] using heta
  exact tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg

/-- The inherited seed and the universal tent ceiling give an actual
bounded interval for the complete producer maximum, for every point. -/
theorem producerProfile_mem_interval (e seed : ℝ) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (t : Point) :
    producerProfile4 e rows licensed seed t ∈ Icc seed (max seed (VariableEnvelope.cap - 2 * e)) := by
  refine ⟨producerProfile4_seed_le e rows licensed seed t, ?_⟩
  apply finiteMax_le rows _ _ seed (max seed (VariableEnvelope.cap - 2 * e)) (le_max_left _ _)
  intro r _hr _he
  have hrow : r.bufferedCandidate e t ≤ VariableEnvelope.cap - 2 * e := by
    rw [r.bufferedCandidate_eq]
    exact sub_le_sub_right (v_le_cap _) _
  exact hrow.trans (le_max_right _ _)

/-- The original admitted positive-cell source equals the difference of
the literal old residual and the actual all-row moving residual, with no
winning-row or fixed-eligibility hypothesis. -/
theorem positiveCellSource_eq_actual_moving_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    positiveCellSource e chi m omega a j rows licensed N cap =
      fourthBoxPlusResidualSumP1 N cap a (19 / 96) (oldExponent e m j) (sourceRegion e m omega j) -
        movingBoxResidualSum N cap a (19 / 96) (sourceRegion e m omega j)
          (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j)) := by
  unfold positiveCellSource
  rw [positive_frontier_weighted_sum e chi m omega a J4 N cap hN hcap j hj]
  unfold fourthBoxPlusResidualSumP1 movingBoxResidualSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hs : actualPrimeTupleLog N p ∈ sourceRegion e m omega j
  · have ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j := by
      have hcell := hs.1
      rwa [HistoricalThirdCoarse.P1OriginalFourth.jointCell_same_mesh] at hcell
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    simp only [if_pos hs]
    rw [literalResidual_eq_variableProfile_on_selected_cell e chi m omega J4 j hj N cap hN p hpos ht]
    ring
  · simp only [if_neg hs, mul_zero, sub_self]

/-- The arithmetic error for the true original source vanishes even when
the selected maximum jumps at closed producer-box faces. -/
theorem tendsto_positiveCellSource_sub_actual_test
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellSource e chi m omega a j rows licensed N (cap N) -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((sourceRegion e m omega j).indicator (fun t => extendedProfile (oldExponent e m j) t -
          extendedProfile (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let R := sourceRegion e m omega j
  let seed := oldExponent e m j
  let profile := producerProfile4 (e : ℝ) rows licensed seed
  have hlegal : ∀ t ∈ R, (∑ i, t i) + t (Fin.last 3) ≤ profile t := by
    intro t ht
    have hold := HistoricalThirdCoarse.P1OriginalFourth.jointRegion_strict_plus
      (e : ℝ) omega m (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j) t ht.2
    rw [← oldExponent_eq_actual] at hold
    exact hold.le.trans (producerProfile4_seed_le (e : ℝ) rows licensed seed t)
  have hbounded : ∀ t ∈ R, profile t ∈ Icc seed (max seed (VariableEnvelope.cap - 2 * (e : ℝ))) :=
    fun t _ => producerProfile_mem_interval (e : ℝ) seed rows licensed t
  have hold := tendsto_original_plus_residual_error e m omega a ha haRho j seed le_rfl cap hcap
  have hnew := tendsto_bounded_movingBoxResidualSum_error a (19 / 96) seed
    (max seed (VariableEnvelope.cap - 2 * (e : ℝ))) ha haRho R profile hbounded hlegal cap hcap
  have hlim := hold.sub hnew
  rw [sub_zero] at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  rw [positiveCellSource_eq_actual_moving_difference e chi m omega a J4 j hj N (cap N) hN hc rows licensed]
  have htest : actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceRegion e m omega j).indicator (fun t => extendedProfile seed t -
        extendedProfile (profile t) t)) =
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        (R.indicator (extendedProfile seed)) -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        (R.indicator (fun t => extendedProfile (profile t) t)) := by
    unfold actualPrimeBoxTestSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hs : actualPrimeTupleLog N p ∈ R
    · simp only [R] at hs
      simp only [indicator_of_mem hs]
      ring
    · simp only [R] at hs
      simp only [indicator_of_not_mem hs, mul_zero, sub_self]
  rw [htest]
  ring

/-- Finite true integrals over the exact row-wall refinement. -/
def refinedCellIntegral (e : ℚ) (m : ℕ) (omega a : ℝ) (j : FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) : ℝ :=
  ∑ s : Pattern rows, ∫ t in truncatedCell e m omega a j ∩ wallAtom rows s,
    fixedCellTest (e : ℝ) rows (eligibleRows rows licensed s) (oldExponent e m j) t * ∏ i, 1 / t i

/-- Actual positive selected-cell convergence: no hfixed, no winning row,
no continuous-on-cube assumption on the literal producer maximum. -/
theorem tendsto_positiveCellSource_refinedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellSource e chi m omega a j rows licensed N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (refinedCellIntegral e m omega a j rows licensed)) := by
  have herror := tendsto_positiveCellSource_sub_actual_test e chi m omega a ha haRho
    J4 j hj rows licensed cap hcap
  have htest := (tendsto_original_variable_cell_test_refinedIntegral e chi m omega a ha haRho
    J4 j hj rows licensed).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  simpa only [sub_add_cancel, zero_add, refinedCellIntegral] using herror.add htest

/-- Every original selected source cell is treated at its actual inherited
rawQ3 seed, with the complete pointwise all-eligible-row fourth profile. -/
theorem tendsto_selected_positive_source_refinedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => ∑ j ∈ selectedFourthCells e chi m omega J4,
      positiveCellSource e chi m omega a j rows licensed N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∑ j ∈ selectedFourthCells e chi m omega J4,
        refinedCellIntegral e m omega a j rows licensed)) := by
  exact tendsto_finsetSum (selectedFourthCells e chi m omega J4) (fun j hj =>
    tendsto_positiveCellSource_refinedIntegral e chi m omega a ha haRho J4 j hj rows licensed cap hcap)

end
end ImbalancedChen.P1OriginalVariableFourthBoundedSourceLimit
