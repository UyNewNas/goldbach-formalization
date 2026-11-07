import ImbalancedChen.P1OriginalVariableFourthSourceCoefficient

/-!
Actual variable-fourth residual limits on selected original source cells.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The new step is the genuine arithmetic residual approximation with a moving
continuous exponent.  Its compact parameter image is passed to the existing
closed quotient supplier.  The original finite firstStop/rawQ3 source is
then identified with that arithmetic sum, before the existing cell-test
limit is used.  No residual-error convergence is an assumed premise.

Eligibility must be fixed on each supplied original mesh cell; this is a
geometric partition obligation.  The positive cutoff remains explicit.
The omitted small-prime and unselected-source terms and any global limit
remain OPEN.  Empty-history policy coefficients are not removed.
-/

namespace ImbalancedChen.P1OriginalVariableFourthSourceLimit
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P1FourthFullCellIntegral P1FourthNearOneKernel
open P1OriginalCoarseContinuation P1OriginalFourthLimit P1OriginalFourthIntegral
open P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthProfileRegularity
open P1OriginalVariableFourthCellTestLimit
open P2OriginalFourthCapProducerInterface

/-- The arithmetic residual is evaluated at the tuple's actual moving cap. -/
def movingBoxResidualSum (N cap : ℕ) (a b : ℝ)
    (R : Set Point) (lambda : Point → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ R then
        fourthTuplePlusResidualP1 N cap (lambda (actualPrimeTupleLog N p)) p else 0)

/-- A continuous moving exponent has one genuine quotient-density threshold
on its closed legal compact image.  No discretization of its values occurs. -/
theorem exists_moving_tuplePlus_uniform_threshold
    (a b : ℝ) (ha : 0 < a) (lambda : Point → ℝ) (hlambda : Continuous lambda)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
        (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p (Fin.last 3) ≤
          lambda (actualPrimeTupleLog N p) →
        |fourthTuplePlusResidualP1 N cap (lambda (actualPrimeTupleLog N p)) p -
          extendedProfile (lambda (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p)| < eta := by
  let C : Set Point := univ.pi (fun _ => Icc a b) ∩
    {t | (∑ i, t i) + t (Fin.last 3) ≤ lambda t}
  let F : Point → ℝ × ℝ := fun t => (lambda t - ∑ i, t i, t (Fin.last 3))
  let T : Set (ℝ × ℝ) := F '' C
  have hform : Continuous (fun t : Point => (∑ i, t i) + t (Fin.last 3)) := by fun_prop
  have hC : IsCompact C := (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
    (isClosed_le hform hlambda)
  have hsum : Continuous (fun t : Point => ∑ i, t i) := by fun_prop
  have hlast : Continuous (fun t : Point => t (Fin.last 3)) := by fun_prop
  have hF : Continuous F := (hlambda.sub hsum).prodMk hlast
  have hT : IsCompact T := hC.image hF
  have hparam : ∀ q ∈ T, 0 < q.2 ∧ q.2 ≤ q.1 := by
    rintro q ⟨t, ht, rfl⟩
    have hh := ht.2
    change (∑ i, t i) + t (Fin.last 3) ≤ lambda t at hh
    exact ⟨ha.trans_le (ht.1 _ (mem_univ _)).1, by dsimp [F]; linarith⟩
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_closed_quotient_compact_normalized_threshold
      T hT hparam eta heta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap p hp hlegal
  have hN1 : 1 < N := by omega
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hx := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
  have ht : actualPrimeTupleLog N p ∈ C :=
    ⟨fun i _ => ⟨(mem_logPrimeBox.mp hx i).1, (mem_logPrimeBox.mp hx i).2.le⟩, hlegal⟩
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hy : (0 : ℝ) < p (Fin.last 3) := by exact_mod_cast hpos (Fin.last 3)
  have hparams : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
      (p (Fin.last 3) : ℝ) (lambda (actualPrimeTupleLog N p)) =
        F (actualPrimeTupleLog N p) := by
    change (lambda (actualPrimeTupleLog N p) - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ),
        actualPrimeTupleLog N p (Fin.last 3)) = _
    rw [actualPrimeTupleLog_sum_prod p hpos]
  have hh := hbound N hN hEven _ _ (lambda (actualPrimeTupleLog N p)) hP hy
    (by rw [hparams]; exact mem_image_of_mem F ht) cap
    ((hpi (Fin.last 3)).2.2.2.le.trans hcap)
  have hu : 0 < actualPrimeTupleLog N p (Fin.last 3) :=
    ha.trans_le (ht.1 _ (mem_univ _)).1
  have hs : 1 ≤ residual (lambda (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p) := by
    apply (le_div_iff₀ hu).mpr
    dsimp [residual]
    linarith
  have hprofile : extendedProfile (lambda (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p) =
      (2 * Real.exp (-Real.eulerMascheroniConstant) / actualPrimeTupleLog N p (Fin.last 3)) *
        closedUpper ((lambda (actualPrimeTupleLog N p) - ∑ i, actualPrimeTupleLog N p i) /
          actualPrimeTupleLog N p (Fin.last 3)) := by
    rw [extendedProfile, maxOneNormalized, max_eq_right hs]
    dsimp [residual]
    ring
  rw [hprofile]
  simpa only [fourthTuplePlusResidualP1, hparams, F] using hh

/-- Bounded reciprocal-prime mass transports the moving arithmetic error.
The region may be discontinuous: only its closed residual legality matters. -/
theorem tendsto_movingBoxResidualSum_error
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (R : Set Point) (lambda : Point → ℝ) (hlambda : Continuous lambda)
    (hlegal : ∀ t ∈ R, (∑ i, t i) + t (Fin.last 3) ≤ lambda t)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => movingBoxResidualSum N (cap N) a b R lambda -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
        (R.indicator (fun t => extendedProfile (lambda t) t)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin 4 → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f (N : ℕ) (p : Fin 4 → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then
      fourthTuplePlusResidualP1 N (cap N) (lambda (actualPrimeTupleLog N p)) p else 0
  let g (N : ℕ) (p : Fin 4 → ℕ) :=
    R.indicator (fun t => extendedProfile (lambda t) t) (actualPrimeTupleLog N p)
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin 4 => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N₀, _, hbound⟩ := exists_moving_tuplePlus_uniform_threshold a b ha lambda hlambda eta heta
    have hNat : ∀ᶠ N in l, N₀ ≤ N := (eventually_ge_atTop N₀).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc p hp
    by_cases hR : actualPrimeTupleLog N p ∈ R
    · simpa only [f, g, if_pos hR, indicator_of_mem hR] using
        hbound N hN hE.2 (cap N) hc p hp (hlegal _ hR)
    · simpa only [f, g, if_neg hR, indicator_of_notMem hR, sub_self, abs_zero] using heta
  exact tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg

/-- Exact original rawQ3 exponent on a selected whole-active fourth cell. -/
theorem seedExponent_eq_old_on_selected_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    seedExponent (e : ℝ) chi m omega (N : ℝ) (tupleHistory p) = oldExponent e m j := by
  have hlic := (mem_selectedFourthCells e chi m omega J4 j).mp hj
  have hexp := effectiveExponent3Q_ancestor_on_wholeActive_cell e chi m omega (N : ℝ)
    (tupleHistory p) (by exact_mod_cast hN) (by simp [tupleHistory])
    (tupleHistory_pos p hp) j hlic.2.1 hlic.2.2 (by simpa only [tupleHistory_log] using ht)
  rw [seedExponent, ← cast_effectiveExponent3Q, hexp]
  rfl

/-- All eligible producer rows participate, including overlaps and losing
candidates; no winner is selected to identify the literal finite summand. -/
theorem literalResidual_eq_variableProfile_on_selected_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p =
      fourthTuplePlusResidualP1 N cap (oldExponent e m j) p -
        fourthTuplePlusResidualP1 N cap
          (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) (actualPrimeTupleLog N p)) p := by
  have hs := seedExponent_eq_old_on_selected_cell e chi m omega J4 j hj N hN p hp ht
  have hold := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
    (e : ℝ) chi m omega (N : ℝ) (tupleHistory p)
  change rawLevel (e : ℝ) chi m omega (N : ℝ) (rosserAncestor 3 (tupleHistory p)) = _ at hold
  rw [hs] at hold
  have hnew : producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed (tupleHistory p) =
      (N : ℝ) ^ producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) (actualPrimeTupleLog N p) := by
    simp only [producerLevel4, level4, exponent4, show (tupleHistory p).length = 4 by simp [tupleHistory],
      if_pos, hs, tupleHistory_log, producerProfile4]
  unfold literalTupleResidualDifference fourthTuplePlusResidualP1
  rw [hold, hnew]
  ring

/-- The literal positive selected-cell contribution of the original
firstStop/rawQ3-to-variable-Q4 policy difference. -/
def positiveCellSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) : ℝ :=
  ∑ p ∈ (firstExitAdmittedTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
        (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
          (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p else 0)

/-- Finite original-frontier dictionary to the moving arithmetic residual,
with fixed eligibility asserted only on this source region. -/
theorem positiveCellSource_eq_moving_residual_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ sourceRegion e m omega j,
      producerEligible licensed r t ↔ r ∈ E) :
    positiveCellSource e chi m omega a j rows licensed N cap =
      fourthBoxPlusResidualSumP1 N cap a (19 / 96) (oldExponent e m j) (sourceRegion e m omega j) -
        movingBoxResidualSum N cap a (19 / 96) (sourceRegion e m omega j)
          (fixedCellExponent (e : ℝ) rows E (oldExponent e m j)) := by
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
    have hprofile := producerProfile4_eq_fixedCellExponent_on_source
      (e : ℝ) rows licensed E (oldExponent e m j) _ hfixed hs
    simp only [if_pos hs]
    rw [literalResidual_eq_variableProfile_on_selected_cell e chi m omega J4 j hj N cap hN p hpos ht,
      hprofile]
    ring
  · simp only [if_neg hs, mul_zero, sub_self]

/-- The missing arithmetic step: the variable finite Rosser coefficient
minus its existing continuous test tends to zero on the true source. -/
theorem tendsto_positiveCellSource_sub_labelledRawCellSum
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ sourceRegion e m omega j,
      producerEligible licensed r t ↔ r ∈ E)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellSource e chi m omega a j rows licensed N (cap N) -
      labelledRawCellSum e m omega a j rows licensed N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let R := sourceRegion e m omega j
  let seed := oldExponent e m j
  let lambda := fixedCellExponent (e : ℝ) rows E seed
  have hprofile : ∀ t ∈ R, producerProfile4 (e : ℝ) rows licensed seed t = lambda t := by
    intro t ht
    exact producerProfile4_eq_fixedCellExponent_on_source (e : ℝ) rows licensed E seed R hfixed ht
  have hlegal : ∀ t ∈ R, (∑ i, t i) + t (Fin.last 3) ≤ lambda t := by
    intro t ht
    have hold := HistoricalThirdCoarse.P1OriginalFourth.jointRegion_strict_plus
      (e : ℝ) omega m (HistoricalThirdCoarse.P1OriginalFourth.prefix3 j) t ht.2
    rw [← oldExponent_eq_actual] at hold
    have hle := producerProfile4_seed_le (e : ℝ) rows licensed seed t
    rw [hprofile t ht] at hle
    exact hold.le.trans hle
  have hold := tendsto_original_plus_residual_error e m omega a ha haRho j seed le_rfl cap hcap
  have hnew := tendsto_movingBoxResidualSum_error a (19 / 96) ha haRho R lambda
    (continuous_fixedCellExponent (e : ℝ) rows E seed) hlegal cap hcap
  have hlim := hold.sub hnew
  rw [sub_zero] at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  rw [positiveCellSource_eq_moving_residual_difference e chi m omega a J4 j hj N (cap N)
    hN hc rows licensed E hfixed,
    labelledRawCellSum_eq_test e m N omega a ha hN j rows licensed]
  have htest : actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
      ((sourceRegion e m omega j).indicator (fun t => extendedProfile seed t -
        extendedProfile (producerProfile4 (e : ℝ) rows licensed seed t) t)) =
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        (R.indicator (extendedProfile seed)) -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        (R.indicator (fun t => extendedProfile (lambda t) t)) := by
    unfold actualPrimeBoxTestSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hs : actualPrimeTupleLog N p ∈ R
    · simp only [R] at hs
      simp only [Set.indicator_of_mem hs, hprofile _ hs]
      ring
    · simp only [R] at hs
      simp only [Set.indicator_of_not_mem hs, mul_zero, sub_self]
  rw [htest]
  ring

/-- A genuine finite-discrete-to-integral limit for the original selected
variable-fourth source.  Its finite summand is the literal Rosser PLUS
residual; the pre-existing fixed cell-test limit is used only after the
new moving arithmetic error has been proved to vanish. -/
theorem tendsto_positiveCellSource
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (E : Finset ProducerRow)
    (hfixed : ∀ r ∈ rows, ∀ t ∈ sourceRegion e m omega j,
      producerEligible licensed r t ↔ r ∈ E)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => positiveCellSource e chi m omega a j rows licensed N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∫ t in truncatedCell e m omega a j,
        (fourthPlusProfileP1 (oldExponent e m j) t -
          fourthPlusProfileP1
            (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t) * ∏ i, 1 / t i)) := by
  have herror := tendsto_positiveCellSource_sub_labelledRawCellSum e chi m omega a ha haRho
    J4 j hj rows licensed E hfixed cap hcap
  have htest := (tendsto_labelledRawCellSum e chi m omega a ha haRho J4 j hj rows licensed E hfixed).mono_left
    (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  simpa only [sub_add_cancel, zero_add] using herror.add htest

/-- Selected source cells are summed only once, with their actual current
rawQ3 seed and every pointwise eligible producer candidate. -/
theorem tendsto_selected_positive_source
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (E : FourthCell m → Finset ProducerRow)
    (hfixed : ∀ j ∈ selectedFourthCells e chi m omega J4,
      ∀ r ∈ rows, ∀ t ∈ sourceRegion e m omega j, producerEligible licensed r t ↔ r ∈ E j)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => ∑ j ∈ selectedFourthCells e chi m omega J4,
      positiveCellSource e chi m omega a j rows licensed N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∑ j ∈ selectedFourthCells e chi m omega J4,
        ∫ t in truncatedCell e m omega a j,
          (fourthPlusProfileP1 (oldExponent e m j) t -
            fourthPlusProfileP1
              (producerProfile4 (e : ℝ) rows licensed (oldExponent e m j) t) t) * ∏ i, 1 / t i)) := by
  exact tendsto_finsetSum (selectedFourthCells e chi m omega J4) (fun j hj =>
    tendsto_positiveCellSource e chi m omega a ha haRho J4 j hj rows licensed (E j) (hfixed j hj) cap hcap)

end
end ImbalancedChen.P1OriginalVariableFourthSourceLimit
