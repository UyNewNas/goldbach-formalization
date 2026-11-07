import ImbalancedChen.P1ActualUpperClosedParameterUniformity
import ImbalancedChen.P1HistoricalFourthFullCellIntegral
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import ImbalancedChen.MovingWeightTransport

/-!
# Full actual fourth cell limits without a whole-box margin

The actual closed-parameter plus supplier includes residual one.  Its
compact parameter image is formed from the closed legal part of the
ambient cube.  The continuous max-one extension is a global prime test;
the original historical T3 gates identify it with the raw profile on the
joint cell.  Both old and new fourth residuals are treated separately,
with their literal natural products, cutoffs and normalization.
-/

namespace ImbalancedChen.P1FourthFullCellLimit
noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open HistoricalPrefixCapData
open P1FourthFullCellIntegral

/-- A closed legal compact image, rather than a strict whole-cell margin,
supplies the genuine actual residual approximation uniformly. -/
theorem exists_tuplePlus_closed_uniform_threshold
    (a b lambda : ℝ) (ha : 0 < a) (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
        (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p (Fin.last 3) ≤ lambda →
        |fourthTuplePlusResidualP1 N cap lambda p -
          extendedProfile lambda (actualPrimeTupleLog N p)| < eta := by
  let C : Set (Fin 4 → ℝ) := univ.pi (fun _ => Icc a b) ∩
    {t | (∑ i, t i) + t (Fin.last 3) ≤ lambda}
  let F : (Fin 4 → ℝ) → ℝ × ℝ := fun t => (lambda - ∑ i, t i, t (Fin.last 3))
  let T : Set (ℝ × ℝ) := F '' C
  have hform : Continuous (fun t : Fin 4 → ℝ => (∑ i, t i) + t (Fin.last 3)) := by
    fun_prop
  have hC : IsCompact C := (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
    (isClosed_le hform continuous_const)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hT : IsCompact T := hC.image hF
  have hparam : ∀ q ∈ T, 0 < q.2 ∧ q.2 ≤ q.1 := by
    rintro q ⟨t, ht, rfl⟩
    have hh := ht.2
    change (∑ i, t i) + t (Fin.last 3) ≤ lambda at hh
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
      (p (Fin.last 3) : ℝ) lambda = F (actualPrimeTupleLog N p) := by
    change (lambda - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ),
        actualPrimeTupleLog N p (Fin.last 3)) =
      (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p (Fin.last 3))
    rw [actualPrimeTupleLog_sum_prod p hpos]
  have hh := hbound N hN hEven _ _ lambda hP hy
    (by rw [hparams]; exact mem_image_of_mem F ht) cap
    ((hpi (Fin.last 3)).2.2.2.le.trans hcap)
  have hu : 0 < actualPrimeTupleLog N p (Fin.last 3) :=
    ha.trans_le (ht.1 _ (mem_univ _)).1
  have hs : 1 ≤ P1FourthNearOneKernel.residual lambda (actualPrimeTupleLog N p) := by
    apply (le_div_iff₀ hu).mpr
    dsimp [P1FourthNearOneKernel.residual]
    linarith
  have hprofile : extendedProfile lambda (actualPrimeTupleLog N p) =
      (2 * Real.exp (-Real.eulerMascheroniConstant) / actualPrimeTupleLog N p (Fin.last 3)) *
        P1FourthNearOneKernel.closedUpper
          ((lambda - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p (Fin.last 3)) := by
    rw [extendedProfile, P1FourthNearOneKernel.maxOneNormalized, max_eq_right hs]
    dsimp [P1FourthNearOneKernel.residual]
    ring
  rw [hprofile]
  simpa only [fourthTuplePlusResidualP1, hparams, F] using hh

/-- On any fixed part of the closed legal region, the genuine actual
residual error has vanishing positive weighted sum. -/
theorem tendsto_boxPlus_closed_error
    (a b lambda : ℝ) (ha : 0 < a) (hab : a < b)
    (R : Set (Fin 4 → ℝ))
    (hlegal : ∀ t ∈ R, (∑ i, t i) + t (Fin.last 3) ≤ lambda)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => fourthBoxPlusResidualSumP1 N (cap N) a b lambda R -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
        (R.indicator (extendedProfile lambda)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin 4 → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f (N : ℕ) (p : Fin 4 → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then fourthTuplePlusResidualP1 N (cap N) lambda p else 0
  let g (N : ℕ) (p : Fin 4 → ℕ) :=
    R.indicator (extendedProfile lambda) (actualPrimeTupleLog N p)
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin 4 => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N₀, _hN₀, hbound⟩ := exists_tuplePlus_closed_uniform_threshold a b lambda ha eta heta
    have hNat : ∀ᶠ N in l, N₀ ≤ N := (eventually_ge_atTop N₀).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc p hp
    by_cases hR : actualPrimeTupleLog N p ∈ R
    · simpa only [f, g, if_pos hR, indicator_of_mem hR] using
        hbound N hN hE.2 (cap N) hc p hp (hlegal _ hR)
    · simpa only [f, g, if_neg hR, indicator_of_notMem hR, sub_self, abs_zero] using heta
  exact tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg

/-- A single true upper residual on the full historical joint cell has
its literal raw profile integral limit, with no whole-box margin. -/
theorem tendsto_boxPlus_full_joint
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (j : Fin 4 → Fin (D.m + 1)) (lambda : ℝ) (hlevel : (D.old4 j : ℝ) ≤ lambda)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => fourthBoxPlusResidualSumP1 N (cap N) (D.a : ℝ) (D.b : ℝ)
      lambda (jointCell D j))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (fourthPlusCellIntegralP1 (D.a : ℝ) (D.b : ℝ) lambda D.m j
        p1_fourthParentGateForms (D.p1_fourthParentGateBounds j))) := by
  have haR : (0 : ℝ) < D.a := by exact_mod_cast ha
  have habR : (D.a : ℝ) < D.b := by exact_mod_cast hab
  have hlegal : ∀ t ∈ jointCell D j, (∑ i, t i) + t (Fin.last 3) ≤ lambda :=
    fun t ht => (jointCell_subset_legal D ha hab j hlevel ht).2
  have herror := tendsto_boxPlus_closed_error (D.a : ℝ) (D.b : ℝ) lambda haR habR
    (jointCell D j) hlegal cap hcap
  have hfixed := (tendsto_actualPrimeBoxTestSum_cube_IcoCell_affineGates haR habR D.m j
    p1_fourthParentGateForms (D.p1_fourthParentGateBounds j) p1_fourthParentGateForms_ne_zero
    (extendedProfile lambda) (continuousOn_extendedProfile haR)).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  have hint : (∫ t in jointCell D j, extendedProfile lambda t * ∏ i, 1 / t i) =
      fourthPlusCellIntegralP1 (D.a : ℝ) (D.b : ℝ) lambda D.m j
        p1_fourthParentGateForms (D.p1_fourthParentGateBounds j) := by
    apply setIntegral_congr_fun (measurableSet_jointCell D j)
    intro t ht
    rw [extendedProfile_eq_raw_on_joint D ha hab j hlevel ht]
  change Tendsto _ _ (𝓝 (∫ t in jointCell D j, extendedProfile lambda t * ∏ i, 1 / t i)) at hfixed
  rw [hint] at hfixed
  have hh := herror.add hfixed
  simpa only [jointCell, sub_add_cancel, zero_add] using hh

theorem tendsto_fourthCellPrimeCorrection
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fourthCellPrimeCorrectionP1 N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (D.fourthCellIntegralP1 j)) := by
  have hlevel : (D.old4 j : ℝ) ≤ (D.cap4 j : ℝ) := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.1 j hj
  have hold := tendsto_boxPlus_full_joint D ha hab j (D.old4 j : ℝ) le_rfl cap hcap
  have hnew := tendsto_boxPlus_full_joint D ha hab j (D.cap4 j : ℝ) hlevel cap hcap
  have hlim := hold.sub hnew
  change Tendsto _ _ (𝓝 (D.fourthCellIntegralP1 j)) at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (D.fourthCellPrimeCorrection_eq_joint_residual_sumsP1 hab hcheck N (cap N) hN hc j hj).symm

theorem tendsto_fourthPrimeCorrection
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fourthPrimeCorrectionP1 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 D.fourthCorrectionIntegralP1) := by
  have hlim := tendsto_finsetSum D.cells4 (fun j hj =>
    tendsto_fourthCellPrimeCorrection D ha hab hcheck j hj cap hcap)
  change Tendsto _ _ (𝓝 D.fourthCorrectionIntegralP1) at hlim
  apply hlim.congr'
  exact Eventually.of_forall (fun N => (D.fourthPrimeCorrection_eq_cellsP1 hab.le N (cap N)).symm)

theorem tendsto_fourthCellPrimeCorrection_fullIntegral
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fourthCellPrimeCorrectionP1 N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (fullCellIntegral D j)) := by
  rw [fullCellIntegral_eq_dictionary D ha hab hcheck j hj]
  exact tendsto_fourthCellPrimeCorrection D ha hab hcheck j hj cap hcap

theorem tendsto_fourthPrimeCorrection_fullIntegral
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fourthPrimeCorrectionP1 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (fullIntegral D)) := by
  rw [fullIntegral_eq_dictionary D ha hab hcheck]
  exact tendsto_fourthPrimeCorrection D ha hab hcheck cap hcap

theorem tendsto_actualHistoricalFourthSaving
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N (cap N) ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 D.fourthCorrectionIntegralP1) := by
  apply (tendsto_fourthPrimeCorrection D ha hab hcheck cap hcap).congr'
  exact Eventually.of_forall (fun N =>
    (D.actualHistoricalFourthSaving_eq_fourthPrimeCorrectionP1 N (cap N)).symm)

theorem tendsto_upperThirdToFourthSaving
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (D.b : ℝ))) -
        firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (D.b : ℝ)))) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 D.fourthCorrectionIntegralP1) := by
  apply (tendsto_fourthPrimeCorrection D ha hab hcheck cap hcap).congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  exact (D.upperThirdToFourthSaving_normalized_eq_fourthPrimeCorrectionP1
    hab.le hcheck N (cap N) (by exact_mod_cast hN)).symm

theorem tendsto_actualHistoricalFourthSaving_ceil
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ => actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 D.fourthCorrectionIntegralP1) := by
  exact tendsto_actualHistoricalFourthSaving D ha hab hcheck _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (D.b : ℝ))))

theorem tendsto_upperThirdToFourthSaving_ceil
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) 0 ((N : ℝ) ^ (D.b : ℝ))) -
        firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) 0 ((N : ℝ) ^ (D.b : ℝ)))) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 D.fourthCorrectionIntegralP1) := by
  exact tendsto_upperThirdToFourthSaving D ha hab hcheck _
    (Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ (D.b : ℝ))))

end
end ImbalancedChen.P1FourthFullCellLimit
