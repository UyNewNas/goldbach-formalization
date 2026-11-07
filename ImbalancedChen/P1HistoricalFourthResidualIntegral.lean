import ImbalancedChen.ActualHistoricalFourthResidualDictionaryP1
import ImbalancedChen.P1HistoricalUpperFourthJointGeometry
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import ImbalancedChen.ActualRosserResidualDensity
import ImbalancedChen.RosserContinuousSourceUniformity
import ImbalancedChen.MovingWeightTransport

/-!
# Fourth upper-residual integrals with a finite legal-cell margin

The exact arithmetic identities hold without an analytic margin.  For the
limit, the displayed finite endpoint inequality keeps the upper residual
strictly above its singular endpoint one.  This is a geometric sufficient
condition, not a density-limit hypothesis.  Cells meeting residual one
still need a separate boundary-strip argument; no such argument is
asserted here.
-/

namespace ImbalancedChen
noncomputable section
open Filter Topology MeasureTheory Set
open MathlibNt.SieveTheory
open scoped Classical BigOperators

def fourthPlusProfileP1 (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / t (Fin.last 3)) *
    suzukiContinuousUpperFactor ((lambda - ∑ i, t i) / t (Fin.last 3))

/-- Continuous auxiliary extension; it equals the true upper profile on
the licensed cell.  It does not change the actual arithmetic residual. -/
def fourthPlusExtendedProfileP1 (sigma lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / t (Fin.last 3)) *
    suzukiContinuousUpperFactor (max sigma ((lambda - ∑ i, t i) / t (Fin.last 3)))

theorem fourthPlusExtendedProfile_eqP1 (sigma lambda : ℝ) (t : Fin 4 → ℝ)
    (ht : 0 < t (Fin.last 3))
    (hlegal : (∑ i, t i) + sigma * t (Fin.last 3) ≤ lambda) :
    fourthPlusExtendedProfileP1 sigma lambda t = fourthPlusProfileP1 lambda t := by
  have hs : sigma ≤ (lambda - ∑ i, t i) / t (Fin.last 3) :=
    (le_div_iff₀ ht).mpr (by linarith)
  simp only [fourthPlusExtendedProfileP1, fourthPlusProfileP1, max_eq_right hs]

theorem continuousOn_fourthPlusExtendedProfileP1 {a b : ℝ}
    (ha : 0 < a) (sigma lambda : ℝ) (hsigma : 1 < sigma) :
    ContinuousOn (fourthPlusExtendedProfileP1 sigma lambda)
      (Set.univ.pi (fun _ : Fin 4 => Set.Icc a b)) := by
  have hlast : Continuous (fun t : Fin 4 → ℝ => t (Fin.last 3)) := by fun_prop
  have hsum : Continuous (fun t : Fin 4 → ℝ => ∑ i, t i) := by fun_prop
  have hne : ∀ t ∈ Set.univ.pi (fun _ : Fin 4 => Set.Icc a b),
      t (Fin.last 3) ≠ 0 := fun t ht => (ha.trans_le (ht _ (Set.mem_univ _)).1).ne'
  have harg : ContinuousOn (fun t : Fin 4 → ℝ =>
      max sigma ((lambda - ∑ i, t i) / t (Fin.last 3)))
      (Set.univ.pi (fun _ : Fin 4 => Set.Icc a b)) :=
    continuousOn_const.sup ((continuousOn_const.sub hsum.continuousOn).div
      hlast.continuousOn hne)
  exact (continuousOn_const.div hlast.continuousOn hne).mul
    (continuousOn_suzukiContinuousUpperFactor.comp harg
      (fun t _ => hsigma.trans_le (le_max_left _ _)))

/-- One true compact supplier controls all legal tuples, at every later
even target and every covering enumeration cap. -/
theorem exists_fourthTuplePlusResidual_uniform_thresholdP1
    (a b sigma lambda : ℝ) (ha : 0 < a) (hsigma : 1 < sigma)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
        (∑ i, actualPrimeTupleLog N p i) + sigma * actualPrimeTupleLog N p (Fin.last 3) ≤
            lambda →
        |fourthTuplePlusResidualP1 N cap lambda p -
          fourthPlusExtendedProfileP1 sigma lambda (actualPrimeTupleLog N p)| < eta := by
  let C : Set (Fin 4 → ℝ) := Set.univ.pi (fun _ => Set.Icc a b) ∩
    {t | (∑ i, t i) + sigma * t (Fin.last 3) ≤ lambda}
  let F : (Fin 4 → ℝ) → ℝ × ℝ := fun t => (lambda - ∑ i, t i, t (Fin.last 3))
  let T : Set (ℝ × ℝ) := F '' C
  have hform : Continuous (fun t : Fin 4 → ℝ => (∑ i, t i) + sigma * t (Fin.last 3)) := by
    fun_prop
  have hC : IsCompact C := (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
    (isClosed_le hform continuous_const)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hT : IsCompact T := hC.image hF
  have hparam : ∀ q ∈ T, 0 < q.2 ∧ q.2 < q.1 := by
    rintro q ⟨t, ht, rfl⟩
    have hpos : 0 < t (Fin.last 3) := ha.trans_le (ht.1 _ (Set.mem_univ _)).1
    have hmul : t (Fin.last 3) < sigma * t (Fin.last 3) := by
      nlinarith
    have hh := ht.2
    change (∑ i, t i) + sigma * t (Fin.last 3) ≤ lambda at hh
    dsimp [F]
    exact ⟨hpos, by linarith⟩
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_quotient_compact_normalized_threshold
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
    (by rw [hparams]; exact Set.mem_image_of_mem F ht) cap
    ((hpi (Fin.last 3)).2.2.2.le.trans hcap)
  rw [fourthPlusExtendedProfile_eqP1 sigma lambda _
    (ha.trans_le (ht.1 _ (Set.mem_univ _)).1) hlegal]
  simpa only [fourthTuplePlusResidualP1, fourthPlusProfileP1, hparams, F] using hh

def fourthBoxPlusResidualSumP1 (N cap : ℕ) (a b lambda : ℝ)
    (R : Set (Fin 4 → ℝ)) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ R then fourthTuplePlusResidualP1 N cap lambda p else 0)

/-- A finite endpoint test supplies the legal margin on every point of
the same half-open cell, including its lower faces. -/
theorem fourthCell_margin_of_endpointsP1 {a b sigma lambda : ℝ} {m : ℕ}
    (j : Fin 4 → Fin (m + 1)) (hsigma : 0 ≤ sigma)
    (hmargin : (∑ i, logPrimeMeshHi a b m j i) +
        sigma * logPrimeMeshHi a b m j (Fin.last 3) ≤ lambda)
    {t : Fin 4 → ℝ} (ht : t ∈ logPrimeMeshCell a b m j) :
    (∑ i, t i) + sigma * t (Fin.last 3) ≤ lambda := by
  have hsum : (∑ i, t i) ≤ ∑ i, logPrimeMeshHi a b m j i :=
    Finset.sum_le_sum (fun i _ => (mem_logPrimeMeshCell.mp ht i).2.le)
  have hlast := mul_le_mul_of_nonneg_left
    (mem_logPrimeMeshCell.mp ht (Fin.last 3)).2.le hsigma
  linarith

theorem tendsto_fourthBoxPlusResidual_errorP1
    (a b sigma lambda : ℝ) (ha : 0 < a) (hab : a < b) (hsigma : 1 < sigma)
    (R : Set (Fin 4 → ℝ))
    (hlegal : ∀ t ∈ R, (∑ i, t i) + sigma * t (Fin.last 3) ≤ lambda)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => fourthBoxPlusResidualSumP1 N (cap N) a b lambda R -
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => b)
        (R.indicator (fourthPlusExtendedProfileP1 sigma lambda)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin 4 → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f (N : ℕ) (p : Fin 4 → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then fourthTuplePlusResidualP1 N (cap N) lambda p else 0
  let g (N : ℕ) (p : Fin 4 → ℕ) :=
    R.indicator (fourthPlusExtendedProfileP1 sigma lambda) (actualPrimeTupleLog N p)
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin 4 => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Filter.Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N₀, _hN₀, hbound⟩ :=
      exists_fourthTuplePlusResidual_uniform_thresholdP1 a b sigma lambda ha hsigma eta heta
    have hNat : ∀ᶠ N in l, N₀ ≤ N := (eventually_ge_atTop N₀).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc p hp
    by_cases hR : actualPrimeTupleLog N p ∈ R
    · simpa only [f, g, if_pos hR, Set.indicator_of_mem hR] using
        hbound N hN hE.2 (cap N) hc p hp (hlegal _ hR)
    · simpa only [f, g, if_neg hR, Set.indicator_of_notMem hR,
        sub_self, abs_zero] using heta
  exact tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg

def fourthPlusCellIntegralP1 {r : ℕ} (a b lambda : ℝ) (m : ℕ)
    (j : Fin 4 → Fin (m + 1))
    (L : Fin r → (Fin 4 → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) : ℝ :=
  ∫ t in logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c,
    fourthPlusProfileP1 lambda t * ∏ i, 1 / t i

/-- Genuine actual plus-residual limit on a fixed joint cell.  The only
extra premise is a displayed finite endpoint margin, strictly above one. -/
theorem tendsto_fourthBoxPlusResidual_IcoCellP1 {r : ℕ}
    (a b sigma lambda : ℝ) (ha : 0 < a) (hab : a < b) (hsigma : 1 < sigma)
    (m : ℕ) (j : Fin 4 → Fin (m + 1))
    (L : Fin r → (Fin 4 → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ i, L i ≠ 0)
    (hmargin : (∑ i, logPrimeMeshHi a b m j i) +
      sigma * logPrimeMeshHi a b m j (Fin.last 3) ≤ lambda)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => fourthBoxPlusResidualSumP1 N (cap N) a b lambda
      (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (fourthPlusCellIntegralP1 a b lambda m j L c)) := by
  have hlegal := fun t (ht : t ∈ logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c) =>
    fourthCell_margin_of_endpointsP1 j (zero_le_one.trans hsigma.le) hmargin ht.1
  have herror := tendsto_fourthBoxPlusResidual_errorP1 a b sigma lambda ha hab hsigma
    (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c) hlegal cap hcap
  have hfixed := (tendsto_actualPrimeBoxTestSum_cube_IcoCell_affineGates ha hab m j L c hL
    (fourthPlusExtendedProfileP1 sigma lambda)
    (continuousOn_fourthPlusExtendedProfileP1 ha sigma lambda hsigma)).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  have hint : (∫ t in logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c,
      fourthPlusExtendedProfileP1 sigma lambda t * ∏ i, 1 / t i) =
      fourthPlusCellIntegralP1 a b lambda m j L c := by
    apply setIntegral_congr_fun
      ((measurableSet_logPrimeMeshCell a b m j).inter (measurableSet_primeAffineGateRegion L c))
    intro t ht
    have hp : 0 < t (Fin.last 3) :=
      ha.trans_le (mem_logPrimeBox.mp (logPrimeMeshCell_subset_box hab m j ht.1) _).1
    rw [fourthPlusExtendedProfile_eqP1 sigma lambda t hp (hlegal t ht)]
  rw [hint] at hfixed
  have hh := herror.add hfixed
  simpa only [sub_add_cancel, zero_add] using hh

namespace HistoricalPrefixCapData

/-- Arbitrary weighted reindexing from the actual admitted historical
frontier to its fixed joint geometric cell. -/
theorem fourthFrontier_cell_weighted_sumP1 (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (f : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
          then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => (D.a : ℝ)) (fun _ => (D.b : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
              primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)
            then f p else 0) := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    p1_historicalUpperFourthAdmittedTuples_cell_filter D hab hcheck N cap hN hcap j]

/-- Both old and new residuals use the same original T3 joint cell. -/
theorem fourthCellPrimeCorrection_eq_joint_residual_sumsP1 (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) :
    D.fourthCellPrimeCorrectionP1 N cap j =
      fourthBoxPlusResidualSumP1 N cap (D.a : ℝ) (D.b : ℝ) (D.old4 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)) -
      fourthBoxPlusResidualSumP1 N cap (D.a : ℝ) (D.b : ℝ) (D.cap4 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)) := by
  rw [D.fourthCellPrimeCorrection_eq_residual_sumsP1 hab.le N cap j hj,
    D.fourthFrontier_cell_weighted_sumP1 hab hcheck N cap hN hcap j,
    D.fourthFrontier_cell_weighted_sumP1 hab hcheck N cap hN hcap j]
  rfl

/-- Literal old-minus-new upper residual integral.  No own-cube gate is
present, and the two levels share the historical T3 parent region. -/
def fourthCellIntegralP1 (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) : ℝ :=
  fourthPlusCellIntegralP1 (D.a : ℝ) (D.b : ℝ) (D.old4 j : ℝ) D.m j
      p1_fourthParentGateForms (D.p1_fourthParentGateBounds j) -
    fourthPlusCellIntegralP1 (D.a : ℝ) (D.b : ℝ) (D.cap4 j : ℝ) D.m j
      p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)

theorem tendsto_fourthCellPrimeCorrection_with_marginP1 (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    (sigma : ℝ) (hsigma : 1 < sigma)
    (hmargin : (∑ i, logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j i) +
      sigma * logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j (Fin.last 3) ≤ (D.old4 j : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fourthCellPrimeCorrectionP1 N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (D.fourthCellIntegralP1 j)) := by
  have hlevel : (D.old4 j : ℝ) ≤ (D.cap4 j : ℝ) := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.1 j hj
  have hold := tendsto_fourthBoxPlusResidual_IcoCellP1 (D.a : ℝ) (D.b : ℝ) sigma
    (D.old4 j : ℝ) (by exact_mod_cast ha) (by exact_mod_cast hab) hsigma D.m j
    p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)
    p1_fourthParentGateForms_ne_zero hmargin cap hcap
  have hnew := tendsto_fourthBoxPlusResidual_IcoCellP1 (D.a : ℝ) (D.b : ℝ) sigma
    (D.cap4 j : ℝ) (by exact_mod_cast ha) (by exact_mod_cast hab) hsigma D.m j
    p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)
    p1_fourthParentGateForms_ne_zero (hmargin.trans hlevel) cap hcap
  have hlim := hold.sub hnew
  change Tendsto _ _ (𝓝 (D.fourthCellIntegralP1 j)) at hlim
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  exact (D.fourthCellPrimeCorrection_eq_joint_residual_sumsP1
    hab hcheck N (cap N) hN hc j hj).symm

def fourthCorrectionIntegralP1 (D : HistoricalPrefixCapData) : ℝ :=
  ∑ j ∈ D.cells4, D.fourthCellIntegralP1 j

/-- A finite family of explicit geometric margins licenses the sum of
the actual historical cell limits.  No cell margin is inferred from the
level-order checker alone. -/
theorem tendsto_fourthPrimeCorrection_with_marginsP1 (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (sigma : (Fin 4 → Fin (D.m + 1)) → ℝ)
    (hsigma : ∀ j ∈ D.cells4, 1 < sigma j)
    (hmargin : ∀ j ∈ D.cells4,
      (∑ i, logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j i) +
        sigma j * logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j (Fin.last 3) ≤ (D.old4 j : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fourthPrimeCorrectionP1 N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 D.fourthCorrectionIntegralP1) := by
  have hlim := tendsto_finsetSum D.cells4 (fun j hj =>
    D.tendsto_fourthCellPrimeCorrection_with_marginP1 ha hab hcheck j hj
      (sigma j) (hsigma j hj) (hmargin j hj) cap hcap)
  change Tendsto _ _ (𝓝 D.fourthCorrectionIntegralP1) at hlim
  apply hlim.congr'
  exact Eventually.of_forall (fun N => (D.fourthPrimeCorrection_eq_cellsP1 hab.le N (cap N)).symm)

theorem tendsto_actualHistoricalFourthSaving_with_marginsP1 (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (sigma : (Fin 4 → Fin (D.m + 1)) → ℝ)
    (hsigma : ∀ j ∈ D.cells4, 1 < sigma j)
    (hmargin : ∀ j ∈ D.cells4,
      (∑ i, logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j i) +
        sigma j * logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j (Fin.last 3) ≤ (D.old4 j : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        N (cap N) ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 D.fourthCorrectionIntegralP1) := by
  apply (D.tendsto_fourthPrimeCorrection_with_marginsP1
    ha hab hcheck sigma hsigma hmargin cap hcap).congr'
  exact Eventually.of_forall (fun N =>
    (D.actualHistoricalFourthSaving_eq_fourthPrimeCorrectionP1 N (cap N)).symm)

end HistoricalPrefixCapData
end
end ImbalancedChen
