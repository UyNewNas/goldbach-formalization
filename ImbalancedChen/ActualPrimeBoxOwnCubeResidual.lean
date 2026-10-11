import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral
import ImbalancedChen.ActualRosserResidualDensity
import ImbalancedChen.RosserContinuousSourceUniformity

/-!
# Uniform actual lower residuals behind their own-cube gate

The gate is the literal integer-prefix product times the last prime squared.
It is identified exactly with a strict affine logarithmic inequality. The
normalized density is the actual lower Rosser density at the quotient level.
Its compact uniform approximation is proved even up to the closed legal
boundary. A continuous extension of the limiting profile is used outside
the gate; this extension is never substituted for an illegal residual.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open MathlibNt.SieveTheory
open scoped Classical BigOperators

/-- The own-cube logarithmic form, on a nonempty tuple. -/
def primeTupleOwnCubeForm {k : ℕ} (t : Fin (k + 1) → ℝ) : ℝ :=
  (∑ i, t i) + 2 * t (Fin.last k)

/-- Continuous extension of the legal normalized lower residual profile. -/
def primeTupleMinusProfile {k : ℕ} (lambda : ℝ) (t : Fin (k + 1) → ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / t (Fin.last k)) *
    suzukiContinuousLowerFactor (max 2 ((lambda - ∑ i, t i) / t (Fin.last k)))

/-- The actual lower residual with the original strict own-cube gate. -/
def actualPrimeTupleOwnCubeMinus {k : ℕ} (N cap : ℕ) (lambda : ℝ)
    (p : Fin (k + 1) → ℕ) : ℝ :=
  if (∏ i, p i : ℕ) * (p (Fin.last k) : ℝ) ^ 2 < (N : ℝ) ^ lambda then
    actualSmallRosserMinusDensity N cap (p (Fin.last k) : ℝ)
      ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) * Real.log (N : ℝ) / singularSeries N
  else 0

theorem continuousOn_primeTupleMinusProfile {k : ℕ} {a b : ℝ}
    (ha : 0 < a) (lambda : ℝ) :
    ContinuousOn (primeTupleMinusProfile (k := k) lambda)
      (Set.univ.pi (fun _ => Set.Icc a b)) := by
  have hlast : Continuous (fun t : Fin (k + 1) → ℝ => t (Fin.last k)) := by fun_prop
  have hsum : Continuous (fun t : Fin (k + 1) → ℝ => ∑ i, t i) := by fun_prop
  have hne : ∀ t ∈ Set.univ.pi (fun _ : Fin (k + 1) => Set.Icc a b),
      t (Fin.last k) ≠ 0 := fun t ht => (ha.trans_le (ht _ (Set.mem_univ _)).1).ne'
  have harg : ContinuousOn (fun t : Fin (k + 1) → ℝ =>
      max 2 ((lambda - ∑ i, t i) / t (Fin.last k)))
      (Set.univ.pi (fun _ => Set.Icc a b)) :=
    continuousOn_const.sup ((continuousOn_const.sub hsum.continuousOn).div
      hlast.continuousOn hne)
  exact (continuousOn_const.div hlast.continuousOn hne).mul
    (continuousOn_suzukiContinuousLowerFactor.comp harg
      (fun t _ => le_max_left (2 : ℝ) ((lambda - ∑ i, t i) / t (Fin.last k))))

theorem primeTupleMinusProfile_of_ownCube {k : ℕ} {lambda : ℝ}
    {t : Fin (k + 1) → ℝ} (ht : 0 < t (Fin.last k))
    (hgate : primeTupleOwnCubeForm t ≤ lambda) :
    primeTupleMinusProfile lambda t =
      (2 * Real.exp (-Real.eulerMascheroniConstant) / t (Fin.last k)) *
        suzukiContinuousLowerFactor ((lambda - ∑ i, t i) / t (Fin.last k)) := by
  have hs : 2 ≤ (lambda - ∑ i, t i) / t (Fin.last k) :=
    (le_div_iff₀ ht).mpr (by dsimp [primeTupleOwnCubeForm] at hgate; linarith)
  simp only [primeTupleMinusProfile, max_eq_right hs]

/-- Strict arithmetic endpoints are preserved exactly. -/
theorem actualPrimeTupleOwnCube_iff {k N : ℕ} (hN : 1 < N)
    (p : Fin (k + 1) → ℕ) (hp : ∀ i, 0 < p i) (lambda : ℝ) :
    (∏ i, p i : ℕ) * (p (Fin.last k) : ℝ) ^ 2 < (N : ℝ) ^ lambda ↔
      primeTupleOwnCubeForm (actualPrimeTupleLog N p) < lambda := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hp i)
  have hprod : (N : ℝ) ^ (∑ i, actualPrimeTupleLog N p i) = (∏ i, p i : ℕ) := by
    rw [actualPrimeTupleLog_sum_prod p hp]
    exact residual_rpow_log_div _ _ hNr hP
  have hpow : (N : ℝ) ^ primeTupleOwnCubeForm (actualPrimeTupleLog N p) =
      (∏ i, p i : ℕ) * (p (Fin.last k) : ℝ) ^ 2 := by
    rw [primeTupleOwnCubeForm, Real.rpow_add (by positivity), hprod,
      mul_comm (2 : ℝ), Real.rpow_mul (by positivity),
      actualPrimeTupleLog_rpow hN p hp, Real.rpow_two]
  rw [← hpow]
  exact Real.rpow_lt_rpow_left_iff hNr

/-- One threshold controls every admitted tuple in the fixed cube. No
positivity assumption for a finite lower sieve density is required. -/
theorem exists_actualPrimeTupleOwnCubeMinus_uniform_threshold
    (k : ℕ) (a b lambda : ℝ) (ha : 0 < a) (eta : ℝ) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
        |actualPrimeTupleOwnCubeMinus N cap lambda p -
          (if primeTupleOwnCubeForm (actualPrimeTupleLog N p) < lambda then
            primeTupleMinusProfile lambda (actualPrimeTupleLog N p) else 0)| < eta := by
  let C : Set (Fin (k + 1) → ℝ) :=
    Set.univ.pi (fun _ => Set.Icc a b) ∩ {t | primeTupleOwnCubeForm t ≤ lambda}
  let F : (Fin (k + 1) → ℝ) → ℝ × ℝ :=
    fun t => (lambda - ∑ i, t i, t (Fin.last k))
  let T : Set (ℝ × ℝ) := F '' C
  have hform : Continuous (primeTupleOwnCubeForm (k := k)) := by
    unfold primeTupleOwnCubeForm; fun_prop
  have hC : IsCompact C := (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
    (isClosed_le hform continuous_const)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hT : IsCompact T := hC.image hF
  have hparam : ∀ q ∈ T, 0 < q.2 ∧ 2 * q.2 ≤ q.1 := by
    rintro q ⟨t, ht, rfl⟩
    refine ⟨ha.trans_le (ht.1 _ (Set.mem_univ _)).1, ?_⟩
    have hh := ht.2
    change (∑ i, t i) + 2 * t (Fin.last k) ≤ lambda at hh
    dsimp [F]
    linarith
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_quotient_compact_normalized_threshold
      T hT hparam eta heta
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap p hp
  have hN1 : 1 < N := by omega
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have hdict := actualPrimeTupleOwnCube_iff hN1 p hpos lambda
  by_cases hg : primeTupleOwnCubeForm (actualPrimeTupleLog N p) < lambda
  · have hx := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
    have ht : actualPrimeTupleLog N p ∈ C :=
      ⟨fun i _ => ⟨(mem_logPrimeBox.mp hx i).1, (mem_logPrimeBox.mp hx i).2.le⟩, hg.le⟩
    have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
    have hy : (0 : ℝ) < p (Fin.last k) := by exact_mod_cast hpos (Fin.last k)
    have hparams : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
        (p (Fin.last k) : ℝ) lambda = F (actualPrimeTupleLog N p) := by
      change (lambda - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ),
          actualPrimeTupleLog N p (Fin.last k)) =
        (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p (Fin.last k))
      rw [actualPrimeTupleLog_sum_prod p hpos]
    have hh := hbound N hN hEven _ _ lambda hP hy
      (by rw [hparams]; exact Set.mem_image_of_mem F ht) cap
      ((hpi (Fin.last k)).2.2.2.le.trans hcap)
    rw [actualPrimeTupleOwnCubeMinus, if_pos (hdict.mpr hg), if_pos hg,
      primeTupleMinusProfile_of_ownCube (ha.trans_le (ht.1 _ (Set.mem_univ _)).1) hg.le]
    simpa only [hparams, F] using hh
  · simp only [actualPrimeTupleOwnCubeMinus, if_neg (mt hdict.mp hg), if_neg hg,
      sub_self, abs_zero]
    exact heta

/-- An additional fixed region retains every strict own-cube test. -/
def actualPrimeBoxOwnCubeMinusSum (k N cap : ℕ) (a b lambda : ℝ)
    (R : Set (Fin (k + 1) → ℝ)) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ R then actualPrimeTupleOwnCubeMinus N cap lambda p else 0)

/-- The true arithmetic residual can be replaced by its gated limiting
profile with an error tending to zero on any fixed additional region.
No regularity of that region is needed for this error estimate. -/
theorem tendsto_actualPrimeBoxOwnCubeMinus_error
    (k : ℕ) (a b lambda : ℝ) (ha : 0 < a) (hab : a < b)
    (R : Set (Fin (k + 1) → ℝ)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualPrimeBoxOwnCubeMinusSum k N (cap N) a b lambda R -
      actualPrimeBoxTestSum N (fun _ : Fin (k + 1) => a) (fun _ => b)
        (fun t => if t ∈ R then
          (if primeTupleOwnCubeForm t < lambda then primeTupleMinusProfile lambda t else 0)
          else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let l : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}
  let T (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b)
  let w (_N : ℕ) (p : Fin (k + 1) → ℕ) := ∏ i, 1 / ((p i : ℝ) - 1)
  let f (N : ℕ) (p : Fin (k + 1) → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then actualPrimeTupleOwnCubeMinus N (cap N) lambda p else 0
  let g (N : ℕ) (p : Fin (k + 1) → ℕ) :=
    if actualPrimeTupleLog N p ∈ R then
      (if primeTupleOwnCubeForm (actualPrimeTupleLog N p) < lambda then
        primeTupleMinusProfile lambda (actualPrimeTupleLog N p) else 0) else 0
  have hmasslimit := (tendsto_actualPrimeBoxMass (fun _ : Fin (k + 1) => a)
    (fun _ => b) (fun _ => ha) (fun _ => hab)).mono_left (show l ≤ atTop from inf_le_left)
  obtain ⟨M, hM, hmass⟩ := exists_eventually_bounded_mass_of_tendsto hmasslimit
  have hw : ∀ᶠ N in l, ∀ p ∈ T N, 0 ≤ w N p :=
    Filter.Eventually.of_forall (fun _ _ hp => actualPrimeBoxWeight_nonneg hp)
  have hfg : ∀ eta > 0, ∀ᶠ N in l, ∀ p ∈ T N, |f N p - g N p| < eta := by
    intro eta heta
    obtain ⟨N₀, _hN₀, hbound⟩ := exists_actualPrimeTupleOwnCubeMinus_uniform_threshold
      k a b lambda ha eta heta
    have hNat : ∀ᶠ N in l, N₀ ≤ N :=
      (eventually_ge_atTop N₀).filter_mono inf_le_left
    have hEven : ∀ᶠ N in l, 0 < N ∧ Even N :=
      Filter.Eventually.filter_mono inf_le_right (by simp)
    filter_upwards [hNat, hEven, hcap] with N hN hE hc p hp
    dsimp [f, g]
    by_cases hR : actualPrimeTupleLog N p ∈ R
    · simpa only [if_pos hR] using hbound N hN hE.2 (cap N) hc p hp
    · simpa only [if_neg hR, sub_self, abs_zero] using heta
  exact tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w f g M hM hw hmass hfg

end

end ImbalancedChen
