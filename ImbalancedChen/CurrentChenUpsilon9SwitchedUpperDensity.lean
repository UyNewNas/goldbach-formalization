import ImbalancedChen.CurrentChenUpsilon9FiniteMean
import ImbalancedChen.CurrentChenSinglePrimeUpperDensity

/-!
# The actual ordinary switched density has factor eight

The native Pan floor and the existing initial Chen floor are exactly the
same.  Thus the unchanged actual upper coefficient at level Q+1 has
logarithmic ratio tending to 5/2 at z=N^(1/5).  The proved relative upper
rectangle and actual Euler normalization give its normalized upper bound.
The fixed canonical source-series identity at 5/2 gives eight, with no
caller density bound or first-interval formula supplied as an assumption.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

theorem currentChenUpsilon9_panCutoff_eq_initialLevel (B : ℝ) (N : ℕ) :
    panModulusCutoff N B = chenInitialLevelCap B N := by
  simp only [panModulusCutoff, chenInitialLevelCap, Real.sqrt_eq_rpow]

private theorem currentChenUpsilon9_switched_level_rpow (B : ℝ)
    {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ^ (chenInitialRosserT B (1 / 5) N * (1 / 5 : ℝ)) =
      ((panModulusCutoff N B + 1 : ℕ) : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
  have hDp : (0 : ℝ) < chenInitialRosserD B N := by
    unfold chenInitialRosserD
    positivity
  have hexponent : chenInitialRosserT B (1 / 5) N * (1 / 5 : ℝ) =
      Real.log (chenInitialRosserD B N : ℝ) / Real.log (N : ℝ) := by
    unfold chenInitialRosserT
    rw [Real.log_rpow hNp]
    field_simp [hlog]
  rw [currentChenUpsilon9_panCutoff_eq_initialLevel]
  change (N : ℝ) ^ (chenInitialRosserT B (1 / 5) N * (1 / 5 : ℝ)) =
    (chenInitialRosserD B N : ℝ)
  rw [hexponent, Real.rpow_def_of_pos hNp, mul_div_cancel₀ _ hlog, Real.exp_log hDp]

/-- The ordinary normalized source value is exactly eight. -/
theorem currentChenUpsilon9_switched_source_factor_eight :
    suzukiContinuousUpperFactor (5 / 2) *
      (2 * Real.exp (-Real.eulerMascheroniConstant) / (1 / 5 : ℝ)) = 8 := by
  have hsource := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub
    (s := (5 / 2 : ℝ)) jr1965Section13HatSourceContract (by norm_num) (by norm_num)
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract] at hsource
  have hfactor : suzukiContinuousUpperFactor (5 / 2) =
      2 * Real.exp Real.eulerMascheroniConstant / (5 / 2 : ℝ) := by
    unfold suzukiContinuousUpperFactor
    linarith only [hsource]
  rw [hfactor, Real.exp_neg]
  field_simp
  all_goals ring

/-- The same complete actual coefficient from the finite count bound has
normalized density at most eight plus every prescribed positive error.
The fixed B is chosen before N; no sign restriction is placed on its
individual Rosser coefficients. -/
theorem eventually_currentChenUpsilon9_switched_density_le_eight
    (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9SwitchedUpperDensity B N
          (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) ((N : ℝ) ^ (1 / 5 : ℝ)) *
        Real.log (N : ℝ) / singularSeries N ≤ 8 + ε := by
  let A : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant) / (1 / 5)
  let η : ℝ := ε / (2 * (A + 1))
  have hA : 0 < A := by dsimp [A]; positivity
  have hη : 0 < η := div_pos hε (by positivity)
  have hs : Tendsto (chenInitialRosserT B (1 / 5)) atTop (𝓝 (5 / 2 : ℝ)) := by
    convert tendsto_chenInitialRosserT B (by norm_num : (0 : ℝ) < 1 / 5) using 1
    norm_num
  have hf : Tendsto (fun N => suzukiContinuousUpperFactor (chenInitialRosserT B (1 / 5) N))
      atTop (𝓝 (suzukiContinuousUpperFactor (5 / 2))) :=
    (continuousOn_currentChen_upperFactor.continuousAt
      (Ici_mem_nhds (by norm_num : (3 / 2 : ℝ) < 5 / 2))).tendsto.comp hs
  let e := fun N : ℕ => actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)))
    ((N : ℝ) ^ (1 / 5 : ℝ)) * Real.log (N : ℝ) / singularSeries N
  have he : Tendsto e (atTop ⊓ principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 A) :=
    tendsto_currentChen_actualEuler_fixed_normalized (by norm_num)
  have hnear : ∀ᶠ N : ℕ in atTop, 0 < N ∧ Even N →
      suzukiContinuousUpperFactor (chenInitialRosserT B (1 / 5) N) * e N < 8 + ε / 2 := by
    have h8 : suzukiContinuousUpperFactor (5 / 2) * A = 8 :=
      currentChenUpsilon9_switched_source_factor_eight
    have h := ((hf.mono_left inf_le_left).mul he).eventually
      (Iio_mem_nhds (show suzukiContinuousUpperFactor (5 / 2) * A < 8 + ε / 2 by
        rw [h8]; linarith only [hε]))
    simpa only [Filter.eventually_inf_principal, Set.mem_ofPred_eq] using h
  have hebound : ∀ᶠ N : ℕ in atTop, 0 < N ∧ Even N → e N < A + 1 := by
    have h := he.eventually (Iio_mem_nhds (lt_add_one A))
    simpa only [Filter.eventually_inf_principal, Set.mem_ofPred_eq] using h
  have hinterval : ∀ᶠ N : ℕ in atTop, chenInitialRosserT B (1 / 5) N ∈ Set.Ioo (2 : ℝ) 3 :=
    hs.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨N₀, _hN₀, hrelative⟩ :=
    exists_currentChen_model_plusDensity_rectangle_upper_threshold
      (1 / 5) (by norm_num) 2 (by norm_num) 3 η hη
  filter_upwards [hnear, hebound, hinterval, eventually_ge_atTop N₀,
    eventually_ge_atTop (2 : ℕ)] with N hnearN heboundN hsN hN₀ hN
  intro hEven
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hV : 0 < actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)))
      ((N : ℝ) ^ (1 / 5 : ℝ)) := currentChen_model_actualEuler_pos N _ _ hEven
  have he0 : 0 ≤ e N :=
    div_nonneg (mul_nonneg hV.le (Real.log_pos hNr).le) (singularSeries_pos N).le
  have hr := hrelative N hN₀ hEven (1 / 5) le_rfl
    (chenInitialRosserT B (1 / 5) N) hsN.1.le hsN.2.le
    (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) (Nat.le_ceil _)
  rw [currentChenUpsilon9_switched_level_rpow B hN] at hr
  have hmult := mul_le_mul_of_nonneg_right hr he0
  have hcancel :
      (actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)))
        ((N : ℝ) ^ (1 / 5 : ℝ)) ((panModulusCutoff N B + 1 : ℕ) : ℝ) /
          actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)))
            ((N : ℝ) ^ (1 / 5 : ℝ))) * e N =
        currentChenUpsilon9SwitchedUpperDensity B N
          (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) ((N : ℝ) ^ (1 / 5 : ℝ)) *
            Real.log (N : ℝ) / singularSeries N := by
    change (_ / _) * e N = actualSmallRosserPlusDensity N _ _ _ * _ / _
    dsimp [e]
    field_simp [hV.ne', (singularSeries_pos N).ne']
  rw [hcancel] at hmult
  have hcost : η * (A + 1) = ε / 2 := by
    dsimp [η]
    field_simp [show A + 1 ≠ 0 by positivity]
  have hcostN := mul_le_mul_of_nonneg_left (heboundN ⟨hNpos, hEven⟩).le hη.le
  have hmain := hnearN ⟨hNpos, hEven⟩
  nlinarith only [hmult, hcostN, hcost, hmain]

end

end ImbalancedChen
