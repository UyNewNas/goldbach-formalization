import ImbalancedChen.CurrentChenPairDensity
import ImbalancedChen.CurrentChenRosserUpperRectangle
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Actual single-prime upper densities at the ordinary row level

The canonical upper factor is retained on its whole legal interval. Its
continuity follows from the proved odd source series and its endpoint
majorant. The actual relative upper rectangle and fixed-power Euler limit
then give a uniform singular-series upper bound on the literal rounded row.
No upper density estimate or continuity assertion is assumed by the caller.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

private theorem singleUpper_odd_domain {s : ℝ} (hs : 1 < s) (k : ℕ) :
    s ∈ suzukiParityDomainOne 2 (2 * k + 1) := by
  simp [suzukiParityDomainOne, KappaOneModel.parityDomain]
  linarith

private theorem singleUpper_layer_bound {s : ℝ} (hs : (3 / 2 : ℝ) ≤ s) (k : ℕ) :
    ‖suzukiLayer 1 2 (2 * k + 1) s‖ ≤ suzukiLayer 1 2 (2 * k + 1) (3 / 2) := by
  have hs1 : 1 < s := by linarith only [hs]
  rw [Real.norm_eq_abs, abs_of_nonneg (suzukiLayer_one_two_odd_nonneg hs1 k)]
  exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * k + 1)
    (singleUpper_odd_domain (by norm_num) k) (singleUpper_odd_domain hs1 k) hs

/-- Genuine source-series continuity; no first-interval formula is used. -/
theorem continuousOn_currentChen_upperFactor :
    ContinuousOn suzukiContinuousUpperFactor (Set.Ici (3 / 2 : ℝ)) := by
  have hcont (k : ℕ) : ContinuousOn (suzukiLayer 1 2 (2 * k + 1))
      (Set.Ici (3 / 2 : ℝ)) := by
    apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num) (2 * k + 1)).mono
    intro s hs
    exact singleUpper_odd_domain (by change 3 / 2 ≤ s at hs; linarith only [hs]) k
  exact continuousOn_const.add (continuousOn_tsum hcont
    (summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract (by norm_num : (1 : ℝ) < 3 / 2))
    (fun k s hs => singleUpper_layer_bound hs k))

theorem currentChen_upperFactor_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤ suzukiContinuousUpperFactor s := by
  unfold suzukiContinuousUpperFactor suzukiProposition118SourceTPlus
  exact add_nonneg (by norm_num) (tsum_nonneg (fun k => suzukiLayer_one_two_odd_nonneg hs k))

private theorem singleUpper_factor_le_left {s : ℝ} (hs : (3 / 2 : ℝ) ≤ s) :
    suzukiContinuousUpperFactor s ≤ suzukiContinuousUpperFactor (3 / 2) := by
  have hs1 : 1 < s := by linarith only [hs]
  unfold suzukiContinuousUpperFactor suzukiProposition118SourceTPlus
  apply add_le_add (le_refl (1 : ℝ))
  apply (summable_suzukiProposition118SourceTPlus_of_sourceContract
    jr1965Section13HatSourceContract hs1).tsum_le_tsum
  · intro k
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * k + 1)
      (singleUpper_odd_domain (by norm_num) k) (singleUpper_odd_domain hs1 k) hs
  · exact summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract (by norm_num)

/-- The exact fixed-cutoff normalized canonical upper factor. -/
def currentChenSinglePrimeOrdinaryUpperFactor (s : ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / (417 / 5000 : ℝ)) *
    suzukiContinuousUpperFactor s

theorem continuousOn_currentChenSinglePrimeOrdinaryUpperFactor :
    ContinuousOn currentChenSinglePrimeOrdinaryUpperFactor (Set.Icc (3 / 2 : ℝ) 5) := by
  exact continuousOn_const.mul (continuousOn_currentChen_upperFactor.mono
    (fun s hs => hs.1))

theorem currentChenSinglePrimeOrdinaryUpperFactor_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤ currentChenSinglePrimeOrdinaryUpperFactor s :=
  mul_nonneg (by positivity) (currentChen_upperFactor_nonneg hs)

/-- The normalization is uniform in all actual row parameters of this compact
interval, with the exact cap, actual coefficient and actual integer level. -/
theorem eventually_currentChen_singleUpperRosserDensity_upper
    (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ p : ℕ,
      chenQuotientRosserT B (417 / 5000) N p ∈ Set.Icc (3 / 2 : ℝ) 5 →
        actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N p : ℝ) *
            Real.log (N : ℝ) / singularSeries N ≤
          currentChenSinglePrimeOrdinaryUpperFactor
            (chenQuotientRosserT B (417 / 5000) N p) + epsilon := by
  let A : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant) / (417 / 5000)
  let M : ℝ := suzukiContinuousUpperFactor (3 / 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 ≤ M := currentChen_upperFactor_nonneg (by norm_num)
  let delta : ℝ := min (1 / 2) (epsilon / (2 * (M + A + 1)))
  have hden : 0 < 2 * (M + A + 1) := by linarith
  have hdeltap : 0 < delta := lt_min (by norm_num) (div_pos hepsilon hden)
  have hdelta1 : delta ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcost : delta * (M + A + 1) ≤ epsilon / 2 := by
    have h := (le_div_iff₀ hden).mp
      (show delta ≤ epsilon / (2 * (M + A + 1)) from min_le_right _ _)
    nlinarith only [h]
  obtain ⟨N0, _hN0, hrelative⟩ :=
    exists_currentChen_model_plusDensity_rectangle_upper_threshold
      (417 / 5000) (by norm_num) (3 / 2) (by norm_num) 5 delta hdeltap
  have heuler : ∀ᶠ N : ℕ in atTop, 0 < N ∧ Even N →
      |actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) * Real.log (N : ℝ) / singularSeries N - A| <
        delta := by
    have h := (Metric.tendsto_nhds.mp
      (tendsto_currentChen_actualEuler_fixed_normalized
        (a := (417 / 5000 : ℝ)) (by norm_num))) delta hdeltap
    simpa only [Real.dist_eq, Filter.eventually_inf_principal, Set.mem_ofPred_eq, A] using h
  filter_upwards [eventually_ge_atTop N0, heuler,
    eventually_ge_atTop (2 : ℕ)] with N hN0 heulerN hN
  intro hEven p hs
  let s : ℝ := chenQuotientRosserT B (417 / 5000) N p
  let z : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)
  let cap : ℕ := Nat.ceil z
  let V : ℝ := actualSmallEulerProduct N cap z
  let D : ℝ := actualSmallRosserPlusDensity N cap z ((N : ℝ) ^ (s * (417 / 5000)))
  let e : ℝ := V * Real.log (N : ℝ) / singularSeries N
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hNreal
  have hSS := singularSeries_pos N
  have hV : 0 < V := currentChen_model_actualEuler_pos N cap z hEven
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg hV.le hlog.le) hSS.le
  have he := heulerN ⟨by omega, hEven⟩
  change |e - A| < delta at he
  obtain ⟨helo, hehi⟩ := abs_lt.mp he
  have hr := hrelative N hN0 hEven (417 / 5000) le_rfl s hs.1 hs.2 cap (Nat.le_ceil _)
  change D / V ≤ suzukiContinuousUpperFactor s + delta at hr
  have hmult := mul_le_mul_of_nonneg_right hr he0
  have hcancel : (D / V) * e = D * Real.log (N : ℝ) / singularSeries N := by
    dsimp [e]
    field_simp [hV.ne', hSS.ne']
  rw [hcancel] at hmult
  have hf0 := currentChen_upperFactor_nonneg (show 1 < s by linarith [hs.1])
  have hfM := singleUpper_factor_le_left hs.1
  have hfe := mul_le_mul_of_nonneg_left
    (show e ≤ A + delta by linarith only [hehi]) hf0
  have hdeltaf := mul_le_mul_of_nonneg_right hfM hdeltap.le
  have heA : e ≤ A + 1 := by linarith only [hehi, hdelta1]
  have hdeltae := mul_le_mul_of_nonneg_left heA hdeltap.le
  have hupper : D * Real.log (N : ℝ) / singularSeries N ≤
      A * suzukiContinuousUpperFactor s + epsilon := by
    change suzukiContinuousUpperFactor s ≤ M at hfM
    nlinarith only [hmult, hfe, hdeltaf, hdeltae, hcost, hepsilon]
  have hlevel := currentChen_quotientRosser_rpow_eq B (417 / 5000) (by norm_num) hN p
  change (N : ℝ) ^ (s * (417 / 5000)) = (chenQuotientRosserD B N p : ℝ) at hlevel
  dsimp [D, cap, z] at hupper
  rw [hlevel] at hupper
  exact hupper

end

end ImbalancedChen