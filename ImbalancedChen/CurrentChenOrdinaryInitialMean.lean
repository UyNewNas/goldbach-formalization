import ImbalancedChen.CurrentChenRosserLowerRectangle
import ImbalancedChen.CurrentChenFixedEulerNormalization
import ImbalancedChen.CurrentChenInitialRosserRemainder
import ImbalancedChen.ChenLogLevelGeometry
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The actual ordinary first Chen mean at its full BV level

The level is the literal Q+1 with Q=floor(sqrt N/(log N)^B).
Its logarithmic parameter tends to 1/(2a), rather than being replaced by
the first-interval lower factor. The genuine canonical source series gives
continuity there. All rounding, the full primitive AP error and the complete
centre correction are paid by proved suppliers. This ordinary initial mean
does not assert the stronger causal improvement or the complete hLower.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

private theorem ordinaryInitial_lowerFactor_continuousOn :
    ContinuousOn suzukiContinuousLowerFactor (Set.Ici 2) := by
  have hbound (k : ℕ) (s : ℝ) (hs : s ∈ Set.Ici (2 : ℝ)) :
      ‖suzukiLayer 1 2 (2 * (k + 1)) s‖ ≤
        suzukiLayer 1 2 (2 * (k + 1)) 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (suzukiLayer_one_two_even_nonneg hs k)]
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * (k + 1))
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain])
      (by simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hs) hs
  have hcont (k : ℕ) :
      ContinuousOn (suzukiLayer 1 2 (2 * (k + 1))) (Set.Ici 2) := by
    apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num) (2 * (k + 1))).mono
    intro s hs
    simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hs
  exact continuousOn_const.sub (continuousOn_tsum hcont
    (summable_suzukiProposition118SourceTMinus_of_sourceContract
      jr1965Section13HatSourceContract (by norm_num : (2 : ℝ) ≤ 2)) hbound)

/-- The ordinary constant at the genuine limiting ratio, including a ratio
above four. This is the canonical factor, not its first-interval formula. -/
def currentChenOrdinaryInitialConstant (a : ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / a) *
    suzukiContinuousLowerFactor (1 / (2 * a))

private theorem ordinaryInitial_rpow_eq (B a : ℝ) (ha : 0 < a)
    {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ^ (chenInitialRosserT B a N * a) = (chenInitialRosserD B N : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
  have hDp : (0 : ℝ) < chenInitialRosserD B N := by
    unfold chenInitialRosserD
    positivity
  have hexponent : chenInitialRosserT B a N * a =
      Real.log (chenInitialRosserD B N : ℝ) / Real.log (N : ℝ) := by
    unfold chenInitialRosserT
    rw [Real.log_rpow hNp a]
    field_simp [ha.ne', hlog]
  rw [hexponent, Real.rpow_def_of_pos hNp, mul_div_cancel₀ _ hlog, Real.exp_log hDp]

/-- Uniform density lower bound at the actual natural level Q+1. The
ordinary BV logarithmic exponent is arbitrary and fixed before N. -/
theorem eventually_currentChen_initial_density_normalized_lower
    (B a : ℝ) (hB : 0 ≤ B) (ha : 0 < a) (haQuarter : a < 1 / 4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenOrdinaryInitialConstant a - epsilon ≤
        actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ a))
          ((N : ℝ) ^ a) (chenInitialRosserD B N : ℝ) *
            Real.log (N : ℝ) / singularSeries N := by
  let A : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant) / a
  let s0 : ℝ := 1 / (2 * a)
  let eta : ℝ := epsilon / (2 * (A + 1))
  have hA : 0 < A := by dsimp [A]; positivity
  have heta : 0 < eta := div_pos hepsilon (by positivity)
  have hs0 : 2 < s0 := by
    dsimp [s0]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mpr
    nlinarith only [haQuarter]
  have hf : Tendsto (fun N => suzukiContinuousLowerFactor (chenInitialRosserT B a N))
      atTop (𝓝 (suzukiContinuousLowerFactor s0)) :=
    (ordinaryInitial_lowerFactor_continuousOn.continuousAt
      (Ici_mem_nhds hs0)).tendsto.comp (tendsto_chenInitialRosserT B ha)
  let e := fun N : ℕ => actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ a))
    ((N : ℝ) ^ a) * Real.log (N : ℝ) / singularSeries N
  have he : Tendsto e (atTop ⊓ principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 A) :=
    tendsto_currentChen_actualEuler_fixed_normalized ha
  have hnear : ∀ᶠ N : ℕ in atTop, 0 < N ∧ Even N →
      currentChenOrdinaryInitialConstant a - epsilon / 2 <
        suzukiContinuousLowerFactor (chenInitialRosserT B a N) * e N := by
    have hlt : currentChenOrdinaryInitialConstant a - epsilon / 2 <
        suzukiContinuousLowerFactor s0 * A := by
      dsimp [currentChenOrdinaryInitialConstant, A, s0]
      nlinarith only [hepsilon]
    have h := ((hf.mono_left inf_le_left).mul he).eventually
      (Ioi_mem_nhds hlt)
    simpa only [Filter.eventually_inf_principal, Set.mem_ofPred_eq] using h
  have hebound : ∀ᶠ N : ℕ in atTop, 0 < N ∧ Even N → e N < A + 1 := by
    have h := he.eventually (Iio_mem_nhds (lt_add_one A))
    simpa only [Filter.eventually_inf_principal, Set.mem_ofPred_eq] using h
  have hsupper : ∀ᶠ N : ℕ in atTop, chenInitialRosserT B a N < s0 + 1 :=
    (tendsto_chenInitialRosserT B ha).eventually (Iio_mem_nhds (lt_add_one s0))
  obtain ⟨N0, _hN0, hrelative⟩ :=
    exists_currentChen_model_minusDensity_rectangle_lower_threshold
      a ha 2 le_rfl (s0 + 1) eta heta
  obtain ⟨N1, hgates⟩ := exists_chenInitialRosser_numeric_gates B a hB ha haQuarter
  filter_upwards [hnear, hebound, hsupper, eventually_ge_atTop N0,
    eventually_ge_atTop N1, eventually_ge_atTop (2 : ℕ)]
    with N hnearN heboundN hsN hN0 hN1 hN
  intro hEven
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hV : 0 < actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a) :=
    currentChen_model_actualEuler_pos N _ _ hEven
  have he0 : 0 ≤ e N :=
    div_nonneg (mul_nonneg hV.le (Real.log_pos hNreal).le) (singularSeries_pos N).le
  have hr := hrelative N hN0 hEven a le_rfl (chenInitialRosserT B a N)
    (hgates N hN1).2.2.1 hsN.le (Nat.ceil ((N : ℝ) ^ a)) (Nat.le_ceil _)
  rw [ordinaryInitial_rpow_eq B a ha hN] at hr
  have hmult := mul_le_mul_of_nonneg_right hr he0
  have hcancel :
      (actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a)
        (chenInitialRosserD B N : ℝ) /
          actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a)) * e N =
        actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a)
          (chenInitialRosserD B N : ℝ) * Real.log (N : ℝ) / singularSeries N := by
    dsimp [e]
    field_simp [hV.ne', (singularSeries_pos N).ne']
  rw [hcancel] at hmult
  have hcost : eta * (A + 1) = epsilon / 2 := by
    dsimp [eta]
    field_simp [show A + 1 ≠ 0 by positivity]
  have hcostN := mul_le_mul_of_nonneg_left (heboundN ⟨hNpos, hEven⟩).le heta.le
  have hmain := hnearN ⟨hNpos, hEven⟩
  nlinarith only [hmult, hcostN, hcost, hmain]

/-- An unconditional ordinary lower mean for the genuine sifted additive
prime receiver count, with its full physical BV support and all errors paid. -/
theorem eventually_currentChen_sifted_ge_ordinary_initial_mean
    (a : ℝ) (ha : 0 < a) (haQuarter : a < 1 / 4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentChenOrdinaryInitialConstant a - epsilon) * singularNormalization N ≤
        ((chenSiftedPrimeSource N ((N : ℝ) ^ a)).card : ℝ) := by
  by_cases hC : 0 < currentChenOrdinaryInitialConstant a
  · obtain ⟨B, hB, hpaid⟩ := eventually_currentChen_initialRosser_density_lower
    let delta : ℝ := min (epsilon / 2) (currentChenOrdinaryInitialConstant a / 2)
    have hdeltap : 0 < delta := lt_min (half_pos hepsilon) (half_pos hC)
    have hdeltae : delta ≤ epsilon / 2 := min_le_left _ _
    have hdeltaC : delta ≤ currentChenOrdinaryInitialConstant a / 2 := min_le_right _ _
    obtain ⟨N0, hgates⟩ := exists_chenInitialRosser_numeric_gates B a hB ha haQuarter
    filter_upwards [eventually_currentChen_initial_density_normalized_lower
      B a hB ha haQuarter delta hdeltap, hpaid (epsilon / 2) (half_pos hepsilon),
      eventually_ge_atTop N0, eventually_ge_atTop (2 : ℕ)]
      with N hnorm hpaidN hN0 hN
    intro hEven
    have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlogp := Real.log_pos hNreal
    have hSSp := singularSeries_pos N
    have hH : 0 ≤ singularNormalization N :=
      div_nonneg (mul_nonneg hSSp.le (Nat.cast_nonneg N)) (sq_nonneg _)
    let D : ℝ := actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ a))
      ((N : ℝ) ^ a) (chenInitialRosserD B N : ℝ)
    have hdensity : currentChenOrdinaryInitialConstant a - delta ≤
        D * Real.log (N : ℝ) / singularSeries N := hnorm hEven
    have hD0 : 0 ≤ D := by
      have hn : 0 < D * Real.log (N : ℝ) / singularSeries N :=
        (show 0 < currentChenOrdinaryInitialConstant a - delta by linarith).trans_le hdensity
      exact ((mul_pos_iff_of_pos_right hlogp).mp
        ((div_pos_iff_of_pos_right hSSp).mp hn)).le
    have hli : (N : ℝ) / Real.log (N : ℝ) ≤ trueLogarithmicIntegral N :=
      MathlibNt.SieveTheory.LiuWeight.div_log_le_liuLogarithmicIntegral
        (by exact_mod_cast hN)
    have hmain : (currentChenOrdinaryInitialConstant a - delta) *
        singularNormalization N ≤ trueLogarithmicIntegral N * D := by
      calc
        _ ≤ (D * Real.log (N : ℝ) / singularSeries N) * singularNormalization N :=
          mul_le_mul_of_nonneg_right hdensity hH
        _ = ((N : ℝ) / Real.log (N : ℝ)) * D := by
          unfold singularNormalization
          field_simp [hSSp.ne', hlogp.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_right hli hD0
    have hlevel : (chenInitialRosserD B N : ℝ) = (chenInitialLevelCap B N : ℝ) + 1 := by
      simp only [chenInitialRosserD, Nat.cast_add, Nat.cast_one]
    have hQ : chenInitialLevelCap B N ≤ panModulusCutoff N B := by
      unfold chenInitialLevelCap panModulusCutoff
      rw [Real.sqrt_eq_rpow]
    have hL : (1 : ℝ) < chenInitialRosserD B N := by
      exact_mod_cast (show 1 < chenInitialRosserD B N from lt_of_lt_of_le (by decide) (hgates N hN0).1)
    have hzL : (N : ℝ) ^ a ≤ (chenInitialRosserD B N : ℝ) := by
      rw [← ordinaryInitial_rpow_eq B a ha hN]
      exact Real.rpow_le_rpow_of_exponent_le hNreal.le
        (by nlinarith only [(hgates N hN0).2.2.1, ha])
    have hfinite := hpaidN (chenInitialLevelCap B N) hQ
      (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a) (chenInitialRosserD B N : ℝ)
      (Nat.le_ceil _) hL hzL hlevel.le
    change trueLogarithmicIntegral N * D - (epsilon / 2) * singularNormalization N ≤ _ at hfinite
    have hbudget := mul_le_mul_of_nonneg_right hdeltae hH
    nlinarith only [hmain, hfinite, hbudget]
  · apply Eventually.of_forall
    intro N _hEven
    have hH : 0 ≤ singularNormalization N :=
      div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith :
      currentChenOrdinaryInitialConstant a - epsilon ≤ 0) hH).trans (Nat.cast_nonneg _)

end

end ImbalancedChen
