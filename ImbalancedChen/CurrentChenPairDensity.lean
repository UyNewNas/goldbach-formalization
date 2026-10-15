import ImbalancedChen.CurrentChenPairLevelGeometry
import ImbalancedChen.ActualRosserCompactAnalyticBounds
import ImbalancedChen.ActualCompactEulerNormalization
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiContinuousLowerFactorSecondInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePTail
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
# One-sided actual current pair-row density suppliers

Only lower means are needed. The proved analytic rectangle lower bound
for the same actual coefficient, together with the proved uniform Euler
normalization, supplies a normalized lower bound directly. No opposite
bound, finite odd-box reconstruction, or density limit is assumed.

The actual rounded row level is recovered exactly from its logarithmic
coordinate. The entire fifth selector supplies its compact interval gate.
This source candidate requires actual Lean and kernel verification.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open Classical
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The logarithmic coordinate recovers the very same natural row level. -/
theorem currentChen_quotientRosser_rpow_eq (B a : ℝ) (ha : 0 < a)
    {N : ℕ} (hN : 2 ≤ N) (b : ℕ) :
    (N : ℝ) ^ (chenQuotientRosserT B a N b * a) =
      (chenQuotientRosserD B N b : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN1).ne'
  have hDp : (0 : ℝ) < chenQuotientRosserD B N b := by
    unfold chenQuotientRosserD chenQuotientRowLevel
    positivity
  have hexponent : chenQuotientRosserT B a N b * a =
      Real.log (chenQuotientRosserD B N b : ℝ) / Real.log (N : ℝ) := by
    unfold chenQuotientRosserT
    rw [Real.log_rpow hNp a]
    field_simp [ha.ne', hlog]
    ring
  rw [hexponent, Real.rpow_def_of_pos hNp, mul_div_cancel₀ _ hlog, Real.exp_log hDp]

private theorem currentChen_lowerFactor_firstInterval (s : ℝ)
    (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    suzukiContinuousLowerFactor s =
      2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract hs hs4,
    suzukiLowerSieveFactorFirstInterval_eq_log hs hs4,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]

private theorem currentChen_normalized_lower_factor_first_interval
    (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    (2 * Real.exp (-Real.eulerMascheroniConstant) / (417 / 5000 : ℝ)) *
        suzukiContinuousLowerFactor s =
      4 * Real.log (s - 1) / (s * (417 / 5000)) := by
  rw [currentChen_lowerFactor_firstInterval s hs hs4, Real.exp_neg]
  field_simp
  ring

private theorem currentChen_lowerFactor_firstInterval_bounds
    {s : ℝ} (hs : s ∈ Set.Icc (2 : ℝ) 4) :
    0 ≤ suzukiContinuousLowerFactor s ∧
      suzukiContinuousLowerFactor s ≤
        2 * Real.exp Real.eulerMascheroniConstant * Real.log 3 := by
  have hl0 : 0 ≤ Real.log (s - 1) := Real.log_nonneg (by linarith [hs.1])
  have hl3 : Real.log (s - 1) ≤ Real.log 3 :=
    Real.log_le_log (by linarith [hs.1]) (by linarith [hs.2])
  rw [currentChen_lowerFactor_firstInterval s hs.1 hs.2]
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) hl0) (by linarith [hs.1])
  · exact (div_le_self (mul_nonneg (by positivity) hl0)
      (by linarith [hs.1])).trans (mul_le_mul_of_nonneg_left hl3 (by positivity))

/-- The analytic rectangle theorem and Euler normalization supply this
uniform normalized lower estimate at the actual rounded row level. -/
theorem eventually_currentChen_quotientRosserDensity_lower
    (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ b : ℕ,
      chenQuotientRosserT B (417 / 5000) N b ∈ Set.Icc (2 : ℝ) 4 →
      4 * Real.log (chenQuotientRosserT B (417 / 5000) N b - 1) /
          (chenQuotientRosserT B (417 / 5000) N b * (417 / 5000)) - epsilon ≤
        actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N b : ℝ) *
            Real.log (N : ℝ) / singularSeries N := by
  let A : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant) / (417 / 5000)
  let M : ℝ := 2 * Real.exp Real.eulerMascheroniConstant * Real.log 3
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by positivity) (Real.log_pos (by norm_num)).le
  let delta : ℝ := min (1 / 2) (epsilon / (2 * (M + A + 1)))
  have hden : 0 < 2 * (M + A + 1) := by linarith
  have hdeltap : 0 < delta := lt_min (by norm_num) (div_pos hepsilon hden)
  have hdelta1 : delta ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcost : delta * (M + A + 1) ≤ epsilon / 2 := by
    have h := (le_div_iff₀ hden).mp
      (show delta ≤ epsilon / (2 * (M + A + 1)) from min_le_right _ _)
    nlinarith only [h]
  obtain ⟨N0, _hN0, hrelative⟩ :=
    exists_actualSmallRosserMinusDensity_rectangle_lower_threshold
      (417 / 5000) (by norm_num) 2 le_rfl 4 delta hdeltap
  let S : Set (ℝ × ℝ) := ({(417 / 5000 : ℝ)} : Set ℝ) ×ˢ Set.Icc (2 : ℝ) 4
  have hS : IsCompact S := isCompact_singleton.prod isCompact_Icc
  have hpos : ∀ p ∈ S, 0 < p.1 := by
    intro p hp
    have h := Set.mem_singleton_iff.mp hp.1
    rw [h]
    norm_num
  obtain ⟨N1, _hN1, heuler⟩ :=
    exists_actualSmallEulerProduct_compact_uniform_threshold S hS hpos delta hdeltap
  filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop N1,
    eventually_ge_atTop (2 : ℕ)] with N hN0 hN1 hN
  intro hEven b hs
  let s : ℝ := chenQuotientRosserT B (417 / 5000) N b
  let z : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)
  let cap : ℕ := Nat.ceil z
  let V : ℝ := actualSmallEulerProduct N cap z
  let D : ℝ := actualSmallRosserMinusDensity N cap z ((N : ℝ) ^ (s * (417 / 5000)))
  let e : ℝ := V * Real.log (N : ℝ) / singularSeries N
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hNreal
  have hSS := singularSeries_pos N
  have hV : 0 < V := actualSmallEulerProduct_pos N cap z hEven
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg hV.le hlog.le) hSS.le
  have hpoint : ((417 / 5000 : ℝ), s) ∈ S := ⟨rfl, hs⟩
  have he := heuler N hN1 hEven ((417 / 5000 : ℝ), s) hpoint cap (Nat.le_ceil _)
  change |e - A| < delta at he
  obtain ⟨helo, hehi⟩ := abs_lt.mp he
  have hr := hrelative N hN0 hEven (417 / 5000) le_rfl s hs.1 hs.2 cap (Nat.le_ceil _)
  change suzukiContinuousLowerFactor s - delta ≤ D / V at hr
  have hmult := mul_le_mul_of_nonneg_right hr he0
  have hcancel : (D / V) * e = D * Real.log (N : ℝ) / singularSeries N := by
    dsimp [e]
    field_simp [hV.ne', hSS.ne']
    ring
  rw [hcancel] at hmult
  obtain ⟨hf0, hfM⟩ := currentChen_lowerFactor_firstInterval_bounds hs
  have hfe := mul_le_mul_of_nonneg_left
    (show A - delta ≤ e by linarith only [helo]) hf0
  have hdeltaf := mul_le_mul_of_nonneg_right hfM hdeltap.le
  have heA : e ≤ A + 1 := by linarith only [hehi, hdelta1]
  have hdeltae := mul_le_mul_of_nonneg_left heA hdeltap.le
  have hlower : A * suzukiContinuousLowerFactor s - epsilon ≤
      D * Real.log (N : ℝ) / singularSeries N := by
    change suzukiContinuousLowerFactor s ≤ M at hfM
    nlinarith only [hmult, hfe, hdeltaf, hdeltae, hcost, hepsilon]
  rw [show A * suzukiContinuousLowerFactor s =
    4 * Real.log (s - 1) / (s * (417 / 5000)) from
      currentChen_normalized_lower_factor_first_interval s hs.1 hs.2] at hlower
  have hlevel := currentChen_quotientRosser_rpow_eq B (417 / 5000) (by norm_num) hN b
  change (N : ℝ) ^ (s * (417 / 5000)) = (chenQuotientRosserD B N b : ℝ) at hlevel
  dsimp [D, cap, z] at hlower
  rw [hlevel] at hlower
  exact hlower

/-- The entire fifth selector supplies the compact numerical gate. -/
theorem eventually_currentChenUpsilon5_ordinary_row_density_lower
    (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ t ∈
      chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ)),
      4 * Real.log (chenQuotientRosserT B (417 / 5000) N (t.1 * t.2) - 1) /
          (chenQuotientRosserT B (417 / 5000) N (t.1 * t.2) * (417 / 5000)) - epsilon ≤
        actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
            Real.log (N : ℝ) / singularSeries N := by
  filter_upwards [eventually_currentChen_quotientRosserDensity_lower B epsilon hepsilon,
    eventually_currentChenUpsilon5_row_first_interval B] with N hdensity hinterval
  intro hEven t ht
  have hs := hinterval t ht
  exact hdensity hEven (t.1 * t.2) ⟨by linarith [hs.1], hs.2.le⟩

end

end ImbalancedChen
