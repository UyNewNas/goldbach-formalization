import ImbalancedChen.ActualRosserResidualDensity
import ImbalancedChen.ActualRosserCubeReduction
import ImbalancedChen.ActualThirdPrefixTailIntegralCore

/-! Uniform one-sided payment for both signed differences on the lower
tree. A change of level compares two literal densities below the same
prime ceiling. The upper formula includes the endpoint where the original
residual ratio is one, using exact first-cube reduction to ratio three. -/

namespace ImbalancedChen.P3OriginalU5ResidualComparison

noncomputable section

open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

private def amplitude : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant)

private theorem amplitude_pos : 0 < amplitude := mul_pos (by norm_num) (Real.exp_pos _)

private theorem upper_factor_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤ suzukiContinuousUpperFactor s := by
  have h : 0 ≤ suzukiProposition118SourceTPlus s :=
    tsum_nonneg (suzukiLayer_one_two_odd_nonneg hs)
  change 0 ≤ 1 + suzukiProposition118SourceTPlus s
  linarith only [h]

private theorem upper_factor_antitone {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    suzukiContinuousUpperFactor y ≤ suzukiContinuousUpperFactor x := by
  have hx1 : 1 < x := by linarith only [hx]
  have hy1 : 1 < y := hx1.trans_le hxy
  have h : suzukiProposition118SourceTPlus y ≤ suzukiProposition118SourceTPlus x := by
    apply Summable.tsum_le_tsum _
      (summable_suzukiProposition118SourceTPlus_of_sourceContract
        jr1965Section13HatSourceContract hy1)
      (summable_suzukiProposition118SourceTPlus_of_sourceContract
        jr1965Section13HatSourceContract hx1)
    intro k
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * k + 1)
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain]; linarith)
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain]; linarith) hxy
  change 1 + suzukiProposition118SourceTPlus y ≤ 1 + suzukiProposition118SourceTPlus x
  linarith only [h]

private def upperCutoff (u beta : ℝ) : ℝ := min u (beta / 3)
private def upperRatio (u beta : ℝ) : ℝ := max 3 (beta / u)

private theorem upper_level_exact {u beta : ℝ} (hu : 0 < u) :
    upperRatio u beta * upperCutoff u beta = beta := by
  by_cases h : beta ≤ 3 * u
  · rw [upperCutoff, upperRatio, min_eq_right (by linarith : beta / 3 ≤ u),
      max_eq_left ((div_le_iff₀ hu).mpr h)]
    ring
  · rw [upperCutoff, upperRatio, min_eq_left (by linarith : u ≤ beta / 3),
      max_eq_right ((le_div_iff₀ hu).mpr (le_of_not_ge h))]
    exact div_mul_cancel₀ _ hu.ne'

private theorem upper_density_exact (N cap : ℕ) (hN : (1 : ℝ) < N) (u beta : ℝ) :
    actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) =
      actualSmallRosserPlusDensity N cap ((N : ℝ) ^ upperCutoff u beta) ((N : ℝ) ^ beta) := by
  by_cases h : beta ≤ 3 * u
  · rw [upperCutoff, min_eq_right (by linarith : beta / 3 ≤ u)]
    exact actualSmallRosserPlusDensity_power_eq_cubeCutoff N cap hN h
  · rw [upperCutoff, min_eq_left (by linarith : u ≤ beta / 3)]

private theorem ratio_upper {d u beta : ℝ} (hd : 0 < d) (hdu : d ≤ u) (hb : beta ≤ 1) :
    beta / u ≤ 1 / d :=
  (div_le_div_of_nonneg_right hb (hd.trans_le hdu).le).trans
    (div_le_div_of_nonneg_left zero_le_one hd hdu)

private theorem upper_profile_antitone {u O M : ℝ} (hu : 0 < u) (huO : u ≤ O) (hOM : O ≤ M) :
    amplitude / upperCutoff u M * suzukiContinuousUpperFactor (upperRatio u M) ≤
      amplitude / upperCutoff u O * suzukiContinuousUpperFactor (upperRatio u O) := by
  have hc : upperCutoff u O ≤ upperCutoff u M :=
    min_le_min le_rfl (div_le_div_of_nonneg_right hOM (by norm_num))
  have hr : upperRatio u O ≤ upperRatio u M :=
    max_le_max le_rfl (div_le_div_of_nonneg_right hOM hu.le)
  have hco : 0 < upperCutoff u O := lt_min hu (div_pos (hu.trans_le huO) (by norm_num))
  have hden := div_le_div_of_nonneg_left amplitude_pos.le hco hc
  have hf := upper_factor_antitone (le_max_left 3 (O / u)) hr
  have hM : 1 < upperRatio u M := (by norm_num : (1 : ℝ) < 3).trans_le (le_max_left _ _)
  exact mul_le_mul hden hf (upper_factor_nonneg hM) (div_nonneg amplitude_pos.le hco.le)

private theorem raw_difference {N : ℕ} (hN : (1 : ℝ) < N) {eta x y X Y : ℝ}
    (hx : |x * Real.log (N : ℝ) / singularSeries N - X| < eta / 2)
    (hy : |y * Real.log (N : ℝ) / singularSeries N - Y| < eta / 2) (hYX : Y ≤ X) :
    -eta * singularSeries N / Real.log (N : ℝ) ≤ x - y := by
  have h : -eta ≤ (x - y) * Real.log (N : ℝ) / singularSeries N := by
    rw [sub_mul, sub_div]
    linarith only [(abs_lt.mp hx).1, (abs_lt.mp hy).2, hYX]
  exact (div_le_iff₀ (Real.log_pos hN)).mpr ((le_div_iff₀ (singularSeries_pos N)).mp h)

/-- The negative prefix sign at an odd full rank gives upper parent minus
child. The positive prefix sign at an even full rank gives lower child minus
parent. Both directions have one threshold before the exponents and caps. -/
theorem exists_ordinary_residual_comparison (d eta : ℝ) (hd : 0 < d) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      ∀ u O M : ℝ, d ≤ u → u ≤ O → O ≤ M → M ≤ 1 →
        ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
          (-eta * singularSeries N / Real.log (N : ℝ) ≤
            actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ O) -
              actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ M)) ∧
          (2 * u ≤ O → -eta * singularSeries N / Real.log (N : ℝ) ≤
            actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ M) -
              actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ O)) := by
  let U : Set (ℝ × ℝ) := Set.Icc (d / 3) 1 ×ˢ Set.Icc (3 : ℝ) (max 3 (1 / d))
  let L : Set (ℝ × ℝ) := Set.Icc d 1 ×ˢ Set.Icc (2 : ℝ) (1 / d)
  have hU : IsCompact U := isCompact_Icc.prod isCompact_Icc
  have hL : IsCompact L := isCompact_Icc.prod isCompact_Icc
  have hparU (p : ℝ × ℝ) (hp : p ∈ U) : 0 < p.1 ∧ 1 < p.2 :=
    ⟨(div_pos hd (by norm_num : (0 : ℝ) < 3)).trans_le hp.1.1,
      (by norm_num : (1 : ℝ) < 3).trans_le hp.2.1⟩
  have hparL (p : ℝ × ℝ) (hp : p ∈ L) : 0 < p.1 ∧ 2 ≤ p.2 := ⟨hd.trans_le hp.1.1, hp.2.1⟩
  obtain ⟨U0, hU0, hupper⟩ :=
    exists_actualSmallRosserPlusDensity_compact_normalized_threshold U hU hparU (eta / 2) (half_pos heta)
  obtain ⟨L0, _, hlower⟩ :=
    exists_actualSmallRosserMinusDensity_compact_normalized_threshold L hL hparL (eta / 2) (half_pos heta)
  refine ⟨max U0 L0, hU0.trans (le_max_left _ _), ?_⟩
  intro N hN hEven u O M hdu huO hOM hM cap hcap
  have hu : 0 < u := hd.trans_le hdu
  have hu₁ : u ≤ 1 := huO.trans (hOM.trans hM)
  have hN2 : 2 ≤ N := hU0.trans ((le_max_left _ _).trans hN)
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hup (beta : ℝ) (hub : u ≤ beta) (hb : beta ≤ 1) :
      |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) *
        Real.log (N : ℝ) / singularSeries N -
          amplitude / upperCutoff u beta * suzukiContinuousUpperFactor (upperRatio u beta)| < eta / 2 := by
    have hp : (upperCutoff u beta, upperRatio u beta) ∈ U := by
      refine ⟨⟨le_min (by linarith only [hd, hdu]) (by linarith only [hdu, hub]),
        (min_le_left _ _).trans hu₁⟩, le_max_left _ _, ?_⟩
      exact max_le_max le_rfl (ratio_upper hd hdu hb)
    have hcov : (N : ℝ) ^ upperCutoff u beta ≤ (cap : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hNr.le (min_le_left _ _)).trans hcap
    have hh := hupper N ((le_max_left _ _).trans hN) hEven _ hp cap hcov
    change |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ upperCutoff u beta)
        ((N : ℝ) ^ (upperRatio u beta * upperCutoff u beta)) * Real.log (N : ℝ) /
          singularSeries N - amplitude / upperCutoff u beta *
            suzukiContinuousUpperFactor (upperRatio u beta)| < eta / 2 at hh
    rwa [upper_level_exact hu, ← upper_density_exact N cap hNr u beta] at hh
  refine ⟨raw_difference hNr (hup O huO (hOM.trans hM)) (hup M (huO.trans hOM) hM)
    (upper_profile_antitone hu huO hOM), ?_⟩
  intro htwo
  have hlow (beta : ℝ) (hub : 2 * u ≤ beta) (hb : beta ≤ 1) :
      |actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ beta) *
        Real.log (N : ℝ) / singularSeries N -
          amplitude / u * suzukiContinuousLowerFactor (beta / u)| < eta / 2 := by
    have hp : (u, beta / u) ∈ L :=
      ⟨⟨hdu, hu₁⟩, (le_div_iff₀ hu).mpr hub, ratio_upper hd hdu hb⟩
    have hh := hlower N ((le_max_right _ _).trans hN) hEven _ hp cap hcap
    change |actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (beta / u * u)) *
      Real.log (N : ℝ) / singularSeries N -
        amplitude / u * suzukiContinuousLowerFactor (beta / u)| < eta / 2 at hh
    rwa [div_mul_cancel₀ _ hu.ne'] at hh
  have hmono := thirdTail_lowerFactor_monotone ((le_div_iff₀ hu).mpr htwo)
    ((le_div_iff₀ hu).mpr (htwo.trans hOM)) (div_le_div_of_nonneg_right hOM hu.le)
  exact raw_difference hNr (hlow M (htwo.trans hOM) hM) (hlow O htwo (hOM.trans hM))
    (mul_le_mul_of_nonneg_left hmono (div_nonneg amplitude_pos.le hu.le))

end

end ImbalancedChen.P3OriginalU5ResidualComparison
