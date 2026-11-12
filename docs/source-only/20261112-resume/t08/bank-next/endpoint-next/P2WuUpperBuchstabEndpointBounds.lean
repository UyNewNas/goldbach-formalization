import MathlibNt.Wu2008DoubleSieve.ImprovementCrossLower
import MathlibNt.Wu2008DoubleSieve.PositiveGainActual
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalStrictMargins
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative consequences of the two actual Wu cross inequalities at the
original physical level. The history and its finite certificates are not imports. -/
namespace ImbalancedChen.P2WuUpperBuchstabEndpointBounds

noncomputable section
open Set MeasureTheory Wu2008DoubleSieve
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval

local notation "H" => wuImprovementLimit true
local notation "h" => wuImprovementLimit false

/-- The signed fourth-row core is affine in 2/(1-2δ). Its two proved
endpoint margins give the same strict gain throughout their interval. -/
theorem upper_anchor_one_hundredth {δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/100) :
    (1/300 : ℝ) < H δ (5/2) := by
  let p := SecondFunctionalParameters.row4
  let cost := Omega3ElementaryFeedback.omegaCost p + SecondFunctionalFourSevenths.elementaryCap p
  have hpos : 0 < 1-2*δ := by linarith
  have hzero : (2 : ℝ)/(1-2*0) ≤ 2/(1-2*δ) :=
    div_le_div_of_nonneg_left (by norm_num) hpos (by linarith)
  have hone : (2 : ℝ)/(1-2*δ) ≤ 2/(1-2*(1/100)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hD : (1/60 : ℝ) < SecondFunctionalSignedCore.D p δ := by
    by_cases hc : 0 ≤ cost
    · apply SecondFunctionalStrictMargins.row4_D_larger_delta.trans_le
      unfold SecondFunctionalSignedCore.D
      exact sub_le_sub_left (mul_le_mul_of_nonneg_right hone hc) _
    · have hstart : (1/60 : ℝ) < SecondFunctionalSignedCore.D p 0 :=
        (by norm_num : (1/60 : ℝ) < 1/50).trans SecondFunctionalStrictMargins.row4_D_zero
      apply hstart.trans_le
      unfold SecondFunctionalSignedCore.D
      exact sub_le_sub_left (mul_le_mul_of_nonpos_right hzero (le_of_not_ge hc)) _
  have hcore := SecondFunctionalStrictMargins.actual_core_lower (3 : Fin 4) hd (by linarith)
  change SecondFunctionalSignedCore.D p δ / 5 ≤ H δ SecondFunctionalParameters.row4.s at hcore
  rw [show SecondFunctionalParameters.row4.s = (5/2 : ℝ) by norm_num [SecondFunctionalParameters.row4]] at hcore
  linarith only [hD, hcore]

/-- Lower comparison from v to 7/2, retaining both actual endpoint terms. -/
theorem lower_from_upper_anchor {δ v : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/10)
    (hv : 2 ≤ v) (hv' : v ≤ 7/2) :
    h δ (7/2) + (7/2-v) * ((2/5)*H δ (5/2)) ≤ h δ v := by
  have hdhalf : δ < 1/2 := by linarith
  have hanchor := wuImprovementLimit_nonneg true hd hdhalf
    (by norm_num : (1 : ℝ) ≤ 5/2) (by norm_num : (5/2 : ℝ) ≤ 10)
  have hcross := wuImprovementLimit_lower_cross hd hd' hv hv' (by norm_num : (7/2 : ℝ) ≤ 10)
  rw [show (7/2 : ℝ)-1 = 5/2 by norm_num] at hcross
  have hmass : (∫ u in (v-1)..(5/2 : ℝ), (2/5)*H δ (5/2)) ≤
      ∫ u in (v-1)..(5/2 : ℝ), H δ u / u := by
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (wuImprovementLimit_div_intervalIntegrable true hd hdhalf
        (by linarith) (by linarith) (by norm_num))
    intro u hu
    apply (le_div_iff₀ (by linarith [hu.1] : 0 < u)).2
    calc
      (2/5 * H δ (5/2)) * u ≤ (2/5 * H δ (5/2)) * (5/2) :=
        mul_le_mul_of_nonneg_left hu.2 (mul_nonneg (by norm_num) hanchor)
      _ = H δ (5/2) := by ring
      _ ≤ H δ u := wuImprovementLimit_upper_antitone hd hd'
        ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by norm_num, by norm_num⟩ hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmass
  linarith only [hcross, hmass]

/-- On the common clamp of the low historical cells the two transfers
retain H(9/2), the lower anchor h(7/2), and the upper seed H(5/2). -/
theorem upper_from_two_buchstab {δ s : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/10)
    (hs : 1 ≤ s) (hs' : s ≤ 3) :
    H δ (9/2) + (3/7)*h δ (7/2) + (9/70)*H δ (5/2) ≤ H δ s := by
  let L := h δ (7/2)
  let U := H δ (5/2)
  have hdhalf : δ < 1/2 := by linarith
  have hL : 0 ≤ L := wuImprovementLimit_nonneg false hd hdhalf (by norm_num) (by norm_num)
  have hU : 0 ≤ U := wuImprovementLimit_nonneg true hd hdhalf (by norm_num) (by norm_num)
  have hmass : (∫ v in (2 : ℝ)..(7/2), (2/7)*L + ((4/35)*U)*(7/2-v)) ≤
      ∫ v in (2 : ℝ)..(7/2), h δ v / v := by
    have hcont : Continuous (fun v : ℝ => (2/7)*L + ((4/35)*U)*(7/2-v)) :=
      continuous_const.add (continuous_const.mul (continuous_const.sub continuous_id))
    apply intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
      (wuImprovementLimit_div_intervalIntegrable false hd hdhalf (by norm_num) (by norm_num) (by norm_num))
    intro v hv
    apply (le_div_iff₀ (by linarith [hv.1] : 0 < v)).2
    have hp : 0 ≤ (2/7)*L + ((4/35)*U)*(7/2-v) :=
      add_nonneg (mul_nonneg (by norm_num) hL)
        (mul_nonneg (mul_nonneg (by norm_num) hU) (sub_nonneg.mpr hv.2))
    calc
      ((2/7)*L + ((4/35)*U)*(7/2-v))*v ≤ ((2/7)*L + ((4/35)*U)*(7/2-v))*(7/2) :=
        mul_le_mul_of_nonneg_left hv.2 hp
      _ = L + (7/2-v)*((2/5)*U) := by ring
      _ ≤ h δ v := lower_from_upper_anchor hd hd' hv.1 hv.2
  have hlinear : (∫ v in (2 : ℝ)..(7/2), (7/2 : ℝ)-v) = 9/8 := by
    rw [intervalIntegral.integral_sub (μ := volume) (f := fun _ : ℝ => (7/2 : ℝ))
      (g := fun v : ℝ => v) (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
    norm_num [smul_eq_mul]
  have hcone : (∫ v in (2 : ℝ)..(7/2), (2/7)*L + ((4/35)*U)*(7/2-v)) =
      (3/7)*L + (9/70)*U := by
    rw [intervalIntegral.integral_add (μ := volume) (f := fun _ : ℝ => (2/7)*L)
      (g := fun v : ℝ => ((4/35)*U)*(7/2-v)) (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hlinear]
    simp only [smul_eq_mul]
    ring
  rw [hcone] at hmass
  have hcross := wuImprovementLimit_upper_cross hd hd' (by norm_num : (2 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) ≤ 9/2) (by norm_num : (9/2 : ℝ) ≤ 10)
  rw [show (3 : ℝ)-1 = 2 by norm_num, show (9/2 : ℝ)-1 = 7/2 by norm_num] at hcross
  have hsmono : H δ 3 ≤ H δ s := wuImprovementLimit_upper_antitone hd hd'
    ⟨hs, by linarith⟩ ⟨by norm_num, by norm_num⟩ hs'
  change H δ (9/2) + (3/7)*L + (9/70)*U ≤ H δ s
  linarith only [hmass, hcross, hsmono]

theorem upper_three_full_delta {δ : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/10) :
    (9/350000 : ℝ) ≤ H δ 3 := by
  have hc := upper_from_two_buchstab hd hd' (by norm_num : (1 : ℝ) ≤ 3) le_rfl
  have hseed := positiveGain_actual_upper_range hd hd' (by norm_num : (1 : ℝ) ≤ 5/2)
    (by norm_num : (5/2 : ℝ) ≤ 29/10)
  have hH := wuImprovementLimit_nonneg true hd (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 9/2) (by norm_num : (9/2 : ℝ) ≤ 10)
  have hh := wuImprovementLimit_nonneg false hd (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 7/2) (by norm_num : (7/2 : ℝ) ≤ 10)
  linarith only [hc, hseed, hH, hh]

theorem upper_small_delta {δ s : ℝ} (hd : 0 < δ) (hd' : δ ≤ 1/100)
    (hs : 1 ≤ s) (hs' : s ≤ 3) : (3/7000 : ℝ) < H δ s := by
  have hc := upper_from_two_buchstab hd (by linarith : δ ≤ 1/10) hs hs'
  have hseed := upper_anchor_one_hundredth hd hd'
  have hH := wuImprovementLimit_nonneg true hd (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 9/2) (by norm_num : (9/2 : ℝ) ≤ 10)
  have hh := wuImprovementLimit_nonneg false hd (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 7/2) (by norm_num : (7/2 : ℝ) ≤ 10)
  linarith only [hc, hseed, hH, hh]

/-- One physical source threshold works for all endpoints in [1,3]. The
strict gap at 3 pays for passing to the actual fixed-depth comparisons. -/
theorem small_delta_native_box_counts (k : ℕ) {δ : ℝ}
    (hd : 0 < δ) (hd' : δ ≤ 1/100) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → 4 ≤ N → Even N → ∀ i Δ (V : Fin i → ℝ),
      wuSourceBox (k+1) δ N i Δ V → ∀ s : ℝ, 1 ≤ s → s ≤ 3 →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
        (1-3/7000)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  have hgap := upper_small_delta hd hd' (by norm_num : (1 : ℝ) ≤ 3) le_rfl
  have hdhalf : δ < 1/2 := by linarith
  have hm := wuImprovementLimit_sub_mem true k hd hdhalf (by norm_num : (1 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) ≤ 10) (sub_pos.mpr hgap)
  rw [show H δ 3 - (H δ 3 - 3/7000) = 3/7000 by ring] at hm
  obtain ⟨T,hT⟩ := hm
  refine ⟨T, ?_⟩
  intro N hN hN4 he i Δ V hb s hs hs'
  have hw := wuAdmissibleImprovements_upper_shift hd hdhalf hs hs' hT
  have hAs : wuUpperCoefficient s = 1 := jr1965F_normalized_initial (by linarith) hs'
  have hAt : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) (by norm_num)
  rw [hAs, hAt, add_sub_cancel_right] at hw
  have hcount := hw N hN hN4 he i Δ V hb
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
    (wuUpperCoefficient s-3/7000)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) at hcount
  simpa only [hAs] using hcount

end
end ImbalancedChen.P2WuUpperBuchstabEndpointBounds
