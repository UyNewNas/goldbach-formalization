import ImbalancedChen.P5U7PrimeCutoffFubini

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An explicit LINEAR prime collar rate, derived from the actual cutoff
rows and global kernel bound. It holds for every nonnegative eta, with
empty rows clamped exactly. No derivative or smoothness premise is used.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeCollarRow (eta t : ℝ) : ℝ :=
  ∫ u in max t ((1-t)/(2+eta))..((1-t)/2), p5U7PrimeEtaExtension ![t,u]

def p5U7PrimeCollarConstant : ℝ :=
  ((1/3 : ℝ)-(59/250 : ℝ)) * (1/(59/250 : ℝ)^3) / 4

theorem p5U7PrimeEtaProduct_continuous :
    Continuous (fun p : ℝ × ℝ => p5U7PrimeEtaExtension ![p.1,p.2]) := by
  apply continuous_p5U7PrimeEtaExtension.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

/-- Actual continuous endpoint functions give moving prime-row continuity. -/
theorem p5U7Prime_interval_row_continuous (a b : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun t : ℝ => ∫ u in a t..b t, p5U7PrimeEtaExtension ![t,u]) := by
  have hf := p5U7PrimeEtaProduct_continuous
  have hu : Continuous (fun t : ℝ => ∫ u in (0 : ℝ)..b t, p5U7PrimeEtaExtension ![t,u]) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf hb
  have hl : Continuous (fun t : ℝ => ∫ u in (0 : ℝ)..a t, p5U7PrimeEtaExtension ![t,u]) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf ha
  have heq : (fun t : ℝ => ∫ u in a t..b t, p5U7PrimeEtaExtension ![t,u]) =
      fun t : ℝ => (∫ u in (0 : ℝ)..b t, p5U7PrimeEtaExtension ![t,u]) -
        ∫ u in (0 : ℝ)..a t, p5U7PrimeEtaExtension ![t,u] := by
    funext t
    exact (intervalIntegral.integral_interval_sub_left
      ((hf.uncurry_left t).intervalIntegrable 0 (b t))
      ((hf.uncurry_left t).intervalIntegrable 0 (a t))).symm
  rw [heq]
  exact hu.sub hl

theorem continuous_p5U7PrimeCutoffRow (eta : ℝ) : Continuous (p5U7PrimeCutoffRow eta) :=
  p5U7Prime_interval_row_continuous _ _ continuous_id
    (continuous_id.max ((continuous_const.sub continuous_id).div_const (2+eta)))

theorem continuous_p5U7PrimeCollarRow (eta : ℝ) : Continuous (p5U7PrimeCollarRow eta) :=
  p5U7Prime_interval_row_continuous _ _
    (continuous_id.max ((continuous_const.sub continuous_id).div_const (2+eta)))
    ((continuous_const.sub continuous_id).div_const 2)

/-- The removed actual inner interval has width at most eta/4.
The max handles the entire removed row when the cutoff falls below t. -/
theorem p5U7PrimeCollar_width {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 ≤ (1-t)/2-max t ((1-t)/(2+eta)) ∧
      (1-t)/2-max t ((1-t)/(2+eta)) ≤ eta/4 := by
  have hden : 0 < 2+eta := by linarith
  have hcap := p5U7PrimeCutoff_cap_le heta ht
  have hmax : max t ((1-t)/(2+eta)) ≤ (1-t)/2 :=
    max_le (by linarith [ht.2]) hcap
  have hraw : (1-t)/2-(1-t)/(2+eta) ≤ eta/4 := by
    have hid : (1-t)/2-(1-t)/(2+eta) = ((1-t)*eta)/(2*(2+eta)) := by
      field_simp [hden.ne']
      <;> ring
    rw [hid]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(2+eta))).mpr
    have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 59/250).trans ht.1
    nlinarith [mul_nonneg heta ht0,sq_nonneg eta]
  exact ⟨sub_nonneg.mpr hmax,by linarith only [hraw,le_max_right t ((1-t)/(2+eta))]⟩

theorem p5U7PrimeEtaExtension_nonneg (x : Fin 2 → ℝ) :
    0 ≤ p5U7PrimeEtaExtension x := by
  unfold p5U7PrimeEtaExtension
  positivity

/-- The actual collar row is positive and paid by the explicit kernel
bound times its proved width. No interval-integrability assumption occurs. -/
theorem p5U7PrimeCollarRow_bounds {eta t : ℝ} (heta : 0 ≤ eta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 ≤ p5U7PrimeCollarRow eta t ∧
      p5U7PrimeCollarRow eta t ≤ (1/(59/250 : ℝ)^3)*(eta/4) := by
  have hw := p5U7PrimeCollar_width heta ht
  have hlu : max t ((1-t)/(2+eta)) ≤ (1-t)/2 := sub_nonneg.mp hw.1
  have hnonneg : 0 ≤ p5U7PrimeCollarRow eta t := by
    apply intervalIntegral.integral_nonneg hlu
    intro u _
    exact p5U7PrimeEtaExtension_nonneg ![t,u]
  have hn : ‖p5U7PrimeCollarRow eta t‖ ≤
      (1/(59/250 : ℝ)^3)*|((1-t)/2)-max t ((1-t)/(2+eta))| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u _
    exact p5U7PrimeEtaExtension_norm_le ![t,u]
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg,abs_of_nonneg hw.1] at hn
  exact ⟨hnonneg,hn.trans (mul_le_mul_of_nonneg_left hw.2 (by positivity))⟩

/-- Exact analytic collar, before taking any bound or limit. -/
theorem p5U7PrimeLeadingIntegral_collar_identity (eta : ℝ) (heta : 0 ≤ eta) :
    p5U7ComponentPrimeIntegral-p5U7PrimeLeadingIntegral eta =
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ), p5U7PrimeCollarRow eta t := by
  have hfull := ContinuousOn.intervalIntegrable_of_Icc
    (by norm_num : (59/250 : ℝ) ≤ 1/3) p5U7ComponentPrimeRow_continuousOn
  have hcut := (continuous_p5U7PrimeCutoffRow eta).intervalIntegrable (59/250) (1/3)
  rw [p5U7ComponentPrimeIntegral,p5U7PrimeLeadingIntegral_eq_cutoff_rows eta heta,
    ← intervalIntegral.integral_sub hfull hcut]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (59/250 : ℝ) ≤ 1/3)] at ht
  have hf := p5U7PrimeEtaProduct_continuous
  have hrow : (∫ u in t..((1-t)/2), p5U7PrimeEtaExtension ![t,u]) =
      p5U7ComponentPrimeRow t := by
    unfold p5U7ComponentPrimeRow
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by linarith [ht.2] : t ≤ (1-t)/2)] at hu
    exact p5U7PrimeEtaExtension_eq_triangle ⟨ht.1,hu.1,hu.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((hf.uncurry_left t).intervalIntegrable t (max t ((1-t)/(2+eta))))
    ((hf.uncurry_left t).intervalIntegrable (max t ((1-t)/(2+eta))) ((1-t)/2))
  change p5U7ComponentPrimeRow t-p5U7PrimeCutoffRow eta t = p5U7PrimeCollarRow eta t
  change p5U7PrimeCutoffRow eta t+p5U7PrimeCollarRow eta t =
    (∫ u in t..((1-t)/2), p5U7PrimeEtaExtension ![t,u]) at hadd
  linarith only [hadd,hrow]

/-- An explicit linear rate for the genuine prime component cutoff.
It holds for EVERY eta>=0; no extra small-margin hypothesis is needed. -/
theorem p5U7PrimeLeadingIntegral_linear_collar (eta : ℝ) (heta : 0 ≤ eta) :
    0 ≤ p5U7ComponentPrimeIntegral-p5U7PrimeLeadingIntegral eta ∧
      p5U7ComponentPrimeIntegral-p5U7PrimeLeadingIntegral eta ≤
        p5U7PrimeCollarConstant*eta := by
  rw [p5U7PrimeLeadingIntegral_collar_identity eta heta]
  have hab : (59/250 : ℝ) ≤ 1/3 := by norm_num
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact (p5U7PrimeCollarRow_bounds heta ht).1
  · have hm := intervalIntegral.integral_mono_on hab
      ((continuous_p5U7PrimeCollarRow eta).intervalIntegrable (59/250) (1/3))
      (continuous_const.intervalIntegrable (59/250) (1/3))
      (fun t ht => (p5U7PrimeCollarRow_bounds heta ht).2)
    have hc : (∫ t in (59/250 : ℝ)..(1/3 : ℝ), (1/(59/250 : ℝ)^3)*(eta/4)) =
        p5U7PrimeCollarConstant*eta := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul,p5U7PrimeCollarConstant]
      ring
    exact hm.trans_eq hc
end
end ImbalancedChen
