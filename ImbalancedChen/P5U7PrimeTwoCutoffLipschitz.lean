import ImbalancedChen.P5U7PrimeLinearCollar

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine TWO-CUTOFF modulus for arbitrary nonnegative margins. The
ordered clamped endpoint difference is bounded directly, not by adding
two zero-cutoff estimates. The literal interval between those endpoints
supplies the exact positive prime-mass difference and global Lipschitz rate.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory Filter Topology
open Classical

def p5U7PrimeTwoCutoffRow (eta theta t : ℝ) : ℝ :=
  ∫ u in max t ((1-t)/(2+theta))..max t ((1-t)/(2+eta)),
    p5U7PrimeEtaExtension ![t,u]

def p5U7PrimeCutoffTolerance (epsilon : ℝ) : ℝ :=
  epsilon/(p5U7PrimeCollarConstant+1)

/-- Direct two-denominator geometry, including both clamped empty rows. -/
theorem p5U7PrimeTwoCutoff_width {eta theta t : ℝ}
    (heta : 0 ≤ eta) (hetatheta : eta ≤ theta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 ≤ max t ((1-t)/(2+eta))-max t ((1-t)/(2+theta)) ∧
      max t ((1-t)/(2+eta))-max t ((1-t)/(2+theta)) ≤ (theta-eta)/4 := by
  have htheta : 0 ≤ theta := heta.trans hetatheta
  have he : 0 < 2+eta := by linarith
  have hth : 0 < 2+theta := by linarith
  have hn : 0 ≤ 1-t := by linarith [ht.2]
  have hdelta : 0 ≤ theta-eta := sub_nonneg.mpr hetatheta
  have hcaps : (1-t)/(2+theta) ≤ (1-t)/(2+eta) :=
    div_le_div_of_nonneg_left hn he (by linarith only [hetatheta])
  have hmax := max_le_max (le_refl t) hcaps
  have hmaxgap : max t ((1-t)/(2+eta))-max t ((1-t)/(2+theta)) ≤
      (1-t)/(2+eta)-(1-t)/(2+theta) := by
    have hh : max t ((1-t)/(2+eta)) ≤
        max t ((1-t)/(2+theta)) + ((1-t)/(2+eta)-(1-t)/(2+theta)) := by
      apply max_le
      · have hm := le_max_left t ((1-t)/(2+theta))
        linarith only [hm,hcaps]
      · have hm := le_max_right t ((1-t)/(2+theta))
        linarith only [hm]
    linarith only [hh]
  have hraw : (1-t)/(2+eta)-(1-t)/(2+theta) ≤ (theta-eta)/4 := by
    have hid : (1-t)/(2+eta)-(1-t)/(2+theta) =
        ((1-t)*(theta-eta))/((2+eta)*(2+theta)) := by
      field_simp [he.ne',hth.ne']
      <;> ring
    have hden : (4 : ℝ) ≤ (2+eta)*(2+theta) := by
      nlinarith [mul_nonneg heta htheta]
    have hden0 : 0 < (2+eta)*(2+theta) := mul_pos he hth
    have hnum : (1-t)*(theta-eta) ≤ theta-eta := by
      have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 59/250).trans ht.1
      nlinarith [mul_nonneg ht0 hdelta]
    rw [hid]
    exact (div_le_div_of_nonneg_right hnum hden0.le).trans
      (div_le_div_of_nonneg_left hdelta (by norm_num) hden)
  exact ⟨sub_nonneg.mpr hmax,hmaxgap.trans hraw⟩

theorem continuous_p5U7PrimeTwoCutoffRow (eta theta : ℝ) :
    Continuous (p5U7PrimeTwoCutoffRow eta theta) :=
  p5U7Prime_interval_row_continuous _ _
    (continuous_id.max ((continuous_const.sub continuous_id).div_const (2+theta)))
    (continuous_id.max ((continuous_const.sub continuous_id).div_const (2+eta)))

/-- Exact signed row identity holds even before ordering the two margins. -/
theorem p5U7PrimeTwoCutoff_row_identity (eta theta t : ℝ) :
    p5U7PrimeCutoffRow eta t-p5U7PrimeCutoffRow theta t =
      p5U7PrimeTwoCutoffRow eta theta t := by
  have hf := p5U7PrimeEtaProduct_continuous
  have hh := intervalIntegral.integral_add_adjacent_intervals
    ((hf.uncurry_left t).intervalIntegrable t (max t ((1-t)/(2+theta))))
    ((hf.uncurry_left t).intervalIntegrable (max t ((1-t)/(2+theta)))
      (max t ((1-t)/(2+eta))))
  change p5U7PrimeCutoffRow theta t+p5U7PrimeTwoCutoffRow eta theta t =
    p5U7PrimeCutoffRow eta t at hh
  linarith only [hh]

theorem p5U7PrimeTwoCutoffRow_bounds {eta theta t : ℝ}
    (heta : 0 ≤ eta) (hetatheta : eta ≤ theta)
    (ht : t ∈ Icc (59/250 : ℝ) (1/3)) :
    0 ≤ p5U7PrimeTwoCutoffRow eta theta t ∧
      p5U7PrimeTwoCutoffRow eta theta t ≤ (1/(59/250 : ℝ)^3)*((theta-eta)/4) := by
  have hw := p5U7PrimeTwoCutoff_width heta hetatheta ht
  have hlu : max t ((1-t)/(2+theta)) ≤ max t ((1-t)/(2+eta)) :=
    sub_nonneg.mp hw.1
  have hp : 0 ≤ p5U7PrimeTwoCutoffRow eta theta t := by
    apply intervalIntegral.integral_nonneg hlu
    intro u _
    exact p5U7PrimeEtaExtension_nonneg ![t,u]
  have hn : ‖p5U7PrimeTwoCutoffRow eta theta t‖ ≤
      (1/(59/250 : ℝ)^3)*|max t ((1-t)/(2+eta))-max t ((1-t)/(2+theta))| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u _
    exact p5U7PrimeEtaExtension_norm_le ![t,u]
  rw [Real.norm_eq_abs,abs_of_nonneg hp,abs_of_nonneg hw.1] at hn
  exact ⟨hp,hn.trans (mul_le_mul_of_nonneg_left hw.2 (by positivity))⟩

/-- Exact native integral difference between two genuine cutoffs. -/
theorem p5U7PrimeLeadingIntegral_two_cutoff_identity (eta theta : ℝ)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    p5U7PrimeLeadingIntegral eta-p5U7PrimeLeadingIntegral theta =
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ), p5U7PrimeTwoCutoffRow eta theta t := by
  rw [p5U7PrimeLeadingIntegral_eq_cutoff_rows eta heta,
    p5U7PrimeLeadingIntegral_eq_cutoff_rows theta htheta,
    ← intervalIntegral.integral_sub
      ((continuous_p5U7PrimeCutoffRow eta).intervalIntegrable (59/250) (1/3))
      ((continuous_p5U7PrimeCutoffRow theta).intervalIntegrable (59/250) (1/3))]
  exact intervalIntegral.integral_congr (fun t _ => p5U7PrimeTwoCutoff_row_identity eta theta t)

/-- Ordered margin difference paid directly by the actual between-cutoff
prime interval. The error is proportional to theta-eta, not theta+eta. -/
theorem p5U7PrimeLeadingIntegral_ordered_cutoff_bound (eta theta : ℝ)
    (heta : 0 ≤ eta) (hetatheta : eta ≤ theta) :
    0 ≤ p5U7PrimeLeadingIntegral eta-p5U7PrimeLeadingIntegral theta ∧
      p5U7PrimeLeadingIntegral eta-p5U7PrimeLeadingIntegral theta ≤
        p5U7PrimeCollarConstant*(theta-eta) := by
  rw [p5U7PrimeLeadingIntegral_two_cutoff_identity eta theta heta (heta.trans hetatheta)]
  have hab : (59/250 : ℝ) ≤ 1/3 := by norm_num
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact (p5U7PrimeTwoCutoffRow_bounds heta hetatheta ht).1
  · have hm := intervalIntegral.integral_mono_on hab
      ((continuous_p5U7PrimeTwoCutoffRow eta theta).intervalIntegrable (59/250) (1/3))
      (continuous_const.intervalIntegrable (59/250) (1/3))
      (fun t ht => (p5U7PrimeTwoCutoffRow_bounds heta hetatheta ht).2)
    have hc : (∫ t in (59/250 : ℝ)..(1/3 : ℝ),
        (1/(59/250 : ℝ)^3)*((theta-eta)/4)) = p5U7PrimeCollarConstant*(theta-eta) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul,p5U7PrimeCollarConstant]
      ring
    exact hm.trans_eq hc

/-- Global two-cutoff Lipschitz estimate on the entire nonnegative ray. -/
theorem p5U7PrimeLeadingIntegral_two_cutoff_lipschitz (eta theta : ℝ)
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) :
    |p5U7PrimeLeadingIntegral eta-p5U7PrimeLeadingIntegral theta| ≤
      p5U7PrimeCollarConstant*|eta-theta| := by
  rcases le_total eta theta with h | h
  · have hb := p5U7PrimeLeadingIntegral_ordered_cutoff_bound eta theta heta h
    rw [abs_of_nonneg hb.1,abs_of_nonpos (sub_nonpos.mpr h),neg_sub]
    exact hb.2
  · have hb := p5U7PrimeLeadingIntegral_ordered_cutoff_bound theta eta htheta h
    rw [abs_sub_comm (p5U7PrimeLeadingIntegral eta) (p5U7PrimeLeadingIntegral theta),
      abs_of_nonneg hb.1,abs_of_nonneg (sub_nonneg.mpr h)]
    exact hb.2

theorem p5U7PrimeLeadingIntegral_antitone :
    AntitoneOn p5U7PrimeLeadingIntegral (Ici (0 : ℝ)) := by
  intro eta heta theta htheta h
  exact sub_nonneg.mp (p5U7PrimeLeadingIntegral_ordered_cutoff_bound eta theta heta h).1

theorem p5U7PrimeCollarConstant_nonneg : 0 ≤ p5U7PrimeCollarConstant := by
  unfold p5U7PrimeCollarConstant
  positivity

theorem p5U7PrimeCutoffTolerance_pos {epsilon : ℝ} (he : 0 < epsilon) :
    0 < p5U7PrimeCutoffTolerance epsilon := by
  apply div_pos he
  linarith only [p5U7PrimeCollarConstant_nonneg]

/-- An explicit native error modulus, uniform in both nonnegative
margins. It chooses the margin tolerance before any arithmetic N. -/
theorem p5U7PrimeLeadingIntegral_native_modulus (epsilon eta theta : ℝ)
    (he : 0 < epsilon) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hnear : |eta-theta| ≤ p5U7PrimeCutoffTolerance epsilon) :
    |p5U7PrimeLeadingIntegral eta-p5U7PrimeLeadingIntegral theta| < epsilon := by
  have hC := p5U7PrimeCollarConstant_nonneg
  have hden : 0 < p5U7PrimeCollarConstant+1 := by linarith only [hC]
  have hscaled := mul_le_mul_of_nonneg_left hnear hC
  have hstrict : p5U7PrimeCollarConstant*p5U7PrimeCutoffTolerance epsilon < epsilon := by
    change p5U7PrimeCollarConstant*(epsilon/(p5U7PrimeCollarConstant+1)) < epsilon
    rw [show p5U7PrimeCollarConstant*(epsilon/(p5U7PrimeCollarConstant+1)) =
      (p5U7PrimeCollarConstant*epsilon)/(p5U7PrimeCollarConstant+1) by ring]
    exact (div_lt_iff₀ hden).mpr (by nlinarith only [he])
  exact (p5U7PrimeLeadingIntegral_two_cutoff_lipschitz eta theta heta htheta).trans_lt
    (hscaled.trans_lt hstrict)
end
end ImbalancedChen
