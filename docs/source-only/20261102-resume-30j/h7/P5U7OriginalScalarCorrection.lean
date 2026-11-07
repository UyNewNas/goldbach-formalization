import ImbalancedChen.P5U7ComponentLeadingIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual original U7 Omega integral is identified with the TWO scalar
integrals used by certify_sharp_switch_midpoint.py and the independent
Simpson producer. The existing prime component supplies the first one.
The second, previously still a nested ordered-semiprime integral, is
evaluated here by two genuine FTC calculations, including its zero seam.

The global max extensions below are only continuous antiderivative
constructions. Their values on every physical integration interval are
proved equal to the original logarithmic kernels. No endpoint certificate,
source mean, ordinary table, policy, or distribution estimate is an input.
The two saved numerical endpoints themselves are NOT proved in this file.
-/

namespace ImbalancedChen.P5U7OriginalScalarCorrection

noncomputable section
open Set MeasureTheory
open scoped Topology

def regularDensity (s : ℝ) : ℝ :=
  Real.log (max 1 (s - 1)) / max 1 s

def regularCorrection (s : ℝ) : ℝ :=
  regularDensity s * Real.log ((191 / 59 : ℝ) / (max 1 s + 1))

def densityPrimitive (s : ℝ) : ℝ := ∫ v in (2 : ℝ)..s, regularDensity v

def correctionPrimitive (s : ℝ) : ℝ := ∫ v in (2 : ℝ)..s, regularCorrection v

def scalarCorrectionKernel (s : ℝ) : ℝ :=
  Real.log (s - 1) / s * Real.log ((191 / 59 : ℝ) / (s + 1))

def scalarCorrection : ℝ := ∫ s in (2 : ℝ)..(132 / 59 : ℝ), scalarCorrectionKernel s

theorem regularDensity_continuous : Continuous regularDensity := by
  have hm : Continuous (fun s : ℝ => max 1 (s - 1)) :=
    continuous_const.max (continuous_id.sub continuous_const)
  have hn : Continuous (fun s : ℝ => max 1 s) := continuous_const.max continuous_id
  exact (hm.log (fun s => ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))).div hn
    (fun s => ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))

theorem regularCorrection_continuous : Continuous regularCorrection := by
  have hp : ∀ s : ℝ, 0 < max 1 s + 1 := by
    intro s
    linarith [le_max_left (1 : ℝ) s]
  have hc : Continuous (fun s : ℝ => (191 / 59 : ℝ) / (max 1 s + 1)) :=
    continuous_const.div ((continuous_const.max continuous_id).add continuous_const)
      (fun s => (hp s).ne')
  exact regularDensity_continuous.mul
    (hc.log (fun s => (div_pos (by norm_num) (hp s)).ne'))

theorem regularDensity_eq {s : ℝ} (hs : 2 ≤ s) :
    regularDensity s = Real.log (s - 1) / s := by
  simp only [regularDensity, max_eq_right (show (1 : ℝ) ≤ s - 1 by linarith),
    max_eq_right (show (1 : ℝ) ≤ s by linarith)]

theorem regularCorrection_eq {s : ℝ} (hs : 2 ≤ s) :
    regularCorrection s = scalarCorrectionKernel s := by
  rw [regularCorrection, regularDensity_eq hs,
    max_eq_right (show (1 : ℝ) ≤ s by linarith)]
  rfl

theorem densityPrimitive_hasDerivAt (s : ℝ) :
    HasDerivAt densityPrimitive (regularDensity s) s :=
  intervalIntegral.integral_hasDerivAt_right
    (regularDensity_continuous.intervalIntegrable 2 s)
    regularDensity_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    regularDensity_continuous.continuousAt

theorem correctionPrimitive_hasDerivAt (s : ℝ) :
    HasDerivAt correctionPrimitive (regularCorrection s) s :=
  intervalIntegral.integral_hasDerivAt_right
    (regularCorrection_continuous.intervalIntegrable 2 s)
    regularCorrection_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    regularCorrection_continuous.continuousAt

@[simp] theorem densityPrimitive_two : densityPrimitive 2 = 0 := by
  simp only [densityPrimitive, intervalIntegral.integral_same]

@[simp] theorem correctionPrimitive_two : correctionPrimitive 2 = 0 := by
  simp only [correctionPrimitive, intervalIntegral.integral_same]

theorem correctionPrimitive_endpoint : correctionPrimitive (132 / 59) = scalarCorrection := by
  unfold correctionPrimitive scalarCorrection
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 132 / 59)] at hs
  exact regularCorrection_eq hs.1

def innerArgument (t u : ℝ) : ℝ := (1 - t - u) / u

def outerArgument (t : ℝ) : ℝ := 1 / t - 2

theorem outerArgument_bounds {t : ℝ} (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 4)) :
    2 ≤ outerArgument t ∧ outerArgument t ≤ (132 / 59 : ℝ) := by
  have ht0 : 0 < t := by linarith [ht.1]
  constructor
  · change 2 ≤ 1 / t - 2
    have h := (le_div_iff₀ ht0).mpr (show (4 : ℝ) * t ≤ 1 by linarith [ht.2])
    linarith only [h]
  · have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 59 / 250) ht.1
    norm_num at h
    dsimp only [outerArgument]
    linarith only [h]

/-- The actual semiprime slice agrees with its logarithm even at s=2.
The closed wall is zero; it is not added as a second branch mass. -/
theorem semiprimeKernel_eq_log_on_active {t u : ℝ} (ht : 0 < t)
    (htu : t ≤ u) (hu : u ≤ (1 - t) / 3) :
    p5U7ComponentSemiprimeKernel t u =
      Real.log ((1 - t - 2 * u) / u) / (t * u * (1 - t - u)) := by
  by_cases hstrict : u < (1 - t) / 3
  · rw [p5U7ComponentSemiprimeKernel, if_pos hstrict]
    exact p5U7Mass_semiprime_integral_slice_eq ht htu hu
  · have heq : u = (1 - t) / 3 := le_antisymm hu (le_of_not_gt hstrict)
    have hu0 : 0 < u := ht.trans_le htu
    have hratio : (1 - t - 2 * u) / u = 1 := by
      apply (div_eq_one_iff_eq hu0.ne').mpr
      linarith only [heq]
    simp only [p5U7ComponentSemiprimeKernel, if_neg hstrict, hratio,
      Real.log_one, zero_div]

private theorem innerPrimitive_hasDerivAt {t u : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 4))
    (hu : u ∈ Icc t ((1 - t) / 3)) :
    HasDerivAt (fun v => -densityPrimitive (innerArgument t v) / (t * (1 - t)))
      (p5U7ComponentSemiprimeKernel t u) u := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hu0 : 0 < u := ht0.trans_le hu.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hs : 2 ≤ innerArgument t u := by
    dsimp only [innerArgument]
    apply (le_div_iff₀ hu0).mpr
    linarith only [hu.2]
  have harg : innerArgument t u - 1 = (1 - t - 2 * u) / u := by
    dsimp only [innerArgument]
    field_simp [hu0.ne']
    <;> ring
  have hd := ((hasDerivAt_id u).const_sub (1 - t)).div (hasDerivAt_id u) hu0.ne'
  have hc := (((densityPrimitive_hasDerivAt (innerArgument t u)).comp u hd).neg).div_const
    (t * (1 - t))
  apply hc.congr_deriv
  rw [regularDensity_eq hs, harg, semiprimeKernel_eq_log_on_active ht0 hu.1 hu.2]
  have hgap : 0 < 1 - t - u := by linarith [hu.2]
  dsimp only [innerArgument]
  field_simp [ht0.ne', hu0.ne', ht1.ne', hgap.ne']
  <;> ring

/-- Exact remaining inner change of variable, proved by a genuine
antiderivative. Both t=1/4 and the internal u=(1-t)/3 wall are included. -/
theorem semiprimeRow_eq_densityPrimitive {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 4)) :
    p5U7ComponentSemiprimeRow t = densityPrimitive (outerArgument t) / (t * (1 - t)) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hcut : t ≤ (1 - t) / 3 := by linarith [ht.2]
  have hcap : (1 - t) / 3 ≤ (1 - t) / 2 := by linarith
  have hcont := p5U7ComponentSemiprimeKernel_row_continuousOn
    (show t ∈ Icc (59 / 250 : ℝ) (1 / 3) from ⟨ht.1, by linarith [ht.2]⟩)
  have hp : IntervalIntegrable (p5U7ComponentSemiprimeKernel t) volume t ((1 - t) / 3) :=
    ContinuousOn.intervalIntegrable_of_Icc hcut
      (hcont.mono (fun u hu => ⟨hu.1, hu.2.trans hcap⟩))
  have hq : IntervalIntegrable (p5U7ComponentSemiprimeKernel t) volume
      ((1 - t) / 3) ((1 - t) / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hcap
      (hcont.mono (fun u hu => ⟨hcut.trans hu.1, hu.2⟩))
  have htail : (∫ u in ((1 - t) / 3)..((1 - t) / 2),
      p5U7ComponentSemiprimeKernel t u) = 0 := by
    calc
      _ = ∫ u in ((1 - t) / 3)..((1 - t) / 2), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hcap] at hu
        simp only [p5U7ComponentSemiprimeKernel, if_neg (not_lt.mpr hu.1)]
      _ = 0 := by simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => innerPrimitive_hasDerivAt ht (by simpa only [uIcc_of_le hcut] using hu)) hp
  have hs : innerArgument t ((1 - t) / 3) = 2 := by
    dsimp only [innerArgument]
    field_simp [ht1.ne']
    <;> ring
  have hl : innerArgument t t = outerArgument t := by
    dsimp only [innerArgument, outerArgument]
    field_simp [ht0.ne']
    <;> ring
  rw [hs, hl, densityPrimitive_two, neg_zero, zero_div, zero_sub, neg_div, neg_neg] at hFTC
  have hadd := intervalIntegral.integral_add_adjacent_intervals hp hq
  rw [htail, add_zero] at hadd
  exact hadd.symm.trans hFTC

theorem semiprimeRow_eq_zero_after_quarter {t : ℝ}
    (ht : t ∈ Icc (1 / 4 : ℝ) (1 / 3)) : p5U7ComponentSemiprimeRow t = 0 := by
  unfold p5U7ComponentSemiprimeRow
  calc
    _ = ∫ u in t..((1 - t) / 2), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by linarith [ht.2] : t ≤ (1 - t) / 2)] at hu
      have hcut : (1 - t) / 3 ≤ u := by linarith [ht.1, hu.1]
      simp only [p5U7ComponentSemiprimeKernel, if_neg (not_lt.mpr hcut)]
    _ = 0 := by simp

def relativeLog (t : ℝ) : ℝ := Real.log ((191 / 59 : ℝ) * t / (1 - t))

theorem relativeLog_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt relativeLog (1 / (t * (1 - t))) t := by
  have hm : 0 < 1 - t := sub_pos.mpr ht1
  have hn : 0 < (191 / 59 : ℝ) * t / (1 - t) := div_pos (mul_pos (by norm_num) ht0) hm
  have hd := ((((hasDerivAt_id t).const_mul (191 / 59 : ℝ)).div
    ((hasDerivAt_id t).const_sub 1) hm.ne').log hn.ne')
  apply hd.congr_deriv
  field_simp [ht0.ne', hm.ne']
  <;> ring

theorem relativeLog_eq_outer {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    relativeLog t = Real.log ((191 / 59 : ℝ) / (outerArgument t + 1)) := by
  have ha : outerArgument t + 1 = (1 - t) / t := by
    dsimp only [outerArgument]
    field_simp [ht0.ne']
    <;> ring
  rw [ha]
  unfold relativeLog
  congr 1
  field_simp [ht0.ne', (sub_pos.mpr ht1).ne']
  <;> ring

def outerPrimitive (t : ℝ) : ℝ :=
  densityPrimitive (outerArgument t) * relativeLog t - correctionPrimitive (outerArgument t)

private theorem outerPrimitive_hasDerivAt {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 4)) :
    HasDerivAt outerPrimitive (p5U7ComponentSemiprimeRow t) t := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : t < 1 := by linarith [ht.2]
  have hs := (outerArgument_bounds ht).1
  have hd : HasDerivAt outerArgument (-(1 / t ^ 2)) t := by
    have hh := (hasDerivAt_inv ht0.ne').sub_const 2
    simpa only [one_div] using hh
  have hG := (densityPrimitive_hasDerivAt (outerArgument t)).comp t hd
  have hH := (correctionPrimitive_hasDerivAt (outerArgument t)).comp t hd
  have hL := relativeLog_hasDerivAt ht0 ht1
  apply ((hG.mul hL).sub hH).congr_deriv
  rw [semiprimeRow_eq_densityPrimitive ht, regularCorrection_eq hs, scalarCorrectionKernel,
    regularDensity_eq hs, relativeLog_eq_outer ht0 ht1]
  ring

/-- Exact scalar correction from the original marked ordered-semiprime
integral. This is the archived Fubini formula, proved without assuming it. -/
theorem semiprimeIntegral_eq_scalarCorrection :
    p5U7ComponentSemiprimeIntegral = scalarCorrection := by
  have hc := p5U7ComponentSemiprimeRow_continuousOn
  have hp : IntervalIntegrable p5U7ComponentSemiprimeRow volume (59 / 250 : ℝ) (1 / 4) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (hc.mono (fun t ht => ⟨ht.1, by linarith [ht.2]⟩))
  have hq : IntervalIntegrable p5U7ComponentSemiprimeRow volume (1 / 4 : ℝ) (1 / 3) :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (hc.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩))
  have htail : (∫ t in (1 / 4 : ℝ)..(1 / 3 : ℝ), p5U7ComponentSemiprimeRow t) = 0 := by
    calc
      _ = ∫ t in (1 / 4 : ℝ)..(1 / 3 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3)] at ht
        exact semiprimeRow_eq_zero_after_quarter ht
      _ = 0 := by simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => outerPrimitive_hasDerivAt
      (by simpa only [uIcc_of_le (by norm_num : (59 / 250 : ℝ) ≤ 1 / 4)] using ht)) hp
  have hl : outerPrimitive (59 / 250) = -scalarCorrection := by
    have ha : outerArgument (59 / 250) = (132 / 59 : ℝ) := by norm_num [outerArgument]
    have hb : relativeLog (59 / 250) = 0 := by norm_num [relativeLog]
    simp only [outerPrimitive, ha, hb, mul_zero, zero_sub, correctionPrimitive_endpoint]
  have hr : outerPrimitive (1 / 4) = 0 := by
    have ha : outerArgument (1 / 4) = (2 : ℝ) := by norm_num [outerArgument]
    simp only [outerPrimitive, ha, densityPrimitive_two, correctionPrimitive_two,
      zero_mul, sub_self]
  rw [hl, hr, zero_sub, neg_neg] at hFTC
  have hadd := intervalIntegral.integral_add_adjacent_intervals hp hq
  rw [htail, add_zero] at hadd
  exact hadd.symm.trans hFTC

/-- The SAME literal original J7, with no density factor or Chen quarter
inserted. The ledger's later factor two remains external to this identity. -/
theorem originalOmegaIntegral_eq_scalar_pair :
    p5U7OriginalOmegaIntegral 1 =
      (∫ t in (59 / 250 : ℝ)..(1 / 3 : ℝ),
        Real.log ((1 - 2 * t) / t) / (t * (1 - t))) +
      ∫ s in (2 : ℝ)..(132 / 59 : ℝ),
        Real.log (s - 1) / s * Real.log ((191 / 59 : ℝ) / (s + 1)) := by
  rw [p5U7Component_integral_split, p5U7ComponentPrimeIntegral_eq_logIntegral,
    semiprimeIntegral_eq_scalarCorrection]
  rfl

/-- Exact K-linearity of the original source functional. In particular
the archived K0 and current manuscript K multiply the entire correction. -/
theorem originalOmegaIntegral_eq_mul (K : ℝ) :
    p5U7OriginalOmegaIntegral K = K * p5U7OriginalOmegaIntegral 1 := by
  have hk (t u : ℝ) : p5U7OmegaKernel K t u = K * p5U7OmegaKernel 1 t u := by
    unfold p5U7OmegaKernel
    ring
  unfold p5U7OriginalOmegaIntegral
  simp_rw [hk, intervalIntegral.integral_const_mul]

theorem currentOriginalOmegaIntegral_eq_components :
    p5U7CurrentOriginalOmegaIntegral =
      currentK * (p5U7ComponentPrimeIntegral + scalarCorrection) := by
  rw [p5U7CurrentOriginalOmegaIntegral, originalOmegaIntegral_eq_mul,
    p5U7Component_integral_split, semiprimeIntegral_eq_scalarCorrection]

end
end ImbalancedChen.P5U7OriginalScalarCorrection
