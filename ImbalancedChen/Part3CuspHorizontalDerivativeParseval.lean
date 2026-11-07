import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24; uncompiled.

This is the horizontal Fourier energy identity for a genuinely periodic
function on a period-one cusp cross-section.  `fourierCoeffOn` is defined in
Mathlib by lifting the function on `(0,1]` to `UnitAddCircle`, so every
coefficient here is an actual normalized-Haar circle coefficient.  No
automorphic spectral expansion or Maass coefficient is assumed.
-/

noncomputable section

namespace P3CuspHorizontalDerivativeParsevalSourceOnly

open MeasureTheory

private theorem unit_interval_pos : (0 : ℝ) < 1 := zero_lt_one

/-- The horizontal derivative of a period-one function has zero Fourier
coefficient at frequency zero.  This is the fundamental theorem of calculus,
not a zero-mode hypothesis. -/
theorem derivative_zero_coefficient
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt f (g x) x)
    (hperiod : f 1 = f 0)
    (hint : IntervalIntegrable g volume 0 1) :
    AddCircle.fourierCoeffOn unit_interval_pos g 0 = 0 := by
  have hftc : (∫ x in (0 : ℝ)..1, g x) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    exact sub_eq_zero.mpr hperiod
  rw [AddCircle.fourierCoeffOn_eq_integral g 0 unit_interval_pos]
  simpa using hftc

/-- On every integer mode, the coefficient of the actual horizontal
derivative is `2πin` times the coefficient of the periodic function.  The
zero mode uses the preceding fundamental-theorem calculation. -/
theorem derivative_fourier_coefficient
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt f (g x) x)
    (hperiod : f 1 = f 0)
    (hint : IntervalIntegrable g volume 0 1) (n : ℤ) :
    AddCircle.fourierCoeffOn unit_interval_pos g n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        AddCircle.fourierCoeffOn unit_interval_pos f n := by
  by_cases hn : n = 0
  · subst n
    simpa using derivative_zero_coefficient f g hderiv hperiod hint
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hden : (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        · exact Complex.I_ne_zero
      · exact hnC
    have h := AddCircle.fourierCoeffOn_of_hasDerivAt
      (a := (0 : ℝ)) (b := 1) unit_interval_pos hn hderiv hint
    have h' : AddCircle.fourierCoeffOn unit_interval_pos f n =
        1 / (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
          (-AddCircle.fourierCoeffOn unit_interval_pos g n) := by
      simpa [hperiod] using h
    field_simp [hden] at h'
    linear_combination h'

/-- Parseval for the actual horizontal derivative, rewritten wholly in
terms of the period-one function's Fourier coefficients.  The sum runs over
all integers, including zero; the zero contribution vanishes by the theorem
above. -/
theorem derivative_parseval
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt f (g x) x)
    (hperiod : f 1 = f 0)
    (hint : IntervalIntegrable g volume 0 1)
    (hgL2 : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    HasSum
      (fun n : ℤ =>
        ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
          AddCircle.fourierCoeffOn unit_interval_pos f n‖ ^ 2)
      (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) := by
  have h := AddCircle.hasSum_sq_fourierCoeffOn unit_interval_pos hgL2
  simp only [sub_zero, inv_one, one_smul] at h
  simpa only [derivative_fourier_coefficient f g hderiv hperiod hint] using h

/-- The finite-frequency version used when testing cusp Fourier polynomials.
It has no cutoff-dependent constant and follows from the same exact mode law. -/
theorem derivative_finite_mode_energy
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt f (g x) x)
    (hperiod : f 1 = f 0)
    (hint : IntervalIntegrable g volume 0 1) (s : Finset ℤ) :
    (∑ n ∈ s, ‖AddCircle.fourierCoeffOn unit_interval_pos g n‖ ^ 2) =
      ∑ n ∈ s,
        ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
          AddCircle.fourierCoeffOn unit_interval_pos f n‖ ^ 2 := by
  simp_rw [derivative_fourier_coefficient f g hderiv hperiod hint]

/-- Sharp period-one Poincaré inequality for a mean-zero horizontal slice.
The derivative is the actual real horizontal derivative, and mean zero is the
ordinary integral over a full period. -/
theorem period_one_poincare
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt f (g x) x)
    (hperiod : f 1 = f 0)
    (hint : IntervalIntegrable g volume 0 1)
    (hfL2 : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hgL2 : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hmean : (∫ x in (0 : ℝ)..1, f x) = 0) :
    (4 * Real.pi ^ 2) * (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤
      ∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2 := by
  let cf : ℤ → ℂ := AddCircle.fourierCoeffOn unit_interval_pos f
  let cg : ℤ → ℂ := AddCircle.fourierCoeffOn unit_interval_pos g
  have hzero : cf 0 = 0 := by
    dsimp [cf]
    rw [AddCircle.fourierCoeffOn_eq_integral f 0 unit_interval_pos]
    simpa using hmean
  have hF := AddCircle.hasSum_sq_fourierCoeffOn unit_interval_pos hfL2
  have hG := derivative_parseval f g hderiv hperiod hint hgL2
  simp only [sub_zero, inv_one, one_smul] at hF
  have hpoint (n : ℤ) :
      (4 * Real.pi ^ 2) * ‖cf n‖ ^ 2 ≤
        ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * cf n‖ ^ 2 := by
    by_cases hn : n = 0
    · subst n
      simp [hzero]
    · have hnormn : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
        rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
        exact Int.one_le_abs hn
      have hfreq : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ =
          (2 * Real.pi) * ‖(n : ℂ)‖ := by
        simp [norm_mul, Complex.norm_ofReal, abs_of_pos Real.pi_pos] <;> ring
      have hfreq_lower : (2 * Real.pi) ≤ (2 * Real.pi) * ‖(n : ℂ)‖ := by
        simpa using mul_le_mul_of_nonneg_left hnormn
          (show 0 ≤ (2 * Real.pi : ℝ) by positivity)
      have hfreq_sq : (2 * Real.pi) ^ 2 ≤
          ((2 * Real.pi) * ‖(n : ℂ)‖) ^ 2 :=
        (sq_le_sq₀ (by positivity)
          (mul_nonneg (by positivity) (norm_nonneg _))).2 hfreq_lower
      calc
        (4 * Real.pi ^ 2) * ‖cf n‖ ^ 2 =
            (2 * Real.pi) ^ 2 * ‖cf n‖ ^ 2 := by ring
        _ ≤ ((2 * Real.pi) * ‖(n : ℂ)‖) ^ 2 * ‖cf n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hfreq_sq (sq_nonneg _)
        _ = ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * cf n‖ ^ 2 := by
          rw [norm_mul, hfreq]
          ring
  have hscaled : Summable (fun n : ℤ =>
      (4 * Real.pi ^ 2) * ‖cf n‖ ^ 2) :=
    hF.summable.mul_left _
  have hle := hscaled.tsum_le_tsum hpoint hG.summable
  calc
    (4 * Real.pi ^ 2) * (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) =
        ∑' n : ℤ, (4 * Real.pi ^ 2) * ‖cf n‖ ^ 2 := by
          rw [← hF.tsum_eq, hF.summable.tsum_mul_left]
    _ ≤ ∑' n : ℤ,
        ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * cf n‖ ^ 2 := hle
    _ = ∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2 := hG.tsum_eq

theorem period_one_poincare_sharp_constant
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt f (g x) x)
    (hperiod : f 1 = f 0)
    (hint : IntervalIntegrable g volume 0 1)
    (hfL2 : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hgL2 : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hmean : (∫ x in (0 : ℝ)..1, f x) = 0) :
    (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤
      (4 * Real.pi ^ 2)⁻¹ *
        (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) := by
  have h := period_one_poincare f g hderiv hperiod hint hfL2 hgL2 hmean
  have hc : 0 < 4 * Real.pi ^ 2 := by positivity
  calc
    (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤
        (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) / (4 * Real.pi ^ 2) := by
          apply (le_div_iff₀ hc).2
          simpa only [mul_comm] using h
    _ = (4 * Real.pi ^ 2)⁻¹ *
        (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) := by ring

/-- Width-`w` Poincaré, with the sharp `w²/(4π²)` constant.  The three
rescaled integrability assumptions make the change-of-variables domain
explicit; they hold in particular for smooth periodic slices. -/
theorem positive_width_poincare
    (w : ℝ) (hw : 0 < w) (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), w]], HasDerivAt f (g x) x)
    (hperiod : f w = f 0)
    (hmean : (∫ x in (0 : ℝ)..w, f x) = 0)
    (hintScaled : IntervalIntegrable
      (fun t : ℝ => (w : ℂ) * g (w * t)) volume 0 1)
    (hfScaled : MemLp (fun t : ℝ => f (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hgScaled : MemLp (fun t : ℝ => (w : ℂ) * g (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (4 * Real.pi ^ 2) * (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) ≤
      w ^ 2 * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := by
  have hwne : w ≠ 0 := ne_of_gt hw
  let F : ℝ → ℂ := fun t => f (w * t)
  let G : ℝ → ℂ := fun t => (w : ℂ) * g (w * t)
  have hscaledDeriv : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt F (G t) t := by
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    have hwt : w * t ∈ [[(0 : ℝ), w]] := by
      rw [uIcc_of_le hw.le]
      exact ⟨mul_nonneg hw.le ht01.1,
        by simpa using mul_le_mul_of_nonneg_left ht01.2 hw.le⟩
    have hlinear : HasDerivAt (fun x : ℝ => w * x) w t := by
      simpa using (hasDerivAt_id t).const_mul w
    simpa only [F, G, Function.comp_def, Complex.real_smul] using
      (hderiv (w * t) hwt).comp t hlinear
  have hscaledPeriod : F 1 = F 0 := by simpa [F] using hperiod
  have hscaledMean : (∫ t in (0 : ℝ)..1, F t) = 0 := by
    change (∫ t in (0 : ℝ)..1, f (w * t)) = 0
    rw [intervalIntegral.integral_comp_mul_left f hwne]
    simpa [hmean]
  have hUnit := period_one_poincare F G hscaledDeriv hscaledPeriod
    hintScaled hfScaled hgScaled hscaledMean
  have hFint : (∫ t in (0 : ℝ)..1, ‖F t‖ ^ 2) =
      w⁻¹ * (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) := by
    change (∫ t in (0 : ℝ)..1, ‖f (w * t)‖ ^ 2) = _
    rw [intervalIntegral.integral_comp_mul_left (fun x => ‖f x‖ ^ 2) hwne]
    simp
  have hGint : (∫ t in (0 : ℝ)..1, ‖G t‖ ^ 2) =
      w ^ 2 * (w⁻¹ * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2)) := by
    have hpoint (t : ℝ) : ‖G t‖ ^ 2 = w ^ 2 * ‖g (w * t)‖ ^ 2 := by
      simp [G, norm_mul, Complex.norm_ofReal, abs_of_pos hw] <;> ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_left (fun x => ‖g x‖ ^ 2) hwne]
    simp
  rw [hFint, hGint] at hUnit
  have hmul := mul_le_mul_of_nonneg_left hUnit hw.le
  calc
    (4 * Real.pi ^ 2) * (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) =
        w * ((4 * Real.pi ^ 2) *
          (w⁻¹ * (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2))) := by
            field_simp [hwne]
            ring
    _ ≤ w * (w ^ 2 *
          (w⁻¹ * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2))) := hmul
    _ = w ^ 2 * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := by
      field_simp [hwne]
      ring

theorem positive_width_poincare_sharp_constant
    (w : ℝ) (hw : 0 < w) (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), w]], HasDerivAt f (g x) x)
    (hperiod : f w = f 0)
    (hmean : (∫ x in (0 : ℝ)..w, f x) = 0)
    (hintScaled : IntervalIntegrable
      (fun t : ℝ => (w : ℂ) * g (w * t)) volume 0 1)
    (hfScaled : MemLp (fun t : ℝ => f (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hgScaled : MemLp (fun t : ℝ => (w : ℂ) * g (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) ≤
      (w ^ 2 / (4 * Real.pi ^ 2)) *
        (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := by
  have h := positive_width_poincare w hw f g hderiv hperiod hmean
    hintScaled hfScaled hgScaled
  have hc : 0 < 4 * Real.pi ^ 2 := by positivity
  calc
    (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) ≤
        (w ^ 2 * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2)) /
          (4 * Real.pi ^ 2) := by
            apply (le_div_iff₀ hc).2
            simpa only [mul_comm] using h
    _ = (w ^ 2 / (4 * Real.pi ^ 2)) *
        (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := by ring

/-- The exact horizontal coercivity inequality at height `y` in a cusp
chart of width `w`.  The hyperbolic horizontal gradient carries the factor
`y²`; this theorem only concerns that horizontal direction. -/
theorem cusp_height_horizontal_coercivity
    (w y : ℝ) (hw : 0 < w) (hy : 0 < y)
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), w]], HasDerivAt f (g x) x)
    (hperiod : f w = f 0)
    (hmean : (∫ x in (0 : ℝ)..w, f x) = 0)
    (hintScaled : IntervalIntegrable
      (fun t : ℝ => (w : ℂ) * g (w * t)) volume 0 1)
    (hfScaled : MemLp (fun t : ℝ => f (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hgScaled : MemLp (fun t : ℝ => (w : ℂ) * g (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    ((4 * Real.pi ^ 2) * y ^ 2 / w ^ 2) *
        (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) ≤
      y ^ 2 * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := by
  have hp := positive_width_poincare w hw f g hderiv hperiod hmean
    hintScaled hfScaled hgScaled
  have hw2 : 0 < w ^ 2 := pow_pos hw _
  have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg y)
  have hquot : ((4 * Real.pi ^ 2) * y ^ 2 *
      (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2)) / w ^ 2 ≤
      y ^ 2 * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := by
    apply (div_le_iff₀ hw2).2
    convert hmul using 1 <;> ring
  convert hquot using 1 <;> ring

/-- Uniform lower bound on the horizontal spectral energy for a cusp tail
`y ≥ Y > 0`, expressed slice by slice.  The proof makes no assertion about
vertical energy, a global quotient Laplacian, or its spectrum. -/
theorem cusp_tail_horizontal_coercivity
    (w Y y : ℝ) (hw : 0 < w) (hY : 0 < Y) (hy : Y ≤ y)
    (f g : ℝ → ℂ)
    (hderiv : ∀ x ∈ [[(0 : ℝ), w]], HasDerivAt f (g x) x)
    (hperiod : f w = f 0)
    (hmean : (∫ x in (0 : ℝ)..w, f x) = 0)
    (hintScaled : IntervalIntegrable
      (fun t : ℝ => (w : ℂ) * g (w * t)) volume 0 1)
    (hfScaled : MemLp (fun t : ℝ => f (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hgScaled : MemLp (fun t : ℝ => (w : ℂ) * g (w * t)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    ((4 * Real.pi ^ 2) * Y ^ 2 / w ^ 2) *
        (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) ≤
      y ^ 2 * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := by
  have hypos : 0 < y := lt_of_lt_of_le hY hy
  have hslice := cusp_height_horizontal_coercivity w y hw hypos f g
    hderiv hperiod hmean hintScaled hfScaled hgScaled
  have henergy_nonneg : 0 ≤ ∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_ae hw.le
      (Filter.Eventually.of_forall (fun x => sq_nonneg (‖f x‖)))
  have hscale_nonneg : 0 ≤ (4 * Real.pi ^ 2) / w ^ 2 := by positivity
  have hsquares : Y ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hY.le hypos.le).2 hy
  have hbound := mul_le_mul_of_nonneg_right hsquares
    (mul_nonneg hscale_nonneg henergy_nonneg)
  calc
    ((4 * Real.pi ^ 2) * Y ^ 2 / w ^ 2) *
        (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) =
      Y ^ 2 * ((4 * Real.pi ^ 2) / w ^ 2 *
        (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2)) := by ring
    _ ≤ y ^ 2 * ((4 * Real.pi ^ 2) / w ^ 2 *
        (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2)) := hbound
    _ = ((4 * Real.pi ^ 2) * y ^ 2 / w ^ 2) *
        (∫ x in (0 : ℝ)..w, ‖f x‖ ^ 2) := by ring
    _ ≤ y ^ 2 * (∫ x in (0 : ℝ)..w, ‖g x‖ ^ 2) := hslice

end P3CuspHorizontalDerivativeParsevalSourceOnly
