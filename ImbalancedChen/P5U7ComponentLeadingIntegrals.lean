import ImbalancedChen.P5U7ActualComponentPartition

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
The prime leading density and the separate ordered-semiprime iterated
integral are genuine integrals. Integrability and their additive split
are proved before any arithmetic prime-mass supplier is used.
-/
namespace ImbalancedChen
noncomputable section
open Set MeasureTheory
open scoped Topology
open Classical

def p5U7ComponentPrimeKernel (t u : ℝ) : ℝ := 1 / (t * u * (1 - t - u))

def p5U7ComponentSemiprimeKernel (t u : ℝ) : ℝ :=
  if u < (1 - t) / 3 then p5U7MassSemiprimeIntegralSlice t u else 0

def p5U7ComponentPrimeRow (t : ℝ) : ℝ :=
  ∫ u in t..((1 - t) / 2), p5U7ComponentPrimeKernel t u

def p5U7ComponentSemiprimeRow (t : ℝ) : ℝ :=
  ∫ u in t..((1 - t) / 2), p5U7ComponentSemiprimeKernel t u

def p5U7ComponentPrimeIntegral : ℝ :=
  ∫ t in (59 / 250 : ℝ)..(1 / 3 : ℝ), p5U7ComponentPrimeRow t

def p5U7ComponentSemiprimeIntegral : ℝ :=
  ∫ t in (59 / 250 : ℝ)..(1 / 3 : ℝ), p5U7ComponentSemiprimeRow t

theorem p5U7Component_kernel_split {t u : ℝ} (h : p5U7OmegaClosedSupport t u) :
    p5U7OmegaKernel 1 t u =
      p5U7ComponentPrimeKernel t u + p5U7ComponentSemiprimeKernel t u := by
  simpa only [p5U7MassRealKernel, p5U7ComponentPrimeKernel,
    p5U7ComponentSemiprimeKernel] using (p5U7MassRealKernel_eq_originalOmega h).symm

theorem p5U7ComponentPrimeKernel_row_continuousOn {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 3)) :
    ContinuousOn (p5U7ComponentPrimeKernel t) (Icc t ((1 - t) / 2)) := by
  have ht0 : 0 < t := by linarith [ht.1]
  unfold p5U7ComponentPrimeKernel
  apply continuousOn_const.div
    ((continuousOn_const.mul continuousOn_id).mul (continuousOn_const.sub continuousOn_id))
  intro u hu
  exact (mul_pos (mul_pos ht0 (ht0.trans_le hu.1)) (by linarith [hu.2, ht.2])).ne'

theorem p5U7ComponentSemiprimeKernel_row_continuousOn {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 3)) :
    ContinuousOn (p5U7ComponentSemiprimeKernel t) (Icc t ((1 - t) / 2)) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hf : ContinuousOn (fun u => p5U7OmegaKernel 1 t u) (Icc t ((1 - t) / 2)) :=
    (p5U7Omega_kernel_continuousOn_positive 1).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨ht0, ht0.trans_le hu.1⟩)
  apply (hf.sub (p5U7ComponentPrimeKernel_row_continuousOn ht)).congr
  intro u hu
  have hs := p5U7Component_kernel_split ⟨ht.1, hu.1, hu.2⟩
  linarith only [hs]

/-- Exact prime-window inner primitive, including t=1/3. -/
theorem p5U7ComponentPrimeRow_eq_log {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 3)) :
    p5U7ComponentPrimeRow t =
      Real.log ((1 - 2 * t) / t) / (t * (1 - t)) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hcap : t ≤ (1 - t) / 2 := by linarith [ht.2]
  unfold p5U7ComponentPrimeRow p5U7ComponentPrimeKernel
  rw [intervalIntegral.integral_of_le hcap, ← integral_Ico_eq_integral_Ioc]
  have h := currentChenUpsilon9Harmonic_inner_integral ht0 (by linarith [ht.2]) ht0 hcap
  simpa only [show 1 - t - t = 1 - 2 * t by ring] using h

/-- Row split uses actual integrability of both components. -/
theorem p5U7Component_row_split {t : ℝ}
    (ht : t ∈ Icc (59 / 250 : ℝ) (1 / 3)) :
    p5U7OmegaRow 1 t = p5U7ComponentPrimeRow t + p5U7ComponentSemiprimeRow t := by
  have hcap : t ≤ (1 - t) / 2 := by linarith [ht.2]
  have hp := ContinuousOn.intervalIntegrable_of_Icc hcap
    (p5U7ComponentPrimeKernel_row_continuousOn ht)
  have hs := ContinuousOn.intervalIntegrable_of_Icc hcap
    (p5U7ComponentSemiprimeKernel_row_continuousOn ht)
  unfold p5U7OmegaRow p5U7ComponentPrimeRow p5U7ComponentSemiprimeRow
  rw [← intervalIntegral.integral_add hp hs]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hcap] at hu
  exact p5U7Component_kernel_split ⟨ht.1, hu.1, hu.2⟩

theorem p5U7ComponentPrimeRow_continuousOn :
    ContinuousOn p5U7ComponentPrimeRow (Icc (59 / 250 : ℝ) (1 / 3)) := by
  have ht0 : ∀ t ∈ Icc (59 / 250 : ℝ) (1 / 3), 0 < t := by
    intro t ht
    linarith [ht.1]
  have hn : ContinuousOn (fun t : ℝ => (1 - 2 * t) / t)
      (Icc (59 / 250 : ℝ) (1 / 3)) :=
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).div
      continuousOn_id (fun t ht => (ht0 t ht).ne')
  have hl := hn.log (fun t ht => (div_pos (by linarith [ht.2] : 0 < 1 - 2 * t)
    (ht0 t ht)).ne')
  have hc : ContinuousOn (fun t : ℝ => Real.log ((1 - 2 * t) / t) / (t * (1 - t)))
      (Icc (59 / 250 : ℝ) (1 / 3)) :=
    hl.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun t ht => (mul_pos (ht0 t ht) (by linarith [ht.2] : 0 < 1 - t)).ne')
  exact hc.congr (fun t ht => (p5U7ComponentPrimeRow_eq_log ht).symm)

theorem p5U7ComponentSemiprimeRow_continuousOn :
    ContinuousOn p5U7ComponentSemiprimeRow (Icc (59 / 250 : ℝ) (1 / 3)) := by
  apply ((p5U7Omega_row_continuousOn 1).sub p5U7ComponentPrimeRow_continuousOn).congr
  intro t ht
  have h := p5U7Component_row_split ht
  linarith only [h]

/-- The full genuine integral is the SUM of its distinct leading
components. This is independent of any arithmetic limiting theorem. -/
theorem p5U7Component_integral_split :
    p5U7OriginalOmegaIntegral 1 =
      p5U7ComponentPrimeIntegral + p5U7ComponentSemiprimeIntegral := by
  have hp := ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (59/250 : ℝ) ≤ 1/3)
    p5U7ComponentPrimeRow_continuousOn
  have hs := ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (59/250 : ℝ) ≤ 1/3)
    p5U7ComponentSemiprimeRow_continuousOn
  unfold p5U7ComponentPrimeIntegral p5U7ComponentSemiprimeIntegral
  rw [← intervalIntegral.integral_add hp hs]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (59/250 : ℝ) ≤ 1/3)] at ht
  exact p5U7Component_row_split ht

/-- Explicit one-dimensional prime-window leading integral. -/
theorem p5U7ComponentPrimeIntegral_eq_logIntegral :
    p5U7ComponentPrimeIntegral =
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ),
        Real.log ((1 - 2*t) / t) / (t * (1-t)) := by
  unfold p5U7ComponentPrimeIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (59/250 : ℝ) ≤ 1/3)] at ht
  exact p5U7ComponentPrimeRow_eq_log ht

/-- The separate ordered-semiprime constant is the full mean's integral
minus the actual terminal-prime leading integral. -/
theorem p5U7ComponentSemiprimeIntegral_eq_sub :
    p5U7ComponentSemiprimeIntegral =
      p5U7OriginalOmegaIntegral 1 - p5U7ComponentPrimeIntegral := by
  linarith only [p5U7Component_integral_split]

/-- This constant is an iterated integral of the ordered terminal-prime
density on u≤v≤(1-t-u)/2; no arithmetic semiprime mean is its definition. -/
theorem p5U7ComponentSemiprimeIntegral_eq_iterated :
    p5U7ComponentSemiprimeIntegral =
      ∫ t in (59/250 : ℝ)..(1/3 : ℝ),
        ∫ u in t..((1-t)/2),
          if u < (1-t)/3 then
            (∫ v in Ico u ((1-t-u)/2), 1/(t*u*v*(1-t-u-v))) else 0 := rfl

end
end ImbalancedChen
