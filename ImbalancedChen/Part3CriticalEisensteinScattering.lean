import ImbalancedChen.Part3ActualComplexEisensteinCanonicalFourier
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Topology.Piecewise
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Actual full-level scalar scattering on the critical line. The existing
Gamma/zeta scattering coefficient is identified with the actual completed
zeta quotient on its explicit Gamma-pole-excluded domain. Native zeta
conjugation and the completed functional equation show that the critical
numerator is the conjugate of the denominator. Native nonvanishing on
Re(z)>=1 then proves norm one for EVERY nonzero real t, with no assumed
nonzero denominator.

The central value t=0 is supplied by the TRUE completed-zeta pole limits:
residue -1 at0 divided by residue +1 at1 yields the removable value -1.
We define the continuous central extension by that value. In particular
neither the totalized completed-zeta quotient at t=0 nor the totalized
Gamma expression at its Gamma pole is asserted to be the removable value.
This is the full-level scalar scattering factor, not a level-N matrix.
-/

namespace ImbalancedChen.Part3.CriticalEisensteinScattering20261025a

noncomputable section

open Set Filter Topology
open Complex
open ImbalancedChen.Part3.ActualComplexEisensteinCanonicalFourier

/-- The actual completed-zeta scattering quotient away from its poles. -/
def completedScattering (s : ℂ) : ℂ :=
  completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)

/-- The literal critical-line parameter. -/
def criticalParameter (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I

@[simp] theorem criticalParameter_re (t : ℝ) : (criticalParameter t).re = 1 / 2 := by
  simp [criticalParameter]

@[simp] theorem criticalParameter_im (t : ℝ) : (criticalParameter t).im = t := by
  simp [criticalParameter]

/-- Recover completed zeta from its Gamma-real dictionary on an explicitly
nonzero-Gamma point. This is a pinned definition identity, not a premise. -/
theorem completedZeta_eq_gammaR_mul_zeta (z : ℂ) (hz : z ≠ 0)
    (hG : Gammaℝ z ≠ 0) :
    completedRiemannZeta z = Gammaℝ z * riemannZeta z := by
  have h := (eq_div_iff hG).mp (riemannZeta_def_of_ne_zero hz)
  simpa only [mul_comm] using h.symm

/-- The exact positive-real-base Gamma-real conjugation dictionary. -/
theorem gammaR_conj (z : ℂ) : Gammaℝ (conj z) = conj (Gammaℝ z) := by
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hp := Complex.cpow_conj (Real.pi : ℂ) (-z / 2) harg
  simp only [map_neg, map_div₀, map_ofNat, conj_ofReal] at hp
  unfold Gammaℝ
  rw [hp, Gamma_conj, map_mul]

/-- Completed-zeta conjugation on the positive-real-part region used by
the critical denominator. No unproved completed-conjugation theorem is assumed. -/
theorem completedZeta_conj_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    completedRiemannZeta (conj z) = conj (completedRiemannZeta z) := by
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hc0 : conj z ≠ 0 := by simpa using hz0
  rw [completedZeta_eq_gammaR_mul_zeta (conj z) hc0
      (Gammaℝ_ne_zero_of_re_pos (by simpa using hz)),
    completedZeta_eq_gammaR_mul_zeta z hz0 (Gammaℝ_ne_zero_of_re_pos hz),
    gammaR_conj, riemannZeta_conj, map_mul]

/-- The completed quotient equals the EXISTING actual Gamma/zeta scalar
on its explicit legal domain, retaining the sqrt(pi) normalization. -/
theorem completedScattering_eq_complexScattering (s : ℂ) (hs : 0 < s.re)
    (hshift : ∀ m : ℕ, s - 1 / 2 ≠ -(m : ℂ)) :
    completedScattering s = complexScattering s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs0 : 2 * s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [mul_re, ofNat_re, ofNat_im, zero_mul, sub_zero, zero_re] at hr
    linarith
  have hsA0 : 2 * s - 1 ≠ 0 := by
    intro h
    apply hshift 0
    norm_num
    linear_combination (1 / 2 : ℂ) * h
  have hGS : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have hGA : Gamma (s - 1 / 2) ≠ 0 := Gamma_ne_zero hshift
  have hP : (Real.pi : ℂ) ^ (-(2 * s) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hGRB : Gammaℝ (2 * s) ≠ 0 := by
    unfold Gammaℝ
    rw [show (2 * s) / 2 = s by ring]
    exact mul_ne_zero hP hGS
  have hGRA : Gammaℝ (2 * s - 1) ≠ 0 := by
    unfold Gammaℝ
    rw [show (2 * s - 1) / 2 = s - 1 / 2 by ring]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)) hGA
  have hhalf : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    simpa only [Real.sqrt_eq_rpow, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm
  have hpower : (Real.pi : ℂ) ^ (-(2 * s - 1) / 2) =
      (Real.sqrt Real.pi : ℂ) * (Real.pi : ℂ) ^ (-(2 * s) / 2) := by
    rw [show -(2 * s - 1) / 2 = (1 / 2 : ℂ) + (-(2 * s) / 2) by ring,
      Complex.cpow_add _ _ hpi, hhalf]
  rw [completedScattering, completedZeta_eq_gammaR_mul_zeta _ hsA0 hGRA,
    completedZeta_eq_gammaR_mul_zeta _ hs0 hGRB]
  unfold Gammaℝ complexScattering
  rw [hpower, show (2 * s - 1) / 2 = s - 1 / 2 by ring,
    show (2 * s) / 2 = s by ring]
  calc
    _ = ((Real.pi : ℂ) ^ (-(2 * s) / 2) *
        ((Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) * riemannZeta (2 * s - 1))) /
      ((Real.pi : ℂ) ^ (-(2 * s) / 2) * (Gamma s * riemannZeta (2 * s))) := by
      congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ hP

/-- The numerator on the critical line is the actual conjugate completed
denominator, by the FUNCTIONAL EQUATION and true zeta conjugation. -/
theorem critical_completed_numerator_eq_conj (t : ℝ) :
    completedRiemannZeta (2 * criticalParameter t - 1) =
      conj (completedRiemannZeta (2 * criticalParameter t)) := by
  have harg : 2 * criticalParameter t - 1 = 1 - conj (2 * criticalParameter t) := by
    apply Complex.ext <;> simp [criticalParameter, mul_re, mul_im] <;> ring
  rw [harg, completedRiemannZeta_one_sub]
  apply completedZeta_conj_of_re_pos
  simp [criticalParameter, mul_re, mul_im]

/-- The native closed-halfplane zeta zero-free theorem removes the
nonvanishing hypothesis entirely on this critical denominator. -/
theorem critical_completed_denominator_ne_zero (t : ℝ) :
    completedRiemannZeta (2 * criticalParameter t) ≠ 0 := by
  have hre : (2 * criticalParameter t).re = 1 := by
    simp [criticalParameter, mul_re, mul_im]
  have hz0 : 2 * criticalParameter t ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    rw [hre] at h'
    norm_num at h'
  rw [completedZeta_eq_gammaR_mul_zeta _ hz0
    (Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num))]
  exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num))
    (riemannZeta_ne_zero_of_one_le_re (by rw [hre]))

/-- The actual completed quotient has unit modulus, with no assumed
nonzero denominator. At t=0 this is only a totalized quotient statement. -/
theorem completedScattering_critical_norm (t : ℝ) :
    ‖completedScattering (criticalParameter t)‖ = 1 := by
  rw [completedScattering, critical_completed_numerator_eq_conj, norm_div, norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (critical_completed_denominator_ne_zero t))

theorem critical_gamma_shift_legal (t : ℝ) (ht : t ≠ 0) :
    ∀ m : ℕ, criticalParameter t - 1 / 2 ≠ -(m : ℂ) := by
  intro m h
  have hi := congrArg Complex.im h
  simp [criticalParameter] at hi
  exact ht hi

/-- Direct critical-line phase formula for the EXISTING Gamma/zeta scalar.
The denominator nonvanishing is separately proved, not an input. -/
theorem complexScattering_critical_eq_conj_quotient (t : ℝ) (ht : t ≠ 0) :
    complexScattering (criticalParameter t) =
      conj (completedRiemannZeta (2 * criticalParameter t)) /
        completedRiemannZeta (2 * criticalParameter t) := by
  rw [← completedScattering_eq_complexScattering _
    (by rw [criticalParameter_re]; norm_num) (critical_gamma_shift_legal t ht)]
  rw [completedScattering, critical_completed_numerator_eq_conj]
/-- The ACTUAL Gamma/zeta scattering coefficient has modulus one at
s=1/2+it for every nonzero real t, with all nonvanishing proved. -/
theorem complexScattering_critical_norm (t : ℝ) (ht : t ≠ 0) :
    ‖complexScattering (criticalParameter t)‖ = 1 := by
  rw [← completedScattering_eq_complexScattering _
    (by rw [criticalParameter_re]; norm_num) (critical_gamma_shift_legal t ht)]
  exact completedScattering_critical_norm t

/-- True residue -1 at zero of completed zeta. The central scattering
calculation uses this punctured limit instead of its totalized pole value. -/
theorem completedZeta_residue_zero :
    Tendsto (fun z : ℂ => z * completedRiemannZeta z) (𝓝[≠] 0) (𝓝 (-1)) := by
  simpa only [completedRiemannZeta, if_pos rfl] using
    HurwitzZeta.completedHurwitzZetaEven_residue_zero (0 : UnitAddCircle)

private theorem add_one_punctured :
    Tendsto (fun z : ℂ => z + 1) (𝓝[≠] 0) (𝓝[≠] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((continuous_id.add_const (1 : ℂ)).tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

/-- Ratio of the two genuine completed-zeta poles: the removable central
scattering value is -1, not a division of two junk pole values. -/
theorem completedZeta_adjacent_ratio_tendsto_zero :
    Tendsto (fun z : ℂ => completedRiemannZeta z / completedRiemannZeta (z + 1))
      (𝓝[≠] 0) (𝓝 (-1)) := by
  have hden : Tendsto (fun z : ℂ => z * completedRiemannZeta (z + 1))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa only [add_sub_cancel_right] using completedRiemannZeta_residue_one.comp add_one_punctured
  have h := completedZeta_residue_zero.div hden (by norm_num : (1 : ℂ) ≠ 0)
  apply Tendsto.congr' _ (by simpa only [div_one] using h)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact mul_div_mul_left _ _ hz0

private theorem central_affine_punctured :
    Tendsto (fun s : ℂ => 2 * s - 1) (𝓝[≠] (1 / 2)) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : Continuous (fun s : ℂ => 2 * s - 1) := by fun_prop
    simpa using (hcont.tendsto (1 / 2 : ℂ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 2 * s - 1 ≠ 0
    intro h
    apply hs
    apply Set.mem_singleton_iff.mpr
    linear_combination (1 / 2 : ℂ) * h

/-- Genuine punctured complex-parameter limit of the completed scattering
quotient at s=1/2. This is not the value of its totalized quotient there. -/
theorem completedScattering_tendsto_half :
    Tendsto completedScattering (𝓝[≠] (1 / 2)) (𝓝 (-1)) := by
  simpa only [completedScattering, sub_add_cancel] using
    completedZeta_adjacent_ratio_tendsto_zero.comp central_affine_punctured

private theorem critical_parameter_punctured :
    Tendsto criticalParameter (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : Continuous criticalParameter := by unfold criticalParameter; fun_prop
    simpa [criticalParameter] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change criticalParameter t ≠ (1 / 2 : ℂ)
    intro h
    have hi := congrArg Complex.im h
    simp only [criticalParameter_im] at hi
    exact ht (by simpa using hi)

/-- The TRUE central limit of the original Gamma/zeta scattering factor
along the critical line is -1, by the two actual completed pole residues. -/
theorem complexScattering_critical_tendsto_zero :
    Tendsto (fun t : ℝ => complexScattering (criticalParameter t))
      (𝓝[≠] 0) (𝓝 (-1)) := by
  have h := completedScattering_tendsto_half.comp critical_parameter_punctured
  apply Tendsto.congr' _ h
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact completedScattering_eq_complexScattering _
    (by rw [criticalParameter_re]; norm_num) (critical_gamma_shift_legal t ht)

/-- Actual critical scattering with its true removable central value. -/
def criticalScattering : ℝ → ℂ :=
  Function.update (fun t : ℝ => complexScattering (criticalParameter t)) 0 (-1)

@[simp] theorem criticalScattering_zero : criticalScattering 0 = -1 := by
  simp [criticalScattering]

theorem criticalScattering_of_ne_zero (t : ℝ) (ht : t ≠ 0) :
    criticalScattering t = complexScattering (criticalParameter t) := by
  exact Function.update_of_ne ht _ _

/-- The central extension is continuous at0 by the genuine punctured
pole-ratio limit. No totalized Gamma or completed-zeta value is substituted. -/
theorem criticalScattering_continuousAt_zero : ContinuousAt criticalScattering 0 := by
  rw [criticalScattering, continuousAt_update_same]
  exact complexScattering_critical_tendsto_zero

/-- Unitarity including the correctly removed central value. -/
theorem criticalScattering_norm (t : ℝ) : ‖criticalScattering t‖ = 1 := by
  by_cases ht : t = 0
  · subst t
    simp
  · rw [criticalScattering_of_ne_zero t ht]
    exact complexScattering_critical_norm t ht

end
end ImbalancedChen.Part3.CriticalEisensteinScattering20261025a



