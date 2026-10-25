import ImbalancedChen.Part3CompletedEisensteinMeromorphic
import ImbalancedChen.Part3ActualEisensteinPointwiseFourier
import ImbalancedChen.Part3PrimitiveEisensteinParameterAutomorphy
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.Uniqueness

/-!
The explicit meromorphic Fourier expression is the actual completion of
the primitive Eisenstein series on Re(s)>1. Its SL(2,Z) automorphy then
extends to the connected complex plane with 0 and 1 removed, by the analytic
identity principle. No reconstruction or automorphy premise is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section

open Set Filter Complex
open scoped Topology UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAutomorphy
open ImbalancedChen.Part3.ActualComplexEisensteinCanonicalFourier
open ImbalancedChen.Part3ActualEisensteinPointwiseFourier
open ImbalancedChen.Part3ActualCanonicalEisensteinFourierSeries
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

namespace ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a

def completionFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)

private theorem completedZeta_factor {t : ℂ} (ht : 0 < t.re) :
    completedRiemannZeta t =
      (Real.pi : ℂ) ^ (-t / 2) * Complex.Gamma (t / 2) * riemannZeta t := by
  have ht0 : t ≠ 0 := by intro h; subst t; simpa using ht
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos ht
  have h := (eq_div_iff hg).mp (riemannZeta_def_of_ne_zero ht0)
  simpa only [Complex.Gammaℝ_def, mul_comm, mul_left_comm, mul_assoc] using h.symm

theorem completionFactor_eq_completedZeta {s : ℂ} (hs : 1 < s.re) :
    completionFactor s = completedRiemannZeta (2 * s) := by
  have ht : 0 < (2 * s).re := by simp; linarith
  rw [completedZeta_factor ht]
  rw [show -(2 * s) / 2 = -s by ring, show (2 * s) / 2 = s by ring]
  rfl

private theorem denominator_ne_zero {s : ℂ} (hs : 1 < s.re) :
    Complex.Gamma s * riemannZeta (2 * s) ≠ 0 := by
  apply mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  apply riemannZeta_ne_zero_of_one_lt_re
  simp
  linarith

private theorem pi_shift (s : ℂ) :
    (Real.pi : ℂ) ^ (-s) * (Real.sqrt Real.pi : ℂ) =
      (Real.pi : ℂ) ^ (-(s - 1 / 2)) := by
  have hhalf : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    simpa only [Real.rpow_half, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)
  rw [hhalf, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  congr 1
  ring

theorem completionFactor_mul_scattering {s : ℂ} (hs : 1 < s.re) :
    completionFactor s * complexScattering s = completedRiemannZeta (2 * s - 1) := by
  have hd := denominator_ne_zero hs
  have hg := (mul_ne_zero_iff.mp hd).1
  have hz := (mul_ne_zero_iff.mp hd).2
  have ht : 0 < (2 * s - 1).re := by simp; linarith
  calc
    _ = (Real.pi : ℂ) ^ (-s) * (Real.sqrt Real.pi : ℂ) *
        Complex.Gamma (s - 1 / 2) * riemannZeta (2 * s - 1) := by
      unfold completionFactor complexScattering
      field_simp [hg, hz]
      <;> ring
    _ = completedRiemannZeta (2 * s - 1) := by
      rw [pi_shift, completedZeta_factor ht,
        show -(2 * s - 1) / 2 = -(s - 1 / 2) by ring,
        show (2 * s - 1) / 2 = s - 1 / 2 by ring]

theorem completionFactor_mul_nonzeroNormalization {s : ℂ} (hs : 1 < s.re) (y : ℝ) :
    completionFactor s * nonzeroNormalization s y = 2 * (Real.sqrt y : ℂ) := by
  have hd := denominator_ne_zero hs
  have hg := (mul_ne_zero_iff.mp hd).1
  have hz := (mul_ne_zero_iff.mp hd).2
  have hp : (Real.pi : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold completionFactor nonzeroNormalization
  rw [Complex.cpow_neg]
  field_simp [hg, hz, hp]
  <;> ring

/-- Actual identification, with the original primitive sum and all normalization factors. -/
theorem completedFourier_eq_completion_of_primitive
    (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    completedEisensteinFourier s y x =
      completionFactor s * primitiveComplexEisenstein s (horizontalPoint y hy x) := by
  have hhalf : s ≠ 1 / 2 := by
    intro h
    subst s
    norm_num at hs
  rw [completedEisensteinFourier_eq_raw s y x hhalf,
    primitiveComplexEisenstein_pointwise_fourier y hy s hs x]
  symm
  calc
    _ = completionFactor s * (y : ℂ) ^ s +
        (completionFactor s * complexScattering s) * (y : ℂ) ^ (1 - s) +
        (completionFactor s * nonzeroNormalization s y) *
          ∑' n, nonzeroFrequencyPair n s y x := by ring
    _ = _ := by rw [completionFactor_mul_scattering hs,
      completionFactor_mul_nonzeroNormalization hs, completionFactor_eq_completedZeta hs]

/-- The actual meromorphic continuation, now expressed on native upper-half-plane points. -/
def completedActualEisenstein (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  completedEisensteinFourier s z.im z.re

theorem completedActualEisenstein_eq_initial (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) :
    completedActualEisenstein s z = completionFactor s * primitiveComplexEisenstein s z := by
  have hz : horizontalPoint z.im z.im_pos z.re = z := by
    ext <;> rfl
  simpa only [completedActualEisenstein, hz] using
    completedFourier_eq_completion_of_primitive z.im z.im_pos s hs z.re

theorem completedActualEisenstein_meromorphic (z : UpperHalfPlane) :
    Meromorphic (fun s => completedActualEisenstein s z) :=
  completedEisensteinFourier_meromorphic z.im_pos z.re

theorem completedActualEisenstein_analyticOnNhd (z : UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun s => completedActualEisenstein s z) ({0, 1} : Set ℂ)ᶜ := by
  intro s hs
  have hs' : s ≠ 0 ∧ s ≠ 1 := by simpa using hs
  exact completedEisensteinFourier_analyticAt z.im_pos z.re hs'.1 hs'.2

private theorem poleExcluded_isPreconnected :
    IsPreconnected (({0, 1} : Set ℂ)ᶜ) := by
  have hc : ({0, 1} : Set ℂ).Countable := (Set.finite_pair 0 1).countable
  have hr : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  exact (Set.Countable.isConnected_compl_of_one_lt_rank hr hc).isPreconnected

/-- Genuine native modular automorphy, propagated from the reconstructed
primitive series through the connected pole-excluded complex plane. -/
theorem completedActualEisenstein_SL2_invariant
    (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (gamma : SL(2, ℤ)) (z : UpperHalfPlane) :
    completedActualEisenstein s (gamma • z) = completedActualEisenstein s z := by
  have heq : (fun w => completedActualEisenstein w (gamma • z)) =ᶠ[𝓝 (2 : ℂ)]
      (fun w => completedActualEisenstein w z) := by
    have hhalf : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hhalf] with w hw
    rw [completedActualEisenstein_eq_initial w hw,
      completedActualEisenstein_eq_initial w hw,
      primitiveComplexEisenstein_SL2_invariant w hw gamma z]
  have htwo : (2 : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by norm_num
  have hglobal := (completedActualEisenstein_analyticOnNhd (gamma • z)).eqOn_of_preconnected_of_eventuallyEq
    (completedActualEisenstein_analyticOnNhd z) poleExcluded_isPreconnected htwo heq
  exact hglobal (by simpa using And.intro hs₀ hs₁)

end ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
