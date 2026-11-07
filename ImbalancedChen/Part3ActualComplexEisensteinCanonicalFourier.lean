import ImbalancedChen.Part3PrimitiveEisensteinFourierParameterAnalytic
import ImbalancedChen.Part3ActualEisensteinCanonicalFourier
import ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The literal complex-parameter primitive Eisenstein Fourier coefficient has
the canonical Gamma/zeta/divisor/K formula throughout Re(s)>1. The actual
Fourier integral is holomorphic by its proved uniform spatial/parameter
majorants. The explicit right side is holomorphic using Gamma and zeta in
their regular half planes and the actual complex-order K integral. Its real
restriction agrees exactly with the separately proved real Fourier caller.
The identity theorem on the connected right half plane completes the proof.

No Fourier identity, analytic RHS, or identity-theorem conclusion is an
input to the public actual coefficient theorems below.
-/

namespace ImbalancedChen.Part3.ActualComplexEisensteinCanonicalFourier

noncomputable section

open Set Complex Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.ActualEisensteinCanonicalFourier20261025a
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
open ImbalancedChen.Part3.ComplexOrderKEntire20261025a

def initialHalfPlane : Set ℂ := {s | 1 < s.re}

def complexScattering (s : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) * riemannZeta (2 * s - 1) /
    (Complex.Gamma s * riemannZeta (2 * s))

def complexNonzeroCoefficient (s : ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  ((2 : ℂ) * (Real.pi : ℂ) ^ s) / (Complex.Gamma s * riemannZeta (2 * s)) *
    (((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * divisorFactor n.natAbs (2 * s) *
      (Real.sqrt y : ℂ) * complexOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y))

def complexCanonicalCoefficient (s : ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  if n = 0 then (y : ℂ) ^ s + complexScattering s * (y : ℂ) ^ (1 - s)
  else complexNonzeroCoefficient s y n

private theorem gamma_differentiableAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gamma s := by
  apply Complex.differentiableAt_Gamma s
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

private theorem zeta_differentiableAt_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ riemannZeta s := by
  apply differentiableAt_riemannZeta
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.one_re] at hre
  linarith

private theorem two_mul_re_gt (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s).re := by
  simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
  linarith

private theorem shifted_two_mul_re_gt (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s - 1).re := by
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
  linarith

private theorem denominator_differentiableAt (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma w * riemannZeta (2 * w)) s :=
  (gamma_differentiableAt_of_re_pos (by linarith : 0 < s.re)).mul
    ((zeta_differentiableAt_of_one_lt_re (two_mul_re_gt s hs)).comp s
      (differentiableAt_id.const_mul (2 : ℂ)))

private theorem denominator_ne_zero (s : ℂ) (hs : 1 < s.re) :
    Complex.Gamma s * riemannZeta (2 * s) ≠ 0 :=
  mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_lt_re (two_mul_re_gt s hs))

theorem complexScattering_differentiableAt (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ complexScattering s := by
  have hhalf : 0 < (s - 1 / 2).re := by
    simp only [Complex.sub_re]
    norm_num
    linarith
  have hg := (gamma_differentiableAt_of_re_pos hhalf).comp s
    (differentiableAt_id.sub_const (1 / 2 : ℂ))
  have hz := (zeta_differentiableAt_of_one_lt_re (shifted_two_mul_re_gt s hs)).comp s
    ((differentiableAt_id.const_mul (2 : ℂ)).sub_const 1)
  exact ((differentiableAt_const.mul hg).mul hz).div
    (denominator_differentiableAt s hs) (denominator_ne_zero s hs)

theorem complexNonzeroCoefficient_differentiableAt
    (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun w => complexNonzeroCoefficient w y n) s := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hna : 0 < |(n : ℝ)| := abs_pos.mpr hnR
  have hnaC : ((|(n : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hna.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ w) s :=
    differentiableAt_id.const_cpow (.inl hpiC)
  have hnPow : DifferentiableAt ℂ (fun w : ℂ =>
      ((|(n : ℝ)| : ℝ) : ℂ) ^ (w - 1 / 2)) s :=
    (differentiableAt_id.sub_const _).const_cpow (.inl hnaC)
  have hd : Differentiable ℂ (fun w : ℂ => divisorFactor n.natAbs (2 * w)) := by
    unfold divisorFactor
    apply Differentiable.fun_sum
    intro d hd
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
    exact (differentiable_const.sub (differentiable_id.const_mul (2 : ℂ))).const_cpow (.inl hdC)
  have hq : 0 < 2 * Real.pi * |(n : ℝ)| * y := by positivity
  have hK : DifferentiableAt ℂ (fun w : ℂ =>
      complexOrderK (w - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y)) s :=
    (complexOrderK_differentiable_all hq).differentiableAt.comp s
      (differentiableAt_id.sub_const _)
  exact ((differentiableAt_const.mul hp).div (denominator_differentiableAt s hs)
    (denominator_ne_zero s hs)).mul
      (((hnPow.mul hd.differentiableAt).mul_const (Real.sqrt y : ℂ)).mul hK)

theorem complexCanonicalCoefficient_differentiableOn (y : ℝ) (hy : 0 < y) (n : ℤ) :
    DifferentiableOn ℂ (fun s => complexCanonicalCoefficient s y n) initialHalfPlane := by
  intro s hs
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  by_cases hn : n = 0
  · subst n
    have hp : DifferentiableAt ℂ (fun w : ℂ => (y : ℂ) ^ w) s :=
      differentiableAt_id.const_cpow (.inl hyC)
    have hq : DifferentiableAt ℂ (fun w : ℂ => (y : ℂ) ^ (1 - w)) s :=
      (differentiableAt_const.sub differentiableAt_id).const_cpow (.inl hyC)
    simpa only [complexCanonicalCoefficient, if_true] using
      (hp.add ((complexScattering_differentiableAt s hs).mul hq)).differentiableWithinAt
  · simpa only [complexCanonicalCoefficient, if_neg hn] using
      (complexNonzeroCoefficient_differentiableAt y hy n hn s hs).differentiableWithinAt

theorem complexCanonicalCoefficient_analyticOnNhd (y : ℝ) (hy : 0 < y) (n : ℤ) :
    AnalyticOnNhd ℂ (fun s => complexCanonicalCoefficient s y n) initialHalfPlane :=
  (complexCanonicalCoefficient_differentiableOn y hy n).analyticOnNhd
    (isOpen_Ioi.preimage Complex.continuous_re)

theorem complexScattering_ofReal (t : ℝ) : complexScattering (t : ℂ) = canonicalScattering t := by
  have hh : (t : ℂ) - 1 / 2 = ((t - 1 / 2 : ℝ) : ℂ) := by push_cast
  have h2 : 2 * (t : ℂ) = ((2 * t : ℝ) : ℂ) := by push_cast
  have h21 : 2 * (t : ℂ) - 1 = ((2 * t - 1 : ℝ) : ℂ) := by push_cast
  unfold complexScattering canonicalScattering
  rw [hh, h21, h2, Complex.Gamma_ofReal, Complex.Gamma_ofReal]

theorem complexNonzeroCoefficient_ofReal (t y : ℝ) (n : ℤ) :
    complexNonzeroCoefficient (t : ℂ) y n = canonicalNonzeroCoefficient t y n := by
  have hh : (t : ℂ) - 1 / 2 = ((t - 1 / 2 : ℝ) : ℂ) := by push_cast
  have h2 : 2 * (t : ℂ) = ((2 * t : ℝ) : ℂ) := by push_cast
  unfold complexNonzeroCoefficient canonicalNonzeroCoefficient canonicalDivisorFactor
  simp only [hh, h2]
  rw [Complex.Gamma_ofReal, divisorFactor_ofReal,
    complexOrderK_real, ← Complex.ofReal_cpow Real.pi_pos.le t,
    ← Complex.ofReal_cpow (abs_nonneg (n : ℝ)) (t - 1 / 2)]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

theorem complexCanonicalCoefficient_ofReal (t y : ℝ) (hy : 0 < y) (n : ℤ) :
    complexCanonicalCoefficient (t : ℂ) y n = canonicalFourierCoefficient t y n := by
  by_cases hn : n = 0
  · subst n
    have h1 : 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast
    simp only [complexCanonicalCoefficient, canonicalFourierCoefficient, if_true]
    rw [complexScattering_ofReal, h1, ← Complex.ofReal_cpow hy.le t,
      ← Complex.ofReal_cpow hy.le (1 - t)]
  · simp only [complexCanonicalCoefficient, canonicalFourierCoefficient, if_neg hn]
    exact complexNonzeroCoefficient_ofReal t y n

theorem primitiveComplexEisenstein_ofReal (t : ℝ) (z : UpperHalfPlane) :
    primitiveComplexEisenstein (t : ℂ) z = (primitiveEisenstein t z : ℂ) := by
  unfold primitiveComplexEisenstein primitiveEisenstein
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_tsum]
  congr 1
  apply tsum_congr
  intro v
  exact complexSeed_ofReal z v t

theorem fourierPhase_eq_realCaller (n : ℤ) (x : ℝ) :
    fourierPhase n x =
      ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini.fourierPhase n x := by
  unfold fourierPhase ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini.fourierPhase
  congr 1
  push_cast
  ring

/-- The real restriction is the already proved actual primitive Fourier
caller, including all Gamma, zeta, divisor, K and factor-two conventions. -/
theorem actualPrimitiveFourier_ofReal (t : ℝ) (ht : 1 < t)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    actualPrimitiveFourier y hy n (t : ℂ) = canonicalFourierCoefficient t y n := by
  calc
    _ = ∫ x in (0 : ℝ)..1,
        ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini.fourierPhase n x *
          (primitiveEisenstein t
            (ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a.horizontalPoint
              y hy x) : ℂ) := by
      unfold actualPrimitiveFourier
      apply intervalIntegral.integral_congr
      intro x hx
      rw [fourierIntegrand, primitiveComplexEisenstein_ofReal, fourierPhase_eq_realCaller]
      rfl
    _ = _ := primitiveEisenstein_scalar_fourier t ht y hy n

/-- The literal actual complex Fourier integral equals its explicit canonical
value on the full initial half plane. No real or complex identity is assumed. -/
theorem actualPrimitiveFourier_eq_complexCanonical
    (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    actualPrimitiveFourier y hy n s = complexCanonicalCoefficient s y n := by
  have hf : AnalyticOnNhd ℂ (actualPrimitiveFourier y hy n) initialHalfPlane :=
    actualPrimitiveFourier_analyticOnNhd y hy n
  have hg := complexCanonicalCoefficient_analyticOnNhd y hy n
  have hU : IsPreconnected initialHalfPlane := (Complex.convex_halfSpace_re_gt (r := 1)).isPreconnected
  have h2 : (2 : ℂ) ∈ initialHalfPlane := by norm_num [initialHalfPlane]
  have hclosure : (2 : ℂ) ∈ closure
      ({z : ℂ | actualPrimitiveFourier y hy n z = complexCanonicalCoefficient z y n} \ {2}) := by
    have hreal : (2 : ℝ) ∈ closure (Ioi (2 : ℝ)) := by simp
    have himage : (2 : ℂ) ∈ closure (Complex.ofReal '' Ioi (2 : ℝ)) :=
      mem_closure_image Complex.continuous_ofReal.continuousAt hreal
    apply (closure_mono ?_) himage
    rintro z ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · change actualPrimitiveFourier y hy n (t : ℂ) = complexCanonicalCoefficient (t : ℂ) y n
      rw [actualPrimitiveFourier_ofReal t (by linarith) y hy n,
        complexCanonicalCoefficient_ofReal t y hy n]
    · simp only [mem_singleton_iff]
      intro h
      have ht2 : t = 2 := by exact_mod_cast h
      linarith
  exact (hf.eqOn_of_preconnected_of_mem_closure hg hU h2 hclosure) s hs

/-- Explicit actual constant Fourier coefficient for every Re(s)>1. -/
theorem actualPrimitiveFourier_zero_complex
    (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    actualPrimitiveFourier y hy 0 s =
      (y : ℂ) ^ s + complexScattering s * (y : ℂ) ^ (1 - s) := by
  simpa only [complexCanonicalCoefficient, if_true] using
    actualPrimitiveFourier_eq_complexCanonical y hy 0 s hs

/-- Explicit actual nonzero Fourier coefficient for every Re(s)>1. -/
theorem actualPrimitiveFourier_nonzero_complex
    (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    actualPrimitiveFourier y hy n s = complexNonzeroCoefficient s y n := by
  simpa only [complexCanonicalCoefficient, if_neg hn] using
    actualPrimitiveFourier_eq_complexCanonical y hy n s hs

end

end ImbalancedChen.Part3.ActualComplexEisensteinCanonicalFourier
