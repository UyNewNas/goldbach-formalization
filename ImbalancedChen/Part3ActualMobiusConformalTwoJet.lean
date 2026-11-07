import ImbalancedChen.Part3Gamma0CompactTensorPoincareC2Core
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual SL(2,Z) action has horizontal/vertical velocities a and a*I,
and accelerations b and -b, where a=(cz+d)^(-2), b=-2c(cz+d)^(-3).
All derivatives below are derivatives of the ACTUAL ofComplex action,
not formal seed eigenrelations. A genuine real-bilinear Hessian trace
calculation cancels mixed terms, and the actual imaginary-part formula
supplies y²*normSq(a)=Im(gz)².

This is the conformal TWO-JET and weighted second-chain algebra needed
for general C2 pullback equivariance. The arbitrary outer-function chain
and identification with the existing upperMaass/chartMaass operator are
separate next steps; no equivariance conclusion is supplied as a premise.
-/

namespace ImbalancedChen.Part3.ActualMobiusConformalTwoJet20261025a

noncomputable section
open Complex Filter Topology Matrix
open scoped UpperHalfPlane MatrixGroups

def realMatrix (g : SL(2, ℤ)) : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ g

/-- Literal action, extended only to state local ordinary derivatives. -/
def actualMobius (g : SL(2, ℤ)) (w : ℂ) : ℂ :=
  ((realMatrix g • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)

def factor (g : SL(2, ℤ)) (w : ℂ) : ℂ :=
  1 / UpperHalfPlane.denom (realMatrix g) w ^ 2

def curvature (g : SL(2, ℤ)) (w : ℂ) : ℂ :=
  -(2 * ((realMatrix g) 1 0 : ℂ)) / UpperHalfPlane.denom (realMatrix g) w ^ 3

theorem actualMobius_eq_smul (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    actualMobius g z = ((g • z : UpperHalfPlane) : ℂ) := by
  simp [actualMobius, realMatrix, UpperHalfPlane.ofComplex_apply]

theorem denom_ne_zero (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    UpperHalfPlane.denom (realMatrix g) (z : ℂ) ≠ 0 :=
  UpperHalfPlane.denom_ne_zero _ z

/-- The pinned genuine holomorphic action derivative, specialized to det=1. -/
theorem actualMobius_hasDerivAt (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    HasDerivAt (actualMobius g) (factor g z) (z : ℂ) := by
  have hdet : (realMatrix g).val.det = 1 := by simp [realMatrix]
  have h := UpperHalfPlane.hasStrictDerivAt_smul
    (g := realMatrix g) (by rw [hdet]; norm_num) z
  simpa only [actualMobius, factor, hdet, Complex.ofReal_one] using h.hasDerivAt

theorem factor_hasDerivAt (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    HasDerivAt (factor g) (curvature g z) (z : ℂ) := by
  have hd := denom_ne_zero g z
  have hden : HasDerivAt (fun w : ℂ => UpperHalfPlane.denom (realMatrix g) w)
      ((realMatrix g) 1 0 : ℂ) (z : ℂ) := by
    simpa only [UpperHalfPlane.denom] using
      ((hasDerivAt_id (z : ℂ)).const_mul ((realMatrix g) 1 0 : ℂ)).add_const
        ((realMatrix g) 1 1 : ℂ)
  convert (hden.pow 2).inv (pow_ne_zero 2 hd) using 1
  · simp only [factor, one_div]
  · dsimp [curvature]
    field_simp [hd]
    <;> ring

/-- The complex second derivative is computed from an actual local
derivative identity on the open upper half-plane. -/
theorem actualMobius_second_deriv (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    deriv (deriv (actualMobius g)) (z : ℂ) = curvature g z := by
  have heq : deriv (actualMobius g) =ᶠ[𝓝 (z : ℂ)] factor g := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    exact (actualMobius_hasDerivAt g ⟨w, hw⟩).deriv
  exact ((factor_hasDerivAt g z).congr_of_eventuallyEq heq.symm).deriv

def linePullback (g : SL(2, ℤ)) (z v : ℂ) (t : ℝ) : ℂ :=
  actualMobius g (z + (t : ℂ) * v)

def lineVelocity (g : SL(2, ℤ)) (z v : ℂ) (t : ℝ) : ℂ :=
  factor g (z + (t : ℂ) * v) * v

theorem linePullback_hasDerivAt
    (g : SL(2, ℤ)) (z v : ℂ) (t : ℝ) (ht : 0 < (z + (t : ℂ) * v).im) :
    HasDerivAt (linePullback g z v) (lineVelocity g z v t) t := by
  have hp : HasDerivAt (fun w : ℂ => z + w * v) v (t : ℂ) := by
    convert ((hasDerivAt_id (t : ℂ)).mul_const v).const_add z using 1 <;> ring
  have h := (actualMobius_hasDerivAt g ⟨z + (t : ℂ) * v, ht⟩).comp (t : ℂ) hp
  simpa only [linePullback, lineVelocity] using h.comp_ofReal

theorem lineVelocity_hasDerivAt_zero (g : SL(2, ℤ)) (z : UpperHalfPlane) (v : ℂ) :
    HasDerivAt (lineVelocity g z v) (curvature g z * v * v) 0 := by
  have hp : HasDerivAt (fun w : ℂ => (z : ℂ) + w * v) v 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).mul_const v).const_add (z : ℂ) using 1 <;> ring
  have hf : HasDerivAt (factor g) (curvature g z) ((z : ℂ) + (0 : ℂ) * v) := by
    simpa only [zero_mul, add_zero] using factor_hasDerivAt g z
  have h := (hf.comp (0 : ℂ) hp).comp_ofReal.mul_const v
  simpa only [lineVelocity] using h

theorem linePullback_second_zero (g : SL(2, ℤ)) (z : UpperHalfPlane) (v : ℂ) :
    deriv (deriv (linePullback g z v)) 0 = curvature g z * v * v := by
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < ((z : ℂ) + (t : ℂ) * v).im := by
    have hc : Continuous (fun t : ℝ => ((z : ℂ) + (t : ℂ) * v).im) := by fun_prop
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      hc.continuousAt.eventually (Ioi_mem_nhds z.im_pos)
  have heq : deriv (linePullback g z v) =ᶠ[𝓝 0] lineVelocity g z v := by
    filter_upwards [hpos] with t ht
    exact (linePullback_hasDerivAt g z v t ht).deriv
  exact ((lineVelocity_hasDerivAt_zero g z v).congr_of_eventuallyEq heq.symm).deriv

/-- Actual horizontal/vertical first derivatives form a complex rotation
and dilation. -/
theorem actual_mobius_first_trace_data (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    deriv (linePullback g z 1) 0 = factor g z ∧
      deriv (linePullback g z Complex.I) 0 = factor g z * Complex.I := by
  constructor
  · simpa only [lineVelocity, Complex.ofReal_zero, zero_mul, add_zero, mul_one] using
      (linePullback_hasDerivAt g z 1 0 (by simpa using z.im_pos)).deriv
  · simpa only [lineVelocity, Complex.ofReal_zero, zero_mul, add_zero] using
      (linePullback_hasDerivAt g z Complex.I 0 (by simpa using z.im_pos)).deriv

/-- The acceleration trace of the ACTUAL action is zero. -/
theorem actual_mobius_second_trace_zero (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    deriv (deriv (linePullback g z 1)) 0 +
      deriv (deriv (linePullback g z Complex.I)) 0 = 0 := by
  rw [linePullback_second_zero, linePullback_second_zero]
  simp [mul_assoc, Complex.I_sq]

/-- Real-bilinear Hessian trace under an arbitrary complex dilation.
The two mixed Hessian terms cancel without assuming Hessian symmetry. -/
theorem real_bilinear_conformal_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (a : ℂ) :
    B a a + B (a * Complex.I) (a * Complex.I) =
      (Complex.normSq a : ℂ) * (B 1 1 + B Complex.I Complex.I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im a).symm
  have hai : a * Complex.I = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.real_smul] <;> ring
  calc
    _ = B (a.re • (1 : ℂ) + a.im • Complex.I) (a.re • (1 : ℂ) + a.im • Complex.I) +
        B ((-a.im) • (1 : ℂ) + a.re • Complex.I) ((-a.im) • (1 : ℂ) + a.re • Complex.I) :=
      congrArg₂ (fun u v : ℂ => B u u + B v v) ha hai
    _ = _ := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_add, smul_smul, Complex.real_smul,
        Complex.normSq_apply]
      push_cast
      ring

/-- Exact hyperbolic compensation for the actual determinant-one action. -/
theorem height_sq_mul_normSq_factor (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    z.im ^ 2 * Complex.normSq (factor g z) = (g • z).im ^ 2 := by
  have him : (g • z).im = z.im / Complex.normSq (UpperHalfPlane.denom (realMatrix g) (z : ℂ)) := by
    simpa [realMatrix] using z.im_smul_eq_div_normSq (realMatrix g)
  have hn : Complex.normSq (factor g z) =
      1 / Complex.normSq (UpperHalfPlane.denom (realMatrix g) (z : ℂ)) ^ 2 := by
    simp [factor, Complex.normSq_div, map_pow]
  rw [hn, him, div_pow]
  ring

/-- The genuine conformal second-chain algebra for arbitrary OUTER real
Hessian B and first derivative D. No outer eigenfunction is involved. -/
theorem actual_weighted_secondChain_trace
    (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (D : ℂ →L[ℝ] ℂ) :
    -((z.im : ℂ) ^ 2 *
      (B (deriv (linePullback g z 1) 0) (deriv (linePullback g z 1) 0) +
        B (deriv (linePullback g z Complex.I) 0) (deriv (linePullback g z Complex.I) 0) +
        D (deriv (deriv (linePullback g z 1)) 0 +
          deriv (deriv (linePullback g z Complex.I)) 0))) =
      -(((g • z).im : ℂ) ^ 2 * (B 1 1 + B Complex.I Complex.I)) := by
  rw [(actual_mobius_first_trace_data g z).1, (actual_mobius_first_trace_data g z).2,
    actual_mobius_second_trace_zero, map_zero, add_zero, real_bilinear_conformal_trace]
  have hc : (z.im : ℂ) ^ 2 * (Complex.normSq (factor g z) : ℂ) = ((g • z).im : ℂ) ^ 2 := by
    exact_mod_cast height_sq_mul_normSq_factor g z
  rw [← mul_assoc, hc]

end
end ImbalancedChen.Part3.ActualMobiusConformalTwoJet20261025a
