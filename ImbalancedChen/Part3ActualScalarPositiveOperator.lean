import ImbalancedChen.Part3ActualScalarRealPolarization
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Actual complex polarization of the actual scalar measures. Sesquilinearity
is derived, not assumed. Native positive-semidefinite Cauchy--Schwarz gives
the sharp norm bound. Riesz representation then constructs an actual bounded
positive contraction E_B with diagonal coefficient equal to the actual
scalar measure on B. No idempotence or projection multiplication is claimed.
-/

namespace ImbalancedChen.Part3.ActualScalarPositiveOperator20261025a

noncomputable section
open Set MeasureTheory InnerProductSpace
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualScalarMeasureQuadratic20261025a
open ImbalancedChen.Part3.ActualScalarRealPolarization20261025a

/-- Conjugate linear in u and linear in v, matching Lean's inner product. -/
def cross (B : Set ResolventSpectrum) (u v : HyperbolicL2) : ℂ :=
  (realPolar B u v : ℂ) + Complex.I * (realPolar B (Complex.I • u) v : ℂ)

theorem cross_conj_symm (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    (starRingEnd ℂ) (cross B v u) = cross B u v := by
  unfold cross
  rw [realPolar_symm B v u, realPolar_I_swap B v u,
    realPolar_symm B v (Complex.I • u)]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem cross_add_left (B : Set ResolventSpectrum) (u v w : HyperbolicL2) :
    cross B (u + v) w = cross B u w + cross B v w := by
  simp only [cross, smul_add, realPolar_add_left, Complex.ofReal_add]
  ring

theorem cross_real_smul_left (B : Set ResolventSpectrum) (c : ℝ)
    (u v : HyperbolicL2) : cross B (c • u) v = (c : ℂ) * cross B u v := by
  have hi : Complex.I • (c • u) = c • (Complex.I • u) := smul_comm _ _ _
  unfold cross
  rw [hi, realPolar_smul_left, realPolar_smul_left]
  simp only [Complex.ofReal_mul]
  ring

theorem cross_I_left (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    cross B (Complex.I • u) v = -Complex.I * cross B u v := by
  simp only [cross, smul_smul, Complex.I_mul_I, neg_one_smul,
    realPolar_neg_left, Complex.ofReal_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem cross_smul_left (B : Set ResolventSpectrum) (z : ℂ)
    (u v : HyperbolicL2) : cross B (z • u) v = (starRingEnd ℂ) z * cross B u v := by
  have hz : z • u = z.re • u + z.im • (Complex.I • u) := by
    calc
      z • u = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • u := by
        rw [Complex.re_add_im]
      _ = _ := by
        simp only [add_smul, mul_smul, ← RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hc : (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
    simpa only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_neg, ← sub_eq_add_neg] using
      congrArg (starRingEnd ℂ) (Complex.re_add_im z).symm
  rw [hz, cross_add_left, cross_real_smul_left, cross_real_smul_left, cross_I_left, hc]
  ring

theorem cross_add_right (B : Set ResolventSpectrum) (u v w : HyperbolicL2) :
    cross B u (v + w) = cross B u v + cross B u w := by
  apply (starRingEnd ℂ).injective
  rw [map_add, cross_conj_symm, cross_conj_symm, cross_conj_symm]
  exact cross_add_left B v w u

theorem cross_smul_right (B : Set ResolventSpectrum) (z : ℂ)
    (u v : HyperbolicL2) : cross B u (z • v) = z * cross B u v := by
  apply (starRingEnd ℂ).injective
  rw [map_mul, cross_conj_symm, cross_conj_symm]
  exact cross_smul_left B z v u

theorem cross_self (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    cross B u u = (spectralQuadratic B u : ℂ) := by
  simp only [cross, realPolar_self, realPolar_I_self, Complex.ofReal_zero, mul_zero, add_zero]

/-- This core is used only to invoke its algebraic Cauchy--Schwarz theorem.
It does not replace the actual Hilbert space's existing norm or inner product. -/
def crossCore (B : Set ResolventSpectrum) : PreInnerProductSpace.Core ℂ HyperbolicL2 where
  inner := cross B
  conj_inner_symm := cross_conj_symm B
  re_inner_nonneg u := by
    rw [cross_self, Complex.ofReal_re]
    exact spectralQuadratic_nonneg B u
  add_left := cross_add_left B
  smul_left u v z := cross_smul_left B z u v

theorem cross_norm_sq_le (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    ‖cross B u v‖ ^ 2 ≤ spectralQuadratic B u * spectralQuadratic B v := by
  letI : PreInnerProductSpace.Core ℂ HyperbolicL2 := crossCore B
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) u v
  change ‖cross B u v‖ * ‖cross B v u‖ ≤
    (cross B u u).re * (cross B v v).re at h
  have hn : ‖cross B v u‖ = ‖cross B u v‖ := by
    simpa only [Complex.norm_conj] using congrArg norm (cross_conj_symm B u v)
  rw [cross_self, cross_self, Complex.ofReal_re, Complex.ofReal_re, hn] at h
  simpa only [pow_two] using h

/-- The sharp bound uses actual scalar-mass domination by the original norm. -/
theorem cross_norm_le (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    ‖cross B u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h := cross_norm_sq_le B u v
  have hp := mul_le_mul (spectralQuadratic_le_norm_sq B u)
    (spectralQuadratic_le_norm_sq B v) (spectralQuadratic_nonneg B v) (sq_nonneg ‖u‖)
  have hn := mul_nonneg (norm_nonneg u) (norm_nonneg v)
  nlinarith [norm_nonneg (cross B u v)]

def crossLinear (B : Set ResolventSpectrum) (u : HyperbolicL2) : HyperbolicL2 →ₗ[ℂ] ℂ where
  toFun := cross B u
  map_add' := cross_add_right B u
  map_smul' z v := cross_smul_right B z u v

def crossFunctional (B : Set ResolventSpectrum) (u : HyperbolicL2) : HyperbolicL2 →L[ℂ] ℂ :=
  (crossLinear B u).mkContinuous ‖u‖ (cross_norm_le B u)

theorem crossFunctional_norm_le (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    ‖crossFunctional B u‖ ≤ ‖u‖ :=
  (crossFunctional B u).opNorm_le_bound (norm_nonneg u) (cross_norm_le B u)

/-- Actual Riesz representing vector of the genuine mixed scalar coefficients. -/
def representingVector (B : Set ResolventSpectrum) (u : HyperbolicL2) : HyperbolicL2 :=
  (InnerProductSpace.toDual ℂ HyperbolicL2).symm (crossFunctional B u)

theorem representingVector_inner (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    inner ℂ (representingVector B u) v = cross B u v :=
  InnerProductSpace.toDual_symm_apply

theorem representingVector_add (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    representingVector B (u + v) = representingVector B u + representingVector B v := by
  apply ext_inner_right ℂ
  intro w
  rw [inner_add_left, representingVector_inner, representingVector_inner,
    representingVector_inner, cross_add_left]

theorem representingVector_smul (B : Set ResolventSpectrum) (z : ℂ) (u : HyperbolicL2) :
    representingVector B (z • u) = z • representingVector B u := by
  apply ext_inner_right ℂ
  intro w
  rw [inner_smul_left, representingVector_inner, representingVector_inner, cross_smul_left]

theorem representingVector_norm_le (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    ‖representingVector B u‖ ≤ ‖u‖ := by
  unfold representingVector
  rw [(InnerProductSpace.toDual ℂ HyperbolicL2).symm.norm_map]
  exact crossFunctional_norm_le B u

def representingLinear (B : Set ResolventSpectrum) : HyperbolicL2 →ₗ[ℂ] HyperbolicL2 where
  toFun := representingVector B
  map_add' := representingVector_add B
  map_smul' := representingVector_smul B

/-- The actual bounded positive contraction supplied by a spectral set.
The name is deliberately not a projection assertion. -/
def spectralEffect (B : Set ResolventSpectrum) : HyperbolicL2 →L[ℂ] HyperbolicL2 :=
  (representingLinear B).mkContinuous 1 (by
    intro u
    simpa only [one_mul] using representingVector_norm_le B u)

theorem spectralEffect_inner (B : Set ResolventSpectrum) (u v : HyperbolicL2) :
    inner ℂ (spectralEffect B u) v = cross B u v := representingVector_inner B u v

theorem spectralEffect_diagonal (B : Set ResolventSpectrum) (u : HyperbolicL2) :
    inner ℂ (spectralEffect B u) u = (spectralQuadratic B u : ℂ) := by
  rw [spectralEffect_inner, cross_self]

theorem spectralEffect_symmetric (B : Set ResolventSpectrum) :
    (spectralEffect B).IsSymmetric := by
  intro u v
  rw [spectralEffect_inner, ← inner_conj_symm, spectralEffect_inner, cross_conj_symm]

theorem spectralEffect_positive (B : Set ResolventSpectrum) :
    (spectralEffect B).IsPositive := by
  refine ⟨spectralEffect_symmetric B, ?_⟩
  intro u
  change 0 ≤ (inner ℂ (spectralEffect B u) u).re
  rw [spectralEffect_diagonal, Complex.ofReal_re]
  exact spectralQuadratic_nonneg B u

theorem spectralEffect_norm_le_one (B : Set ResolventSpectrum) :
    ‖spectralEffect B‖ ≤ 1 := by
  apply (spectralEffect B).opNorm_le_bound zero_le_one
  intro u
  simpa only [one_mul] using representingVector_norm_le B u

end
end ImbalancedChen.Part3.ActualScalarPositiveOperator20261025a
