import ImbalancedChen.Part3PrimitiveRealEisensteinFrechetDerivative
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The genuine Frechet derivative of the actual primitive Eisenstein gradient.
We first prove two-variable differentiability of firstX and firstY directly
from their real-power formulas. Their Frechet derivatives are then identified
using the already proved coordinate formulas and uniqueness of derivatives.
The derivative of the gradient is an explicit operator-valued Hessian with
summable local operator-norm bound. Mathlib's Frechet series theorem gives
the derivative of the infinite gradient series, hence the second Frechet
derivative of the normalized actual chart function.

This file proves twice Frechet differentiability. Continuity of the Hessian
series, needed for a full ContDiffOn order-two theorem, is separate work.
-/

namespace ImbalancedChen.Part3.PrimitiveRealEisensteinHessian

noncomputable section

open Set Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedLaplacian
open ImbalancedChen.Part3.RealEisensteinDerivativeMajorant
open ImbalancedChen.Part3.PrimitiveRealEisensteinFirstDerivatives
open ImbalancedChen.Part3.PrimitiveRealEisensteinLaplacian
open ImbalancedChen.Part3.PrimitiveRealEisensteinMixedDerivatives
open ImbalancedChen.Part3.PrimitiveRealEisensteinFrechetDerivative

private theorem primitive_nonzero (v : PrimitivePair) :
    (v.1 0 : ℝ) ≠ 0 ∨ (v.1 1 : ℝ) ≠ 0 := by
  by_contra h
  push_neg at h
  have hv : v.1 = 0 := by
    ext i
    fin_cases i
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hg : (v.1 0).gcd (v.1 1) = 1 := v.2.2
  simp [hv] at hg

private theorem lattice_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun v : PrimitivePair => ‖v.1‖ ^ (-(2 * s))) :=
  (EisensteinSeries.summable_one_div_norm_rpow
    (by linarith : (2 : ℝ) < 2 * s)).subtype _

def pairLinear (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem pairLinear_apply (a b : ℝ) (h : ℝ × ℝ) :
    pairLinear a b h = a * h.1 + b * h.2 := by simp [pairLinear]

theorem norm_pairLinear_le (a b : ℝ) : ‖pairLinear a b‖ ≤ |a| + |b| := by
  simpa [pairLinear, norm_smul, Real.norm_eq_abs] using
    norm_add_le (a • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (b • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Identification of a Frechet derivative from its coordinate restrictions.
The hypothesis is genuine two-variable differentiability, proved before use. -/
private theorem hasFDerivAt_pairLinear {f : ℝ × ℝ → ℝ} {x y a b : ℝ}
    (hf : DifferentiableAt ℝ f (x, y))
    (hx : HasDerivAt (fun t : ℝ => f (t, y)) a x)
    (hy : HasDerivAt (fun t : ℝ => f (x, t)) b y) :
    HasFDerivAt f (pairLinear a b) (x, y) := by
  have hpathx : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hpathy : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h1 : fderiv ℝ f (x, y) (1, 0) = a :=
    (hf.hasFDerivAt.comp_hasDerivAt x hpathx).unique hx
  have h2 : fderiv ℝ f (x, y) (0, 1) = b :=
    (hf.hasFDerivAt.comp_hasDerivAt y hpathy).unique hy
  have heq : fderiv ℝ f (x, y) = pairLinear a b := by
    ext h
    have hsplit : h = h.1 • (1, 0) + h.2 • (0, 1) := by ext <;> simp
    calc
      fderiv ℝ f (x, y) h =
          fderiv ℝ f (x, y) (h.1 • (1, 0) + h.2 • (0, 1)) := congrArg _ hsplit
      _ = h.1 * a + h.2 * b := by simp [h1, h2, smul_eq_mul]
      _ = pairLinear a b h := by simp; ring
  exact hf.hasFDerivAt.congr_fderiv heq

private theorem q_differentiableAt (c d x y : ℝ) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => Q c d p.1 p.2) (x, y) := by
  unfold Q
  fun_prop

private theorem ypow_differentiableAt (p x y : ℝ) (hy : 0 < y) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => z.2 ^ p) (x, y) :=
  (Real.differentiableAt_rpow_const_of_ne p hy.ne').comp (x, y) differentiableAt_snd

private theorem qpow_differentiableAt (p c d x y : ℝ) (hq : 0 < Q c d x y) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ => Q c d z.1 z.2 ^ p) (x, y) :=
  (Real.differentiableAt_rpow_const_of_ne p hq.ne').comp (x, y)
    (q_differentiableAt c d x y)

/-- Genuine real-pair derivative of the horizontal first seed derivative. -/
theorem firstX_hasFDerivAt (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => firstX s c d p.1 p.2)
      (pairLinear (secondX s c d x y) (mixedXY s c d x y)) (x, y) := by
  have hq : 0 < Q c d x y := Q_pos hcd hy
  have hqx : DifferentiableAt ℝ (fun p : ℝ × ℝ => Qx c d p.1) (x, y) := by
    unfold Qx
    fun_prop
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => firstX s c d p.1 p.2) (x, y) := by
    unfold firstX
    exact (((ypow_differentiableAt s x y hy).const_mul (-s)).mul
      (qpow_differentiableAt (-s - 1) c d x y hq)).mul hqx
  exact hasFDerivAt_pairLinear hd (firstX_hasDerivAt_x s c d x y hcd hy)
    (firstX_hasDerivAt_y s c d x y hcd hy)

/-- Genuine real-pair derivative of the vertical first seed derivative. -/
theorem firstY_hasFDerivAt (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => firstY s c d p.1 p.2)
      (pairLinear (mixedXY s c d x y) (secondY s c d x y)) (x, y) := by
  have hq : 0 < Q c d x y := Q_pos hcd hy
  have hqy : DifferentiableAt ℝ (fun p : ℝ × ℝ => Qy c p.2) (x, y) := by
    unfold Qy
    fun_prop
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => firstY s c d p.1 p.2) (x, y) := by
    unfold firstY
    exact (((ypow_differentiableAt (s - 1) x y hy).const_mul s).mul
      (qpow_differentiableAt (-s) c d x y hq)).sub
        ((((ypow_differentiableAt s x y hy).const_mul s).mul
          (qpow_differentiableAt (-s - 1) c d x y hq)).mul hqy)
  exact hasFDerivAt_pairLinear hd (firstY_hasDerivAt_x s c d x y hcd hy)
    (firstY_hasDerivAt_y s c d x y hcd hy)

/-- The explicit derivative of the continuous-linear-map seed gradient. -/
def seedHessian (s c d x y : ℝ) :
    (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  (pairLinear (secondX s c d x y) (mixedXY s c d x y)).smulRight
      (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (pairLinear (mixedXY s c d x y) (secondY s c d x y)).smulRight
      (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The seed gradient is truly Frechet differentiable, with this Hessian. -/
theorem seedGradient_hasFDerivAt (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasFDerivAt (fun p : ℝ × ℝ => seedGradient s c d p.1 p.2)
      (seedHessian s c d x y) (x, y) := by
  exact ((firstX_hasFDerivAt s c d x y hcd hy).smul_const
    (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
      ((firstY_hasFDerivAt s c d x y hcd hy).smul_const
        (ContinuousLinearMap.snd ℝ ℝ ℝ))

/-- Operator norm of the actual Hessian is bounded by its four entries. -/
theorem norm_seedHessian_le (s c d x y : ℝ) :
    ‖seedHessian s c d x y‖ ≤
      |secondX s c d x y| + 2 * |mixedXY s c d x y| + |secondY s c d x y| := by
  have hn : ‖seedHessian s c d x y‖ ≤
      ‖pairLinear (secondX s c d x y) (mixedXY s c d x y)‖ +
        ‖pairLinear (mixedXY s c d x y) (secondY s c d x y)‖ := by
    simpa [seedHessian] using
      norm_add_le
        ((pairLinear (secondX s c d x y) (mixedXY s c d x y)).smulRight
          (ContinuousLinearMap.fst ℝ ℝ ℝ))
        ((pairLinear (mixedXY s c d x y) (secondY s c d x y)).smulRight
          (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hx := norm_pairLinear_le (secondX s c d x y) (mixedXY s c d x y)
  have hy := norm_pairLinear_le (mixedXY s c d x y) (secondY s c d x y)
  linarith

/-- Pointwise summable comparison for the Hessian operator norm. -/
theorem norm_seedHessian_le_seed (s c d x y : ℝ) (hs : 1 < s)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    ‖seedHessian s c d x y‖ ≤
      (16 * s ^ 2 + 12 * s) * coordinateSeed s c d x y / y ^ 2 := by
  have hn := norm_seedHessian_le s c d x y
  have hx := abs_secondX_le s c d x y hs hcd hy
  have hm := abs_mixedXY_le s c d x y hs hcd hy
  have hv := abs_secondY_le s c d x y hs hcd hy
  nlinarith

theorem seedHessian_summable (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : PrimitivePair => seedHessian s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  apply Summable.of_norm_bounded
    ((primitive_coordinateSeed_summable s hs x y hy).mul_left
      ((16 * s ^ 2 + 12 * s) / y ^ 2))
  intro v
  calc
    _ ≤ (16 * s ^ 2 + 12 * s) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y ^ 2 :=
      norm_seedHessian_le_seed s _ _ x y hs (primitive_nonzero v) hy
    _ = ((16 * s ^ 2 + 12 * s) / y ^ 2) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by ring

/-- Uniform summable Hessian operator-norm bound on bounded strips. -/
theorem seedHessian_boundedStrip (s : ℝ) (hs : 1 < s)
    (A B Y x y : ℝ) (hB : 0 < B) (hx : |x| ≤ A)
    (hy : B ≤ y) (hY : y ≤ Y) (v : PrimitivePair) :
    ‖seedHessian s (v.1 0 : ℝ) (v.1 1 : ℝ) x y‖ ≤
      ((16 * s ^ 2 + 12 * s) / B ^ 2 *
        (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)))) *
        ‖v.1‖ ^ (-(2 * s)) := by
  have hn := norm_seedHessian_le s (v.1 0 : ℝ) (v.1 1 : ℝ) x y
  have hb := coordinateDerivatives_boundedStrip s hs A B Y x y hB hx hy hY v
  have hm := mixedXY_boundedStrip s hs A B Y x y hB hx hy hY v
  have hx' := hb.2.2.1
  have hy' := hb.2.2.2
  nlinarith

/-- Genuine Frechet differentiation under the operator-valued gradient sum. -/
theorem primitive_gradient_tsum_hasFDerivAt (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    HasFDerivAt
      (fun p : ℝ × ℝ => ∑' v : PrimitivePair,
        seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) p.1 p.2)
      (∑' v : PrimitivePair, seedHessian s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) (x, y) := by
  have hB : 0 < y / 2 := by linarith
  let A : ℝ := |x| + 1
  let C : ℝ := (3 * y / 2) ^ s *
    EisensteinSeries.r ⟨⟨A, y / 2⟩, hB⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    ((16 * s ^ 2 + 12 * s) / (y / 2) ^ 2 * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u :=
    (lattice_summable s hs).mul_left ((16 * s ^ 2 + 12 * s) / (y / 2) ^ 2 * C)
  have hp : (x, y) ∈ Ioo (x - 1) (x + 1) ×ˢ Ioo (y / 2) (3 * y / 2) := by
    constructor <;> constructor <;> linarith
  refine hasFDerivAt_tsum_of_isPreconnected
    (f := fun (v : PrimitivePair) (p : ℝ × ℝ) =>
      seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) p.1 p.2)
    (f' := fun (v : PrimitivePair) (p : ℝ × ℝ) =>
      seedHessian s (v.1 0 : ℝ) (v.1 1 : ℝ) p.1 p.2)
    (u := u) (s := Ioo (x - 1) (x + 1) ×ˢ Ioo (y / 2) (3 * y / 2))
    hu (isOpen_Ioo.prod isOpen_Ioo) (isPreconnected_Ioo.prod isPreconnected_Ioo)
    (fun v p ht => seedGradient_hasFDerivAt s _ _ p.1 p.2 (primitive_nonzero v)
      (hB.trans ht.2.1))
    ?_ hp (seedGradient_summable s x y hs hy) hp
  intro v p ht
  have htA : |p.1| ≤ A := by
    apply abs_le.mpr
    constructor <;> dsimp [A] <;>
      linarith [neg_abs_le x, le_abs_self x, ht.1.1, ht.1.2]
  have hb := seedHessian_boundedStrip s hs A (y / 2) (3 * y / 2)
    p.1 p.2 hB htA ht.2.1.le ht.2.2.le v
  simpa only [u, C] using hb

/-- The actual Frechet derivative of the normalized Eisenstein series is
itself Frechet differentiable, with the literal summed Hessian. -/
theorem actual_fderiv_hasFDerivAt (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    HasFDerivAt
      (fderiv ℝ (fun p : ℝ × ℝ => coordinateEisenstein s p.1 p.2))
      ((1 / 2 : ℝ) • ∑' v : PrimitivePair,
        seedHessian s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) (x, y) := by
  have hp : ∀ᶠ p : ℝ × ℝ in 𝓝 (x, y), 0 < p.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hy
  have hevent : fderiv ℝ (fun p : ℝ × ℝ => coordinateEisenstein s p.1 p.2)
      =ᶠ[𝓝 (x, y)] (fun p => (1 / 2 : ℝ) • ∑' v : PrimitivePair,
        seedGradient s (v.1 0 : ℝ) (v.1 1 : ℝ) p.1 p.2) := by
    filter_upwards [hp] with p hpos
    exact (coordinateEisenstein_hasFDerivAt s p.1 p.2 hs hpos).fderiv
  have hsum := (primitive_gradient_tsum_hasFDerivAt s x y hs hy).const_smul (1 / 2 : ℝ)
  exact hsum.congr_of_eventuallyEq hevent.symm

/-- Twice Frechet differentiability on the full positive-height chart. -/
theorem actual_fderiv_differentiableOn (s : ℝ) (hs : 1 < s) :
    DifferentiableOn ℝ
      (fderiv ℝ (fun p : ℝ × ℝ => coordinateEisenstein s p.1 p.2))
      {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  exact (actual_fderiv_hasFDerivAt s p.1 p.2 hs hp).differentiableAt.differentiableWithinAt

end

end ImbalancedChen.Part3.PrimitiveRealEisensteinHessian
