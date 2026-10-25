import ImbalancedChen.Part3PrimitiveRealEisensteinFirstDerivatives
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

Second derivative exchange for the genuine real primitive Eisenstein series.
We differentiate the literal first-derivative sums using the concrete second
derivative majorants and then sum the already calculated seed Laplace identity.
The conclusion is the real-chart Laplace eigenrelation for the actual primitive
series when s > 1. No eigenrelation, derivative exchange, or spectral identity
for the infinite series appears among the hypotheses.
-/

namespace ImbalancedChen.Part3.PrimitiveRealEisensteinLaplacian

noncomputable section

open Set Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedLaplacian
open ImbalancedChen.Part3.RealEisensteinDerivativeMajorant
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.PrimitiveRealEisensteinFirstDerivatives

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

private theorem q_hasDerivAt_x (c d x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q c d t y) (Qx c d x) x := by
  have h : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    convert ((hasDerivAt_id x).const_mul c).add_const d using 1 <;> ring
  convert (h.pow 2).add_const ((c * y) ^ 2) using 1 <;>
    simp [Q, Qx] <;> ring

private theorem q_hasDerivAt_y (c d x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q c d x t) (Qy c y) y := by
  have h : HasDerivAt (fun t : ℝ => c * t) c y := by
    convert (hasDerivAt_id y).const_mul c using 1 <;> ring
  convert (hasDerivAt_const y ((c * x + d) ^ 2)).add (h.pow 2)
    using 1 <;> simp [Q, Qy] <;> ring

private theorem qpow_hasDerivAt_y (p c d x y : ℝ) (hq : 0 < Q c d x y) :
    HasDerivAt (fun t : ℝ => Q c d x t ^ p)
      (p * Q c d x y ^ (p - 1) * Qy c y) y := by
  convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := p)
    (Or.inl hq.ne')).comp y (q_hasDerivAt_y c d x y) using 1 <;> ring

/-- Differentiate the explicit horizontal first derivative of one seed. -/
theorem firstX_hasDerivAt_x (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => firstX s c d t y)
      (secondX s c d x y) x := by
  have hq := Q_pos hcd hy (x := x)
  have hp : HasDerivAt (fun t : ℝ => Q c d t y ^ (-s - 1))
      ((-s - 1) * Q c d x y ^ (-s - 2) * Qx c d x) x := by
    convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := -s - 1)
      (Or.inl hq.ne')).comp x (q_hasDerivAt_x c d x y) using 1 <;> ring
  have hqx : HasDerivAt (Qx c d) (2 * c ^ 2) x := by
    have h : HasDerivAt (fun t : ℝ => c * t + d) c x := by
      convert ((hasDerivAt_id x).const_mul c).add_const d using 1 <;> ring
    convert h.const_mul (2 * c) using 1 <;> simp [Qx] <;> ring
  convert (hp.mul hqx).const_mul (-s * y ^ s) using 1 <;>
    simp [firstX, secondX] <;> ring

/-- Differentiate the explicit vertical first derivative of one seed. -/
theorem firstY_hasDerivAt_y (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => firstY s c d x t)
      (secondY s c d x y) y := by
  have hq := Q_pos hcd hy (x := x)
  have hp0 : HasDerivAt (fun t : ℝ => t ^ (s - 1))
      ((s - 1) * y ^ (s - 2)) y := by
    convert (Real.hasDerivAt_rpow_const (x := y) (p := s - 1)
      (Or.inl hy.ne')) using 1 <;> ring
  have hp1 : HasDerivAt (fun t : ℝ => t ^ s)
      (s * y ^ (s - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have hq0 : HasDerivAt (fun t : ℝ => Q c d x t ^ (-s))
      ((-s) * Q c d x y ^ (-s - 1) * Qy c y) y :=
    qpow_hasDerivAt_y (-s) c d x y hq
  have hq1 : HasDerivAt (fun t : ℝ => Q c d x t ^ (-s - 1))
      ((-s - 1) * Q c d x y ^ (-s - 2) * Qy c y) y := by
    convert qpow_hasDerivAt_y (-s - 1) c d x y hq using 1 <;> ring
  have hqy : HasDerivAt (Qy c) (2 * c ^ 2) y := by
    convert (hasDerivAt_id y).const_mul (2 * c ^ 2)
      using 1 <;> simp [Qy] <;> ring
  have hfirst := (hp0.mul hq0).const_mul s
  have hsecond := ((hp1.mul hq1).mul hqy).const_mul s
  convert hfirst.sub hsecond using 1 <;> simp [firstY, secondY] <;> ring

/-- Absolute convergence of the horizontal second derivative series. -/
theorem secondX_summable (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : PrimitivePair =>
      secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  apply Summable.of_norm_bounded
    ((primitive_coordinateSeed_summable s hs x y hy).mul_left (s * (s + 3) / y ^ 2))
  intro v
  calc
    ‖secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y‖ =
        |secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| := Real.norm_eq_abs _
    _ ≤ s * (s + 3) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y / y ^ 2 :=
      abs_secondX_le s _ _ x y hs (primitive_nonzero v) hy
    _ = (s * (s + 3) / y ^ 2) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by ring

/-- Absolute convergence of the vertical second derivative series. -/
theorem secondY_summable (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    Summable (fun v : PrimitivePair =>
      secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
  apply Summable.of_norm_bounded
    ((primitive_coordinateSeed_summable s hs x y hy).mul_left
      ((9 * s ^ 2 + 5 * s) / y ^ 2))
  intro v
  calc
    ‖secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y‖ =
        |secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y| := Real.norm_eq_abs _
    _ ≤ (9 * s ^ 2 + 5 * s) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y /
        y ^ 2 := abs_secondY_le s _ _ x y hs (primitive_nonzero v) hy
    _ = ((9 * s ^ 2 + 5 * s) / y ^ 2) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by ring

/-- Differentiate the actual horizontal first-derivative sum. -/
theorem primitive_firstX_tsum_hasDerivAt_x (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt
      (fun t : ℝ => ∑' v : PrimitivePair, firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) t y)
      (∑' v : PrimitivePair, secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) x := by
  let A : ℝ := |x| + 1
  let C : ℝ := y ^ s * EisensteinSeries.r ⟨⟨A, y⟩, hy⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    (s * (s + 3) / y ^ 2 * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u :=
    (lattice_summable s hs).mul_left (s * (s + 3) / y ^ 2 * C)
  have hx : x ∈ Ioo (x - 1) (x + 1) := by constructor <;> linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := u)
    (t := Ioo (x - 1) (x + 1)) hu isOpen_Ioo isPreconnected_Ioo
    (fun v t ht => firstX_hasDerivAt_x s _ _ t y (primitive_nonzero v) hy)
    ?_ hx (firstX_summable s x y hs hy) hx
  intro v t ht
  have htA : |t| ≤ A := by
    apply abs_le.mpr
    constructor <;> dsimp [A] <;>
      linarith [neg_abs_le x, le_abs_self x, ht.1, ht.2]
  have hb := (coordinateDerivatives_boundedStrip s hs A y y t y hy
    htA le_rfl le_rfl v).2.2.1
  simpa only [Real.norm_eq_abs, u, C] using hb

/-- Differentiate the actual vertical first-derivative sum. -/
theorem primitive_firstY_tsum_hasDerivAt_y (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    HasDerivAt
      (fun t : ℝ => ∑' v : PrimitivePair, firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x t)
      (∑' v : PrimitivePair, secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) y := by
  have hB : 0 < y / 2 := by linarith
  let C : ℝ := (3 * y / 2) ^ s *
    EisensteinSeries.r ⟨⟨|x|, y / 2⟩, hB⟩ ^ (-(2 * s))
  let u : PrimitivePair → ℝ := fun v =>
    ((9 * s ^ 2 + 5 * s) / (y / 2) ^ 2 * C) * ‖v.1‖ ^ (-(2 * s))
  have hu : Summable u :=
    (lattice_summable s hs).mul_left ((9 * s ^ 2 + 5 * s) / (y / 2) ^ 2 * C)
  have hyI : y ∈ Ioo (y / 2) (3 * y / 2) := by constructor <;> linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := u)
    (t := Ioo (y / 2) (3 * y / 2)) hu isOpen_Ioo isPreconnected_Ioo
    (fun v t ht => firstY_hasDerivAt_y s _ _ x t (primitive_nonzero v)
      (hB.trans ht.1))
    ?_ hyI (firstY_summable s x y hs hy) hyI
  intro v t ht
  have hb := (coordinateDerivatives_boundedStrip s hs |x| (y / 2)
    (3 * y / 2) x t hB le_rfl ht.1.le ht.2.le v).2.2.2
  simpa only [Real.norm_eq_abs, u, C] using hb

/-- The actual second horizontal coordinate derivative of the normalized series. -/
theorem coordinateEisenstein_second_x (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => coordinateEisenstein s t y)) x =
      (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by
  have hfirst : deriv (fun t : ℝ => coordinateEisenstein s t y) =
      (fun t => (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        firstX s (v.1 0 : ℝ) (v.1 1 : ℝ) t y) :=
    funext fun t => (coordinateEisenstein_hasDerivAt_x s t y hs hy).deriv
  rw [hfirst]
  exact ((primitive_firstX_tsum_hasDerivAt_x s x y hs hy).const_mul (1 / 2 : ℝ)).deriv

/-- The actual second vertical coordinate derivative of the normalized series. -/
theorem coordinateEisenstein_second_y (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => coordinateEisenstein s x t)) y =
      (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by
  have hevent : (fun t : ℝ => deriv (fun r : ℝ => coordinateEisenstein s x r) t)
      =ᶠ[𝓝 y] (fun t => (1 / 2 : ℝ) * ∑' v : PrimitivePair,
        firstY s (v.1 0 : ℝ) (v.1 1 : ℝ) x t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (coordinateEisenstein_hasDerivAt_y s x t hs ht).deriv
  have hsum := (primitive_firstY_tsum_hasDerivAt_y s x y hs hy).const_mul (1 / 2 : ℝ)
  exact (hsum.congr_of_eventuallyEq hevent.symm).deriv

private theorem primitive_second_sum_eigen (s x y : ℝ) (hs : 1 < s) (hy : 0 < y) :
    -(y ^ 2) *
      ((∑' v : PrimitivePair, secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) +
        (∑' v : PrimitivePair, secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y)) =
      s * (1 - s) * ∑' v : PrimitivePair,
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by
  have hv (v : PrimitivePair) :
      -(y ^ 2) *
        (secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y +
          secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) =
        s * (1 - s) * coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := by
    have h := coordinateSeed_laplace_eigen s (v.1 0 : ℝ) (v.1 1 : ℝ)
      x y (primitive_nonzero v) hy
    change -(y ^ 2) *
      (deriv (deriv (fun t : ℝ => coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) t y)) x +
        deriv (deriv (fun t : ℝ => coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x t)) y) = _ at h
    rw [coordinateSeed_second_x s _ _ x y (primitive_nonzero v) hy,
      coordinateSeed_second_y s _ _ x y (primitive_nonzero v) hy] at h
    exact h
  calc
    _ = ∑' v : PrimitivePair, -(y ^ 2) *
        (secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y +
          secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
      rw [tsum_mul_left, (secondX_summable s x y hs hy).tsum_add
        (secondY_summable s x y hs hy)]
    _ = ∑' v : PrimitivePair, s * (1 - s) *
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y := tsum_congr hv
    _ = _ := tsum_mul_left

/-- Genuine Laplace eigenrelation of the normalized primitive infinite series.
All summability and both second derivative exchanges are established above. -/
theorem coordinateEisenstein_laplace_eigen (s x y : ℝ)
    (hs : 1 < s) (hy : 0 < y) :
    negativeHyperbolicLaplacian (fun p : ℝ × ℝ => coordinateEisenstein s p.1 p.2) x y =
      s * (1 - s) * coordinateEisenstein s x y := by
  change -(y ^ 2) *
    (deriv (deriv (fun t : ℝ => coordinateEisenstein s t y)) x +
      deriv (deriv (fun t : ℝ => coordinateEisenstein s x t)) y) = _
  rw [coordinateEisenstein_second_x s x y hs hy,
    coordinateEisenstein_second_y s x y hs hy]
  calc
    _ = (1 / 2 : ℝ) * (-(y ^ 2) *
        ((∑' v : PrimitivePair, secondX s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) +
          (∑' v : PrimitivePair, secondY s (v.1 0 : ℝ) (v.1 1 : ℝ) x y))) := by ring
    _ = (1 / 2 : ℝ) * (s * (1 - s) * ∑' v : PrimitivePair,
        coordinateSeed s (v.1 0 : ℝ) (v.1 1 : ℝ) x y) := by
      rw [primitive_second_sum_eigen s x y hs hy]
    _ = _ := by unfold coordinateEisenstein; ring

/-- The actual previously constructed automorphic primitive Eisenstein series
has eigenvalue s(1-s) in its real chart throughout the half plane s > 1. -/
theorem actualEisenstein_laplace_eigen (s : ℝ) (hs : 1 < s) (z : UpperHalfPlane) :
    negativeHyperbolicLaplacian (fun p : ℝ × ℝ => coordinateEisenstein s p.1 p.2)
      z.re z.im = s * (1 - s) * primitiveEisenstein s z := by
  rw [← coordinateEisenstein_eq_actual s z]
  exact coordinateEisenstein_laplace_eigen s z.re z.im hs z.im_pos

end

end ImbalancedChen.Part3.PrimitiveRealEisensteinLaplacian
