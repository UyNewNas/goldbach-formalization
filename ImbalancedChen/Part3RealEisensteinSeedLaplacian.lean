import ImbalancedChen.Part3RealEisensteinSeedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

This module computes the actual two coordinate derivatives of a single
nonholomorphic Eisenstein lattice summand. On `y > 0`, for `(c,d) ≠ (0,0)`,
the coordinate seed `y^s / ((cx+d)^2+(cy)^2)^s` satisfies the negative
hyperbolic Laplace equation with eigenvalue `s(1-s)`. The final bridge
identifies it with the literal upper-half-plane seed in the preceding module.

This file does not interchange derivatives with the infinite primitive sum.
That requires separate local uniform majorants for both derivatives.
-/

namespace ImbalancedChen.Part3.RealEisensteinSeedLaplacian

noncomputable section

open Complex UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedConvergence

def Q (c d x y : ℝ) : ℝ := (c * x + d) ^ 2 + (c * y) ^ 2

def Qx (c d x : ℝ) : ℝ := 2 * c * (c * x + d)
def Qy (c y : ℝ) : ℝ := 2 * c ^ 2 * y

def coordinateSeed (s c d x y : ℝ) : ℝ := y ^ s * Q c d x y ^ (-s)

def firstX (s c d x y : ℝ) : ℝ :=
  -s * y ^ s * Q c d x y ^ (-s - 1) * Qx c d x

def firstY (s c d x y : ℝ) : ℝ :=
  s * y ^ (s - 1) * Q c d x y ^ (-s) -
    s * y ^ s * Q c d x y ^ (-s - 1) * Qy c y

def secondX (s c d x y : ℝ) : ℝ :=
  s * (s + 1) * y ^ s * Q c d x y ^ (-s - 2) * (Qx c d x) ^ 2 -
    s * y ^ s * Q c d x y ^ (-s - 1) * (2 * c ^ 2)

def secondY (s c d x y : ℝ) : ℝ :=
  s * (s - 1) * y ^ (s - 2) * Q c d x y ^ (-s) -
    2 * s ^ 2 * y ^ (s - 1) * Q c d x y ^ (-s - 1) * Qy c y +
    s * (s + 1) * y ^ s * Q c d x y ^ (-s - 2) * (Qy c y) ^ 2 -
    s * y ^ s * Q c d x y ^ (-s - 1) * (2 * c ^ 2)

theorem Q_pos {c d x y : ℝ} (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    0 < Q c d x y := by
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by
      rcases hcd with hc' | hd
      · exact (hc' hc).elim
      · exact hd
    simpa [Q, hc] using (sq_pos_of_ne_zero hd)
  · have hcy : c * y ≠ 0 := mul_ne_zero hc hy.ne'
    have hs : 0 < (c * y) ^ 2 := sq_pos_of_ne_zero hcy
    unfold Q
    nlinarith [sq_nonneg (c * x + d)]

private theorem Q_hasDerivAt_x (c d x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q c d t y) (Qx c d x) x := by
  have h : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    convert ((hasDerivAt_id x).const_mul c).add_const d using 1 <;> ring
  convert (h.pow 2).add_const ((c * y) ^ 2) using 1 <;> simp [Q, Qx] <;> ring

private theorem Q_hasDerivAt_y (c d x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q c d x t) (Qy c y) y := by
  have h : HasDerivAt (fun t : ℝ => c * t) c y := by
    convert (hasDerivAt_id y).const_mul c using 1 <;> ring
  convert (hasDerivAt_const y ((c * x + d) ^ 2)).add (h.pow 2)
    using 1 <;> simp [Q, Qy] <;> ring

private theorem Qx_hasDerivAt (c d x : ℝ) :
    HasDerivAt (Qx c d) (2 * c ^ 2) x := by
  have h : HasDerivAt (fun t : ℝ => c * t + d) c x := by
    convert ((hasDerivAt_id x).const_mul c).add_const d using 1 <;> ring
  convert h.const_mul (2 * c) using 1 <;> simp [Qx] <;> ring

private theorem Qy_hasDerivAt (c y : ℝ) :
    HasDerivAt (Qy c) (2 * c ^ 2) y := by
  convert (hasDerivAt_id y).const_mul (2 * c ^ 2)
    using 1 <;> simp [Qy] <;> ring

private theorem powerQ_hasDerivAt_x (s c d x y : ℝ)
    (hq : 0 < Q c d x y) :
    HasDerivAt (fun t : ℝ => Q c d t y ^ (-s))
      ((-s) * Q c d x y ^ (-s - 1) * Qx c d x) x := by
  convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := -s)
    (Or.inl hq.ne')).comp x (Q_hasDerivAt_x c d x y) using 1 <;> ring

private theorem powerQ_hasDerivAt_y (s c d x y : ℝ)
    (hq : 0 < Q c d x y) :
    HasDerivAt (fun t : ℝ => Q c d x t ^ (-s))
      ((-s) * Q c d x y ^ (-s - 1) * Qy c y) y := by
  convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := -s)
    (Or.inl hq.ne')).comp y (Q_hasDerivAt_y c d x y) using 1 <;> ring

private theorem powerQ1_hasDerivAt_x (s c d x y : ℝ)
    (hq : 0 < Q c d x y) :
    HasDerivAt (fun t : ℝ => Q c d t y ^ (-s - 1))
      ((-s - 1) * Q c d x y ^ (-s - 2) * Qx c d x) x := by
  convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := -s - 1)
    (Or.inl hq.ne')).comp x (Q_hasDerivAt_x c d x y) using 1 <;> ring

private theorem powerQ1_hasDerivAt_y (s c d x y : ℝ)
    (hq : 0 < Q c d x y) :
    HasDerivAt (fun t : ℝ => Q c d x t ^ (-s - 1))
      ((-s - 1) * Q c d x y ^ (-s - 2) * Qy c y) y := by
  convert (Real.hasDerivAt_rpow_const (x := Q c d x y) (p := -s - 1)
    (Or.inl hq.ne')).comp y (Q_hasDerivAt_y c d x y) using 1 <;> ring

/-- Actual first horizontal derivative of the single seed. -/
theorem coordinateSeed_hasDerivAt_x (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => coordinateSeed s c d t y)
      (firstX s c d x y) x := by
  have hq := Q_pos hcd hy (x := x)
  convert (powerQ_hasDerivAt_x s c d x y hq).const_mul (y ^ s)
    using 1 <;> simp [coordinateSeed, firstX] <;> ring

/-- Actual first vertical derivative of the single seed. -/
theorem coordinateSeed_hasDerivAt_y (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => coordinateSeed s c d x t)
      (firstY s c d x y) y := by
  have hq := Q_pos hcd hy (x := x)
  have hpow : HasDerivAt (fun t : ℝ => t ^ s)
      (s * y ^ (s - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  convert hpow.mul (powerQ_hasDerivAt_y s c d x y hq)
    using 1 <;> simp [coordinateSeed, firstY] <;> ring

private theorem firstX_hasDerivAt_x (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => firstX s c d t y)
      (secondX s c d x y) x := by
  have hq := Q_pos hcd hy (x := x)
  have h := (powerQ1_hasDerivAt_x s c d x y hq).mul
    (Qx_hasDerivAt c d x)
  convert h.const_mul (-s * y ^ s) using 1 <;> simp [firstX, secondX] <;> ring

private theorem firstY_hasDerivAt_y (s c d x y : ℝ)
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
  have hfirst := (hp0.mul (powerQ_hasDerivAt_y s c d x y hq)).const_mul s
  have hsecond := ((hp1.mul (powerQ1_hasDerivAt_y s c d x y hq)).mul
    (Qy_hasDerivAt c y)).const_mul s
  convert hfirst.sub hsecond using 1 <;> simp [firstY, secondY] <;> ring

theorem coordinateSeed_second_x (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => coordinateSeed s c d t y)) x =
      secondX s c d x y := by
  have hfirst : deriv (fun t : ℝ => coordinateSeed s c d t y) =
      fun t : ℝ => firstX s c d t y :=
    funext fun t => (coordinateSeed_hasDerivAt_x s c d t y hcd hy).deriv
  rw [hfirst]
  exact (firstX_hasDerivAt_x s c d x y hcd hy).deriv

theorem coordinateSeed_second_y (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => coordinateSeed s c d x t)) y =
      secondY s c d x y := by
  have hevent : (fun t : ℝ => deriv (fun r : ℝ => coordinateSeed s c d x r) t)
      =ᶠ[𝓝 y] (fun t : ℝ => firstY s c d x t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (coordinateSeed_hasDerivAt_y s c d x t hcd ht).deriv
  exact ((firstY_hasDerivAt_y s c d x y hcd hy).congr_of_eventuallyEq
    hevent.symm).deriv

/-- The negative hyperbolic Laplacian, defined using the actual two second
coordinate derivatives, on a real chart function. -/
def negativeHyperbolicLaplacian (F : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  -(y ^ 2) *
    (deriv (deriv (fun t : ℝ => F (t, y))) x +
      deriv (deriv (fun t : ℝ => F (x, t))) y)

/-- Exact algebraic cancellation of the two computed second derivatives. -/
private theorem second_sum_eigen (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    -(y ^ 2) * (secondX s c d x y + secondY s c d x y) =
      s * (1 - s) * coordinateSeed s c d x y := by
  have hq : 0 < Q c d x y := Q_pos hcd hy
  have hy1 : y ^ (s - 1) = y ^ s / y := by
    simpa only [Real.rpow_one] using Real.rpow_sub hy s 1
  have hy2 : y ^ (s - 2) = y ^ s / y ^ 2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_sub hy s 2
  have hq1 : Q c d x y ^ (-s - 1) = Q c d x y ^ (-s) / Q c d x y := by
    simpa only [Real.rpow_one] using Real.rpow_sub hq (-s) 1
  have hq2 : Q c d x y ^ (-s - 2) =
      Q c d x y ^ (-s) / Q c d x y ^ 2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_sub hq (-s) 2
  unfold secondX secondY coordinateSeed
  rw [hy1, hy2, hq1, hq2]
  dsimp [Q, Qx, Qy] at *
  field_simp [hy.ne', hq.ne'] <;> ring

/-- A genuine nonzero real-parameter seed is a negative hyperbolic Laplace
eigenfunction with eigenvalue `s(1-s)`; no summation is involved. -/
theorem coordinateSeed_laplace_eigen (s c d x y : ℝ)
    (hcd : c ≠ 0 ∨ d ≠ 0) (hy : 0 < y) :
    negativeHyperbolicLaplacian
      (fun p : ℝ × ℝ => coordinateSeed s c d p.1 p.2) x y =
      s * (1 - s) * coordinateSeed s c d x y := by
  rw [negativeHyperbolicLaplacian,
    coordinateSeed_second_x s c d x y hcd hy,
    coordinateSeed_second_y s c d x y hcd hy]
  exact second_sum_eigen s c d x y hcd hy

/-- The coordinate function is exactly the genuine upper-half-plane seed,
since the quadratic `Q` is the squared norm of `c*z+d`. -/
theorem coordinateSeed_eq_seed (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ) :
    coordinateSeed s (v 0 : ℝ) (v 1 : ℝ) z.re z.im = seed s z v := by
  let L : ℂ := (v 0 : ℂ) * (z : ℂ) + (v 1 : ℂ)
  have hQ : Q (v 0 : ℝ) (v 1 : ℝ) z.re z.im = ‖L‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Q, L, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] <;> ring
  have hpow : (‖L‖ ^ 2) ^ (-s) = ‖L‖ ^ (-(2 * s)) := by
    calc
      (‖L‖ ^ 2) ^ (-s) = ‖L‖ ^ ((2 : ℝ) * (-s)) := by
        simpa only [Real.rpow_natCast] using
          (Real.rpow_mul (norm_nonneg L) 2 (-s)).symm
      _ = ‖L‖ ^ (-(2 * s)) := by congr 1; ring
  simp only [coordinateSeed, seed, hQ, hpow, L]

/-- The actual upper-half-plane seed has the claimed eigenvalue in its real
coordinate chart, for each nonzero integer pair. -/
theorem actual_seed_laplace_eigen (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ)
    (hv : v ≠ 0) :
    negativeHyperbolicLaplacian
      (fun p : ℝ × ℝ => coordinateSeed s (v 0 : ℝ) (v 1 : ℝ) p.1 p.2)
      z.re z.im = s * (1 - s) * seed s z v := by
  have hcd : (v 0 : ℝ) ≠ 0 ∨ (v 1 : ℝ) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    ext i
    fin_cases i
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  rw [← coordinateSeed_eq_seed s z v]
  exact coordinateSeed_laplace_eigen s (v 0 : ℝ) (v 1 : ℝ)
    z.re z.im hcd z.im_pos

end

end ImbalancedChen.Part3.RealEisensteinSeedLaplacian
