import ImbalancedChen.Part3ContinuedFourierMomentSeriesCalculus
import ImbalancedChen.Part3ComplexOrderKQODE
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The literal continued completed nonconstant Fourier kernel satisfies the
Maass eigenrelation at every complex s and every positive real height.
Both pure second coordinate derivatives are actual derivatives of the
infinite kernel, obtained from the moment-series exchanges. The seed ODE
is the actual unrestricted complex-order qMoment equation, multiplied by
the genuine frequency/divisor coefficient and summed absolutely.

This proves the nonconstant eigenrelation. A two-variable C2 theorem and
the completed constant term, including the central divided difference,
remain separate work.
-/

namespace ImbalancedChen.Part3.ContinuedFourierNonconstantMaass

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.ComplexOrderKQCalculus
open ImbalancedChen.Part3.ComplexOrderKQODE
open ImbalancedChen.Part3.ContinuedFourierSpatialMoments
open ImbalancedChen.Part3.ContinuedFourierWeightedMixed
open ImbalancedChen.Part3.ContinuedFourierMomentSeriesCalculus

def root0 (y : ℝ) : ℂ := ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ)
def root1 (y : ℝ) : ℂ := (((1 / 2 : ℝ) * y ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ)
def root2 (y : ℝ) : ℂ :=
  (((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) * y ^ ((1 / 2 : ℝ) - 2) : ℝ) : ℂ)

theorem root0_eq_sqrt (y : ℝ) : root0 y = (Real.sqrt y : ℂ) := by
  rw [root0, Real.sqrt_eq_rpow]

theorem root0_hasDerivAt {y : ℝ} (hy : 0 < y) : HasDerivAt root0 (root1 y) y := by
  exact (Real.hasDerivAt_rpow_const (x := y) (p := (1 / 2 : ℝ))
    (Or.inl hy.ne')).ofReal_comp

theorem root1_hasDerivAt {y : ℝ} (hy : 0 < y) : HasDerivAt root1 (root2 y) y := by
  have h := ((Real.hasDerivAt_rpow_const (x := y) (p := (1 / 2 : ℝ) - 1)
    (Or.inl hy.ne')).const_mul (1 / 2 : ℝ)).ofReal_comp
  convert h using 1 <;> simp [root1, root2] <;> norm_num <;> ring

theorem root1_relation {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * root1 y = (1 / 2 : ℂ) * root0 y := by
  have h : y * ((1 / 2 : ℝ) * y ^ ((1 / 2 : ℝ) - 1)) =
      (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_sub hy (1 / 2 : ℝ) 1, Real.rpow_one]
    field_simp [hy.ne'] <;> ring
  simpa only [root0, root1, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal h

theorem root2_relation {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * root2 y = -(1 / 4 : ℂ) * root0 y := by
  have h : y ^ 2 * ((1 / 2 : ℝ) * ((1 / 2 : ℝ) - 1) *
      y ^ ((1 / 2 : ℝ) - 2)) = -(1 / 4 : ℝ) * y ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_sub hy (1 / 2 : ℝ) 2]
    norm_num
    field_simp [hy.ne'] <;> ring
  simpa only [root0, root2, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal h

/-- Actual frequency-rescaled K equation for one literal Fourier term. -/
theorem spatialMomentTerm_equation (n : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ 2 * (spatialMomentTerm 0 2 n s y x + spatialMomentTerm 2 0 n s y x) +
      (y : ℂ) * spatialMomentTerm 0 1 n s y x -
        (s - 1 / 2) ^ 2 * spatialMomentTerm 0 0 n s y x = 0 := by
  have hw : 0 < frequency (n + 1) := by unfold frequency; positivity
  have h := complexOrderK_qMoment_ODE (s - 1 / 2) (mul_pos hw hy)
  have hI : (Complex.I * (frequency (n + 1) : ℂ)) ^ 2 =
      -(frequency (n + 1) : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  unfold spatialMomentTerm
  simp only [pow_zero, pow_one, mul_one, qMoment_zero]
  rw [hI]
  push_cast at h
  linear_combination (spectralCoefficient n s * phase (n + 1) x) * h

/-- The actual K ODE can be summed because every derivative family here is
already absolutely convergent; no summed ODE is assumed. -/
theorem momentSum_equation (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ 2 * (momentSum 0 2 s y x + momentSum 2 0 s y x) +
      (y : ℂ) * momentSum 0 1 s y x - (s - 1 / 2) ^ 2 * momentSum 0 0 s y x = 0 := by
  have h02 := (spatialMoment_norm_summable 0 2 s hy x).of_norm
  have h20 := (spatialMoment_norm_summable 2 0 s hy x).of_norm
  have h01 := (spatialMoment_norm_summable 0 1 s hy x).of_norm
  have h00 := (spatialMoment_norm_summable 0 0 s hy x).of_norm
  have h2 := (h02.add h20).mul_left ((y : ℂ) ^ 2)
  have h1 := h01.mul_left (y : ℂ)
  have hn := h00.mul_left ((s - 1 / 2) ^ 2)
  have hsum := tsum_congr (fun n : ℕ => spatialMomentTerm_equation n s y x hy)
  simp only [tsum_zero] at hsum
  rw [(h2.add h1).tsum_sub hn, h2.tsum_add h1, tsum_mul_left, tsum_mul_left,
    tsum_mul_left, h02.tsum_add h20] at hsum
  exact hsum

theorem signedMomentSum_equation (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ 2 * (signedMomentSum 0 2 s y x + signedMomentSum 2 0 s y x) +
      (y : ℂ) * signedMomentSum 0 1 s y x -
        (s - 1 / 2) ^ 2 * signedMomentSum 0 0 s y x = 0 := by
  have hp := momentSum_equation s y x hy
  have hn := momentSum_equation s y (-x) hy
  unfold signedMomentSum
  norm_num
  linear_combination hp + hn

def weightedKernelY (s : ℂ) (y x : ℝ) : ℂ :=
  2 * root1 y * signedMomentSum 0 0 s y x + 2 * root0 y * signedMomentSum 0 1 s y x

def weightedKernelXX (s : ℂ) (y x : ℝ) : ℂ :=
  2 * root0 y * signedMomentSum 2 0 s y x

def weightedKernelYY (s : ℂ) (y x : ℝ) : ℂ :=
  2 * root2 y * signedMomentSum 0 0 s y x + 4 * root1 y * signedMomentSum 0 1 s y x +
    2 * root0 y * signedMomentSum 0 2 s y x

theorem weightedKernel_hasDerivAt_y (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => weightedKernel s t x) (weightedKernelY s y x) y := by
  have hevent : (fun t : ℝ => weightedKernel s t x) =ᶠ[𝓝 y]
      (fun t => 2 * root0 t * signedMomentSum 0 0 s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    rw [weightedKernel, root0_eq_sqrt, signedMomentSum_zero_zero_eq_actual s t x ht]
  have h := ((root0_hasDerivAt hy).const_mul (2 : ℂ)).mul
    (signedMomentSum_hasDerivAt_y 0 0 s y x hy)
  exact h.congr_of_eventuallyEq hevent

theorem weightedKernelY_hasDerivAt_y (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => weightedKernelY s t x) (weightedKernelYY s y x) y := by
  have h0 := signedMomentSum_hasDerivAt_y 0 0 s y x hy
  have h1 := signedMomentSum_hasDerivAt_y 0 1 s y x hy
  have hr0 := root0_hasDerivAt hy
  have hr1 := root1_hasDerivAt hy
  have h := ((hr1.const_mul (2 : ℂ)).mul h0).add ((hr0.const_mul (2 : ℂ)).mul h1)
  convert h using 1 <;> simp [weightedKernelY, weightedKernelYY] <;> ring

theorem weightedKernel_second_x (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => weightedKernel s y t)) x = weightedKernelXX s y x := by
  have hfirst : deriv (fun t : ℝ => weightedKernel s y t) =
      (fun t => weightedKernelX s y t) :=
    funext fun t => (weightedKernel_hasDerivAt_x s y t hy).deriv
  rw [hfirst]
  have h := (signedMomentSum_hasDerivAt_x 1 0 s y x hy).const_mul (2 * root0 y)
  simpa only [weightedKernelX, weightedKernelXX, root0_eq_sqrt] using h.deriv

theorem weightedKernel_second_y (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (deriv (fun t : ℝ => weightedKernel s t x)) y = weightedKernelYY s y x := by
  have hevent : (fun t : ℝ => deriv (fun r : ℝ => weightedKernel s r x) t)
      =ᶠ[𝓝 y] (fun t => weightedKernelY s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (weightedKernel_hasDerivAt_y s t x ht).deriv
  exact ((weightedKernelY_hasDerivAt_y s y x hy).congr_of_eventuallyEq hevent).deriv

/-- Literal negative hyperbolic Laplacian using actual real derivatives and
complex values, independently of the held real-coordinate Laplacian chain. -/
def maassLaplacian (F : ℝ × ℝ → ℂ) (x y : ℝ) : ℂ :=
  -(y : ℂ) ^ 2 *
    (deriv (deriv (fun t : ℝ => F (t, y))) x +
      deriv (deriv (fun t : ℝ => F (x, t))) y)

/-- The continued completed nonconstant Fourier kernel is an actual Maass
eigenfunction for every complex parameter, without an ODE supplier premise. -/
theorem weightedKernel_maass_eigen (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    maassLaplacian (fun p : ℝ × ℝ => weightedKernel s p.2 p.1) x y =
      s * (1 - s) * weightedKernel s y x := by
  change -(y : ℂ) ^ 2 *
    (deriv (deriv (fun t : ℝ => weightedKernel s y t)) x +
      deriv (deriv (fun t : ℝ => weightedKernel s t x)) y) = _
  rw [weightedKernel_second_x s y x hy, weightedKernel_second_y s y x hy]
  have hode := signedMomentSum_equation s y x hy
  have h1 := root1_relation hy
  have h2 := root2_relation hy
  have hweight : weightedKernel s y x = 2 * root0 y * signedMomentSum 0 0 s y x := by
    rw [weightedKernel, root0_eq_sqrt, signedMomentSum_zero_zero_eq_actual s y x hy]
  rw [hweight]
  unfold weightedKernelXX weightedKernelYY
  linear_combination -(2 * root0 y) * hode -
    (4 * (y : ℂ) * signedMomentSum 0 1 s y x) * h1 -
      (2 * signedMomentSum 0 0 s y x) * h2

end

end ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
