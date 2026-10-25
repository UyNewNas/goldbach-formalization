import ImbalancedChen.Part3ContinuedFourierWeightedMixed
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

Actual spatial differentiation under every continued Fourier moment series.
The x derivative uses a global summable derivative bound; the y derivative
uses a positive-height interval and the proved uniform q-moment bounds.
Both signed frequencies are retained. In particular, the actual mixed
derivative of the sqrt-weighted completed nonconstant kernel equals the
literal sum of the mixed terms computed in the preceding module.

This does not assert the completed constant-term eigenrelation or the final
continued Maass theorem.
-/

namespace ImbalancedChen.Part3.ContinuedFourierMomentSeriesCalculus

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.ContinuedFourierSpatialMoments
open ImbalancedChen.Part3.ContinuedFourierWeightedMixed

def momentSum (j k : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  ∑' n : ℕ, spatialMomentTerm j k n s y x

/-- True horizontal derivative exchange for every moment order. -/
theorem momentSum_hasDerivAt_x (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => momentSum j k s y t)
      (momentSum (j + 1) k s y x) x := by
  let M : ℕ := Nat.ceil |s.re|
  refine hasDerivAt_tsum (u := spatialMajorant (j + 1) k M y)
    (spatialMajorant_summable (j + 1) k M hy)
    (fun n t => spatialMomentTerm_hasDerivAt_x j k n s y t)
    (fun n t => spatialMomentTerm_norm_bound (j + 1) k M hy n (Nat.le_ceil _) le_rfl t)
    (spatialMoment_norm_summable j k s hy x).of_norm x

/-- True vertical derivative exchange for every moment order. -/
theorem momentSum_hasDerivAt_y (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => momentSum j k s t x)
      (momentSum j (k + 1) s y x) y := by
  let M : ℕ := Nat.ceil |s.re|
  have ha : 0 < y / 2 := by linarith
  have hyI : y ∈ Ioo (y / 2) (3 * y / 2) := by constructor <;> linarith
  refine hasDerivAt_tsum_of_isPreconnected
    (u := spatialMajorant j (k + 1) M (y / 2))
    (t := Ioo (y / 2) (3 * y / 2))
    (spatialMajorant_summable j (k + 1) M ha) isOpen_Ioo isPreconnected_Ioo
    (fun n t ht => spatialMomentTerm_hasDerivAt_y j k n s t x (ha.trans ht.1))
    (fun n t ht => spatialMomentTerm_norm_bound j (k + 1) M ha n (Nat.le_ceil _) ht.1.le x)
    hyI (spatialMoment_norm_summable j k s hy x).of_norm hyI

/-- The sign (-1)^j is forced by differentiating the negative phase. -/
def signedMomentSum (j k : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  momentSum j k s y x + (-1 : ℂ) ^ j * momentSum j k s y (-x)

theorem signedMomentSum_hasDerivAt_x (j k : ℕ) (s : ℂ)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => signedMomentSum j k s y t)
      (signedMomentSum (j + 1) k s y x) x := by
  have hp := momentSum_hasDerivAt_x j k s y x hy
  have hn := ((momentSum_hasDerivAt_x j k s y (-x) hy).comp x
    ((hasDerivAt_id x).neg)).const_mul ((-1 : ℂ) ^ j)
  convert hp.add hn using 1 <;> simp [signedMomentSum, pow_succ] <;> ring

theorem signedMomentSum_hasDerivAt_y (j k : ℕ) (s : ℂ)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => signedMomentSum j k s t x)
      (signedMomentSum j (k + 1) s y x) y := by
  exact (momentSum_hasDerivAt_y j k s y x hy).add
    ((momentSum_hasDerivAt_y j k s y (-x) hy).const_mul ((-1 : ℂ) ^ j))

theorem signedMomentSum_zero_zero_eq_actual (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    signedMomentSum 0 0 s y x = ∑' n : ℕ, nonzeroFrequencyPair n s y x := by
  unfold signedMomentSum momentSum nonzeroFrequencyPair
  simp only [pow_zero, one_mul]
  rw [← tsum_add (spatialMoment_norm_summable 0 0 s hy x).of_norm
    (spatialMoment_norm_summable 0 0 s hy (-x)).of_norm]
  apply tsum_congr
  intro n
  rw [spatialMomentTerm_zero_zero, spatialMomentTerm_zero_zero]

/-- Literal nonconstant part of the completed continued Fourier expression. -/
def weightedKernel (s : ℂ) (y x : ℝ) : ℂ :=
  2 * (Real.sqrt y : ℂ) * ∑' n : ℕ, nonzeroFrequencyPair n s y x

def weightedKernelX (s : ℂ) (y x : ℝ) : ℂ :=
  2 * (Real.sqrt y : ℂ) * signedMomentSum 1 0 s y x

def weightedKernelMixed (s : ℂ) (y x : ℝ) : ℂ :=
  2 * sqrtSlope y * signedMomentSum 1 0 s y x +
    2 * (Real.sqrt y : ℂ) * signedMomentSum 1 1 s y x

theorem weightedKernel_hasDerivAt_x (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => weightedKernel s y t) (weightedKernelX s y x) x := by
  have heq : (fun t : ℝ => weightedKernel s y t) =
      (fun t : ℝ => 2 * (Real.sqrt y : ℂ) * signedMomentSum 0 0 s y t) := by
    funext t
    rw [weightedKernel, signedMomentSum_zero_zero_eq_actual s y t hy]
  rw [heq]
  exact (signedMomentSum_hasDerivAt_x 0 0 s y x hy).const_mul (2 * (Real.sqrt y : ℂ))

theorem weightedKernelX_hasDerivAt_y (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => weightedKernelX s t x) (weightedKernelMixed s y x) y := by
  have hroot := ((Real.hasDerivAt_sqrt hy.ne').ofReal_comp).const_mul (2 : ℂ)
  have hmoment := signedMomentSum_hasDerivAt_y 1 0 s y x hy
  convert hroot.mul hmoment using 1 <;>
    simp [weightedKernelX, weightedKernelMixed, sqrtSlope] <;> ring

theorem weightedKernelMixed_eq_tsum (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    weightedKernelMixed s y x = ∑' n : ℕ, weightedPairMixed n s y x := by
  have h10p := (spatialMoment_norm_summable 1 0 s hy x).of_norm
  have h10n := (spatialMoment_norm_summable 1 0 s hy (-x)).of_norm
  have h11p := (spatialMoment_norm_summable 1 1 s hy x).of_norm
  have h11n := (spatialMoment_norm_summable 1 1 s hy (-x)).of_norm
  have h10 := (h10p.sub h10n).mul_left (2 * sqrtSlope y)
  have h11 := (h11p.sub h11n).mul_left (2 * (Real.sqrt y : ℂ))
  symm
  calc
    _ = ∑' n : ℕ,
        (2 * sqrtSlope y * (spatialMomentTerm 1 0 n s y x - spatialMomentTerm 1 0 n s y (-x)) +
          2 * (Real.sqrt y : ℂ) *
            (spatialMomentTerm 1 1 n s y x - spatialMomentTerm 1 1 n s y (-x))) := by
      apply tsum_congr
      intro n
      unfold weightedPairMixed weightedMixed
      ring
    _ = 2 * sqrtSlope y *
          ((∑' n : ℕ, spatialMomentTerm 1 0 n s y x) -
            ∑' n : ℕ, spatialMomentTerm 1 0 n s y (-x)) +
        2 * (Real.sqrt y : ℂ) *
          ((∑' n : ℕ, spatialMomentTerm 1 1 n s y x) -
            ∑' n : ℕ, spatialMomentTerm 1 1 n s y (-x)) := by
      rw [h10.tsum_add h11, tsum_mul_left, tsum_mul_left,
        h10p.tsum_sub h10n, h11p.tsum_sub h11n]
    _ = weightedKernelMixed s y x := by
      simp [weightedKernelMixed, signedMomentSum, momentSum] <;> ring

/-- Actual mixed second derivative exchange for the completed nonconstant
Fourier kernel, at every complex parameter and positive height. -/
theorem weightedKernel_actual_mixed_derivative (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun r : ℝ => weightedKernel s t r) x) y =
      ∑' n : ℕ, weightedPairMixed n s y x := by
  have hevent : (fun t : ℝ => deriv (fun r : ℝ => weightedKernel s t r) x)
      =ᶠ[𝓝 y] (fun t => weightedKernelX s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (weightedKernel_hasDerivAt_x s t x ht).deriv
  rw [← weightedKernelMixed_eq_tsum s y x hy]
  exact ((weightedKernelX_hasDerivAt_y s y x hy).congr_of_eventuallyEq hevent).deriv

end

end ImbalancedChen.Part3.ContinuedFourierMomentSeriesCalculus
