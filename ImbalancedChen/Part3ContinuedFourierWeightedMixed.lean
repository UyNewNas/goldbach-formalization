import ImbalancedChen.Part3ContinuedFourierSpatialMoments
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-25. UNCOMPILED; NOT ROOT ACCEPTED.

The actual completed nonconstant term is 2 sqrt(y) times the two Fourier
signs. Its horizontal derivative and its mixed horizontal/vertical derivative
are differentiated literally here. The mixed family has a supplied summable
uniform majorant on every positive compact height interval, uniformly in x
and bounded real-part strips of s. This is new continued-Fourier mathematics;
it imports no held primitive-coordinate derivative source.

The completed constant term, second pure derivatives of the weighted sum,
and final continued Maass eigenrelation are not asserted in this module.
-/

namespace ImbalancedChen.Part3.ContinuedFourierWeightedMixed

noncomputable section

open Set Filter
open scoped Topology
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.ContinuedFourierSpatialMoments

def sqrtSlope (y : ℝ) : ℂ := ((1 / (2 * Real.sqrt y) : ℝ) : ℂ)

def weightedTerm (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  2 * (Real.sqrt y : ℂ) * spatialMomentTerm 0 0 n s y x

def weightedX (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  2 * (Real.sqrt y : ℂ) * spatialMomentTerm 1 0 n s y x

def weightedMixed (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  2 * sqrtSlope y * spatialMomentTerm 1 0 n s y x +
    2 * (Real.sqrt y : ℂ) * spatialMomentTerm 1 1 n s y x

theorem weightedTerm_hasDerivAt_x (n : ℕ) (s : ℂ) (y x : ℝ) :
    HasDerivAt (fun t : ℝ => weightedTerm n s y t) (weightedX n s y x) x := by
  exact (spatialMomentTerm_hasDerivAt_x 0 0 n s y x).const_mul (2 * (Real.sqrt y : ℂ))

theorem weightedX_hasDerivAt_y (n : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => weightedX n s t x) (weightedMixed n s y x) y := by
  have hroot := ((Real.hasDerivAt_sqrt hy.ne').ofReal_comp).const_mul (2 : ℂ)
  have hmoment := spatialMomentTerm_hasDerivAt_y 1 0 n s y x hy
  convert hroot.mul hmoment using 1 <;>
    simp [weightedX, weightedMixed, sqrtSlope] <;> ring

def mixedMajorant (M : ℕ) (a B : ℝ) (n : ℕ) : ℝ :=
  (2 * (1 / (2 * Real.sqrt a))) * spatialMajorant 1 0 M a n +
    (2 * Real.sqrt B) * spatialMajorant 1 1 M a n

theorem mixedMajorant_summable (M : ℕ) {a : ℝ} (ha : 0 < a) (B : ℝ) :
    Summable (mixedMajorant M a B) :=
  ((spatialMajorant_summable 1 0 M ha).mul_left (2 * (1 / (2 * Real.sqrt a)))).add
    ((spatialMajorant_summable 1 1 M ha).mul_left (2 * Real.sqrt B))

/-- Uniform summable bound for the genuine mixed second derivative of one
sqrt-weighted completed Fourier term. -/
theorem weightedMixed_norm_bound (M : ℕ) {a B : ℝ} (ha : 0 < a)
    (n : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) {y : ℝ}
    (hya : a ≤ y) (hyB : y ≤ B) (x : ℝ) :
    ‖weightedMixed n s y x‖ ≤ mixedMajorant M a B n := by
  have hy : 0 < y := ha.trans_le hya
  have hroota : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hrooty : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hroot : Real.sqrt a ≤ Real.sqrt y := Real.sqrt_le_sqrt hya
  have hslope : |(1 / (2 * Real.sqrt y) : ℝ)| ≤ 1 / (2 * Real.sqrt a) := by
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hcoef : ‖(2 : ℂ) * sqrtSlope y‖ ≤ 2 * (1 / (2 * Real.sqrt a)) := by
    simpa [sqrtSlope, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hslope (show (0 : ℝ) ≤ 2 by norm_num)
  have hweight : ‖(2 : ℂ) * (Real.sqrt y : ℂ)‖ ≤ 2 * Real.sqrt B := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg y)] using
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hyB) (show (0 : ℝ) ≤ 2 by norm_num)
  have hm0 := spatialMomentTerm_norm_bound 1 0 M ha n hs hya x
  have hm1 := spatialMomentTerm_norm_bound 1 1 M ha n hs hya x
  calc
    _ ≤ ‖2 * sqrtSlope y * spatialMomentTerm 1 0 n s y x‖ +
        ‖2 * (Real.sqrt y : ℂ) * spatialMomentTerm 1 1 n s y x‖ := norm_add_le _ _
    _ = ‖(2 : ℂ) * sqrtSlope y‖ * ‖spatialMomentTerm 1 0 n s y x‖ +
        ‖(2 : ℂ) * (Real.sqrt y : ℂ)‖ * ‖spatialMomentTerm 1 1 n s y x‖ := by
      simp only [norm_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul hcoef hm0 (norm_nonneg _) (by positivity))
      (mul_le_mul hweight hm1 (norm_nonneg _) (by positivity))

/-- The exact two-sign completed nonconstant summand. -/
def weightedPair (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  weightedTerm n s y x + weightedTerm n s y (-x)

def weightedPairX (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  weightedX n s y x - weightedX n s y (-x)

def weightedPairMixed (n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  weightedMixed n s y x - weightedMixed n s y (-x)

/-- Literal agreement with the bilateral term of completedEisensteinFourier. -/
theorem weightedPair_eq_actual (n : ℕ) (s : ℂ) (y x : ℝ) :
    weightedPair n s y x = 2 * (Real.sqrt y : ℂ) * nonzeroFrequencyPair n s y x := by
  unfold weightedPair weightedTerm nonzeroFrequencyPair
  rw [spatialMomentTerm_zero_zero, spatialMomentTerm_zero_zero]
  ring

theorem weightedPair_hasDerivAt_x (n : ℕ) (s : ℂ) (y x : ℝ) :
    HasDerivAt (fun t : ℝ => weightedPair n s y t) (weightedPairX n s y x) x := by
  have hp := weightedTerm_hasDerivAt_x n s y x
  have hn := (weightedTerm_hasDerivAt_x n s y (-x)).comp x ((hasDerivAt_id x).neg)
  convert hp.add hn using 1 <;> simp [weightedPair, weightedPairX] <;> ring

theorem weightedPairX_hasDerivAt_y (n : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => weightedPairX n s t x) (weightedPairMixed n s y x) y := by
  exact (weightedX_hasDerivAt_y n s y x hy).sub (weightedX_hasDerivAt_y n s y (-x) hy)

/-- Both signed modes have the same proved norm majorant. -/
theorem weightedPairMixed_norm_bound (M : ℕ) {a B : ℝ} (ha : 0 < a)
    (n : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) {y : ℝ}
    (hya : a ≤ y) (hyB : y ≤ B) (x : ℝ) :
    ‖weightedPairMixed n s y x‖ ≤ 2 * mixedMajorant M a B n := by
  have hp := weightedMixed_norm_bound M ha n hs hya hyB x
  have hn := weightedMixed_norm_bound M ha n hs hya hyB (-x)
  calc
    _ ≤ ‖weightedMixed n s y x‖ + ‖weightedMixed n s y (-x)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- The actual completed mixed-derivative term series is absolutely convergent. -/
theorem weightedPairMixed_norm_summable (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖weightedPairMixed n s y x‖) := by
  let M : ℕ := Nat.ceil |s.re|
  exact ((mixedMajorant_summable M hy y).mul_left 2).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => weightedPairMixed_norm_bound M hy n (Nat.le_ceil _) le_rfl le_rfl x)

/-- Local uniform convergence of the genuine completed mixed-derivative
family, uniform in every horizontal coordinate and parameter strip. -/
theorem weightedPairMixed_uniform_convergence (M : ℕ) {a B : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun H : ℕ => fun p : ℂ × ℝ × ℝ =>
        ∑ n ∈ Finset.range H, weightedPairMixed n p.1 p.2.1 p.2.2)
      (fun p : ℂ × ℝ × ℝ => ∑' n, weightedPairMixed n p.1 p.2.1 p.2.2)
      atTop {p | |p.1.re| ≤ (M : ℝ) ∧ a ≤ p.2.1 ∧ p.2.1 ≤ B} :=
  tendstoUniformlyOn_tsum_nat ((mixedMajorant_summable M ha B).mul_left 2)
    (fun n p hp => weightedPairMixed_norm_bound M ha n hp.1 hp.2.1 hp.2.2 p.2.2)

end

end ImbalancedChen.Part3.ContinuedFourierWeightedMixed
