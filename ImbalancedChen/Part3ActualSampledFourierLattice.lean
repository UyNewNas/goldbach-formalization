/-
SOURCE ONLY -- 2026-10-23. No Lean/lake/compiler/typechecker/CI was run.
Author: /root/p3_common_interval_phase_separation_sol_max_oct22.

This is an append-only source continuation of these two already delivered
SOURCEONLY drafts, after collecting all Mathlib imports at the beginning:
  20261023-P3-compact-coordinate-IBP-and-coefficient-continuity-SOURCEONLY.lean.txt
    P3CompactCoordinateSourceOnly.compact_fourier_weight_bound
  20261023-P3-native-torus-period64-actual-Fourier-sampling-SOURCEONLY.lean.txt
    P3NativePeriod64SamplingSourceOnly.native_period64_fourier_sample
    and its actual definitions D4,E4,inside64,period64,sampleFreq.
These are declarations with full by bodies in those drafts, NOT new hypotheses
or invented project imports. This continuation is not a standalone Lean module.
All new declarations below have full uncompiled by bodies. No checked-Lean
status is asserted.

The final actual-amplitude specialization also follows the declarations of
 source-reviews/drafts/20261023-P3-actual-normalizedF-smooth-compact-astra-SOURCEONLY.lean.txt
 namespace ImbalancedChen.Part3.ActualNormalizedSmoothF,
 SHA256 d01819910af3971b5d3aa071bd500cefc8a120d7a332422d1e3bef72e0dce56f.
This extra source dependency is used ONLY for that last specialization; it
supplies actual normalizedF smoothness/compactness/support, not Fourier decay.

MAIN OUTPUT, for an ACTUAL f : EuclideanSpace Real (Fin 4) -> Complex:
  actual compact C^(4L) + actual support inside period64 box
    -> actual native torus coefficients have product decay
    -> first-coordinate-J0 weighted absolute summability,
       L=J0+3, with explicit bound
       [64^-4 * 64^(4L) * 2^(4L) * (1+2^(4L))]
       * [sum j<=4L integral norm(D^j f)] * [finite positive p-series cost].
No unknown pointwise-decay hb, unknown lattice sum, or unknown coefficient
normalization is a premise of any of the main theorems.

The elementary product/p-series core below is copied from the earlier tensor
draft. This is only positive-series algebra; the old four iterated 1D Fourier
inversions are NOT repeated or used.

FIXED mathlib pin e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Additional primary APIs read for this continuation:
 Analysis/Normed/Lp/PiLp.lean, blob6961e020117a12f4c823a0cd1d6ebe77931ccacc:
   norm_apply_le712--714, actual coordinate norm <= Euclidean norm.
 Topology/Algebra/InfiniteSum/Basic.lean:
   generated Equiv.summable_iff192--193 and Equiv.tsum_eq562--563.
 Analysis/PSeries.lean, blob6499506f39f848904fbf7c0aca08bc303c19dca4:
   Real.summable_one_div_nat_add_rpow453--463.
 Analysis/Normed/Ring/InfiniteSum.lean,
   blobd9c1d83eba2ec955c3914387cf1ed15b09f052af:
   Summable.mul_of_nonneg34--37.
 Analysis/Normed/Group/InfiniteSum.lean,
   blob9b88acb3c7b6034cb118bde2e1c34c5030d0f531:
   Summable.of_norm_bounded111--114.

The coefficient is ALWAYS native mFourierCoeff(period64 f), not a generic
coefficient array retroactively called Fourier. The exact frequency is k/64
in EuclideanSpace, and the exact sampling factor 64^-4 remains in scaleCost.
-/

import ImbalancedChen.Part3ActualNormalizedSmoothF
import ImbalancedChen.Part3CompactCoordinateFourier
import ImbalancedChen.Part3NativePeriod64Sampling

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory
open scoped BigOperators FourierTransform ContDiff

namespace P3ActualSampledLatticeSourceOnly

open P3NativePeriod64SamplingSourceOnly
  (D4 E4 inside64 period64 sampleFreq)

def coeff (f : E4 → ℂ) (k : D4 → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (period64 f) k

def derivMass (f : E4 → ℂ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r+1), ∫ v : E4, ‖iteratedFDeriv ℝ j f v‖

def radialFactor (r : ℕ) : ℝ := (2 : ℝ)^r * (1 + (2 : ℝ)^r)

def scaleCost (r : ℕ) : ℝ :=
  ((64 : ℝ)^4)⁻¹ * (64 : ℝ)^r * radialFactor r

def latticeCost (f : E4 → ℂ) (r : ℕ) : ℝ :=
  scaleCost r * derivMass f r

lemma derivMass_nonneg (f : E4 → ℂ) (r : ℕ) : 0 ≤ derivMass f r := by
  exact Finset.sum_nonneg (fun j _hj => integral_nonneg (fun _v => norm_nonneg _))

lemma scaleCost_nonneg (r : ℕ) : 0 ≤ scaleCost r := by
  dsimp [scaleCost, radialFactor]
  positivity

lemma latticeCost_nonneg (f : E4 → ℂ) (r : ℕ) : 0 ≤ latticeCost f r := by
  exact mul_nonneg (scaleCost_nonneg r) (derivMass_nonneg f r)

lemma zeroth_integral_le_derivMass (f : E4 → ℂ) (r : ℕ) :
    (∫ v : E4, ‖f v‖) ≤ derivMass f r := by
  have h :
      (∫ v : E4, ‖iteratedFDeriv ℝ 0 f v‖) ≤ derivMass f r := by
    change (∫ v : E4, ‖iteratedFDeriv ℝ 0 f v‖) ≤
      ∑ j ∈ Finset.range (r+1), ∫ v : E4, ‖iteratedFDeriv ℝ j f v‖
    exact Finset.single_le_sum
      (f := fun j : ℕ => ∫ v : E4, ‖iteratedFDeriv ℝ j f v‖) (a := 0)
      (fun j _hj => integral_nonneg (fun v : E4 => norm_nonneg (iteratedFDeriv ℝ j f v)))
      (by simp)
  simpa only [norm_iteratedFDeriv_zero] using h

/- The (1+norm w)^r bound is DERIVED from the actual r-th Fourier estimate
   and the actual zeroth estimate. Only actual compact support and finite
   C^r regularity are inputs. There is no radial-decay hypothesis. -/
theorem compact_radial_fourier_bound (f : E4 → ℂ) (r : ℕ)
    (hf : ContDiff ℝ r f) (hc : HasCompactSupport f) (w : E4) :
    (1 + ‖w‖)^r * ‖𝓕 f w‖ ≤ radialFactor r * derivMass f r := by
  have hf0 : ContDiff ℝ 0 f := hf.of_le (by exact_mod_cast Nat.zero_le r)
  have h0 : ‖𝓕 f w‖ ≤ ∫ v : E4, ‖f v‖ := by
    simpa [norm_iteratedFDeriv_zero] using
      P3CompactCoordinateSourceOnly.compact_fourier_weight_bound f 0 hf0 hc w
  have hzero : ‖𝓕 f w‖ ≤ derivMass f r :=
    h0.trans (zeroth_integral_le_derivMass f r)
  have hr : ‖w‖^r * ‖𝓕 f w‖ ≤ (2 : ℝ)^r * derivMass f r := by
    simpa only [derivMass] using
      P3CompactCoordinateSourceOnly.compact_fourier_weight_bound f r hf hc w
  have hM : 0 ≤ derivMass f r := derivMass_nonneg f r
  have htwo : 0 ≤ (2 : ℝ)^r := by positivity
  by_cases hw : ‖w‖ ≤ 1
  · have hp : (1 + ‖w‖)^r ≤ (2 : ℝ)^r :=
      pow_le_pow_left₀ (by positivity) (by linarith) r
    have hM1 : derivMass f r ≤ (1 + (2 : ℝ)^r) * derivMass f r := by
      nlinarith [mul_nonneg htwo hM]
    calc
      (1 + ‖w‖)^r * ‖𝓕 f w‖ ≤ (2 : ℝ)^r * ‖𝓕 f w‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (2 : ℝ)^r * derivMass f r :=
        mul_le_mul_of_nonneg_left hzero htwo
      _ ≤ (2 : ℝ)^r * ((1 + (2 : ℝ)^r) * derivMass f r) :=
        mul_le_mul_of_nonneg_left hM1 htwo
      _ = radialFactor r * derivMass f r := by
        dsimp [radialFactor]
        ring
  · have hw' : 1 ≤ ‖w‖ := le_of_lt (lt_of_not_ge hw)
    have hp : (1 + ‖w‖)^r ≤ ((2 : ℝ) * ‖w‖)^r :=
      pow_le_pow_left₀ (by positivity) (by linarith) r
    have hM2 : (2 : ℝ)^r * derivMass f r ≤
        (1 + (2 : ℝ)^r) * derivMass f r := by nlinarith [hM]
    calc
      (1 + ‖w‖)^r * ‖𝓕 f w‖ ≤ ((2 : ℝ) * ‖w‖)^r * ‖𝓕 f w‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = (2 : ℝ)^r * (‖w‖^r * ‖𝓕 f w‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ)^r * ((2 : ℝ)^r * derivMass f r) :=
        mul_le_mul_of_nonneg_left hr htwo
      _ ≤ (2 : ℝ)^r * ((1 + (2 : ℝ)^r) * derivMass f r) :=
        mul_le_mul_of_nonneg_left hM2 htwo
      _ = radialFactor r * derivMass f r := by
        dsimp [radialFactor]
        ring

def weight4 (L : ℕ) (k : D4 → ℤ) : ℝ :=
  (1 + |(k 0 : ℝ)|)^L *
    ((1 + |(k 1 : ℝ)|)^L *
      ((1 + |(k 2 : ℝ)|)^L * (1 + |(k 3 : ℝ)|)^L))

lemma weight4_pos (L : ℕ) (k : D4 → ℤ) : 0 < weight4 L k := by
  dsimp [weight4]
  positivity

lemma sample_coordinate_bound (k : D4 → ℤ) (i : D4) :
    |(k i : ℝ)| ≤ (64 : ℝ) * ‖sampleFreq k‖ := by
  have hi : |(k i : ℝ)| / 64 ≤ ‖sampleFreq k‖ := by
    simpa [sampleFreq, Real.norm_eq_abs, abs_div] using
      PiLp.norm_apply_le (sampleFreq k) i
  nlinarith

lemma sample_base_bound (k : D4 → ℤ) (i : D4) :
    1 + |(k i : ℝ)| ≤ (64 : ℝ) * (1 + ‖sampleFreq k‖) := by
  linarith [sample_coordinate_bound k i]

/- Four coordinate weights cost EXACTLY r=4L derivatives and 64^(4L).
   No fifth coordinate and no extra x^eta power is introduced. -/
lemma weight4_le_scaled_radial (L : ℕ) (k : D4 → ℤ) :
    weight4 L k ≤ (64 : ℝ)^(4*L) * (1 + ‖sampleFreq k‖)^(4*L) := by
  let B : ℝ := (64 : ℝ) * (1 + ‖sampleFreq k‖)
  have hi (i : D4) : (1 + |(k i : ℝ)|)^L ≤ B^L :=
    pow_le_pow_left₀ (by positivity) (sample_base_bound k i) L
  calc
    weight4 L k ≤ B^L * (B^L * (B^L * B^L)) := by
      exact mul_le_mul (hi 0)
        (mul_le_mul (hi 1)
          (mul_le_mul (hi 2) (hi 3) (by positivity) (by positivity))
          (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = B^(4*L) := by
      rw [Nat.mul_comm 4 L, pow_mul]
      ring
    _ = (64 : ℝ)^(4*L) * (1 + ‖sampleFreq k‖)^(4*L) := by
      dsimp [B]
      rw [mul_pow]

/- This uses the ACTUAL proved sampling equality, retaining 64^-4.
   The coefficient is not an arbitrary masked DFT. -/
theorem native_coeff_product_weight_bound (f : E4 → ℂ) (L : ℕ)
    (hf : ContDiff ℝ (4*L) f) (hc : HasCompactSupport f)
    (hb : Function.support f ⊆ inside64) (k : D4 → ℤ) :
    ‖coeff f k‖ * weight4 L k ≤ latticeCost f (4*L) := by
  have hn : ‖coeff f k‖ =
      ((64 : ℝ)^4)⁻¹ * ‖𝓕 f (sampleFreq k)‖ := by
    rw [coeff,
      P3NativePeriod64SamplingSourceOnly.native_period64_fourier_sample f hb k,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp := mul_le_mul_of_nonneg_right (weight4_le_scaled_radial L k)
    (norm_nonneg (𝓕 f (sampleFreq k)))
  have hq : 0 ≤ ((64 : ℝ)^4)⁻¹ := by positivity
  calc
    ‖coeff f k‖ * weight4 L k =
        ((64 : ℝ)^4)⁻¹ * (weight4 L k * ‖𝓕 f (sampleFreq k)‖) := by
      rw [hn]
      ring
    _ ≤ ((64 : ℝ)^4)⁻¹ *
        ((64 : ℝ)^(4*L) *
          ((1 + ‖sampleFreq k‖)^(4*L) * ‖𝓕 f (sampleFreq k)‖)) := by
      apply mul_le_mul_of_nonneg_left _ hq
      simpa only [mul_assoc] using hp
    _ ≤ ((64 : ℝ)^4)⁻¹ *
        ((64 : ℝ)^(4*L) * (radialFactor (4*L) * derivMass f (4*L))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (compact_radial_fourier_bound f (4*L) hf hc (sampleFreq k))
          (by positivity)) hq
    _ = latticeCost f (4*L) := by
      dsimp [latticeCost, scaleCost]
      ring

/- Elementary four-factor positive-series core. -/
abbrev K2 := ℤ × ℤ
abbrev K3 := ℤ × K2
abbrev K4 := ℤ × K3

def tupleToIndex : K4 ≃ (D4 → ℤ) where
  toFun q := ![q.1, q.2.1, q.2.2.1, q.2.2.2]
  invFun k := (k 0, k 1, k 2, k 3)
  left_inv q := by rcases q with ⟨a,b,c,d⟩; rfl
  right_inv k := by funext i; fin_cases i <;> rfl

@[simp] lemma tupleToIndex_zero (q : K4) : tupleToIndex q 0 = q.1 := rfl
@[simp] lemma tupleToIndex_one (q : K4) : tupleToIndex q 1 = q.2.1 := rfl
@[simp] lemma tupleToIndex_two (q : K4) : tupleToIndex q 2 = q.2.2.1 := rfl
@[simp] lemma tupleToIndex_three (q : K4) : tupleToIndex q 3 = q.2.2.2 := rfl

def prod4 (u0 u1 u2 u3 : ℤ → ℝ) (q : K4) : ℝ :=
  u0 q.1 * (u1 q.2.1 * (u2 q.2.2.1 * u3 q.2.2.2))

def decay (p : ℕ) (n : ℤ) : ℝ := 1 / (1 + |(n : ℝ)|)^p

def testWeight (J0 : ℕ) (n : ℤ) : ℝ := (1 + |(n : ℝ)|)^J0

lemma decay_nonneg (p : ℕ) (n : ℤ) : 0 ≤ decay p n := by
  dsimp [decay]
  positivity

lemma testWeight_nonneg (J0 : ℕ) (n : ℤ) : 0 ≤ testWeight J0 n := by
  dsimp [testWeight]
  positivity

lemma product_decay_eq_inv_weight (L : ℕ) (k : D4 → ℤ) :
    prod4 (decay L) (decay L) (decay L) (decay L) (tupleToIndex.symm k) =
      (weight4 L k)⁻¹ := by
  change
    (1 / (1 + |(k 0 : ℝ)|)^L) *
      ((1 / (1 + |(k 1 : ℝ)|)^L) *
        ((1 / (1 + |(k 2 : ℝ)|)^L) * (1 / (1 + |(k 3 : ℝ)|)^L))) =
    ((1 + |(k 0 : ℝ)|)^L *
      ((1 + |(k 1 : ℝ)|)^L *
        ((1 + |(k 2 : ℝ)|)^L * (1 + |(k 3 : ℝ)|)^L)))⁻¹
  simp only [one_div, mul_inv_rev]
  ring

/- Genuine product-decay OUTPUT for the actual native coefficients. -/
theorem native_coeff_product_decay (f : E4 → ℂ) (L : ℕ)
    (hf : ContDiff ℝ (4*L) f) (hc : HasCompactSupport f)
    (hb : Function.support f ⊆ inside64) (k : D4 → ℤ) :
    ‖coeff f k‖ ≤ latticeCost f (4*L) *
      prod4 (decay L) (decay L) (decay L) (decay L) (tupleToIndex.symm k) := by
  calc
    ‖coeff f k‖ ≤ latticeCost f (4*L) / weight4 L k :=
      (le_div_iff₀ (weight4_pos L k)).2
        (native_coeff_product_weight_bound f L hf hc hb k)
    _ = latticeCost f (4*L) *
        prod4 (decay L) (decay L) (decay L) (decay L) (tupleToIndex.symm k) := by
      rw [product_decay_eq_inv_weight, div_eq_mul_inv]

lemma summable_prod4 (u0 u1 u2 u3 : ℤ → ℝ)
    (h0 : Summable u0) (h1 : Summable u1)
    (h2 : Summable u2) (h3 : Summable u3)
    (n0 : ∀ i, 0 ≤ u0 i) (n1 : ∀ i, 0 ≤ u1 i)
    (n2 : ∀ i, 0 ≤ u2 i) (n3 : ∀ i, 0 ≤ u3 i) :
    Summable (prod4 u0 u1 u2 u3) := by
  have h23 := h2.mul_of_nonneg h3 n2 n3
  have h123 := h1.mul_of_nonneg h23 n1
    (fun q : K2 => mul_nonneg (n2 q.1) (n3 q.2))
  exact h0.mul_of_nonneg h123 n0
    (fun q : K3 => mul_nonneg (n1 q.1) (mul_nonneg (n2 q.2.1) (n3 q.2.2)))

lemma tsum_prod4 (u0 u1 u2 u3 : ℤ → ℝ)
    (h0 : Summable u0) (h1 : Summable u1)
    (h2 : Summable u2) (h3 : Summable u3)
    (n0 : ∀ i, 0 ≤ u0 i) (n1 : ∀ i, 0 ≤ u1 i)
    (n2 : ∀ i, 0 ≤ u2 i) (n3 : ∀ i, 0 ≤ u3 i) :
    (∑' q : K4, prod4 u0 u1 u2 u3 q) =
      (∑' i, u0 i) * ((∑' j, u1 j) * ((∑' k, u2 k) * ∑' l, u3 l)) := by
  have h23 := h2.mul_of_nonneg h3 n2 n3
  have h123 := h1.mul_of_nonneg h23 n1
    (fun q : K2 => mul_nonneg (n2 q.1) (n3 q.2))
  have h0123 := h0.mul_of_nonneg h123 n0
    (fun q : K3 => mul_nonneg (n1 q.1) (mul_nonneg (n2 q.2.1) (n3 q.2.2)))
  unfold prod4
  rw [← h0.tsum_mul_tsum h123 h0123,
      ← h1.tsum_mul_tsum h23 h123,
      ← h2.tsum_mul_tsum h3 h23]

lemma summable_decay {p : ℕ} (hp : 1 < p) : Summable (decay p) := by
  have hnat : Summable (fun n : ℕ => 1 / (1 + (n : ℝ))^p) := by
    have hh := (Real.summable_one_div_nat_add_rpow 1 (p : ℝ)).2
      (by exact_mod_cast hp)
    apply hh.congr
    intro n
    rw [abs_of_nonneg (by positivity), Real.rpow_natCast]
    simp only [add_comm]
  apply Summable.of_nat_of_neg
  · convert! hnat using 1
    funext n
    simp only [decay, Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  · convert! hnat using 1
    funext n
    simp only [decay, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]

lemma decay_mul_testWeight (J0 : ℕ) (n : ℤ) :
    decay (J0+3) n * testWeight J0 n = decay 3 n := by
  have hbase : (1 + |(n : ℝ)|) ≠ 0 := by positivity
  dsimp only [decay, testWeight]
  rw [pow_add,
    mul_comm ((1 + |(n : ℝ)|)^J0) ((1 + |(n : ℝ)|)^3), ← div_div]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hbase)

def seriesCost (J0 : ℕ) : ℝ :=
  (∑' i : ℤ, decay 3 i) *
    ((∑' j : ℤ, decay (J0+3) j) *
      ((∑' k : ℤ, decay (J0+3) k) * ∑' l : ℤ, decay (J0+3) l))

lemma seriesCost_nonneg (J0 : ℕ) : 0 ≤ seriesCost J0 := by
  have hp (p : ℕ) : 0 ≤ ∑' n : ℤ, decay p n :=
    tsum_nonneg (fun n => decay_nonneg p n)
  exact mul_nonneg (hp 3) (mul_nonneg (hp (J0+3))
    (mul_nonneg (hp (J0+3)) (hp (J0+3))))

lemma weighted_l1_from_product_decay (a : K4 → ℂ) (J0 : ℕ) (K : ℝ)
    (ha : ∀ q, ‖a q‖ ≤ K *
      prod4 (decay (J0+3)) (decay (J0+3)) (decay (J0+3)) (decay (J0+3)) q) :
    Summable (fun q : K4 => ‖a q‖ * testWeight J0 q.1) ∧
      (∑' q : K4, ‖a q‖ * testWeight J0 q.1) ≤ K * seriesCost J0 := by
  have h3 : Summable (decay 3) := summable_decay (by norm_num)
  have hL : Summable (decay (J0+3)) := summable_decay (by omega)
  have hp := summable_prod4 (decay 3) (decay (J0+3))
    (decay (J0+3)) (decay (J0+3)) h3 hL hL hL
    (decay_nonneg 3) (decay_nonneg (J0+3))
    (decay_nonneg (J0+3)) (decay_nonneg (J0+3))
  have hmajor := hp.mul_left K
  have hb : ∀ q : K4, ‖a q‖ * testWeight J0 q.1 ≤
      K * prod4 (decay 3) (decay (J0+3)) (decay (J0+3)) (decay (J0+3)) q := by
    intro q
    calc
      ‖a q‖ * testWeight J0 q.1 ≤
          (K * prod4 (decay (J0+3)) (decay (J0+3))
            (decay (J0+3)) (decay (J0+3)) q) * testWeight J0 q.1 :=
        mul_le_mul_of_nonneg_right (ha q) (testWeight_nonneg J0 q.1)
      _ = K * prod4 (decay 3) (decay (J0+3))
          (decay (J0+3)) (decay (J0+3)) q := by
        dsimp [prod4]
        rw [← decay_mul_testWeight J0 q.1]
        ring
  have habs : Summable (fun q : K4 => ‖a q‖ * testWeight J0 q.1) :=
    hmajor.of_nonneg_of_le
      (fun q => mul_nonneg (norm_nonneg _) (testWeight_nonneg J0 q.1)) hb
  refine ⟨habs, (hasSum_le hb habs.hasSum hmajor.hasSum).trans_eq ?_⟩
  rw [hp.tsum_mul_left K,
    tsum_prod4 (decay 3) (decay (J0+3)) (decay (J0+3)) (decay (J0+3))
      h3 hL hL hL (decay_nonneg 3) (decay_nonneg (J0+3))
      (decay_nonneg (J0+3)) (decay_nonneg (J0+3))]
  rfl

def weightedL1 (f : E4 → ℂ) (J0 : ℕ) : ℝ :=
  ∑' k : D4 → ℤ, ‖coeff f k‖ * testWeight J0 (k 0)

/- MAIN CLOSED GENERIC CHAIN. Every input concerns the actual f:
   finite C^r, compact support, support geometry.
   The coefficient, radial/product decay, and weighted lattice conclusion
   are outputs. In particular the helper's ha is proved here, not supplied. -/
theorem native_weighted_l1 (f : E4 → ℂ) (J0 : ℕ)
    (hf : ContDiff ℝ (4*(J0+3)) f) (hc : HasCompactSupport f)
    (hb : Function.support f ⊆ inside64) :
    Summable (fun k : D4 → ℤ => ‖coeff f k‖ * testWeight J0 (k 0)) ∧
      weightedL1 f J0 ≤ latticeCost f (4*(J0+3)) * seriesCost J0 := by
  let a : K4 → ℂ := fun q => coeff f (tupleToIndex q)
  have hdecay (q : K4) : ‖a q‖ ≤ latticeCost f (4*(J0+3)) *
      prod4 (decay (J0+3)) (decay (J0+3)) (decay (J0+3)) (decay (J0+3)) q := by
    simpa only [a, Equiv.symm_apply_apply] using
      native_coeff_product_decay f (J0+3) hf hc hb (tupleToIndex q)
  have h := weighted_l1_from_product_decay a J0 (latticeCost f (4*(J0+3))) hdecay
  have htuple : Summable
      ((fun k : D4 → ℤ => ‖coeff f k‖ * testWeight J0 (k 0)) ∘ tupleToIndex) := by
    change Summable (fun q : K4 =>
      ‖coeff f (tupleToIndex q)‖ * testWeight J0 (tupleToIndex q 0))
    simpa only [tupleToIndex_zero, a] using h.1
  refine ⟨tupleToIndex.summable_iff.mp htuple, ?_⟩
  unfold weightedL1
  rw [← tupleToIndex.tsum_eq
    (fun k : D4 → ℤ => ‖coeff f k‖ * testWeight J0 (k 0))]
  simpa only [tupleToIndex_zero, a] using h.2

/- This is exactly the absolute summability input required by the native
   AddCircleMulti inverse once continuity of period64 f has been bundled. -/
theorem native_coeff_summable (f : E4 → ℂ) (J0 : ℕ)
    (hf : ContDiff ℝ (4*(J0+3)) f) (hc : HasCompactSupport f)
    (hb : Function.support f ⊆ inside64) :
    Summable (UnitAddTorus.mFourierCoeff (period64 f)) := by
  change Summable (coeff f)
  apply (native_weighted_l1 f J0 hf hc hb).1.of_norm_bounded
  intro k
  have hw : (1 : ℝ) ≤ testWeight J0 (k 0) := by
    change (1 : ℝ) ≤ (1 + |(k 0 : ℝ)|)^J0
    calc
      (1 : ℝ) = (1 : ℝ)^J0 := by simp
      _ ≤ (1 + |(k 0 : ℝ)|)^J0 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [abs_nonneg (k 0 : ℝ)]) J0
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (norm_nonneg (coeff f k))

/- Quantitative accounting with X=x^eta >=0. Thus X^(4L)=x^(4L eta)
   and X^(8L)=x^(8L eta), for x>0. The derivative MASS is the only extra
   quantitative input; it is a finite actual sum of genuine integrals.
   No weighted lattice conclusion is an assumption. -/
theorem weighted_l1_and_square_cost (f : E4 → ℂ) (J0 : ℕ) (D X : ℝ)
    (hf : ContDiff ℝ (4*(J0+3)) f) (hc : HasCompactSupport f)
    (hb : Function.support f ⊆ inside64) (hD : 0 ≤ D) (hX : 0 ≤ X)
    (hderiv : derivMass f (4*(J0+3)) ≤ D * X^(4*(J0+3))) :
    weightedL1 f J0 ≤
        (scaleCost (4*(J0+3)) * seriesCost J0 * D) * X^(4*(J0+3)) ∧
      (weightedL1 f J0)^2 ≤
        (scaleCost (4*(J0+3)) * seriesCost J0 * D)^2 * X^(8*(J0+3)) := by
  have hC : 0 ≤ scaleCost (4*(J0+3)) * seriesCost J0 :=
    mul_nonneg (scaleCost_nonneg _) (seriesCost_nonneg _)
  have hW : weightedL1 f J0 ≤
      (scaleCost (4*(J0+3)) * seriesCost J0 * D) * X^(4*(J0+3)) := by
    calc
      weightedL1 f J0 ≤ latticeCost f (4*(J0+3)) * seriesCost J0 :=
        (native_weighted_l1 f J0 hf hc hb).2
      _ = (scaleCost (4*(J0+3)) * seriesCost J0) * derivMass f (4*(J0+3)) := by
        dsimp [latticeCost]
        ring
      _ ≤ (scaleCost (4*(J0+3)) * seriesCost J0) * (D * X^(4*(J0+3))) :=
        mul_le_mul_of_nonneg_left hderiv hC
      _ = (scaleCost (4*(J0+3)) * seriesCost J0 * D) * X^(4*(J0+3)) := by ring
  have hW0 : 0 ≤ weightedL1 f J0 := by
    exact tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (testWeight_nonneg _ _))
  have hR0 : 0 ≤
      (scaleCost (4*(J0+3)) * seriesCost J0 * D) * X^(4*(J0+3)) :=
    mul_nonneg (mul_nonneg hC hD) (pow_nonneg hX _)
  have hsq : (weightedL1 f J0)^2 ≤
      ((scaleCost (4*(J0+3)) * seriesCost J0 * D) * X^(4*(J0+3)))^2 := by
    simpa only [pow_two] using mul_le_mul hW hW hW0 hR0
  refine ⟨hW, hsq.trans_eq ?_⟩
  have he : (4*(J0+3))*2 = 8*(J0+3) := by omega
  rw [mul_pow, ← pow_mul, he]

end P3ActualSampledLatticeSourceOnly

/- ACTUAL AMPLITUDE SPECIALIZATION. No regularity/support/Fourier-decay
   assumptions are arguments here: the other worker's actual zero-extension
   by proofs supply them. This does not yet replace its derivative-integral
   sum by a uniform rho bound. -/
namespace P3ActualSampledLatticeSourceOnly

open P3NativePeriod64SamplingSourceOnly (D4 inside64)

theorem actual_normalizedF_weighted_l1 (rho sigma : ℝ) (J0 : ℕ) :
    Summable (fun k : D4 → ℤ =>
      ‖coeff (ImbalancedChen.Part3.ActualNormalizedSmoothF.normalizedF rho sigma) k‖ *
        testWeight J0 (k 0)) ∧
      weightedL1 (ImbalancedChen.Part3.ActualNormalizedSmoothF.normalizedF rho sigma) J0 ≤
        latticeCost (ImbalancedChen.Part3.ActualNormalizedSmoothF.normalizedF rho sigma)
          (4*(J0+3)) * seriesCost J0 := by
  apply native_weighted_l1
  · exact (ImbalancedChen.Part3.ActualNormalizedSmoothF.normalizedF_contDiff rho sigma).of_le
      (show ((4 * (J0 + 3) : ℕ) : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)
  · exact ImbalancedChen.Part3.ActualNormalizedSmoothF.normalizedF_hasCompactSupport rho sigma
  · simpa only [inside64] using
      ImbalancedChen.Part3.ActualNormalizedSmoothF.normalizedF_support_inside64 rho sigma

end P3ActualSampledLatticeSourceOnly

/-
EXACT APPLICATION BOUNDARY AND PARAMETER ORDER

1. The first MAIN theorem has no derivative-mass inequality as a hypothesis:
   it bounds the actual native weighted L1 by the actual finite integral sum.
   The final quantitative theorem merely consumes a bound for that real sum.

2. The actual original normalized amplitude is the positive-orthant zero
   extension of
     alpha(v) alpha(w) alpha(zeta) sqrt(zeta)
       psi(sqrt(v*w/zeta)/t)
       phiHat(sigma*rho*t*sqrt(v*zeta/w)),
   with rho=VB/C<=x^eta. The independent actualF supplier now gives its
   ContDiff order4L, compact support, and support subset inside64, consumed
   explicitly by actual_normalizedF_weighted_l1 above.
   The remaining quantitative supplier is exactly
     derivMass actualF (4L) <= D_L * (x^eta)^(4L)
   with D_L independent of rho,x,a,V,y,z,m,spectral height.
   It is a finite real derivative-integral estimate, not a Fourier hypothesis.

3. J0 (the original spectral derivative budget) is fixed FIRST. Then choose
   L=J0+3 and r=4L. The separation weighted L1 costs x^(4L eta); its square
   costs x^(8L eta). The fixed factors scaleCost(r), seriesCost(J0), D_L
   depend on J0/cutoffs only and can be absorbed after choosing eta.
   Choose eta only after J0,L and the available positive exponent slack.
   Choose the Poisson tail differentiation order J only AFTER eta, large
   enough to pay the already identified short tail. This J is not J0.

4. This generic lattice argument never changes the previously fixed common
   m interval I_V, nor any coordinate's evaluation point. The m character
   remains e((k_m/64)*m/V), the scalar y,z modulation remains independent of
   future m and spectral height, and a remains absent from the normalized
   amplitude. No additional kappa fee appears: the original 5*kappa is paid
   only where already charged upstream.

5. Genuine remaining independent steps are continuous four-coordinate
   periodization (to bundle period64 f as a ContinuousMap for the native
   inverse), and the actual uniform-rho derivative-mass supplier. Neither is
   silently assumed to be this lattice theorem's conclusion. No original
   paper error is inferred from either formalization boundary.

This file is SOURCEONLY and uncompiled as explicitly required. It is a
concrete by-proof candidate, not a proof-checker or completed-supplier claim.
-/


end
