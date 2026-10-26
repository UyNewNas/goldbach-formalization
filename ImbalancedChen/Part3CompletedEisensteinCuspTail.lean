import ImbalancedChen.Part3CompletedActualEisensteinIdentity
import ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
import ImbalancedChen.Part3ComplexOrderKUniformStripDecay
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

A genuine cusp-tail bound for the ACTUAL completed full-level Eisenstein
continuation. The existing physical object is identified with its actual
completed Fourier expression. We retain the height y in the native uniform
K-order-strip exponential bound, instead of replacing y by a fixed lower
height. A frequency/height split leaves a summable n^(3M+2) exp(-pi*n/4)
majorant and exp(-3*pi*y/4). The actual factor sqrt(y) is absorbed into
exp(pi*y/4). Thus the tail is bounded by C_M exp(-pi*y/2), uniformly for
all horizontal positions, y>=1 and |Re(s)|<=M. Constants are defined before
s,x,y. Every compact complex parameter set is then covered by one such
strip, including the correctly regularized central parameter s=1/2.
No asymptotic, summability, Fourier reconstruction or tail bound is an input.
-/

namespace ImbalancedChen.Part3.CompletedEisensteinCuspTail20261025a

noncomputable section

open Set Filter Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
open ImbalancedChen.Part3.ComplexOrderKUniformStripDecay20261025a

/-- One fixed, genuinely summable frequency mass, selected before height,
parameter and horizontal position. The base height is literally 1/4. -/
def tailSeriesMass (M : ℕ) : ℝ := ∑' n : ℕ, majorant M (1 / 4) n

def cuspTailConstant (M : ℕ) : ℝ := 1 + (16 / Real.pi) * tailSeriesMass M

theorem tailSeriesMass_nonneg (M : ℕ) : 0 ≤ tailSeriesMass M := by
  apply tsum_nonneg
  intro n
  unfold majorant decayConstant stripDecayConstant
  positivity

theorem cuspTailConstant_pos (M : ℕ) : 0 < cuspTailConstant M := by
  have h := tailSeriesMass_nonneg M
  unfold cuspTailConstant
  positivity

/-- The actual K exponential keeps a height factor while reserving a
summable frequency factor. This is a proved elementary inequality. -/
theorem exponential_height_frequency_split (N : ℕ) (hN : 0 < N)
    {y : ℝ} (hy : 1 ≤ y) :
    Real.exp (-(2 * Real.pi * (N : ℝ) * y / 2)) ≤
      Real.exp (-(3 * Real.pi / 4) * y) * Real.exp (-(Real.pi / 4) * (N : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have h1 : 0 ≤ y * ((N : ℝ) - 1) := mul_nonneg hy0 (sub_nonneg.mpr hN1)
  have h2 : 0 ≤ (N : ℝ) * (y - 1) :=
    mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hy)
  have hbase : 3 * y + (N : ℝ) ≤ 4 * (N : ℝ) * y := by nlinarith
  have hpi := mul_le_mul_of_nonneg_left hbase Real.pi_pos.le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hpi]

/-- A quantitative bound for the EXISTING actual Fourier-Bessel term,
retaining exp(-3*pi*y/4) uniformly in its full complex order strip. -/
theorem fourierBesselTerm_height_bound (M : ℕ) (n : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖fourierBesselTerm n s y x‖ ≤
      Real.exp (-(3 * Real.pi / 4) * y) * majorant M (1 / 4) n := by
  let N : ℕ := n + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hq0 : 0 < 2 * Real.pi * (1 / 4 : ℝ) := by positivity
  have hNy : 1 ≤ (N : ℝ) * y := one_le_mul hN1 hy
  have hq : 2 * Real.pi * (1 / 4 : ℝ) ≤ 2 * Real.pi * (N : ℝ) * y := by
    have h := mul_le_mul_of_nonneg_left hNy (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith [Real.pi_pos]
  have hnu : |(s - 1 / 2).re| ≤ (M : ℝ) + 1 := by
    have h := abs_sub_le s.re (1 / 2 : ℝ)
    norm_num at h
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hK := complexOrderK_uniform_exp_bound hq0 hq hnu
  have hExp := exponential_height_frequency_split N hN hy
  have hK' : ‖complexOrderK (s - 1 / 2) (2 * Real.pi * (N : ℝ) * y)‖ ≤
      decayConstant M (1 / 4) *
        (Real.exp (-(3 * Real.pi / 4) * y) * Real.exp (-(Real.pi / 4) * (N : ℝ))) := by
    exact hK.trans (mul_le_mul_of_nonneg_left hExp
      (stripDecayConstant_pos 0 (2 * Real.pi * (1 / 4)) ((M : ℝ) + 1)).le)
  have hc : ‖(N : ℂ) ^ (s - 1 / 2) * divisorFactor N (2 * s)‖ ≤
      (N : ℝ) ^ (3 * M + 2) := by
    rw [norm_mul]
    calc
      _ ≤ (N : ℝ) ^ M * (N : ℝ) ^ (2 * M + 2) :=
        mul_le_mul (power_prefactor_bound hN M hs) (divisorFactor_polynomial_bound hN M hs)
          (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg N) _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hprod := mul_le_mul hc hK' (norm_nonneg _)
    (pow_nonneg (Nat.cast_nonneg N) (3 * M + 2))
  unfold fourierBesselTerm
  rw [norm_mul, norm_mul, norm_phase, mul_one]
  calc
    _ ≤ (N : ℝ) ^ (3 * M + 2) * (decayConstant M (1 / 4) *
        (Real.exp (-(3 * Real.pi / 4) * y) * Real.exp (-(Real.pi / 4) * (N : ℝ)))) := hprod
    _ = _ := by
      unfold majorant
      rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring]
      dsimp [N]
      ring

theorem nonzeroFrequencyPair_height_bound (M : ℕ) (n : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖nonzeroFrequencyPair n s y x‖ ≤
      (2 * Real.exp (-(3 * Real.pi / 4) * y)) * majorant M (1 / 4) n := by
  have hp := fourierBesselTerm_height_bound M n hs hy x
  have hn := fourierBesselTerm_height_bound M n hs hy (-x)
  unfold nonzeroFrequencyPair
  exact (norm_add_le _ _).trans (by linarith)

/-- The ENTIRE actual nonzero-frequency sum, after genuine summability,
keeps the proved height exponential uniformly in x and s. -/
theorem nonzeroFrequencyPair_sum_height_bound (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖∑' n : ℕ, nonzeroFrequencyPair n s y x‖ ≤
      (2 * Real.exp (-(3 * Real.pi / 4) * y)) * tailSeriesMass M := by
  have hg := (majorant_summable M (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (2 * Real.exp (-(3 * Real.pi / 4) * y))
  have h := tsum_of_norm_bounded hg.hasSum
    (fun n => nonzeroFrequencyPair_height_bound M n hs hy x)
  simpa only [tsum_mul_left, tailSeriesMass] using h

/-- Explicit absorption of the actual sqrt(y) factor, leaving the final
height rate pi/2. No asymptotic comparison hypothesis is used. -/
theorem sqrt_height_exponential_absorption {y : ℝ} (hy : 1 ≤ y) :
    Real.sqrt y * Real.exp (-(3 * Real.pi / 4) * y) ≤
      (4 / Real.pi) * Real.exp (-(Real.pi / 2) * y) := by
  have hroot : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy)
  have hlin : y ≤ (4 / Real.pi) * Real.exp (Real.pi * y / 4) := by
    calc
      y = (4 / Real.pi) * (Real.pi * y / 4) := by
        field_simp [Real.pi_ne_zero] <;> ring
      _ ≤ (4 / Real.pi) * Real.exp (Real.pi * y / 4) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (Real.pi * y / 4)])
          (by positivity)
  calc
    _ ≤ ((4 / Real.pi) * Real.exp (Real.pi * y / 4)) *
        Real.exp (-(3 * Real.pi / 4) * y) :=
      mul_le_mul_of_nonneg_right (hroot.trans hlin) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

/-- The literal completed expression minus its CORRECT central-regularized
constant term has an actual uniform cusp-tail exponential estimate. -/
theorem completedFourier_cusp_tail_bound_strip (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖completedEisensteinFourier s y x - completedConstant y s‖ ≤
      cuspTailConstant M * Real.exp (-(Real.pi / 2) * y) := by
  have hmass := tailSeriesMass_nonneg M
  have hsum := nonzeroFrequencyPair_sum_height_bound M hs hy x
  have hsqrt : ‖(2 : ℂ) * (Real.sqrt y : ℂ)‖ = 2 * Real.sqrt y := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]
  have htail : completedEisensteinFourier s y x - completedConstant y s =
      (2 : ℂ) * (Real.sqrt y : ℂ) * ∑' n : ℕ, nonzeroFrequencyPair n s y x := by
    unfold completedEisensteinFourier
    ring
  rw [htail, norm_mul, hsqrt]
  calc
    _ ≤ (2 * Real.sqrt y) *
        ((2 * Real.exp (-(3 * Real.pi / 4) * y)) * tailSeriesMass M) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (4 * tailSeriesMass M) *
        (Real.sqrt y * Real.exp (-(3 * Real.pi / 4) * y)) := by ring
    _ ≤ (4 * tailSeriesMass M) *
        ((4 / Real.pi) * Real.exp (-(Real.pi / 2) * y)) :=
      mul_le_mul_of_nonneg_left (sqrt_height_exponential_absorption hy) (by positivity)
    _ = ((16 / Real.pi) * tailSeriesMass M) * Real.exp (-(Real.pi / 2) * y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold cuspTailConstant; linarith)
      (Real.exp_pos _).le

/-- The estimate is for the existing actual physical continuation at native
upper-half-plane points, not merely for an abstract Fourier kernel. -/
theorem completedActualEisenstein_cusp_tail_bound_strip (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (z : UpperHalfPlane) (hz : 1 ≤ z.im) :
    ‖completedActualEisenstein s z - completedConstant z.im s‖ ≤
      cuspTailConstant M * Real.exp (-(Real.pi / 2) * z.im) := by
  exact completedFourier_cusp_tail_bound_strip M hs hz z.re

/-- One constant chosen BEFORE s, x and y bounds the actual cusp tail for
all s in any compact subset of the genuine pole-excluded complex plane.
The bound includes s=1/2 and its true dslope central correction. -/
theorem completedActualEisenstein_cusp_tail_uniform_compact
    {K : Set ℂ} (hK : IsCompact K) (hKpole : K ⊆ ({0, 1} : Set ℂ)ᶜ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ z : UpperHalfPlane, 1 ≤ z.im →
      ‖completedActualEisenstein s z - completedConstant z.im s‖ ≤
        C * Real.exp (-(Real.pi / 2) * z.im) := by
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  let M : ℕ := Nat.ceil B
  refine ⟨cuspTailConstant M, cuspTailConstant_pos M, ?_⟩
  intro s hs z hz
  have hstrip : |s.re| ≤ (M : ℝ) :=
    (Complex.abs_re_le_norm s).trans ((hB s hs).trans (Nat.le_ceil B))
  exact completedActualEisenstein_cusp_tail_bound_strip M hstrip z hz

end
end ImbalancedChen.Part3.CompletedEisensteinCuspTail20261025a
