import ImbalancedChen.Part3LevelEisensteinFourierParameterAnalytic
import ImbalancedChen.Part3ActualEisensteinRamanujanCSum
import ImbalancedChen.Part3ActualRamanujanSinglePrimeLevelSplit
import ImbalancedChen.Part3ComplexOrderKEntire
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
Actual complex level-N Fourier coefficients on Re(s)>1. The literal N|c
arithmetic series is holomorphic by its proved coefficient growth and the
native L-series theorem. The actual level Fourier integral is holomorphic
by the independent genuine level lattice domination. Real all-level Fourier
coefficients identify both sides on a real interval, so the connected-domain
identity theorem proves the complex formula. N is never replaced by 1.
SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualLevelComplexEisensteinFourier

noncomputable section

open Set Complex Topology
open scoped UpperHalfPlane BigOperators
open PrimitiveEisensteinFourierParameterAnalytic
open LevelPrimitiveComplexEisenstein LevelEisensteinFourierParameterAnalytic
open ActualEisensteinRamanujanCSum20261025a
open ActualRamanujanSinglePrimeLevelSplit
open RamanujanMultiplicativeGcdBound20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKEntire20261025a
open OriginalSmoothPoissonTail.Physical.ZeroMode

/-- Literal arithmetic coefficient with the true level divisibility gate. -/
def levelArithmetic (N : ℕ) (n : ℤ) (c : ℕ) : ℂ :=
  if N ∣ c then ramanujan c n else 0

private theorem levelArithmetic_zero (N : ℕ) (n : ℤ) : levelArithmetic N n 0 = 0 := by
  simp [levelArithmetic, ramanujan, kloosterman]

private theorem levelArithmetic_norm_le (N : ℕ) (n : ℤ) {c : ℕ} (hc : c ≠ 0) :
    ‖levelArithmetic N n c‖ ≤ (c : ℝ) := by
  by_cases hNc : N ∣ c
  · rw [levelArithmetic, if_pos hNc]
    exact (norm_ramanujan_le_gcd c n).trans (by
      exact_mod_cast Nat.gcd_le_left n.natAbs (Nat.pos_of_ne_zero hc))
  · simp [levelArithmetic, hNc]

/-- The actual restricted series is an ordinary L-series with the exact
same coefficients. This is not an assumed evaluation of its c-sum. -/
theorem restrictedSeries_eq_LSeries (N : ℕ) (n : ℤ) (w : ℂ) :
    restrictedSeries N n w = LSeries (levelArithmetic N n) w := by
  apply tsum_congr
  intro c
  rw [LSeries.term_def₀ (levelArithmetic_zero N n)]
  unfold levelArithmetic actualTerm
  split_ifs <;> simp

private theorem levelArithmetic_abscissa_le_two (N : ℕ) (n : ℤ) :
    LSeries.abscissaOfAbsConv (levelArithmetic N n) ≤ (2 : ℝ) := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
    (f := levelArithmetic N n) (x := (1 : ℝ))
    ⟨1, fun c hc => by simpa only [one_mul, Real.rpow_one] using levelArithmetic_norm_le N n hc⟩
  simpa using h

/-- True analyticity of the actual level-restricted c-series in its
required parameter halfplane, including zero frequency. -/
theorem restrictedSeries_two_mul_analyticOnNhd (N : ℕ) (n : ℤ) :
    AnalyticOnNhd ℂ (fun s : ℂ => restrictedSeries N n (2 * s)) {s : ℂ | 1 < s.re} := by
  have heq : (fun s : ℂ => restrictedSeries N n (2 * s)) =
      (fun s : ℂ => LSeries (levelArithmetic N n) (2 * s)) :=
    funext (fun s => restrictedSeries_eq_LSeries N n (2 * s))
  rw [heq]
  have hd : DifferentiableOn ℂ (fun s : ℂ => LSeries (levelArithmetic N n) (2 * s))
      {s : ℂ | 1 < s.re} := by
    intro s hs
    have htwo : (2 : ℝ) < (2 * s).re := by
      simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
      linarith
    have hconv : LSeries.abscissaOfAbsConv (levelArithmetic N n) < (2 * s).re :=
      (levelArithmetic_abscissa_le_two N n).trans_lt (by exact_mod_cast htwo)
    exact ((LSeries_hasDerivAt hconv).differentiableAt.comp s
      (differentiableAt_id.const_mul (2 : ℂ))).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)

private theorem actualTerm_twice_ofReal (n : ℤ) (t : ℝ) (c : ℕ) :
    actualTerm n (2 * (t : ℂ)) c = (((c : ℝ) ^ (-(2 * t)) : ℝ) : ℂ) * ramanujan c n := by
  have hpow : (c : ℂ) ^ (-(2 * (t : ℂ))) = (((c : ℝ) ^ (-(2 * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg c)]
    push_cast
    rfl
  rw [actualTerm, hpow]
  ring

/-- The complex c-series restricts to the original real positive-c series,
with its same literal N|c condition and zero natural summand. -/
theorem restrictedSeries_twice_ofReal (N : ℕ) (n : ℤ) (t : ℝ) :
    restrictedSeries N n (2 * (t : ℂ)) = levelRamanujanSeries N t n := by
  have hzero : (if N ∣ (0 : ℕ) then actualTerm n (2 * (t : ℂ)) 0 else 0) = 0 := by simp
  unfold restrictedSeries levelRamanujanSeries
  rw [← tsum_pnat_eq_tsum_of_eq_zero hzero]
  apply tsum_congr
  intro c
  unfold levelRamanujanTerm
  by_cases hNc : N ∣ (c : ℕ)
  · simp only [if_pos hNc]
    exact actualTerm_twice_ofReal n t (c : ℕ)
  · simp only [if_neg hNc]

/-- The actual complex power-seed coefficient, without its c-arithmetic factor. -/
def seedFourierKernel (s : ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  if n = 0 then
    (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s * (y : ℂ) ^ (1 - s)
  else
    (2 * (Real.pi : ℂ) ^ s / Complex.Gamma s) *
      ((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * (Real.sqrt y : ℂ) *
        complexOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y)

/-- The complete canonical level coefficient, preserving the actual c-series. -/
def levelCanonicalCoefficient (N : ℕ) (s : ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  (if n = 0 then (y : ℂ) ^ s else 0) +
    restrictedSeries N n (2 * s) * seedFourierKernel s y n

private theorem gamma_differentiableAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gamma s := by
  apply Complex.differentiableAt_Gamma s
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  linarith [Nat.cast_nonneg m]

theorem seedFourierKernel_differentiableAt (y : ℝ) (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) : DifferentiableAt ℂ (fun w => seedFourierKernel w y n) s := by
  have hg := gamma_differentiableAt_of_re_pos (s := s) (by linarith)
  have hgne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hhalf : 0 < (s - 1 / 2).re := by simp only [Complex.sub_re]; norm_num; linarith
  have hshift := (gamma_differentiableAt_of_re_pos hhalf).comp s
    (differentiableAt_id.sub_const (1 / 2 : ℂ))
  by_cases hn : n = 0
  · have hp : DifferentiableAt ℂ (fun w : ℂ => (y : ℂ) ^ (1 - w)) s :=
      (differentiableAt_const.sub differentiableAt_id).const_cpow (.inl hyC)
    simpa only [seedFourierKernel, if_pos hn] using
      (((differentiableAt_const.mul hshift).div hg hgne).mul hp)
  · have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnC : ((|(n : ℝ)| : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (abs_pos.mpr hnR).ne'
    have hp : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ w) s :=
      differentiableAt_id.const_cpow (.inl hpi)
    have hnp : DifferentiableAt ℂ (fun w : ℂ => ((|(n : ℝ)| : ℝ) : ℂ) ^ (w - 1 / 2)) s :=
      (differentiableAt_id.sub_const _).const_cpow (.inl hnC)
    have hq : 0 < 2 * Real.pi * |(n : ℝ)| * y := by positivity
    have hK := (complexOrderK_differentiable_all hq).differentiableAt.comp s
      (differentiableAt_id.sub_const (1 / 2 : ℂ))
    simpa only [seedFourierKernel, if_neg hn] using
      (((((differentiableAt_const.mul hp).div hg hgne).mul hnp).mul_const (Real.sqrt y : ℂ)).mul hK)

theorem levelCanonicalCoefficient_analyticOnNhd (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    AnalyticOnNhd ℂ (fun s => levelCanonicalCoefficient N s y n) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (fun s => levelCanonicalCoefficient N s y n) {s : ℂ | 1 < s.re} := by
    intro s hs
    have harith := (restrictedSeries_two_mul_analyticOnNhd N n s hs).differentiableAt
    have hkernel := seedFourierKernel_differentiableAt y hy n s hs
    have hheight : DifferentiableAt ℂ (fun w : ℂ => if n = 0 then (y : ℂ) ^ w else 0) s := by
      by_cases hn : n = 0
      · simpa only [if_pos hn] using
          differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
      · simpa only [if_neg hn] using (differentiableAt_const (c := (0 : ℂ)))
    exact (hheight.add (harith.mul hkernel)).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)

private theorem phase_eq_realCaller (n : ℤ) (x : ℝ) :
    fourierPhase n x = PowerSeedFourierLaplaceFubini.fourierPhase n x := by
  unfold fourierPhase PowerSeedFourierLaplaceFubini.fourierPhase
  push_cast
  congr 1
  ring

/-- The literal complex level Fourier integral restricts to the previously
proved actual real level coefficient, not to an assumed canonical value. -/
theorem actualLevelFourier_ofReal (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ)
    (t : ℝ) (ht : 1 < t) :
    actualLevelFourier N y hy n (t : ℂ) =
      ActualEisensteinFourierInterchange20261025a.actualEisensteinFourier N t y hy n := by
  unfold actualLevelFourier levelFourierIntegrand
    ActualEisensteinFourierInterchange20261025a.actualEisensteinFourier
  apply intervalIntegral.integral_congr
  intro x _hx
  rw [levelPrimitiveComplexEisenstein_ofReal N t ht, phase_eq_realCaller]
  rfl

/-- The already proved all-level real coefficient is the real restriction
of this literal complex canonical c-series/Gamma/K expression. -/
theorem actualLevelFourier_real_canonical (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ)
    (t : ℝ) (ht : 1 < t) :
    actualLevelFourier N y hy n (t : ℂ) = levelCanonicalCoefficient N (t : ℂ) y n := by
  rw [actualLevelFourier_ofReal N y hy n t ht]
  have hh : (t : ℂ) - 1 / 2 = ((t - 1 / 2 : ℝ) : ℂ) := by push_cast
  have h1 : 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast
  by_cases hn : n = 0
  · subst n
    rw [actualEisensteinFourier_zero N t ht y hy]
    unfold levelCanonicalCoefficient seedFourierKernel
    rw [if_pos rfl, if_pos rfl, restrictedSeries_twice_ofReal]
    have harith : levelRamanujanSeries N t 0 =
        ((∑' c : ℕ+, levelTotientTerm N t c : ℝ) : ℂ) := by
      simp only [levelRamanujanSeries, levelRamanujanTerm_zero, Complex.ofReal_tsum]
    rw [harith, hh, h1, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
      ← Complex.ofReal_cpow hy.le t, ← Complex.ofReal_cpow hy.le (1 - t)]
    push_cast
    ring
  · rw [actualEisensteinFourier_nonzero N t ht y hy n hn]
    unfold levelCanonicalCoefficient seedFourierKernel
    rw [if_neg hn, if_neg hn, zero_add, restrictedSeries_twice_ofReal,
      hh, Complex.Gamma_ofReal, complexOrderK_real,
      ← Complex.ofReal_cpow Real.pi_pos.le t,
      ← Complex.ofReal_cpow (abs_nonneg (n : ℝ)) (t - 1 / 2)]
    push_cast
    ring

/-- Actual all-level complex Fourier evaluation throughout Re(s)>1.
The identity theorem consumes two independently proved holomorphic functions
and the actual all-level real Fourier identity; none is a target premise. -/
theorem actualLevelFourier_eq_levelCanonical (N : ℕ) (y : ℝ) (hy : 0 < y) (n : ℤ)
    (s : ℂ) (hs : 1 < s.re) :
    actualLevelFourier N y hy n s = levelCanonicalCoefficient N s y n := by
  have hf := actualLevelFourier_analyticOnNhd N y hy n
  have hg := levelCanonicalCoefficient_analyticOnNhd N y hy n
  let U : Set ℂ := {z | 1 < z.re}
  have hU : IsPreconnected U := (Complex.convex_halfSpace_re_gt (r := 1)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by norm_num [U]
  have hclosure : (2 : ℂ) ∈ closure
      ({z : ℂ | actualLevelFourier N y hy n z = levelCanonicalCoefficient N z y n} \ {2}) := by
    have hreal : (2 : ℝ) ∈ closure (Ioi (2 : ℝ)) := by simp
    have himage : (2 : ℂ) ∈ closure (Complex.ofReal '' Ioi (2 : ℝ)) :=
      mem_closure_image Complex.continuous_ofReal.continuousAt hreal
    apply (closure_mono ?_) himage
    rintro z ⟨t, ht, rfl⟩
    refine ⟨actualLevelFourier_real_canonical N y hy n t (by linarith), ?_⟩
    simp only [mem_singleton_iff]
    intro h
    have ht2 : t = 2 := by exact_mod_cast h
    linarith
  exact (hf.eqOn_of_preconnected_of_mem_closure hg hU h2 hclosure) s hs

end
end ImbalancedChen.Part3.ActualLevelComplexEisensteinFourier

