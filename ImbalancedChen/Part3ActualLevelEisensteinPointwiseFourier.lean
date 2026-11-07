import ImbalancedChen.Part3LevelEisensteinFourierAbsoluteConvergence
import Mathlib.Analysis.Fourier.AddCircle

/-!
Pointwise all-level complex Eisenstein Fourier reconstruction. The literal
level-N horizontal trace is continuous and periodic; its native circle
coefficients equal the actual c-series/Gamma/K coefficients. Their proved
absolute convergence permits native pointwise Fourier inversion. Signed
regrouping gives an explicit constant plus positive/negative Bessel pairs,
retaining the literal N|c Ramanujan series at both signed frequencies.
SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualLevelEisensteinPointwiseFourier

noncomputable section

open Set Filter
open scoped Topology BigOperators UpperHalfPlane
open PrimitiveEisensteinFourierParameterAnalytic
open LevelPrimitiveComplexEisenstein LevelPrimitiveComplexEisensteinRegularity
open LevelEisensteinFourierParameterAnalytic ActualLevelComplexEisensteinFourier
open LevelEisensteinFourierAbsoluteConvergence ActualRamanujanSinglePrimeLevelSplit
open Part3ActualRamanujanBesselNormalConvergence
open ComplexOrderKBridgeSourceOnly

/-- The genuine level-N periodic trace bundled on the native period-one circle. -/
def levelTraceCircle (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun := (levelPrimitiveComplexEisenstein_horizontal_periodic N y hy s hs).lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact (levelPrimitiveComplexEisenstein_horizontal_continuous N y hy s hs).quotient_liftOn' _

@[simp] theorem levelTraceCircle_coe_apply (N : ℕ) (y : ℝ) (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    levelTraceCircle N y hy s hs (x : AddCircle (1 : ℝ)) =
      levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x) := rfl

private theorem native_negative_phase (n : ℤ) (x : ℝ) :
    AddCircle.fourier (-n) (x : AddCircle (1 : ℝ)) = fourierPhase n x := by
  rw [AddCircle.fourier_coe_apply]
  unfold fourierPhase
  simp only [div_one]
  push_cast
  congr 1
  ring

theorem levelTraceCircle_fourierCoeff (N : ℕ) (y : ℝ) (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (n : ℤ) :
    AddCircle.fourierCoeff (levelTraceCircle N y hy s hs) n = levelCanonicalCoefficient N s y n := by
  calc
    _ = actualLevelFourier N y hy n s := by
      rw [AddCircle.fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)]
      simp only [div_one, one_smul, zero_add, smul_eq_mul]
      unfold actualLevelFourier levelFourierIntegrand
      apply intervalIntegral.integral_congr
      intro x _hx
      rw [native_negative_phase, levelTraceCircle_coe_apply]
    _ = _ := actualLevelFourier_eq_levelCanonical N y hy n s hs

/-- Actual HasSum, derived from the physical level trace and native Fourier
inversion; it is a conclusion and never a target hypothesis. -/
theorem levelPrimitiveComplexEisenstein_fourier_hasSum
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    HasSum (fun n : ℤ => levelCanonicalCoefficient N s y n *
      AddCircle.fourier n (x : AddCircle (1 : ℝ)))
      (levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x)) := by
  have hcoeff : AddCircle.fourierCoeff (levelTraceCircle N y hy s hs) =
      levelCanonicalCoefficient N s y := funext (levelTraceCircle_fourierCoeff N y hy s hs)
  have hsum : Summable (AddCircle.fourierCoeff (levelTraceCircle N y hy s hs)) := by
    rw [hcoeff]
    exact (levelCanonicalCoefficient_norm_summable N s hs hy).of_norm
  have h := AddCircle.has_pointwise_sum_fourier_series_of_summable
    (f := levelTraceCircle N y hy s hs) hsum (x : AddCircle (1 : ℝ))
  simpa only [hcoeff, levelTraceCircle_coe_apply, smul_eq_mul] using h

/-- The literal level-N pointwise Fourier expansion, with no reconstruction premise. -/
theorem levelPrimitiveComplexEisenstein_pointwise_fourier
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x) =
      ∑' n : ℤ, levelCanonicalCoefficient N s y n *
        AddCircle.fourier n (x : AddCircle (1 : ℝ)) :=
  (levelPrimitiveComplexEisenstein_fourier_hasSum N y hy s hs x).tsum_eq.symm

/-- This same expansion belongs to the genuine GammaInfinity\Gamma0(N)
parabolic coset object by its already proved half-pair identity. -/
theorem actualComplexParabolicEisenstein_pointwise_fourier
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    actualComplexParabolicEisenstein N s (horizontalPoint y hy x) =
      ∑' n : ℤ, levelCanonicalCoefficient N s y n *
        AddCircle.fourier n (x : AddCircle (1 : ℝ)) := by
  rw [actualComplexParabolicEisenstein_eq_half_pair_sum N s hs]
  exact levelPrimitiveComplexEisenstein_pointwise_fourier N y hy s hs x

/-- Common nonzero seed factor before its actual restricted c-series. -/
def levelNonzeroNormalization (s : ℂ) (y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) ^ s / Complex.Gamma s) * (Real.sqrt y : ℂ)

/-- Both signed arithmetic frequencies, each counted once and with the
same absolute-frequency K factor. No evenness of a free c-series is assumed. -/
def levelBesselPair (N : ℕ) (s : ℂ) (y x : ℝ) (k : ℕ) : ℂ :=
  (((k + 1 : ℕ) : ℂ) ^ (s - 1 / 2) *
    complexOrderK (s - 1 / 2) (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * y)) *
    (restrictedSeries N (((k + 1 : ℕ) : ℤ)) (2 * s) * phase (k + 1) x +
      restrictedSeries N (-((k + 1 : ℕ) : ℤ)) (2 * s) * phase (k + 1) (-x))

private theorem signed_pair_term (N : ℕ) (s : ℂ) (y x : ℝ) (k : ℕ) :
    (levelCanonicalCoefficient N s y ((k + 1 : ℕ) : ℤ) *
        AddCircle.fourier (((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) +
      levelCanonicalCoefficient N s y (-((k + 1 : ℕ) : ℤ)) *
        AddCircle.fourier (-((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ))) =
          levelNonzeroNormalization s y * levelBesselPair N s y x k := by
  have hk : ((k + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hkneg : -((k + 1 : ℕ) : ℤ) ≠ 0 := neg_ne_zero.mpr hk
  have hkr : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
  have hp : AddCircle.fourier (((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) = phase (k + 1) x := by
    rw [AddCircle.fourier_coe_apply]
    unfold phase
    simp only [div_one]
    push_cast
    congr 1
    ring
  have hm : AddCircle.fourier (-((k + 1 : ℕ) : ℤ)) (x : AddCircle (1 : ℝ)) = phase (k + 1) (-x) := by
    rw [AddCircle.fourier_coe_apply]
    unfold phase
    simp only [div_one]
    push_cast
    congr 1
    ring
  rw [hp, hm]
  unfold levelCanonicalCoefficient seedFourierKernel levelNonzeroNormalization levelBesselPair
  simp only [if_neg hk, if_neg hkneg, zero_add, Int.cast_natCast, Int.cast_neg,
    abs_neg, abs_of_nonneg hkr, Complex.ofReal_natCast]
  ring

/-- Explicit actual all-level Fourier-Bessel expansion, with literal
restricted c-series, zero Gamma coefficient and both nonzero Fourier signs. -/
theorem levelPrimitiveComplexEisenstein_pointwise_bessel
    (N : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    levelPrimitiveComplexEisenstein N s (horizontalPoint y hy x) =
      (y : ℂ) ^ s + restrictedSeries N 0 (2 * s) *
        ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - 1 / 2) / Complex.Gamma s * (y : ℂ) ^ (1 - s)) +
          levelNonzeroNormalization s y * ∑' k : ℕ, levelBesselPair N s y x k := by
  let f : ℤ → ℂ := fun n => levelCanonicalCoefficient N s y n *
    AddCircle.fourier n (x : AddCircle (1 : ℝ))
  have hf : Summable f := by
    apply Summable.of_norm_bounded (levelCanonicalCoefficient_norm_summable N s hs hy)
    intro n
    simp only [norm_mul, AddCircle.fourier_apply, Circle.norm_coe, mul_one, le_refl]
  have hp : Summable (fun k : ℕ => f ((k + 1 : ℕ) : ℤ)) :=
    hf.comp_injective (by intro i j hij; exact Nat.succ_injective (Int.ofNat_injective hij))
  have hn : Summable (fun k : ℕ => f (-((k + 1 : ℕ) : ℤ))) :=
    hf.comp_injective (by intro i j hij; exact Nat.succ_injective (Int.ofNat_injective (neg_injective hij)))
  have hp0 : Summable (fun k : ℕ => f (k : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  calc
    _ = ∑' n : ℤ, f n := levelPrimitiveComplexEisenstein_pointwise_fourier N y hy s hs x
    _ = (∑' k : ℕ, f (k : ℤ)) + ∑' k : ℕ, f (-((k + 1 : ℕ) : ℤ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using tsum_of_nat_of_neg_add_one hp0
        (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
    _ = f 0 + ∑' k : ℕ, (f ((k + 1 : ℕ) : ℤ) + f (-((k + 1 : ℕ) : ℤ))) := by
      rw [hp0.tsum_eq_zero_add, tsum_add hp hn]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := by
      simp_rw [show ∀ k, f ((k + 1 : ℕ) : ℤ) + f (-((k + 1 : ℕ) : ℤ)) =
        levelNonzeroNormalization s y * levelBesselPair N s y x k from signed_pair_term N s y x]
      rw [tsum_mul_left]
      simp only [f, levelCanonicalCoefficient, seedFourierKernel, if_true,
        AddCircle.fourier_zero, mul_one]

end
end ImbalancedChen.Part3.ActualLevelEisensteinPointwiseFourier
