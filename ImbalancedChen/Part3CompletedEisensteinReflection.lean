import ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
import ImbalancedChen.Part3ComplexOrderKShiftDerivative
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Reflection of the actual completed Fourier expression. The finite divisor
involution d -> N/d proves the exact complex-power reflection of the
normalized divisor coefficient. Together with actual K-order evenness this
reflects every actual Fourier-Bessel term and the normally convergent
bilateral sum previously constructed in cbc150.

The constant expression uses Mathlib's pole-removed completed zeta and an
ENTIRE divided difference at s=1/2. Naively adding the totalized values
Lambda(2s)y^s + Lambda(2s-1)y^(1-s) at s=1/2 loses a removable correction.
The dslope definition below supplies that correction canonically. Away
from s=1/2 the literal two-Lambda formula is proved. The completed expression
then satisfies s -> 1-s, with poles s=0,1 explicitly excluded in the final
functional-equation statement. Analyticity/meromorphicity and identification
with a continued physical Eisenstein series are separate tasks.
-/

namespace ImbalancedChen.Part3.CompletedEisensteinReflection20261025a

noncomputable section

open Set MeasureTheory Finset
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
open ImbalancedChen.Part3.ComplexOrderKShiftDerivativeSourceOnly

/-- The actual finite divisor involution gives reflection of the full
normalized coefficient, including the literal complex-power branches. -/
theorem normalized_divisor_reflection (N : ℕ) (hN : 0 < N) (s : ℂ) :
    (N : ℂ) ^ ((1 - s) - 1 / 2) * divisorFactor N (2 * (1 - s)) =
      (N : ℂ) ^ (s - 1 / 2) * divisorFactor N (2 * s) := by
  unfold divisorFactor
  calc
    _ = (N : ℂ) ^ ((1 - s) - 1 / 2) *
        ∑ d ∈ N.divisors, ((N / d : ℕ) : ℂ) ^ (1 - 2 * (1 - s)) := by
      congr 1
      exact (Nat.sum_div_divisors N
        (fun d : ℕ => (d : ℂ) ^ (1 - 2 * (1 - s)))).symm
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hdiv : d ∣ N := Nat.dvd_of_mem_divisors hd
      have hqpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdiv) hdpos
      have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
      have hqC : ((N / d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
      have hprod : (d : ℂ) * ((N / d : ℕ) : ℂ) = (N : ℂ) := by
        exact_mod_cast Nat.mul_div_cancel' hdiv
      rw [← hprod]
      simp only [Complex.natCast_mul_natCast_cpow,
        Complex.cpow_def_of_ne_zero hdC, Complex.cpow_def_of_ne_zero hqC,
        ← Complex.exp_add]
      congr 1
      ring

/-- Reflection is an identity of the existing ACTUAL K-Bessel terms. -/
theorem fourierBesselTerm_reflection (n : ℕ) (s : ℂ) (y x : ℝ) :
    fourierBesselTerm n (1 - s) y x = fourierBesselTerm n s y x := by
  unfold fourierBesselTerm
  rw [normalized_divisor_reflection (n + 1) (by omega) s]
  rw [show (1 - s) - 1 / 2 = -(s - 1 / 2) by ring, actual_K_even_order]

theorem nonzeroFrequencyPair_reflection (n : ℕ) (s : ℂ) (y x : ℝ) :
    nonzeroFrequencyPair n (1 - s) y x = nonzeroFrequencyPair n s y x := by
  unfold nonzeroFrequencyPair
  rw [fourierBesselTerm_reflection, fourierBesselTerm_reflection]

/-- The actual entire bilateral Fourier kernel is reflection invariant.
Its absolute and locally uniform convergence is supplied by the imported
actual normal-convergence theorem, not assumed by this statement. -/
theorem nonzeroFrequencyPair_sum_reflection (s : ℂ) (y x : ℝ) :
    (∑' n : ℕ, nonzeroFrequencyPair n (1 - s) y x) =
      ∑' n : ℕ, nonzeroFrequencyPair n s y x :=
  tsum_congr (fun n => nonzeroFrequencyPair_reflection n s y x)

/-- The numerator that vanishes at the central parameter 1/2. -/
def heightDifference (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ s - (y : ℂ) ^ (1 - s)

/-- The removable central divided difference, INCLUDING its derivative
value at s=1/2. This avoids the false naive totalized-Lambda central value. -/
def reflectionHeightQuotient (y : ℝ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * dslope (heightDifference y) (1 / 2 : ℂ) s

theorem heightDifference_half (y : ℝ) : heightDifference y (1 / 2) = 0 := by
  unfold heightDifference
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, sub_self]

theorem reflectionHeightQuotient_eq_div (y : ℝ) (s : ℂ) (hs : s ≠ 1 / 2) :
    reflectionHeightQuotient y s = heightDifference y s / (2 * s - 1) := by
  have hd : s - (1 / 2 : ℂ) ≠ 0 := sub_ne_zero.mpr hs
  have hd' : 2 * s - 1 ≠ 0 := by
    intro h
    apply hs
    linear_combination (1 / 2 : ℂ) * h
  rw [reflectionHeightQuotient, dslope_of_ne _ hs, slope_def_field,
    heightDifference_half, sub_zero]
  field_simp [hd, hd']
  ring

/-- The regularized central term reflects even at the central parameter. -/
theorem reflectionHeightQuotient_reflection (y : ℝ) (s : ℂ) :
    reflectionHeightQuotient y (1 - s) = reflectionHeightQuotient y s := by
  by_cases hs : s = 1 / 2
  · subst s
    norm_num
  · have href : 1 - s ≠ (1 / 2 : ℂ) := by
      intro h
      apply hs
      linear_combination -h
    rw [reflectionHeightQuotient_eq_div y (1 - s) href,
      reflectionHeightQuotient_eq_div y s hs]
    have hnum : heightDifference y (1 - s) = -heightDifference y s := by
      unfold heightDifference
      rw [show (1 : ℂ) - (1 - s) = s by ring]
      ring
    rw [hnum, show (2 : ℂ) * (1 - s) - 1 = -(2 * s - 1) by ring,
      neg_div_neg_eq]

/-- The completed constant term with the central removable singularity
resolved. Its only possible genuine poles are s=0 and s=1. -/
def completedConstant (y : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta₀ (2 * s) * (y : ℂ) ^ s +
    completedRiemannZeta₀ (2 * s - 1) * (y : ℂ) ^ (1 - s) -
    (y : ℂ) ^ s / (2 * s) - (y : ℂ) ^ (1 - s) / (2 * (1 - s)) +
    reflectionHeightQuotient y s

/-- Exact agreement with the literal two-Lambda constant expression away
from the removable central point; the genuine pole values are not asserted. -/
theorem completedConstant_eq_raw (y : ℝ) (s : ℂ) (hs : s ≠ 1 / 2) :
    completedConstant y s =
      completedRiemannZeta (2 * s) * (y : ℂ) ^ s +
        completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) := by
  have hd : 2 * s - 1 ≠ 0 := by
    intro h
    apply hs
    linear_combination (1 / 2 : ℂ) * h
  rw [completedConstant, reflectionHeightQuotient_eq_div y s hs,
    completedRiemannZeta_eq, completedRiemannZeta_eq]
  unfold heightDifference
  rw [show (1 : ℂ) - 2 * s = -(2 * s - 1) by ring,
    show (1 : ℂ) - (2 * s - 1) = 2 * (1 - s) by ring]
  simp only [div_neg, div_eq_mul_inv, one_mul]
  ring

/-- Mathlib's actual completed-zeta functional equation exchanges the two
constant pieces; the dslope correction is itself reflection invariant. -/
theorem completedConstant_reflection (y : ℝ) (s : ℂ) :
    completedConstant y (1 - s) = completedConstant y s := by
  have hA : completedRiemannZeta₀ (2 * (1 - s)) =
      completedRiemannZeta₀ (2 * s - 1) := by
    calc
      _ = completedRiemannZeta₀ (1 - (2 * s - 1)) := by congr 1; ring
      _ = _ := completedRiemannZeta₀_one_sub (2 * s - 1)
  have hB : completedRiemannZeta₀ (2 * (1 - s) - 1) =
      completedRiemannZeta₀ (2 * s) := by
    calc
      _ = completedRiemannZeta₀ (1 - 2 * s) := by congr 1; ring
      _ = _ := completedRiemannZeta₀_one_sub (2 * s)
  unfold completedConstant
  rw [hA, hB, show (1 : ℂ) - (1 - s) = s by ring,
    reflectionHeightQuotient_reflection]
  ring

/-- The genuine completed Fourier expression: canonical completed
constant term plus the actual normally convergent bilateral K kernel.
The common factor is exactly 2 sqrt(y), after completion by Lambda(2s). -/
def completedEisensteinFourier (s : ℂ) (y x : ℝ) : ℂ :=
  completedConstant y s + 2 * (Real.sqrt y : ℂ) *
    ∑' n : ℕ, nonzeroFrequencyPair n s y x

/-- Away from the central removable point this is the standard explicit
completed Fourier expression with two actual completed-zeta constants. -/
theorem completedEisensteinFourier_eq_raw (s : ℂ) (y x : ℝ) (hs : s ≠ 1 / 2) :
    completedEisensteinFourier s y x =
      completedRiemannZeta (2 * s) * (y : ℂ) ^ s +
        completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) +
          2 * (Real.sqrt y : ℂ) * ∑' n : ℕ, nonzeroFrequencyPair n s y x := by
  rw [completedEisensteinFourier, completedConstant_eq_raw y s hs]

/-- Functional equation of the completed Fourier expression on the true
pole-excluded domain. y>0 also ensures its literal K series is absolutely
convergent by the existing actual normal-convergence supplier. This does
not assume or assert a physical meromorphic continuation or reconstruction. -/
theorem completedEisensteinFourier_reflection (s : ℂ) (y : ℝ) (hy : 0 < y)
    (x : ℝ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedEisensteinFourier (1 - s) y x = completedEisensteinFourier s y x := by
  unfold completedEisensteinFourier
  rw [completedConstant_reflection, nonzeroFrequencyPair_sum_reflection]

end
end ImbalancedChen.Part3.CompletedEisensteinReflection20261025a

