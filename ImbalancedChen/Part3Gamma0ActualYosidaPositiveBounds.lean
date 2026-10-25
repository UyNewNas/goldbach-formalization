import ImbalancedChen.Part3Gamma0ActualYosidaGraphApproximation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Bounded positive self-adjoint Yosida approximants on the ACTUAL Gamma0
quotient Hilbert space. The already constructed B_n=(n+1)R_{n+1} is positive
and contractive, so 0<=B_n<=I. Thus I-B_n is another positive contraction,
and A_n=(n+1)(I-B_n) is genuinely positive self-adjoint with norm <=n+1.

All operators are the actual operators of the actual Friedrichs graph
approximation. No positivity, self-adjointness or norm conclusion is a
caller premise. No heat semigroup or Trotter limit is asserted here.
-/

namespace ImbalancedChen.Part3.Gamma0ActualYosidaPositiveBounds20261025a

noncomputable section
open MeasureTheory
open scoped ComplexOrder
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a
open Gamma0ActualYosidaGraphApproximation20261025a

theorem yosidaParameter_complex_nonneg (n : ℕ) :
    0 ≤ ((yosidaParameter n:ℝ):ℂ) := by
  exact_mod_cast (yosidaParameter_pos n).le

/-- Actual positivity of B_n follows from the actual shifted resolvent,
with the true positive real scalar n+1. -/
theorem actualYosidaSmoother_isPositive (N : ℕ) [NeZero N] (n : ℕ) :
    (actualYosidaSmoother N n).IsPositive :=
  (actualGammaShiftedResolvent_isPositive N (yosidaParameter_pos n)).smul_of_nonneg
    (yosidaParameter_complex_nonneg n)

theorem actualYosidaSmoother_nonneg (N : ℕ) [NeZero N] (n : ℕ) :
    0 ≤ actualYosidaSmoother N n :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (actualYosidaSmoother_isPositive N n)

theorem actualYosidaSmoother_selfAdjoint (N : ℕ) [NeZero N] (n : ℕ) :
    IsSelfAdjoint (actualYosidaSmoother N n) :=
  (actualYosidaSmoother_isPositive N n).isSelfAdjoint

/-- The order bound is derived from genuine positive operator order and
the previously proved actual contraction bound, not assumed spectrally. -/
theorem actualYosidaSmoother_le_one (N : ℕ) [NeZero N] (n : ℕ) :
    actualYosidaSmoother N n ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (actualYosidaSmoother_nonneg N n)).mp
    (actualYosidaSmoother_norm_le_one N n)

theorem actualYosidaComplement_nonneg (N : ℕ) [NeZero N] (n : ℕ) :
    0 ≤ 1-actualYosidaSmoother N n :=
  sub_nonneg.mpr (actualYosidaSmoother_le_one N n)

theorem actualYosidaComplement_le_one (N : ℕ) [NeZero N] (n : ℕ) :
    1-actualYosidaSmoother N n ≤ 1 :=
  sub_le_self _ (actualYosidaSmoother_nonneg N n)

theorem actualYosidaComplement_norm_le_one (N : ℕ) [NeZero N] (n : ℕ) :
    ‖1-actualYosidaSmoother N n‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (actualYosidaComplement_nonneg N n)).mpr
    (actualYosidaComplement_le_one N n)

/-- Actual A_n positivity, as a bounded operator on the same physical
quotient Hilbert space as A_F, is a derived native operator predicate. -/
theorem actualYosidaOperator_isPositive (N : ℕ) [NeZero N] (n : ℕ) :
    (actualYosidaOperator N n).IsPositive :=
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (actualYosidaComplement_nonneg N n)).smul_of_nonneg
      (yosidaParameter_complex_nonneg n)

theorem actualYosidaOperator_nonneg (N : ℕ) [NeZero N] (n : ℕ) :
    0 ≤ actualYosidaOperator N n :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (actualYosidaOperator_isPositive N n)

/-- Genuine bounded self-adjointness, not merely an inner-product
symmetry label: the native CLM star equals the operator. -/
theorem actualYosidaOperator_selfAdjoint (N : ℕ) [NeZero N] (n : ℕ) :
    IsSelfAdjoint (actualYosidaOperator N n) :=
  (actualYosidaOperator_isPositive N n).isSelfAdjoint

theorem actualYosidaOperator_adjoint (N : ℕ) [NeZero N] (n : ℕ) :
    (actualYosidaOperator N n).adjoint=actualYosidaOperator N n :=
  (actualYosidaOperator_selfAdjoint N n).adjoint_eq

theorem actualYosidaOperator_norm_le (N : ℕ) [NeZero N] (n : ℕ) :
    ‖actualYosidaOperator N n‖ ≤ (n:ℝ)+1 := by
  calc
    _ = yosidaParameter n*‖1-actualYosidaSmoother N n‖ := by
      rw [actualYosidaOperator,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (yosidaParameter_pos n)]
    _ ≤ yosidaParameter n*1 :=
      mul_le_mul_of_nonneg_left (actualYosidaComplement_norm_le_one N n)
        (yosidaParameter_pos n).le
    _ = (n:ℝ)+1 := by rw [mul_one]; rfl

theorem actualYosidaOperator_apply_norm_le (N : ℕ) [NeZero N]
    (n : ℕ) (u : QuotientL2 N) :
    ‖actualYosidaOperator N n u‖ ≤ ((n:ℝ)+1)*‖u‖ :=
  ((actualYosidaOperator N n).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (actualYosidaOperator_norm_le N n) (norm_nonneg u))

theorem actualYosidaOperator_quadratic_nonneg (N : ℕ) [NeZero N]
    (n : ℕ) (u : QuotientL2 N) :
    0 ≤ (inner ℂ u (actualYosidaOperator N n u)).re :=
  (actualYosidaOperator_isPositive N n).re_inner_nonneg_right u

end
end ImbalancedChen.Part3.Gamma0ActualYosidaPositiveBounds20261025a
