import ImbalancedChen.Part3EntireEisensteinPrimeAmplitude
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-! Actual finite divisor multiplicativity, using Mathlib's proved
Dirichlet-convolution multiplicativity theorem. The exact positive-base
complex power arithmetic function is constructed and verified; convolution
with actual zeta is identified with the literal finite divisor carrier.
Thus no multiplicativity or divisor rearrangement is supplied as a premise.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Finset Complex
open scoped BigOperators
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b

namespace ImbalancedChen.Part3.EisensteinAmplitudeMultiplicativity20261026b

def positivePowerArithmetic (w : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ) ^ (1 - w), by simp⟩

theorem positivePowerArithmetic_isMultiplicative (w : ℂ) :
    (positivePowerArithmetic w).IsMultiplicative := by
  classical
  constructor
  · simp [positivePowerArithmetic]
  · intro a b hab
    by_cases ha : a = 0
    · simp [positivePowerArithmetic, ha]
    by_cases hb : b = 0
    · simp [positivePowerArithmetic, hb]
    simp only [positivePowerArithmetic, ArithmeticFunction.coe_mk,
      if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb), Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

def divisorArithmetic (w : ℂ) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * positivePowerArithmetic w

/-- The convolution's finite divisor bijection is the genuine Mathlib
supplier, and every summand is matched to the actual project divisor sum. -/
theorem divisorArithmetic_apply (n : ℕ) (w : ℂ) :
    divisorArithmetic w n = divisorFactor n w := by
  rw [divisorArithmetic, ArithmeticFunction.coe_zeta_mul_apply]
  unfold divisorFactor
  apply Finset.sum_congr rfl
  intro d hd
  simp only [positivePowerArithmetic, ArithmeticFunction.coe_mk,
    if_neg (Nat.pos_of_mem_divisors hd).ne']

theorem divisorArithmetic_isMultiplicative (w : ℂ) :
    (divisorArithmetic w).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (positivePowerArithmetic_isMultiplicative w)

/-- Native finite complex divisor factors multiply at coprime frequencies,
for every complex w. Zero frequency uses the actual empty divisor carrier. -/
theorem divisorFactor_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) (w : ℂ) :
    divisorFactor (m * n) w = divisorFactor m w * divisorFactor n w := by
  have h := (divisorArithmetic_isMultiplicative w).map_mul_of_coprime hmn
  simpa only [divisorArithmetic_apply] using h

/-- The actual normalized amplitudes are multiplicative: the complex
power branches are paid by the positive-natural-base power identity. -/
theorem normalizedAmplitude_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) (s : ℂ) :
    normalizedDivisorAmplitude (m * n) s =
      normalizedDivisorAmplitude m s * normalizedDivisorAmplitude n s := by
  unfold normalizedDivisorAmplitude
  rw [divisorFactor_mul_of_coprime hmn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

end ImbalancedChen.Part3.EisensteinAmplitudeMultiplicativity20261026b
