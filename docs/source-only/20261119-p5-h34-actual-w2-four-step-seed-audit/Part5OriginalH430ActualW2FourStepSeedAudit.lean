import ImbalancedChen.Part5OriginalH430ExactQ80FullSeedBase
import ImbalancedChen.P2EnhancedSeedActualSevenLogIdentity

/-!
P5.6 h34: the manuscript's EXACT four-step rational seed benchmark
is compared to the unchanged original seven-integral W2 feedback
operator and the actual Q80 positive seed.

IMPORTANT: the intercept 20249/1000000 below is the manuscript's
BENCHMARK contribution. This module does NOT prove that the frozen
analytic counting source supplies that intercept. Similarly the seven
actual integrals are NOT proved to exceed 13/100 in this module.
No adopted seed soundness, closed-cell base, or h34 theorem is assumed.
These are proof-producing conditional consequences with the precise
missing lower bound exposed at its original integral source.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualW2FourStepSeedAudit
noncomputable section

open Part5OriginalH430ExactQ80FullSeedBase
open P2EnhancedSeedActualFeedbackAssembly

/-- Four-step manuscript numerical benchmark; not the certified
analytic source itself. Both fractions are unchanged. -/
def benchmarkSeed : ℕ → ℝ
  | 0 => 1 / 50
  | n + 1 => (20249 : ℝ) / 1000000 + (13 / 100 : ℝ) * benchmarkSeed n

/-- The SAME benchmark intercept, but with the original geometric
seven-term W2 operator rather than a synthetic 13%-gain action.
This model is not identified with the complete frozen H functional. -/
def actualW2Model : ℕ → ℝ
  | 0 => 1 / 50
  | n + 1 => (20249 : ℝ) / 1000000 + actualFeedback (actualW2Model n)

theorem benchmarkSeed_nonneg (n : ℕ) : 0 ≤ benchmarkSeed n := by
  induction n with
  | zero =>
      norm_num [benchmarkSeed]
  | succ n ih =>
      change (0 : ℝ) ≤
        (20249 : ℝ) / 1000000 + (13 / 100 : ℝ) * benchmarkSeed n
      exact add_nonneg (by norm_num)
        (mul_nonneg (by norm_num) ih)

/-- A SINGLE coefficient condition on the ACTUAL original seven
integrals propagates to all finite benchmark steps. The fixed
intercept is algebraic here, not an independently proved count credit. -/
theorem actualW2Model_ge_benchmark
    (hLambda : (13 / 100 : ℝ) ≤ lambda) (n : ℕ) :
    benchmarkSeed n ≤ actualW2Model n := by
  have hLambdaNonneg : 0 ≤ lambda :=
    (by norm_num : (0 : ℝ) ≤ 13 / 100).trans hLambda
  induction n with
  | zero =>
      exact le_refl _
  | succ n ih =>
      change (20249 : ℝ) / 1000000 + (13 / 100 : ℝ) * benchmarkSeed n ≤
        (20249 : ℝ) / 1000000 + actualFeedback (actualW2Model n)
      rw [actualFeedback_eq_mul_lambda]
      have hCoeff :
          (13 / 100 : ℝ) * benchmarkSeed n ≤ benchmarkSeed n * lambda := by
        calc
          _ ≤ lambda * benchmarkSeed n :=
            mul_le_mul_of_nonneg_right hLambda (benchmarkSeed_nonneg n)
          _ = _ := mul_comm _ _
      have hStep :
          benchmarkSeed n * lambda ≤ actualW2Model n * lambda :=
        mul_le_mul_of_nonneg_right ih hLambdaNonneg
      exact add_le_add_left (hCoeff.trans hStep)
        ((20249 : ℝ) / 1000000)

/-- Exact rational output after the four manuscript benchmark rounds:
0.020000 -> 0.022849 -> 0.02321937 -> 0.0232675181
-> 0.023273777353. No floating point computation. -/
theorem benchmarkSeed_four_exact :
    benchmarkSeed 4 = (23273777353 : ℝ) / 1000000000000 := by
  norm_num [benchmarkSeed]

theorem benchmarkSeed_four_strictly_above_analytic_seed :
    (2327 : ℝ) / 100000 < benchmarkSeed 4 := by
  rw [benchmarkSeed_four_exact]
  norm_num

/-- The original Q80 truncation is NOT upgraded to the larger
unrounded benchmark. Its exact seed is strictly below the model
if the original W2 coefficient lower bound can actually be proved. -/
theorem originalQ80Seed_lt_actualW2Model_four
    (hLambda : (13 / 100 : ℝ) ≤ lambda) :
    literalSeedHeight < actualW2Model 4 := by
  calc
    literalSeedHeight < (2327 : ℝ) / 100000 :=
      literal_seed_height_below_analytic
    _ < benchmarkSeed 4 :=
      benchmarkSeed_four_strictly_above_analytic_seed
    _ ≤ actualW2Model 4 :=
      actualW2Model_ge_benchmark hLambda 4

/-- Precisely the still-UNPROVED original W2 seven-integral lower
bound, with its singleton and pair domains unaltered. In particular
this implication does not supply the missing analytic F seed licence. -/
theorem seven_actual_W2_integrals_suffice_for_Q80_model
    (hSeven :
      (13 / 100 : ℝ) ≤
        (singletonCoefficient 0 + singletonCoefficient 1 +
          singletonCoefficient 2 +
          P2EnhancedSeedActualSevenLogIdentity.d5Logs +
          P2EnhancedSeedActualSevenLogIdentity.d6Log +
          P2EnhancedSeedActualSevenLogIdentity.d7Log +
          P2EnhancedSeedActualSevenLogIdentity.d8Logs) / 5) :
    literalSeedHeight < actualW2Model 4 := by
  apply originalQ80Seed_lt_actualW2Model_four
  simpa only [P2EnhancedSeedActualSevenLogIdentity.lambda_exact_seven_logs]
    using hSeven

end
end ImbalancedChen.Part5OriginalH430ActualW2FourStepSeedAudit
