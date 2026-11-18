import ImbalancedChen.P4AOriginalFull87StoppedQ0RoughSixLower
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Exact fixed-exponent specialization of the preceding literal-w rough-six
support theorem, at the UPPER manuscript's rho0 = 19/96.
This proves the real-power comparison rather than inserting an unproved
"w^6 > q0" certificate. The specialization is for the ACTUAL original
receiverTest / sharedRankFour term evaluated with the literal argument
w = (N:Real) ^ (19/96). It does NOT establish that every separate
lower/marked/changed call supplies this argument.

N is fixed before the comparison; there is no asymptotic limit,
rounding, reselected parent, altered Rosser index, or new external input.
-/

namespace ImbalancedChen.P4AOriginalFull87Rho0SixCutoff
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87StoppedQ0RoughSixLower
  (actual_fixed_fifth_q0_zero_of_rough_six_cutoff
   actual_fixed_fifth_centre_eq_lower_of_rough_six_cutoff)
open P4AOriginalFull87StoppedCentreExceptionFibre
  (exceptionalCentreFibre)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedCentreUpperThird
  (lowerThirdCentre)

/-- The frozen UPPER exponent is above the six-factor threshold:
6 * (19/96) = 19/16 > 1.  The inequality is an actual theorem about
real powers, not a field masquerading as the original cutoff. -/
theorem upper_rho0_six_power_gt_N (N : ℕ) (hN : 8 ≤ N) :
    (N : ℝ) < ((N : ℝ) ^ ((19 : ℝ) / 96)) ^ (6 : ℕ) := by
  have hbase : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hexp :
      ((N : ℝ) ^ ((19 : ℝ) / 96)) ^ (6 : ℕ) =
        (N : ℝ) ^ ((19 : ℝ) / 16) := by
    calc
      ((N : ℝ) ^ ((19 : ℝ) / 96)) ^ (6 : ℕ) =
          (N : ℝ) ^ (((19 : ℝ) / 96) * (6 : ℝ)) := by
            rw [Real.rpow_mul hnonneg, Real.rpow_natCast]
      _ = (N : ℝ) ^ ((19 : ℝ) / 16) := by
          congr 1
          norm_num
  rw [hexp]
  exact Real.self_lt_rpow_of_one_lt hbase (by norm_num)

/-- The exact natural division convention for q0 is retained.  It is
strictly below N, hence below the original six-rough-prime cutoff.
No division is performed in Real before converting the natural q0. -/
theorem upper_rho0_q0_lt_six_power (N : ℕ) (hN : 8 ≤ N) :
    (((N - 2) / 2 : ℕ) : ℝ) <
      ((N : ℝ) ^ ((19 : ℝ) / 96)) ^ (6 : ℕ) := by
  have hqNat : (N - 2) / 2 < N := by omega
  have hqReal : (((N - 2) / 2 : ℕ) : ℝ) < (N : ℝ) :=
    by exact_mod_cast hqNat
  exact lt_trans hqReal (upper_rho0_six_power_gt_N N hN)

/-- Genuine original stopped q0 signed fibre with the SAME actual
receiver test, event list, PLUS-beta and sixth occurrence multiplicity,
specialized only to the literal upper w = N^(19/96) argument. -/
theorem actual_upper_rho0_stopped_q0_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (z L : ℝ) (X : ℕ)
    (hN : 8 ≤ N) :
    actualFixedSignedFifthTail delta n e q om N cap
      ((N : ℝ) ^ ((19 : ℝ) / 96)) z L X
      (exceptionalCentreFibre N) = 0 := by
  exact actual_fixed_fifth_q0_zero_of_rough_six_cutoff
    delta n e q om N cap ((N : ℝ) ^ ((19 : ℝ) / 96))
    z L X hN (by positivity) (upper_rho0_q0_lt_six_power N hN)

/-- This is a conditional ORIGINAL stopped-tree invoice transfer.
Only the manuscript-upper power specialization is discharged; the
low-third correction and the independent reserve invoices remain. -/
theorem actual_upper_rho0_stopped_centre_eq_lower
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) (hmod : N % 4 = 0)
    (hN : 8 ≤ N) :
    actualFixedSignedFifthTail delta n e q om N cap
      ((N : ℝ) ^ ((19 : ℝ) / 96)) z L X
      (chenCentrePrimeAPCount N N) =
    actualFixedSignedFifthTail delta n e q om N cap
      ((N : ℝ) ^ ((19 : ℝ) / 96)) z L X
      (lowerThirdCentre N) := by
  exact actual_fixed_fifth_centre_eq_lower_of_rough_six_cutoff
    delta n e q om N cap ((N : ℝ) ^ ((19 : ℝ) / 96))
    z L X hcomp hmod hN (by positivity)
    (upper_rho0_q0_lt_six_power N hN)

end
end ImbalancedChen.P4AOriginalFull87Rho0SixCutoff
