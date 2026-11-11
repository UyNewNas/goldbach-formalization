import ImbalancedChen.P4AOriginalFull87CentreFrozenHN
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An INTERNAL normalization and invoice payment lemma for the ORIGINAL full87
physical sixth/eighth receiver. The two sharp-prime PP errors remain distinct,
unproved prerequisites. Their quantitative format here is the frozen
manuscript's permitted fixed-A (A=4) O_A(N/log^A N) conclusion, not an
unrestricted signed sieve assertion.

The actual centre-prime budget is paid ONCE using the preceding genuine
C_N/H_N packet, without reintroducing the cancelled modulus-prime correction.
All old/new policies and full-q physical coefficients are inherited unchanged.
-/

namespace ImbalancedChen.P4AOriginalFull87SharpFrozenLog4
noncomputable section

open Real
open scoped Classical BigOperators
open MathlibNt.SieveTheory.SingularSeries
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)
open P4AOriginalFull87EighthPrimeMeanLedger
  (gain primeMass receiverTest densityTest)
open P4AOriginalFull87CentreCoprimeDivisors
  (centreCoprimeDivisorBudget original_full87_receiver_sharp_coprime_invoice)
open P4AOriginalFull87CentreFrozenHN
  (frozenHN frozenHN_pos frozenHN_lower
   original87_centre_budget_div_frozenHN_le)

/-- Internal pointwise payment of ONE fixed-logarithmic-accuracy sharp
discrepancy against the LITERAL frozen H_N. This is algebra and positivity
only; it does not claim that either physical coefficient satisfies PP. -/
private theorem fixed_log_four_cost_div_frozenHN
    (N : ℕ) (hN : 4 ≤ N) (M : ℝ) (hM : 0 ≤ M) :
    (M * (N : ℝ) / Real.log (N : ℝ) ^ 4) / frozenHN N ≤
      M / (liuUniversalProduct * Real.log (N : ℝ) ^ 2) := by
  have hx : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc : 0 < liuUniversalProduct := liuUniversalProduct_pos
  have hsmall : 0 ≤ M * (N : ℝ) / Real.log (N : ℝ) ^ 4 := by
    positivity
  have hlow : 0 <
      liuUniversalProduct * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
    positivity
  calc
    (M * (N : ℝ) / Real.log (N : ℝ) ^ 4) / frozenHN N ≤
        (M * (N : ℝ) / Real.log (N : ℝ) ^ 4) /
        (liuUniversalProduct * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_left hsmall hlow (frozenHN_lower N)
    _ = M / (liuUniversalProduct * Real.log (N : ℝ) ^ 2) := by
      have hnx : (N : ℝ) ≠ 0 := ne_of_gt hx
      have hln : Real.log (N : ℝ) ≠ 0 := ne_of_gt hl
      have hcn : liuUniversalProduct ≠ 0 := ne_of_gt hc
      field_simp
      ring

/-- The actual original87 receiver comparison, on the exact frozen H_N
scale. The hypotheses are TWO separate original signed sixth/eighth
sharp-prime discrepancies with fixed logarithmic accuracy A=4. They are
not proved by this file and cannot be inferred from the absolute leaf
primitive invoice or from coefficient support alone.

The centre correction is the actual coprime-divisor bill already shown
to be o(H_N) by the preceding source-only packet. -/
theorem original_full87_receiver_sharp_log_four_frozen_invoice
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (M6 M8 : ℝ)
    (hN : 4 ≤ N) (hNComposite : ¬Nat.Prime N)
    (hM6 : 0 ≤ M6) (hM8 : 0 ≤ M8)
    (hSixth :
      |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤
          M6 * (N : ℝ) / Real.log (N : ℝ) ^ 4)
    (hEighth :
      |physical (policy (width r) n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤
          M8 * (N : ℝ) / Real.log (N : ℝ) ^ 4) :
    |gain (width r) n e q om N cap w z L (receiverTest N) -
      primeMass N * gain (width r) n e q om N cap w z L densityTest| /
        frozenHN N ≤
      (M6 + M8) /
        (liuUniversalProduct * Real.log (N : ℝ) ^ 2) +
      (8 / (liuUniversalProduct * Real.log (2 : ℝ))) *
        (Real.log (N : ℝ) ^ 3 / Real.sqrt (N : ℝ)) := by
  have hN0 : N ≠ 0 := by omega
  have hH : 0 < frozenHN N := frozenHN_pos N (by omega)
  have hactual :=
    original_full87_receiver_sharp_coprime_invoice
      r n e q om N cap w z L
      (M6 * (N : ℝ) / Real.log (N : ℝ) ^ 4)
      (M8 * (N : ℝ) / Real.log (N : ℝ) ^ 4)
      hNComposite hSixth hEighth
  have hlogpayment :=
    fixed_log_four_cost_div_frozenHN N hN (M6 + M8)
      (add_nonneg hM6 hM8)
  have hcentre :=
    original87_centre_budget_div_frozenHN_le N hN
  calc
    |gain (width r) n e q om N cap w z L (receiverTest N) -
        primeMass N * gain (width r) n e q om N cap w z L densityTest| /
        frozenHN N ≤
      (M6 * (N : ℝ) / Real.log (N : ℝ) ^ 4 +
        M8 * (N : ℝ) / Real.log (N : ℝ) ^ 4 +
        centreCoprimeDivisorBudget N) / frozenHN N := by
          exact div_le_div_of_nonneg_right hactual hH.le
    _ = ((M6 + M8) * (N : ℝ) / Real.log (N : ℝ) ^ 4) /
          frozenHN N +
        centreCoprimeDivisorBudget N / frozenHN N := by ring
    _ ≤ (M6 + M8) /
          (liuUniversalProduct * Real.log (N : ℝ) ^ 2) +
        (8 / (liuUniversalProduct * Real.log (2 : ℝ))) *
          (Real.log (N : ℝ) ^ 3 / Real.sqrt (N : ℝ)) := by
            exact add_le_add hlogpayment hcentre

end
end ImbalancedChen.P4AOriginalFull87SharpFrozenLog4
