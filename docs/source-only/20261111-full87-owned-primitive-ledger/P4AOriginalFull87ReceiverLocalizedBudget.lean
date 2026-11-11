import ImbalancedChen.P4AOriginalFull87OwnedPrimitiveLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Replace ONLY the primitive discrepancy component of the existing exact
receiver-density-error ledger with the genuine changed-source full-modulus
primitive leaf bill. Modulus-prime and centre-prime terms remain separate,
with their original signs and full physical coefficients.

No relative size comparison with the older global absolutePhysical budget
is asserted: different cancellations can change numerical magnitudes.
The localization is by support/occurrence, not an H_N reserve payment.
-/
namespace ImbalancedChen.P4AOriginalFull87ReceiverLocalizedBudget
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OwnedPrimitiveLedger
  (ownedPrimitiveBudget full87_primitive_owned_budget)
open P4AOriginalFull87EighthPrimeMeanLedger
  (gain receiverTest densityTest primeMass primitiveError modulusPrimeTerm
   receiver_gain_decomposition absoluteGainBudget abs_gain_le)

private theorem abs_sub_basic (a b : ℝ) :
    |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add a (-b)

/-- The original actual receiver count, with the original literal
physical sixth/eighth rho, is bounded by a primitive PP invoice localized
to the ORIGINAL 87 owner/trim states, plus the TWO distinct exceptional
prime invoices. No input is marked paid. -/
theorem full87_receiver_density_with_owned_primitive
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain (width r) n e q om N cap w z L (receiverTest N) -
      primeMass N * gain (width r) n e q om N cap w z L densityTest| ≤
      (∑ c : Cell, ownedPrimitiveBudget r n e q om N cap w z L c) +
      absoluteGainBudget (width r) n e q om N cap w z L
        (modulusPrimeTerm N) +
      absoluteGainBudget (width r) n e q om N cap w z L
        (chenCentrePrimeAPCount N N) := by
  have hdecompose :
      gain (width r) n e q om N cap w z L (receiverTest N) -
        primeMass N * gain (width r) n e q om N cap w z L densityTest =
      (gain (width r) n e q om N cap w z L (primitiveError N) -
        gain (width r) n e q om N cap w z L (modulusPrimeTerm N)) -
        gain (width r) n e q om N cap w z L
          (chenCentrePrimeAPCount N N) := by
    rw [receiver_gain_decomposition]
    ring
  rw [hdecompose]
  have hprimitive := full87_primitive_owned_budget r n e q om N cap w z L
  have hmodulus := abs_gain_le (width r) n e q om N cap w z L
    (modulusPrimeTerm N)
  have hcentre := abs_gain_le (width r) n e q om N cap w z L
    (chenCentrePrimeAPCount N N)
  calc
    |(gain (width r) n e q om N cap w z L (primitiveError N) -
        gain (width r) n e q om N cap w z L (modulusPrimeTerm N)) -
        gain (width r) n e q om N cap w z L
          (chenCentrePrimeAPCount N N)| ≤
      |gain (width r) n e q om N cap w z L (primitiveError N) -
        gain (width r) n e q om N cap w z L (modulusPrimeTerm N)| +
      |gain (width r) n e q om N cap w z L
        (chenCentrePrimeAPCount N N)| :=
        abs_sub_basic _ _
    _ ≤
      (|gain (width r) n e q om N cap w z L (primitiveError N)| +
        |gain (width r) n e q om N cap w z L (modulusPrimeTerm N)|) +
      |gain (width r) n e q om N cap w z L
        (chenCentrePrimeAPCount N N)| :=
        add_le_add_right (abs_sub_basic _ _) _
    _ ≤
      ((∑ c : Cell, ownedPrimitiveBudget r n e q om N cap w z L c) +
        absoluteGainBudget (width r) n e q om N cap w z L
          (modulusPrimeTerm N)) +
      absoluteGainBudget (width r) n e q om N cap w z L
        (chenCentrePrimeAPCount N N) :=
        add_le_add (add_le_add hprimitive hmodulus) hcentre
    _ = _ := by ring

end
end ImbalancedChen.P4AOriginalFull87ReceiverLocalizedBudget
