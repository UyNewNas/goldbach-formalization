import ImbalancedChen.P4AOriginalFull87LowQAbsoluteEnvelope
import ImbalancedChen.P4AOriginalFull87SameQCellLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The preceding literal low-q primitive invoice used the whole union of RAW
and LICENSED moduli, with a coarse bound by its cardinality. This packet
instead charges that SAME q <= X complement to the actual first-disagreement
stopped-terminal invoice and the actual three signed producer books.

The pointwise input is the previously constructed common fourth-history
first-disagreement L1 and REAL eighth-frontier Cell ledger. Each modulus
is probed by the original positive full-q qProbe. The common early-stop
histories are subtracted BEFORE taking absolute values. This is an
ALTERNATIVE to the coarse low-q invoice, not an additional cost to be paid
alongside it. It does not establish a small H_N-bound or certify saved87.
-/

namespace ImbalancedChen.P4AOriginalFull87LowQRealLedgerEnvelope
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87FullRhoQBridge
  (supportedPhysicalRho qProbe)
open P4AOriginalFull87PhysicalQAggregateInvoice
  (pairActualPhysicalModuli pairActualHighQModuli)
open P4AOriginalFull87PPCutoffLowQInvoice
  (pairActualLowQModuli actual_raw_licensed_full_q_arithmetic_support)
open P4AOriginalFull87LowQAbsoluteEnvelope
  (actual_raw_licensed_lowq_primitive_le_coefficient_variation
   actual_raw_licensed_highq_primitive_le_full_plus_source_mass)
open P4AOriginalFull87SameQCellLedger
  (actual_full_rho_q_abs_le_once_paid_real_invoices)
open P4AOriginalFull87FirstDisagreementTerminalL1
  (actualFirstDisagreementTerminalL1)
open P4AOriginalFull87RawTrimSignedHighQ
  (rawOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices
  (actualProducerThreeClassLeafBill)
open P4AOriginalFull87LicensedOutsideThreeInvoices
  (licensedOutsideHighQInvoice)

/-- The ACTUAL per-modulus bill obtained by probing the real shared-history
first-disagreement stopped ledger and the three original signed frontier
producer books at the SAME complete physical modulus d. No new policy,
parent, beta coefficient, or numerical witness is introduced here. -/
def actualPerQFirstDisagreementLedgerCharge
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) : ℝ :=
  actualFirstDisagreementTerminalL1 delta n e q om
    N cap w z L 0 (qProbe d) +
  ((rawOutsideHighQInvoice delta e q om N cap w z L 0 (qProbe d) +
    actualProducerThreeClassLeafBill delta n e q om
      N cap w z L 0 (qProbe d)) +
    licensedOutsideHighQInvoice delta n e q om
      N cap w z L 0 (qProbe d))

/-- The original, low-q COMPLETE coefficient variation is charged to its
real one-sided stopped and owned/outside frontier occurrences, rather than
the total cardinality of the two independent policy supports.
This lemma needs ONLY positivity of the real modulus, already established
for both actual physical support lists. -/
private theorem actual_lowq_variation_le_real_first_disagreement_ledger
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let Q := pairActualLowQModuli R S N cap w z X
    (∑ d ∈ Q,
      |supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d|) ≤
    ∑ d ∈ Q,
      actualPerQFirstDisagreementLedgerCharge
        delta n e q om N cap w z L d := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let Q := pairActualLowQModuli R S N cap w z X
  change (∑ d ∈ Q,
    |supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d|) ≤
    ∑ d ∈ Q,
      actualPerQFirstDisagreementLedgerCharge
        delta n e q om N cap w z L d
  apply Finset.sum_le_sum
  intro d hd
  have hfull : d ∈ pairActualPhysicalModuli R S N cap w z :=
    (Finset.mem_filter.mp hd).1
  have hvalid : 0 < d ∧ Squarefree d ∧ d.Coprime N :=
    (actual_raw_licensed_full_q_arithmetic_support
      delta n e q om N cap w z) d hfull
  have hpoint :=
    actual_full_rho_q_abs_le_once_paid_real_invoices
      delta n e q om N cap w z L d hvalid.1
  dsimp only at hpoint
  change |supportedPhysicalRho R N cap w z L d -
    supportedPhysicalRho S N cap w z L d| ≤
    actualPerQFirstDisagreementLedgerCharge
      delta n e q om N cap w z L d at hpoint
  exact hpoint

/-- The genuine low-q primitive discrepancy, with its original signed
full rho and ALL complete modulus factors, is bounded by the REAL
first-disagreement and three signed frontier books. This REFRAINS from
claiming that a whole-rho PP theorem separately applies to each book. -/
theorem actual_lowq_primitive_abs_le_real_first_disagreement_ledger
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let Q := pairActualLowQModuli R S N cap w z X
    let T := ∑ p ∈ chenPrimePrefix (N + D), |W p|
    |∑ d ∈ Q,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| ≤
    (2 * T) * (∑ d ∈ Q,
      actualPerQFirstDisagreementLedgerCharge
        delta n e q om N cap w z L d) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let Q := pairActualLowQModuli R S N cap w z X
  let T : ℝ := ∑ p ∈ chenPrimePrefix (N + D), |W p|
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let E : ℕ → ℝ := fun d =>
    finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let B : ℕ → ℝ := fun d =>
    actualPerQFirstDisagreementLedgerCharge delta n e q om
      N cap w z L d
  have hT : 0 ≤ T :=
    Finset.sum_nonneg (fun p _ => abs_nonneg (W p))
  have hvariation :=
    actual_lowq_variation_le_real_first_disagreement_ledger
      delta n e q om N cap w z L X
  dsimp only at hvariation
  change (∑ d ∈ Q, |A d|) ≤ (∑ d ∈ Q, B d) at hvariation
  have hbase :=
    actual_raw_licensed_lowq_primitive_le_coefficient_variation
      delta n e q om N D cap w z L W X
  dsimp only at hbase
  change |∑ d ∈ Q, A d * E d| ≤
    (2 * T) * (∑ d ∈ Q, |A d|) at hbase
  change |∑ d ∈ Q, A d * E d| ≤
    (2 * T) * (∑ d ∈ Q, B d)
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hvariation
      (mul_nonneg (by norm_num) hT))

/-- Explicit transfer of a FULL original-rho PP error to strict d > X
with a single alternative low-q book of genuine stopped first disagreements,
real Cell owner/trim occurrences, and the two outside populations.
The cost still requires quantitative payment relative to the same H_N. -/
theorem actual_highq_primitive_abs_le_full_plus_real_first_disagreement_ledger
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ) (X : ℕ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let T := ∑ p ∈ chenPrimePrefix (N + D), |W p|
    |∑ d ∈ pairActualHighQModuli R S N cap w z X,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| ≤
    |∑ d ∈ pairActualPhysicalModuli R S N cap w z,
      (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| +
    (2 * T) *
      (∑ d ∈ pairActualLowQModuli R S N cap w z X,
        actualPerQFirstDisagreementLedgerCharge
          delta n e q om N cap w z L d) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let Q := pairActualLowQModuli R S N cap w z X
  let H := pairActualHighQModuli R S N cap w z X
  let M := pairActualPhysicalModuli R S N cap w z
  let T : ℝ := ∑ p ∈ chenPrimePrefix (N + D), |W p|
  let A : ℕ → ℝ := fun d =>
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d
  let E : ℕ → ℝ := fun d =>
    finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let B : ℕ → ℝ := fun d =>
    actualPerQFirstDisagreementLedgerCharge delta n e q om
      N cap w z L d
  have hT : 0 ≤ T :=
    Finset.sum_nonneg (fun p _ => abs_nonneg (W p))
  have hvariation :=
    actual_lowq_variation_le_real_first_disagreement_ledger
      delta n e q om N cap w z L X
  dsimp only at hvariation
  change (∑ d ∈ Q, |A d|) ≤ (∑ d ∈ Q, B d) at hvariation
  have hbase :=
    actual_raw_licensed_highq_primitive_le_full_plus_source_mass
      delta n e q om N D cap w z L W X
  dsimp only at hbase
  change |∑ d ∈ H, A d * E d| ≤
    |∑ d ∈ M, A d * E d| +
      (2 * T) * (∑ d ∈ Q, |A d|) at hbase
  change |∑ d ∈ H, A d * E d| ≤
    |∑ d ∈ M, A d * E d| +
      (2 * T) * (∑ d ∈ Q, B d)
  exact hbase.trans
    (add_le_add_left
      (mul_le_mul_of_nonneg_left hvariation
        (mul_nonneg (by norm_num) hT)) _)

end
end ImbalancedChen.P4AOriginalFull87LowQRealLedgerEnvelope
