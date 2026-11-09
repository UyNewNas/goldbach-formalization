import ImbalancedChen.P4AOriginalFull87RankEightLeafQFibres
import ImbalancedChen.P4AOriginalFull87FirstDisagreementTerminalL1
import ImbalancedChen.P4AOriginalFull87ThreeClassLeafInvoices
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The real RAW and LICENSED rank-eight leaf populations have already been
identified as signed complete-modulus q fibres. The earlier TRUE 87-Cell
producer ledger, however, was still a finite high-q test identity. Here
we probe that SAME ledger at one strictly positive full modulus q and
combine it with the original stopped population. This gives one signed
identity for the ORIGINAL supportedPhysicalRho, without a new rho,
reassigned parent, dropped occurrence or separately assumed Cell gain.

The second theorem specializes the already-proved first-disagreement
stopped and five-frontier-class absolute bill to that SAME complete q.
It is a FINITE pointwise invoice, NOT a bound by H_N and NOT a grant
of the external prime-AP input to any subcoefficient.
-/

namespace ImbalancedChen.P4AOriginalFull87SameQCellLedger
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FullRhoQBridge
  (supportedPhysicalRho rootRankEightRho positiveQProbe qProbe
   physical_positive_probe_eq_supported_rho)
open P4AOriginalFull87StoppedModulusFibres (rootStoppedRho)
open P4AOriginalFull87RankEightLeafQFibres
  (rootRankEightOccurrenceFibre
   real_rank_eight_q_probe_eq_occurrence_fibre
   actual_raw_licensed_full_rho_difference_by_real_occurrences)
open P4AOriginalFull87LicensedOutsideThreeInvoices
  (raw_minus_full_licensed_signed_eq_three_books
   rawOutsideSigned licensedOutsideSigned
   licensedOutsideHighQInvoice)
open P4AOriginalFull87ProducerChangeInvoice (actualCellLedger)
open P4AOriginalFull87RawTrimSignedHighQ (rawOutsideHighQInvoice)
open P4AOriginalFull87ThreeClassLeafInvoices
  (actualProducerThreeClassLeafBill)
open P4AOriginalFull87FirstDisagreementTerminalL1
  (actualFirstDisagreementTerminalL1
   abs_full_physical_difference_le_first_disagreement_terminal_l1)

/-- The real COMPLETE RAW-minus-LICENSED physical coefficient at positive
full q equals the original stopped coefficient difference, plus the RAW
outside source, plus every original 87-Cell signed producer ledger, minus
the LICENSED outside source. Each invoice is PROBED by the same q, not by
two independently estimated sieve coefficients. The genuine rank-eight
continuations and all multiplicities were established by the predecessor. -/
theorem actual_full_rho_q_eq_stops_and_real_signed_cell_books
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) (hd : 0 < d) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d =
    (rootStoppedRho R N cap w z L d -
      rootStoppedRho S N cap w z L d) +
    (rawOutsideSigned delta e q om N cap w z L 0 (qProbe d) +
      (∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L
          0 (qProbe d) c).1) -
      licensedOutsideSigned delta n e q om N cap w z L
        0 (qProbe d)) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  have hfull :=
    actual_raw_licensed_full_rho_difference_by_real_occurrences
      delta n e q om N cap w z L d hd
  have hfront :=
    raw_minus_full_licensed_signed_eq_three_books
      delta n e q om N cap w z L 0 (qProbe d)
  change
    rootRankEightRho R N cap w z L d -
      rootRankEightRho S N cap w z L d =
    rawOutsideSigned delta e q om N cap w z L 0 (qProbe d) +
      (∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L
          0 (qProbe d) c).1) -
      licensedOutsideSigned delta n e q om N cap w z L
        0 (qProbe d) at hfront
  rw [real_rank_eight_q_probe_eq_occurrence_fibre
        R N cap w z L d hd,
      real_rank_eight_q_probe_eq_occurrence_fibre
        S N cap w z L d hd] at hfront
  calc
    _ = (rootStoppedRho R N cap w z L d -
          rootStoppedRho S N cap w z L d) +
        (rootRankEightOccurrenceFibre R N cap w z L d -
          rootRankEightOccurrenceFibre S N cap w z L d) := hfull
    _ = _ := by rw [hfront]

/-- The matching FINITE absolute charge at one physical q: the first
TRUE fifth/sixth/seventh one-sided stopped-terminal invoice plus the
RAW outside, real 87-Cell three-class, and LICENSED outside frontier
invoices, each on precisely the SAME original qProbe. This does NOT
claim that the RHS is o(H_N), or allow a whole-rho AP estimate to be
applied to one individual Cell or to a stopped-only coefficient. -/
theorem actual_full_rho_q_abs_le_once_paid_real_invoices
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) (hd : 0 < d) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    |supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d| ≤
    actualFirstDisagreementTerminalL1 delta n e q om
      N cap w z L 0 (qProbe d) +
    ((rawOutsideHighQInvoice delta e q om
        N cap w z L 0 (qProbe d) +
      actualProducerThreeClassLeafBill delta n e q om
        N cap w z L 0 (qProbe d)) +
      licensedOutsideHighQInvoice delta n e q om
        N cap w z L 0 (qProbe d)) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy
    e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  have hbound :=
    abs_full_physical_difference_le_first_disagreement_terminal_l1
      delta n e q om N cap w z L 0 (qProbe d)
  change
    |P4AOriginalLicensedSixthSignedLedger.physical
        R N cap w z L (positiveQProbe d) -
      P4AOriginalLicensedSixthSignedLedger.physical
        S N cap w z L (positiveQProbe d)| ≤
    actualFirstDisagreementTerminalL1 delta n e q om
      N cap w z L 0 (qProbe d) +
    ((rawOutsideHighQInvoice delta e q om
        N cap w z L 0 (qProbe d) +
      actualProducerThreeClassLeafBill delta n e q om
        N cap w z L 0 (qProbe d)) +
      licensedOutsideHighQInvoice delta n e q om
        N cap w z L 0 (qProbe d)) at hbound
  rw [physical_positive_probe_eq_supported_rho R N cap w z L d hd,
      physical_positive_probe_eq_supported_rho S N cap w z L d hd] at hbound
  exact hbound

end
end ImbalancedChen.P4AOriginalFull87SameQCellLedger
