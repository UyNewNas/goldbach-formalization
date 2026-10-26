import ImbalancedChen.OriginalFourthRationalScanArithmetic
import ImbalancedChen.P1OriginalCoarseContinuationCells

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The rational scan's value and ORIGINAL first occurrence equal the actual
real producer maximum and least owner after the common -2e loss. Explicit
Boolean licence flags must match the original licensing predicate; this
file never infers or certifies the flags.

For the physical history specialization the existing effectiveExponent3Q
is reused, not reconstructed. Adding back 2e gives the rational seed used
by the unbuffered scan. Exact rational-coordinate identification is an
explicit condition: arbitrary prime logarithms are not declared rational.
No archive evaluation, whole-row pass, or chronological22 claim occurs.
-/

namespace ImbalancedChen.OriginalFourthRationalScanOwner20261026b

noncomputable section
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalCoarseContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthBankAppendMaximum20261026b
open OriginalFourthBankStreamingScan20261026b
open OriginalFourthRationalScanArithmetic20261026b

/-- Full computed state equality, with repeated raw occurrences retained
by the same list length and the same original positional owner. -/
theorem rationalScan_actual_state (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflag : ∀ r, flag r = true ↔ licensed r) (t : RationalPoint) (e : ℝ) :
    castScanState e (rationalScan records seed flag t) =
      ⟨records.length,
        producerProfile4 e (fourthFamily records) licensed ((seed : ℝ) - 2 * e) (castPoint t),
        (owner records e ((seed : ℝ) - 2 * e) licensed (castPoint t)).val⟩ := by
  rw [rationalScan_cast records seed flag licensed hflag t e,
    scan_eq_actual_maximum_and_owner]

theorem rationalScan_value_eq_maximum (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflag : ∀ r, flag r = true ↔ licensed r) (t : RationalPoint) (e : ℝ) :
    ((rationalScan records seed flag t).value : ℝ) - 2 * e =
      producerProfile4 e (fourthFamily records) licensed ((seed : ℝ) - 2 * e) (castPoint t) :=
  congrArg ScanState.value (rationalScan_actual_state records seed flag licensed hflag t e)

theorem rationalScan_first_eq_owner (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflag : ∀ r, flag r = true ↔ licensed r) (t : RationalPoint) (e : ℝ) :
    (rationalScan records seed flag t).first =
      (owner records e ((seed : ℝ) - 2 * e) licensed (castPoint t)).val :=
  congrArg ScanState.first (rationalScan_actual_state records seed flag licensed hflag t e)

/-- The returned occurrence is an actual slot of the full raw bank. The
proof uses the explicit input flags themselves, without asserting that
any particular flag is true. -/
def rationalScannedOwner (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (t : RationalPoint) : BankPosition records :=
  ⟨(rationalScan records seed flag t).first, by
    rw [rationalScan_first_eq_owner records seed flag (fun r => flag r = true)
      (fun _ => Iff.rfl) t 0]
    exact (owner records 0 ((seed : ℝ) - 2 * 0) (fun r => flag r = true) (castPoint t)).isLt⟩

theorem rationalScannedOwner_eq_actual (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflag : ∀ r, flag r = true ↔ licensed r) (t : RationalPoint) (e : ℝ) :
    rationalScannedOwner records seed flag t =
      owner records e ((seed : ℝ) - 2 * e) licensed (castPoint t) := by
  apply Fin.ext
  exact rationalScan_first_eq_owner records seed flag licensed hflag t e

/-- Reuse the already established ORIGINAL third rational exponent. Its
raw/frozen cutoff and selected-cell fallback branches are not altered. -/
private theorem original_unbuffered_seed (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    ((effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) + 2 * e : ℚ) : ℝ) -
        2 * (e : ℝ) = seedExponent (e : ℝ) chi m omega N history := by
  rw [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, cast_effectiveExponent3Q]
  change P1CoarseFirstCubeFallbackMargin.effectiveExponent (e : ℝ) chi m omega N
      (rosserAncestor 3 history) + 2 * (e : ℝ) - 2 * (e : ℝ) =
    P1CoarseFirstCubeFallbackMargin.effectiveExponent (e : ℝ) chi m omega N
      (rosserAncestor 3 history)
  ring

/-- Exact physical-history specialization, with rational-coordinate
identification explicitly supplied rather than inferred for prime logs. -/
theorem rationalScan_original_parent (records : List FourthWireRow) (e : ℚ)
    (chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) (hlen : history.length = 4)
    (t : RationalPoint) (hpoint : primeHistoryLogCoordinates N 4 history = castPoint t)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflag : ∀ r, flag r = true ↔ licensed r) :
    rationalScannedOwner records
        (effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) + 2 * e) flag t =
      owner records (e : ℝ) (seedExponent (e : ℝ) chi m omega N history) licensed
        (primeHistoryLogCoordinates N 4 history) ∧
      N ^ (((rationalScan records
        (effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) + 2 * e) flag t).value : ℝ) -
          2 * (e : ℝ)) =
        producerLevel4 (e : ℝ) chi m omega N (fourthFamily records) licensed history := by
  constructor
  · rw [rationalScannedOwner_eq_actual records _ flag licensed hflag t (e : ℝ),
      original_unbuffered_seed, ← hpoint]
  · rw [rationalScan_value_eq_maximum records _ flag licensed hflag t (e : ℝ),
      original_unbuffered_seed, ← hpoint, producerLevel4_rank_four _ _ _ _ _ _ _ _ hlen]

end
end ImbalancedChen.OriginalFourthRationalScanOwner20261026b
