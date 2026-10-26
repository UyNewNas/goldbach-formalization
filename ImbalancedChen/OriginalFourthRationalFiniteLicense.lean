import ImbalancedChen.OriginalFourthRationalScanOwner

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite licence interface for the rational original fourth-bank scan.
Flags need match the original licence predicate ONLY on the literal input
records. No global Boolean decision procedure for all possible original
rows is assumed. The returned positive position has an actual input-row
witness, its explicit flag, original licence and original closed-box test.
All duplicate occurrences and the inherited seed slot remain unchanged.

No flag, row licence, archive pass or chronological22 policy is inferred.
-/

namespace ImbalancedChen.OriginalFourthRationalFiniteLicense20261026b

noncomputable section
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthBankStreamingScan20261026b
open OriginalFourthRationalScanArithmetic20261026b
open OriginalFourthRationalScanOwner20261026b

/-- The ACTUAL real scan never queries a licence outside its raw bank.
This is proved from its fold transitions, not a final owner hypothesis. -/
theorem scan_licenses_congr_on_records (records : List FourthWireRow) (e seed : ℝ)
    (licensed₁ licensed₂ : ProducerRow → Prop) (t : Point)
    (hflags : ∀ raw ∈ records, licensed₁ raw.toProducerRow ↔ licensed₂ raw.toProducerRow) :
    scan records e seed licensed₁ t = scan records e seed licensed₂ t := by
  revert hflags
  induction records using List.reverseRecOn with
  | nil => intro _hflags; rfl
  | append_singleton front raw ih =>
      intro hflags
      have hf : ∀ wire ∈ front, licensed₁ wire.toProducerRow ↔ licensed₂ wire.toProducerRow := by
        intro wire hw
        exact hflags wire (by simp only [List.mem_append]; exact Or.inl hw)
      have hr : licensed₁ raw.toProducerRow ↔ licensed₂ raw.toProducerRow := hflags raw (by simp)
      rw [scan_append_one, scan_append_one, ih hf]
      unfold scanStep producerEligible
      rw [hr]

/-- Finite per-record flag witnesses suffice for the complete exact
rational-to-real maximum/position correspondence. Unused rows are free. -/
theorem rationalScan_actual_state_of_record_flags (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflags : ∀ raw ∈ records, flag raw.toProducerRow = true ↔ licensed raw.toProducerRow)
    (t : RationalPoint) (e : ℝ) :
    castScanState e (rationalScan records seed flag t) =
      ⟨records.length,
        producerProfile4 e (fourthFamily records) licensed ((seed : ℝ) - 2 * e) (castPoint t),
        (owner records e ((seed : ℝ) - 2 * e) licensed (castPoint t)).val⟩ := by
  calc
    castScanState e (rationalScan records seed flag t) =
        scan records e ((seed : ℝ) - 2 * e) (fun r => flag r = true) (castPoint t) :=
      rationalScan_cast records seed flag (fun r => flag r = true) (fun _ => Iff.rfl) t e
    _ = scan records e ((seed : ℝ) - 2 * e) licensed (castPoint t) :=
      scan_licenses_congr_on_records records e _ _ licensed _ hflags
    _ = _ := scan_eq_actual_maximum_and_owner records e _ licensed _

theorem rationalScan_value_of_record_flags (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflags : ∀ raw ∈ records, flag raw.toProducerRow = true ↔ licensed raw.toProducerRow)
    (t : RationalPoint) (e : ℝ) :
    ((rationalScan records seed flag t).value : ℝ) - 2 * e =
      producerProfile4 e (fourthFamily records) licensed ((seed : ℝ) - 2 * e) (castPoint t) :=
  congrArg ScanState.value
    (rationalScan_actual_state_of_record_flags records seed flag licensed hflags t e)

theorem rationalScan_first_of_record_flags (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflags : ∀ raw ∈ records, flag raw.toProducerRow = true ↔ licensed raw.toProducerRow)
    (t : RationalPoint) (e : ℝ) :
    (rationalScan records seed flag t).first =
      (owner records e ((seed : ℝ) - 2 * e) licensed (castPoint t)).val :=
  congrArg ScanState.first
    (rationalScan_actual_state_of_record_flags records seed flag licensed hflags t e)

theorem rationalScannedOwner_of_record_flags (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflags : ∀ raw ∈ records, flag raw.toProducerRow = true ↔ licensed raw.toProducerRow)
    (t : RationalPoint) (e : ℝ) :
    rationalScannedOwner records seed flag t =
      owner records e ((seed : ℝ) - 2 * e) licensed (castPoint t) := by
  apply Fin.ext
  exact rationalScan_first_of_record_flags records seed flag licensed hflags t e

/-- A positive computed slot cannot be an unattached winner statistic:
it supplies its actual ordered raw occurrence, flag, licence, containment
and exact buffered value. No duplicate is collapsed in this witness. -/
theorem rational_winner_actual_record (records : List FourthWireRow) (seed : ℚ)
    (flag : ProducerRow → Bool) (licensed : ProducerRow → Prop)
    (hflags : ∀ raw ∈ records, flag raw.toProducerRow = true ↔ licensed raw.toProducerRow)
    (t : RationalPoint) (e : ℝ) (hpos : 0 < (rationalScan records seed flag t).first) :
    ∃ i : Fin records.length,
      (rationalScan records seed flag t).first = i.val + 1 ∧
      flag (rowAt records i) = true ∧ licensed (rowAt records i) ∧
      castPoint t ∈ (rowAt records i).box ∧
      ((rationalScan records seed flag t).value : ℝ) - 2 * e =
        (rowAt records i).bufferedCandidate e (castPoint t) := by
  have hlt : (rationalScan records seed flag t).first < records.length + 1 :=
    (rationalScannedOwner records seed flag t).isLt
  let i : Fin records.length := ⟨(rationalScan records seed flag t).first - 1, by omega⟩
  have hi : (rationalScan records seed flag t).first = i.val + 1 := by dsimp [i]; omega
  have ho : owner records e ((seed : ℝ) - 2 * e) licensed (castPoint t) = i.succ := by
    apply Fin.ext
    rw [← rationalScan_first_of_record_flags records seed flag licensed hflags t e]
    exact hi
  have hr := owned_row_is_actual_source records e ((seed : ℝ) - 2 * e) licensed (castPoint t) i ho
  have hflag : flag (rowAt records i) = true :=
    (hflags (records.get i) (List.get_mem _ _)).mpr hr.2.1
  refine ⟨i, hi, hflag, hr.2.1, hr.2.2.1, ?_⟩
  exact (rationalScan_value_of_record_flags records seed flag licensed hflags t e).trans hr.2.2.2

end
end ImbalancedChen.OriginalFourthRationalFiniteLicense20261026b
