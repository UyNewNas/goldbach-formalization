import ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics
import ImbalancedChen.P1HistoricalFifthTypedKeyPartition

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO CREDIT.
The actual original143-block source, not a supplied abstract row family.
This decomposes the missing byte association into exact positional scalar
obligations. It does NOT supply those obligations for cells.npy, declare a
SHA theorem, generate new bulk literals, or execute any finite data guard.
-/
namespace ImbalancedChen.P1HistoricalFifthOriginalNpyAssociation
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload
open P1HistoricalFifthNpyFrame P1HistoricalFifthNpyPositionalSemantics
open P1HistoricalFifthTypedArchiveShape P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthTypedKeyPartition P1HistoricalFifthTypedBaseGeometry

/-- The remaining scalar association is about the actual original bytes
and the actual full archive index. Each window includes its original mask
or opaque statistic; no hash or self-generated encoding enters this predicate. -/
def OriginalFieldAssociation (bytes : List ℕ) : Prop :=
  ∀ i : ArchiveIndex, ∀ column : Fin 10,
    decodeSigned64 (unsignedLE (frameFieldBytes bytes i.val column)) =
      wireColumns (archiveRow i) column

/-- Necessary positional witness from a successful actual-table parse. -/
theorem original_parse_implies_field_association (bytes : List ℕ)
    (h : decodeFrame bytes = some Data.P1HistoricalFifthSavedTableData.rows.toList) :
    OriginalFieldAssociation bytes := by
  intro i column
  have hf := decodeFrame_field_value bytes Data.P1HistoricalFifthSavedTableData.rows.toList
    h (archiveRow i) i.val i.isLt column
  simpa only [List.getD_eq_getElem _ _ i.isLt, archiveRow] using hf

/-- Sufficient positional witness: structural byte validity gives a parse;
all scalar positions then identify its complete ten-column rows with the
independent original table. No typed signed-range or finite guard is needed. -/
theorem original_parse_of_field_association (bytes : List ℕ)
    (hhead : bytes.take authenticHeader.length = authenticHeader)
    (hlen : (bytes.drop authenticHeader.length).length = 80 * rowCount)
    (hb : ∀ b ∈ bytes.drop authenticHeader.length, b < 256)
    (hfields : OriginalFieldAssociation bytes) :
    decodeFrame bytes = some Data.P1HistoricalFifthSavedTableData.rows.toList := by
  obtain ⟨parsed, hparsed⟩ := decodeFrame_exists_of_structure bytes hhead hlen hb
  have hparsedLength := decodeFrame_some_row_count bytes parsed hparsed
  have hsameLength : parsed.length = Data.P1HistoricalFifthSavedTableData.rows.toList.length := by
    rw [hparsedLength, rows_toList_length]
    rfl
  have heq : parsed = Data.P1HistoricalFifthSavedTableData.rows.toList := by
    apply List.ext_getElem hsameLength
    intro k hkp hkt
    let i : ArchiveIndex := ⟨k, hkt⟩
    have hcolumns : wireColumns (parsed[k]) =
        wireColumns (Data.P1HistoricalFifthSavedTableData.rows.toList[k]) := by
      funext column
      have hp := decodeFrame_field_value bytes parsed hparsed (archiveRow i) k hkp column
      have ht := hfields i column
      rw [List.getD_eq_getElem _ _ hkp] at hp
      exact hp.symm.trans ht
    have hwire := congrArg wireOfColumns hcolumns
    simpa only [wireOfColumns_wireColumns] using hwire
  rw [← heq]
  exact hparsed

/-- Exact full143-block criterion. The right side is an explicit unresolved
immutable-byte witness, not a declaration that the historical file passes. -/
theorem original_parse_iff_field_association (bytes : List ℕ)
    (hhead : bytes.take authenticHeader.length = authenticHeader)
    (hlen : (bytes.drop authenticHeader.length).length = 80 * rowCount)
    (hb : ∀ b ∈ bytes.drop authenticHeader.length, b < 256) :
    decodeFrame bytes = some Data.P1HistoricalFifthSavedTableData.rows.toList ↔
      OriginalFieldAssociation bytes := by
  constructor
  · exact original_parse_implies_field_association bytes
  · exact original_parse_of_field_association bytes hhead hlen hb

/-- Exact source order may equivalently be exposed at ANY original block
boundary, by reusing the existing hub's concatenation proof. -/
theorem original_parse_split_at_block (bytes : List ℕ)
    (hhead : bytes.take authenticHeader.length = authenticHeader)
    (hlen : (bytes.drop authenticHeader.length).length = 80 * rowCount)
    (hb : ∀ b ∈ bytes.drop authenticHeader.length, b < 256)
    (hfields : OriginalFieldAssociation bytes) (k : ℕ) :
    decodeFrame bytes = some (prefixRows k ++ suffixRows k) := by
  rw [← rows_split_at_block k]
  exact original_parse_of_field_association bytes hhead hlen hb hfields

/-- Every source-associated field keeps its original bits, not only its
signed integer interpretation. This applies uniformly to all ten fields. -/
theorem original_field_bytes (bytes : List ℕ)
    (hhead : bytes.take authenticHeader.length = authenticHeader)
    (hlen : (bytes.drop authenticHeader.length).length = 80 * rowCount)
    (hb : ∀ b ∈ bytes.drop authenticHeader.length, b < 256)
    (hfields : OriginalFieldAssociation bytes) (i : ArchiveIndex) (column : Fin 10) :
    encodeWord8 (wireColumns (archiveRow i) column) = frameFieldBytes bytes i.val column := by
  have hp := original_parse_of_field_association bytes hhead hlen hb hfields
  have hf := decodeFrame_field_bytes bytes Data.P1HistoricalFifthSavedTableData.rows.toList hp
    (archiveRow i) i.val i.isLt column
  simpa only [List.getD_eq_getElem _ _ i.isLt, archiveRow] using hf

/-- The mask's bit i is still the original zero-based processing slot i.
The scalar field predicate does not reinterpret masks as geometry or licences. -/
theorem original_mask_slot (bytes : List ℕ) (hfields : OriginalFieldAssociation bytes)
    (i : ArchiveIndex) (slot : Fin 5) :
    slot ∈ maskSlots 5
        (decodeSigned64 (unsignedLE (frameFieldBytes bytes i.val 6))).toNat ↔
      Nat.testBit (archiveRow i).mask.toNat slot.val = true := by
  rw [hfields i 6]
  exact mem_maskSlots slot

/-- Reuse F's full-table key result after the genuine source association.
No second finite uniqueness decision is introduced here. -/
theorem associated_parse_keys_nodup (bytes : List ℕ) (parsed : List FifthWireRow)
    (hhead : bytes.take authenticHeader.length = authenticHeader)
    (hlen : (bytes.drop authenticHeader.length).length = 80 * rowCount)
    (hb : ∀ b ∈ bytes.drop authenticHeader.length, b < 256)
    (hfields : OriginalFieldAssociation bytes) (hparsed : decodeFrame bytes = some parsed) :
    (parsed.map P1FifthGrid400UnitBoxPartition.rowKey).Nodup := by
  have hp := original_parse_of_field_association bytes hhead hlen hb hfields
  have heq : parsed = Data.P1HistoricalFifthSavedTableData.rows.toList :=
    Option.some.inj (hparsed.symm.trans hp)
  rw [heq]
  exact actual_typed_keys_nodup

/-- F's actual baseGeometry is transported to the SAME parsed source
position. It supplies no current-parent/history/physical gate licence. -/
theorem associated_parse_baseGeometry (bytes : List ℕ) (parsed : List FifthWireRow)
    (hhead : bytes.take authenticHeader.length = authenticHeader)
    (hlen : (bytes.drop authenticHeader.length).length = 80 * rowCount)
    (hb : ∀ b ∈ bytes.drop authenticHeader.length, b < 256)
    (hfields : OriginalFieldAssociation bytes) (hparsed : decodeFrame bytes = some parsed)
    (i : ArchiveIndex) : baseGeometry (parsed.getD i.val (archiveRow i)) := by
  have hp := original_parse_of_field_association bytes hhead hlen hb hfields
  have heq : parsed = Data.P1HistoricalFifthSavedTableData.rows.toList :=
    Option.some.inj (hparsed.symm.trans hp)
  rw [heq, List.getD_eq_getElem _ _ i.isLt]
  exact archiveRow_baseGeometry i

end
end ImbalancedChen.P1HistoricalFifthOriginalNpyAssociation

