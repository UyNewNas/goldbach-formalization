import ImbalancedChen.P1HistoricalFifthOriginalByteLiteral
import ImbalancedChen.P1HistoricalFifthOriginalNpyAssociation

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO CREDIT.

The independent original binary is embedded by the file reader, never by
encodeFrame applied to typed rows. Retain the registered source-relative
binary fixture when installing this source. The reader and every decisive finite
proof below are deliberately unexecuted at authoring time.

Original file SHA256 (provenance, not a proved hash theorem):
d6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7.
NPY v1.0;128-byte header; dtype<i8; C order; shape(292633,10).
The full association guard traverses parsed rows sequentially, avoiding
292633 independent drops through the full original byte list.
-/
namespace ImbalancedChen.P1HistoricalFifthOriginalNpyKernel
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload
open P1HistoricalFifthNpyFrame P1HistoricalFifthNpyPositionalSemantics
open P1HistoricalFifthOriginalByteLiteral P1HistoricalFifthOriginalNpyAssociation
open P1HistoricalFifthTypedArchiveShape P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthTypedKeyPartition P1HistoricalFifthTypedBaseGeometry

/-- This term is produced solely from the original binary at user compile
time. Changing the file changes the term and requires every check again. -/
set_option maxHeartbeats 0 in
def originalLiteral : ByteLiteral := include_original_bytes%
  "provenance/original-fifth/cells.npy"

def originalBytes : List Nat := originalLiteral.bytes

theorem original_bytes_bound : ∀ b ∈ originalBytes, b < 256 :=
  originalLiteral.bytes_bound

/-- UNEVALUATED structural guard. This computes only tree lengths. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem original_literal_length : originalLiteral.byteLength = 23410768 := by
  decide

theorem original_bytes_length : originalBytes.length = 23410768 :=
  originalLiteral.bytes_length.trans original_literal_length

/-- UNEVALUATED128-byte guard, including magic/version/header length,
dtype/order/shape and every original padding/newline byte. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem original_header :
    originalBytes.take authenticHeader.length = authenticHeader := by
  decide

theorem original_payload_length :
    (originalBytes.drop authenticHeader.length).length = 80 * rowCount := by
  rw [List.length_drop, original_bytes_length, authenticHeader_length]
  rfl

theorem original_payload_bound :
    ∀ b ∈ originalBytes.drop authenticHeader.length, b < 256 := by
  intro b hb
  have hm : b ∈ originalBytes.take authenticHeader.length ++
      originalBytes.drop authenticHeader.length := List.mem_append.mpr (Or.inr hb)
  rw [List.take_append_drop] at hm
  exact original_bytes_bound b hm

/-- A computable comparison of precisely the ten signed columns. This uses
finite Int equality, avoiding an arbitrary classical equality on lo functions. -/
def SameColumns (parsed typed : FifthWireRow) : Prop :=
  ∀ column : Fin 10, wireColumns parsed column = wireColumns typed column

instance sameColumnsDecidable (parsed typed : FifthWireRow) :
    Decidable (SameColumns parsed typed) :=
  inferInstanceAs (Decidable (∀ column : Fin 10,
    wireColumns parsed column = wireColumns typed column))

theorem sameColumns_eq (parsed typed : FifthWireRow) (h : SameColumns parsed typed) :
    parsed = typed := by
  have hw : wireColumns parsed = wireColumns typed := funext h
  simpa only [wireOfColumns_wireColumns] using congrArg wireOfColumns hw

/-- Sequential comparison retains row order, multiplicity and every opaque
statistic, with exact terminal length on both sides. -/
def OrderedColumns : List FifthWireRow → List FifthWireRow → Prop
  | [], [] => True
  | parsed :: ps, typed :: ts => SameColumns parsed typed ∧ OrderedColumns ps ts
  | _, _ => False

instance orderedColumnsDecidable (parsed typed : List FifthWireRow) :
    Decidable (OrderedColumns parsed typed) := by
  induction parsed generalizing typed with
  | nil =>
      cases typed with
      | nil => exact isTrue trivial
      | cons _ _ => exact isFalse id
  | cons parsed ps ih =>
      cases typed with
      | nil => exact isFalse id
      | cons typed ts =>
          change Decidable (SameColumns parsed typed ∧ OrderedColumns ps ts)
          letI : Decidable (OrderedColumns ps ts) := ih ts
          infer_instance

theorem orderedColumns_eq (parsed typed : List FifthWireRow)
    (h : OrderedColumns parsed typed) : parsed = typed := by
  induction parsed generalizing typed with
  | nil =>
      cases typed with
      | nil => rfl
      | cons _ _ => exact False.elim h
  | cons parsed ps ih =>
      cases typed with
      | nil => exact False.elim h
      | cons typed ts =>
          exact congrArg₂ List.cons (sameColumns_eq parsed typed h.1) (ih ts h.2)

def ParseColumns (parsed : Option (List FifthWireRow)) (typed : List FifthWireRow) : Prop :=
  match parsed with
  | none => False
  | some rows => OrderedColumns rows typed

instance parseColumnsDecidable (parsed : Option (List FifthWireRow))
    (typed : List FifthWireRow) : Decidable (ParseColumns parsed typed) := by
  cases parsed with
  | none => exact isFalse id
  | some rows => exact orderedColumnsDecidable rows typed

theorem parseColumns_eq (parsed : Option (List FifthWireRow)) (typed : List FifthWireRow)
    (h : ParseColumns parsed typed) : parsed = some typed := by
  cases parsed with
  | none => exact False.elim h
  | some rows => exact congrArg some (orderedColumns_eq rows typed h)

/-- THE decisive full historical check, UNEVALUATED. The left side runs the
real fixed-frame/signed64 parser on the independent embedded original bytes;
the right side is the real independent143-block hub, in its original order.
No success/association hypothesis occurs in this closed proof body.

Resource feasibility of this large kernel reduction has NOT been tested.
Neither a passing flag nor formal credit is asserted before user compilation. -/
set_option maxRecDepth 50000000 in
set_option maxHeartbeats 0 in
theorem original_complete_ordered_columns :
    ParseColumns (decodeFrame originalBytes)
      Data.P1HistoricalFifthSavedTableData.rows.toList := by
  decide

/-- Actual full292633-row parse target, supplied as a closed source proof
term. It is not an agreement criterion or an assumed OriginalFieldAssociation. -/
theorem original_complete_parse :
    decodeFrame originalBytes = some Data.P1HistoricalFifthSavedTableData.rows.toList :=
  parseColumns_eq _ _ original_complete_ordered_columns

/-- J's parser/window semantics now consume the closed parse body. -/
theorem original_complete_field_association : OriginalFieldAssociation originalBytes :=
  original_parse_implies_field_association originalBytes original_complete_parse

theorem original_signed64_at_source_position (i : ArchiveIndex) (column : Fin 10) :
    decodeSigned64 (unsignedLE
      ((originalBytes.drop (128 + 80 * i.val + 8 * column.val)).take 8)) =
      wireColumns (archiveRow i) column := by
  rw [← frameFieldBytes_offset]
  exact original_complete_field_association i column

theorem original_exact_eight_bytes (i : ArchiveIndex) (column : Fin 10) :
    encodeWord8 (wireColumns (archiveRow i) column) =
      (originalBytes.drop (128 + 80 * i.val + 8 * column.val)).take 8 := by
  rw [← frameFieldBytes_offset]
  exact original_field_bytes originalBytes original_header original_payload_length
    original_payload_bound original_complete_field_association i column

theorem original_parse_at_every_block (k : Nat) :
    decodeFrame originalBytes = some (prefixRows k ++ suffixRows k) := by
  rw [← rows_split_at_block k]
  exact original_complete_parse

theorem original_mask_processing_slot (i : ArchiveIndex) (slot : Fin 5) :
    slot ∈ maskSlots 5
      (decodeSigned64 (unsignedLE (frameFieldBytes originalBytes i.val 6))).toNat ↔
      Nat.testBit (archiveRow i).mask.toNat slot.val = true :=
  original_mask_slot originalBytes original_complete_field_association i slot

/-- F's existing independent finite proof candidates are reused. Parsing
alone supplies no additional physical/current-parent/history gate. -/
theorem original_parsed_keys_nodup (parsed : List FifthWireRow)
    (h : decodeFrame originalBytes = some parsed) :
    (parsed.map P1FifthGrid400UnitBoxPartition.rowKey).Nodup := by
  have heq := Option.some.inj (h.symm.trans original_complete_parse)
  rw [heq]
  exact actual_typed_keys_nodup

theorem original_parsed_baseGeometry (parsed : List FifthWireRow)
    (h : decodeFrame originalBytes = some parsed) (i : ArchiveIndex) :
    baseGeometry (parsed.getD i.val (archiveRow i)) := by
  have heq := Option.some.inj (h.symm.trans original_complete_parse)
  rw [heq, List.getD_eq_getElem _ _ i.isLt]
  exact archiveRow_baseGeometry i

/-- Exact reconstruction is a consequence of actual original parsing;
it was not used to manufacture the independent input bytes. -/
theorem original_complete_reconstruction :
    encodeFrame Data.P1HistoricalFifthSavedTableData.rows.toList = originalBytes :=
  encodeFrame_of_decodeFrame _ _ original_complete_parse

end
end ImbalancedChen.P1HistoricalFifthOriginalNpyKernel
