import ImbalancedChen.P1HistoricalFifthSigned64PayloadCompleteness

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO CREDIT.

Fixed authentic cells.npy frame validator, not a general Python-dictionary
or NPY parser. Only the exact first128 archived bytes and saved header
metadata were read. No payload was traversed or parsed for this source.
NPY v1.0 magic, little-endian signed64 '<i8', C order False, shape(292633,10),
and all padding/newline bytes are checked by exact prefix equality.
The v1 little-endian header-text length is118, hence the data offset128.
Archived cells.npy SHA d6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7.
First128 SHA 12288c541a12287f21818f0218e51ce9d708cba7bad3a3e42f92de493bddf422.
There is NO concrete full292633-row success or geometry/checker witness.
-/

namespace ImbalancedChen.P1HistoricalFifthNpyFrame
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload
open P1HistoricalFifthSigned64PayloadCompleteness

def rowCount : ℕ := 292633
def columnCount : ℕ := 10

def authenticHeader : List ℕ :=
  [147, 78, 85, 77, 80, 89, 1, 0, 118, 0, 123, 39, 100, 101, 115, 99,
   114, 39, 58, 32, 39, 60, 105, 56, 39, 44, 32, 39, 102, 111, 114, 116,
   114, 97, 110, 95, 111, 114, 100, 101, 114, 39, 58, 32, 70, 97, 108,
   115, 101, 44, 32, 39, 115, 104, 97, 112, 101, 39, 58, 32, 40, 50, 57,
   50, 54, 51, 51, 44, 32, 49, 48, 41, 44, 32, 125, 32, 32, 32, 32, 32,
   32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
   32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
   32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 10]

theorem authenticHeader_length : authenticHeader.length = 128 := rfl

theorem authenticHeader_magic_version_length :
    authenticHeader.take 10 = [147, 78, 85, 77, 80, 89, 1, 0, 118, 0] := rfl

def decimalValue (digits : List ℕ) : ℕ :=
  digits.foldl (fun n byte => 10 * n + (byte - 48)) 0

theorem authenticHeader_dtype_little_endian_signed64 :
    (authenticHeader.drop 20).take 5 = [39, 60, 105, 56, 39] := rfl

theorem authenticHeader_C_order_false :
    (authenticHeader.drop 44).take 5 = [70, 97, 108, 115, 101] := rfl

theorem authenticHeader_shape_rows :
    decimalValue ((authenticHeader.drop 61).take 6) = rowCount := rfl

theorem authenticHeader_shape_columns :
    decimalValue ((authenticHeader.drop 69).take 2) = columnCount := rfl

theorem authenticHeader_v1_text_length :
    authenticHeader.getD 8 0 + 256 * authenticHeader.getD 9 0 = 118 := rfl

theorem authenticHeader_payload_offset :
    10 + (authenticHeader.getD 8 0 + 256 * authenticHeader.getD 9 0) =
      authenticHeader.length := rfl

def headerCheck (bytes : List ℕ) : Bool :=
  decide (bytes.take authenticHeader.length = authenticHeader)

def stripHeader (bytes : List ℕ) : Option (List ℕ) :=
  if bytes.take authenticHeader.length = authenticHeader
    then some (bytes.drop authenticHeader.length) else none

def decodeFrame (bytes : List ℕ) : Option (List FifthWireRow) :=
  match stripHeader bytes with
  | none => none
  | some payload => if payload.length = 80 * rowCount then decodeRows payload else none

def encodeFrame (rows : List FifthWireRow) : List ℕ :=
  authenticHeader ++ encodeRows rows

theorem headerCheck_iff (bytes : List ℕ) :
    headerCheck bytes = true ↔ bytes.take authenticHeader.length = authenticHeader := by
  simp [headerCheck]

theorem stripHeader_append (payload : List ℕ) :
    stripHeader (authenticHeader ++ payload) = some payload := by
  unfold stripHeader
  rw [List.take_left' (rfl : authenticHeader.length = authenticHeader.length), if_pos rfl,
    List.drop_left' (rfl : authenticHeader.length = authenticHeader.length)]

theorem stripHeader_some (bytes payload : List ℕ)
    (h : stripHeader bytes = some payload) :
    bytes.take authenticHeader.length = authenticHeader ∧
      bytes = authenticHeader ++ payload := by
  unfold stripHeader at h
  split_ifs at h with hhead
  · have hdrop := Option.some.inj h
    refine ⟨hhead, ?_⟩
    have hparts := List.take_append_drop authenticHeader.length bytes
    rw [hhead, hdrop] at hparts
    exact hparts.symm
  · cases h

theorem decodeFrame_parts (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) :
    ∃ payload, stripHeader bytes = some payload ∧ payload.length = 80 * rowCount ∧
      decodeRows payload = some rows := by
  unfold decodeFrame at h
  cases hs : stripHeader bytes with
  | none => simp only [hs] at h; cases h
  | some payload =>
      simp only [hs] at h
      split_ifs at h with hlen
      · exact ⟨payload, hs, hlen, h⟩
      · cases h

theorem decodeFrame_some_header (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) : headerCheck bytes = true := by
  obtain ⟨payload, hs, _hlen, _hp⟩ := decodeFrame_parts bytes rows h
  exact (headerCheck_iff bytes).mpr (stripHeader_some bytes payload hs).1

/-- The header's literal shape is enforced by the payload count, rather
than silently accepting arbitrary output length. -/
theorem decodeFrame_some_row_count (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) : rows.length = rowCount := by
  obtain ⟨payload, _hs, hlen, hp⟩ := decodeFrame_parts bytes rows h
  have hrows := decodeRows_some_length payload rows hp
  omega

theorem decodeFrame_some_file_length (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) : bytes.length = 128 + 80 * rowCount := by
  obtain ⟨payload, hs, hlen, _hp⟩ := decodeFrame_parts bytes rows h
  rw [(stripHeader_some bytes payload hs).2, List.length_append, authenticHeader_length, hlen]

/-- Both row order and every signed field are retained: encoding the
output reconstructs the identical full frame, including opaque gap/A/B.
No particular archived payload is evaluated to establish this theorem. -/
theorem encodeFrame_of_decodeFrame (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) : encodeFrame rows = bytes := by
  obtain ⟨payload, hs, _hlen, hp⟩ := decodeFrame_parts bytes rows h
  rw [encodeFrame, encodeRows_of_decodeRows payload rows hp]
  exact (stripHeader_some bytes payload hs).2.symm

theorem decodeFrame_some_signed_fields (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) :
    ∀ wire ∈ rows, ∀ column : Fin 10,
      -(half64 : ℤ) ≤ wireColumns wire column ∧ wireColumns wire column < (half64 : ℤ) := by
  obtain ⟨payload, _hs, _hlen, hp⟩ := decodeFrame_parts bytes rows h
  exact decodeRows_some_signed_range payload rows hp

/-- The converse holds for any in-range typed table with the authentic
shape. The concrete historical table's success is not supplied as a fact. -/
theorem decodeFrame_encodeFrame (rows : List FifthWireRow)
    (hlen : rows.length = rowCount)
    (hrange : ∀ wire ∈ rows, ∀ column : Fin 10,
      -(half64 : ℤ) ≤ wireColumns wire column ∧ wireColumns wire column < (half64 : ℤ)) :
    decodeFrame (encodeFrame rows) = some rows := by
  unfold decodeFrame encodeFrame
  rw [stripHeader_append]
  have hp : (encodeRows rows).length = 80 * rowCount := by
    rw [encodeRows_length, hlen]
  rw [if_pos hp]
  exact decodeRows_encodeRows rows hrange

theorem decodeFrame_rejects_header (bytes : List ℕ)
    (hbad : bytes.take authenticHeader.length ≠ authenticHeader) :
    decodeFrame bytes = none := by
  simp only [decodeFrame, stripHeader, if_neg hbad]

end
end ImbalancedChen.P1HistoricalFifthNpyFrame
