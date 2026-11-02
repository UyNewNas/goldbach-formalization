import ImbalancedChen.P1HistoricalFifthNpyFrame

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO CREDIT.
Positional semantics of the existing signed64 and authentic fixed NPY parser.
No original payload is evaluated and no new literal byte table is introduced.
The recursion proof ties each original byte window to its output position;
this is separate from an immutable original-byte-to-typed-table witness.
-/
namespace ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload
open P1HistoricalFifthSigned64PayloadCompleteness P1HistoricalFifthNpyFrame

/-- Successful chunk parsing associates position i with the actual i-th
input window. It cannot permute two equal-sized rows or fields. -/
theorem decodeChunks_getD {α : Type*} (size : ℕ) (decode : List ℕ → Option α)
    (fallback : α) (n : ℕ) (bytes : List ℕ) (values : List α)
    (h : decodeChunks size decode n bytes = some values) (i : ℕ) (hi : i < n) :
    decode ((bytes.drop (size * i)).take size) = some (values.getD i fallback) := by
  induction n generalizing bytes values i with
  | zero => omega
  | succ n ih =>
      simp only [decodeChunks] at h
      cases hd : decode (bytes.take size) with
      | none => simp only [hd] at h; cases h
      | some value =>
          cases ht : decodeChunks size decode n (bytes.drop size) with
          | none => simp only [hd, ht] at h; cases h
          | some tail =>
              simp only [hd, ht, Option.some.injEq] at h
              subst values
              cases i with
              | zero => simpa only [Nat.mul_zero, List.drop_zero, List.getD_cons_zero] using hd
              | succ i =>
                  have hnext := ih (bytes.drop size) tail ht i (by omega)
                  simpa only [List.drop_drop, Nat.mul_succ, Nat.add_comm,
                    List.getD_cons_succ] using hnext

/-- All ten columns are associated with their own eight-byte windows,
including the opaque vertex-gap/A/B statistics. -/
theorem decodeRow80_column (bytes : List ℕ) (wire : FifthWireRow)
    (h : decodeRow80 bytes = some wire) (column : Fin 10) :
    decodeWord8 ((bytes.drop (8 * column.val)).take 8) = some (wireColumns wire column) := by
  unfold decodeRow80 at h
  cases hf : decodeFields 10 bytes with
  | none => simp only [hf, Option.map_none] at h; cases h
  | some fields =>
      have heq : wireOfColumns (listColumns fields) = wire := by
        simpa only [hf, Option.map_some] using h
      rw [← heq, wireColumns_wireOfColumns]
      exact decodeChunks_getD 8 decodeWord8 0 10 bytes fields hf column.val column.isLt

/-- Position semantics for complete rows; fallback is irrelevant at i<length. -/
theorem decodeRows_row (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeRows bytes = some rows) (fallback : FifthWireRow)
    (i : ℕ) (hi : i < rows.length) :
    decodeRow80 ((bytes.drop (80 * i)).take 80) = some (rows.getD i fallback) := by
  unfold decodeRows at h
  split_ifs at h with hmod
  · have hcounts := (decodeChunks_some_lengths 80 decodeRow80 decodeRow80_some_length
      (bytes.length / 80) bytes rows h).1
    exact decodeChunks_getD 80 decodeRow80 fallback (bytes.length / 80) bytes rows h i (by omega)
  · cases h

/-- The row slice is taken from the actual stripped input, not a fresh
encoding of a typed table. The header is exactly the existing 128-byte frame. -/
def frameRowBytes (bytes : List ℕ) (row : ℕ) : List ℕ :=
  ((bytes.drop authenticHeader.length).drop (80 * row)).take 80

def frameFieldBytes (bytes : List ℕ) (row : ℕ) (column : Fin 10) : List ℕ :=
  ((frameRowBytes bytes row).drop (8 * column.val)).take 8

/-- Full original zero-based address. This is injective across the complete
292633 x 10 x 8 source positions, without a mask-dependent reordering. -/
def fieldByteOffset (row : ℕ) (column : Fin 10) (byte : Fin 8) : ℕ :=
  128 + 80 * row + 8 * column.val + byte.val

theorem fieldByteOffset_injective :
    Function.Injective (fun p : ℕ × Fin 10 × Fin 8 => fieldByteOffset p.1 p.2.1 p.2.2) := by
  intro p q heq
  have hpc := p.2.1.isLt
  have hqc := q.2.1.isLt
  have hpb := p.2.2.isLt
  have hqb := q.2.2.isLt
  have hr : p.1 = q.1 := by unfold fieldByteOffset at heq; omega
  have hc : p.2.1 = q.2.1 := by apply Fin.ext; unfold fieldByteOffset at heq; omega
  have hb : p.2.2 = q.2.2 := by apply Fin.ext; unfold fieldByteOffset at heq; omega
  exact Prod.ext hr (Prod.ext hc hb)

theorem frameRowBytes_offset (bytes : List ℕ) (row : ℕ) :
    frameRowBytes bytes row = (bytes.drop (128 + 80 * row)).take 80 := by
  simp only [frameRowBytes, List.drop_drop, authenticHeader_length, Nat.add_comm]

/-- A field fully inside a row is unaffected by the row's outer cut.
The proof follows list constructors, rather than an NPY evaluation. -/
theorem take_drop_take_inside (bytes : List ℕ) (start count limit : ℕ)
    (h : start + count ≤ limit) :
    ((bytes.take limit).drop start).take count = (bytes.drop start).take count := by
  induction start generalizing bytes limit with
  | zero =>
      have hc : count ≤ limit := by omega
      simp only [List.drop_zero, List.take_take, Nat.min_eq_left hc, Nat.min_eq_right hc]
  | succ start ih =>
      cases bytes with
      | nil => simp
      | cons byte tail =>
          cases limit with
          | zero => omega
          | succ limit =>
              simpa only [List.take_succ_cons, List.drop_succ_cons] using
                ih tail limit (by omega)

/-- The scalar parser window is exactly the original file interval
[128+80*row+8*column, 128+80*row+8*column+8). -/
theorem frameFieldBytes_offset (bytes : List ℕ) (row : ℕ) (column : Fin 10) :
    frameFieldBytes bytes row column =
      (bytes.drop (128 + 80 * row + 8 * column.val)).take 8 := by
  unfold frameFieldBytes frameRowBytes
  rw [take_drop_take_inside _ (8 * column.val) 8 80 (by have hc := column.isLt; omega)]
  simp only [List.drop_drop, authenticHeader_length, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]
/-- Genuine successful-frame row/column semantics, obtained by two separate
recursion inductions through the existing parser. -/
theorem decodeFrame_field (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) (fallback : FifthWireRow)
    (i : ℕ) (hi : i < rows.length) (column : Fin 10) :
    decodeWord8 (frameFieldBytes bytes i column) = some (wireColumns (rows.getD i fallback) column) := by
  obtain ⟨payload, hs, _hlen, hp⟩ := decodeFrame_parts bytes rows h
  have hdrop : bytes.drop authenticHeader.length = payload := by
    rw [(stripHeader_some bytes payload hs).2]
    exact List.drop_left' rfl
  have hrow := decodeRows_row payload rows hp fallback i hi
  have hfield := decodeRow80_column _ _ hrow column
  simpa only [frameFieldBytes, frameRowBytes, hdrop] using hfield

/-- Scalar semantics in the original little-endian two's-complement convention. -/
theorem decodeFrame_field_value (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) (fallback : FifthWireRow)
    (i : ℕ) (hi : i < rows.length) (column : Fin 10) :
    decodeSigned64 (unsignedLE (frameFieldBytes bytes i column)) =
      wireColumns (rows.getD i fallback) column := by
  have hf := decodeFrame_field bytes rows h fallback i hi column
  have hlen := decodeWord8_some_length _ _ hf
  have hb := decodeWord8_some_bytes _ _ hf
  unfold decodeWord8 at hf
  rw [if_pos hlen, if_pos hb] at hf
  exact Option.some.inj hf

/-- The same field witness preserves the exact original eight bytes,
including the negative signed half and high zero bytes. -/
theorem decodeFrame_field_bytes (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeFrame bytes = some rows) (fallback : FifthWireRow)
    (i : ℕ) (hi : i < rows.length) (column : Fin 10) :
    encodeWord8 (wireColumns (rows.getD i fallback) column) = frameFieldBytes bytes i column :=
  encodeWord8_of_decodeWord8 _ _ (decodeFrame_field bytes rows h fallback i hi column)

/-- Structural NPY acceptance follows from the original header, exact payload
length and byte domain. No typed-row identity or gate condition is assumed. -/
theorem decodeFrame_exists_of_structure (bytes : List ℕ)
    (hhead : bytes.take authenticHeader.length = authenticHeader)
    (hlen : (bytes.drop authenticHeader.length).length = 80 * rowCount)
    (hb : ∀ b ∈ bytes.drop authenticHeader.length, b < 256) :
    ∃ rows, decodeFrame bytes = some rows := by
  obtain ⟨rows, hrows⟩ := decodeRows_exists_of_length
    (bytes.drop authenticHeader.length) rowCount hlen hb
  refine ⟨rows, ?_⟩
  simp only [decodeFrame, stripHeader, if_pos hhead, if_pos hlen]
  exact hrows

end
end ImbalancedChen.P1HistoricalFifthNpyPositionalSemantics

