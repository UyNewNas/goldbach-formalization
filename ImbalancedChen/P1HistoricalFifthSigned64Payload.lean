import ImbalancedChen.P1HistoricalFifthSigned64Arithmetic

/-!
Pure sequential original signed64 payload codec (no NPY header parser).
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.
Eight little-endian bytes form one signed value; ten values form one wire
row;80-byte rows concatenate in source order. Option parsers reject invalid
byte values and residual lengths. No historical payload is evaluated, no
full292633-row parse witness is supplied, and no data module is imported.
-/

namespace ImbalancedChen.P1HistoricalFifthSigned64Payload
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic

/-- Least-significant byte first, with exactly n output bytes. -/
def encodeNatLE : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, word => word % 256 :: encodeNatLE n (word / 256)

def unsignedLE : List ℕ → ℕ
  | [] => 0
  | byte :: tail => byte + 256 * unsignedLE tail

theorem encodeNatLE_length (n word : ℕ) : (encodeNatLE n word).length = n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih => simp [encodeNatLE, ih]

theorem encodeNatLE_byte_bound (n word : ℕ) : ∀ byte ∈ encodeNatLE n word, byte < 256 := by
  induction n generalizing word with
  | zero => simp [encodeNatLE]
  | succ n ih =>
      intro byte hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Nat.mod_lt _ (by norm_num)
      · exact ih _ byte hb

/-- Radix reconstruction is proved for arbitrary n without inspecting any
source table. The word-range premise excludes discarded high digits. -/
theorem unsignedLE_encodeNatLE (n word : ℕ) (hword : word < 256 ^ n) :
    unsignedLE (encodeNatLE n word) = word := by
  induction n generalizing word with
  | zero =>
      have hw : word = 0 := by norm_num at hword; omega
      simp [encodeNatLE, unsignedLE, hw]
  | succ n ih =>
      have hdiv : word / 256 < 256 ^ n := by
        rw [pow_succ] at hword
        omega
      simp only [encodeNatLE, unsignedLE, ih _ hdiv]
      exact Nat.mod_add_div word 256

theorem unsignedLE_lt (bytes : List ℕ) (hbytes : ∀ b ∈ bytes, b < 256) :
    unsignedLE bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => norm_num [unsignedLE]
  | cons b tail ih =>
      have hb := hbytes b (by simp)
      have ht := ih (fun x hx => hbytes x (List.mem_cons_of_mem _ hx))
      simp only [unsignedLE, List.length_cons, pow_succ]
      omega

/-- This sequential value is the same unsignedLE8 function as the scalar
arithmetic module, with the same byte order. -/
theorem unsignedLE_ofFn8 (bytes : Bytes8) :
    unsignedLE (List.ofFn bytes) = unsigned64LE8 bytes := by
  norm_num [List.ofFn_succ, unsignedLE, unsigned64LE8, Fin.sum_univ_succ] <;> omega

def encodeWord8 (z : ℤ) : List ℕ := encodeNatLE 8 (encodeSigned64 z)

def decodeWord8 (bytes : List ℕ) : Option ℤ :=
  if bytes.length = 8 then
    if ∀ b ∈ bytes, b < 256 then some (decodeSigned64 (unsignedLE bytes)) else none
  else none

theorem encodeWord8_length (z : ℤ) : (encodeWord8 z).length = 8 := encodeNatLE_length _ _

theorem encodeWord8_byte_bound (z : ℤ) : ∀ b ∈ encodeWord8 z, b < 256 := encodeNatLE_byte_bound _ _

theorem decodeWord8_encodeWord8 (z : ℤ)
    (hlo : -(half64 : ℤ) ≤ z) (hhi : z < (half64 : ℤ)) :
    decodeWord8 (encodeWord8 z) = some z := by
  have hword : encodeSigned64 z < 256 ^ 8 := by
    have h := encodeSigned64_lt z
    norm_num [modulus64] at h ⊢
    exact h
  unfold decodeWord8
  rw [if_pos (encodeWord8_length z), if_pos (encodeWord8_byte_bound z)]
  rw [encodeWord8, unsignedLE_encodeNatLE 8 _ hword, decodeSigned64_encodeSigned64 z hlo hhi]

theorem decodeWord8_some_length (bytes : List ℕ) (z : ℤ) (h : decodeWord8 bytes = some z) :
    bytes.length = 8 := by
  unfold decodeWord8 at h
  split_ifs at h with hlen hvalid
  · exact hlen
  · cases h
  · cases h

theorem decodeWord8_some_bytes (bytes : List ℕ) (z : ℤ) (h : decodeWord8 bytes = some z) :
    ∀ b ∈ bytes, b < 256 := by
  unfold decodeWord8 at h
  split_ifs at h with hlen hvalid
  · exact hvalid
  · cases h
  · cases h

theorem decodeWord8_some_range (bytes : List ℕ) (z : ℤ) (h : decodeWord8 bytes = some z) :
    -(half64 : ℤ) ≤ z ∧ z < (half64 : ℤ) := by
  have hlen := decodeWord8_some_length bytes z h
  have hb := decodeWord8_some_bytes bytes z h
  have hw := unsignedLE_lt bytes hb
  have hw64 : unsignedLE bytes < modulus64 := by
    rw [hlen] at hw
    norm_num [modulus64] at hw ⊢
    exact hw
  have heq : decodeSigned64 (unsignedLE bytes) = z := by
    unfold decodeWord8 at h
    rw [if_pos hlen, if_pos hb] at h
    exact Option.some.inj h
  rw [← heq]
  exact decodeSigned64_bounds _ hw64

/-- Fuel counts complete fixed-size chunks. The final branch rejects
unconsumed bytes instead of silently dropping a suffix. -/
def decodeChunks {α : Type*} (size : ℕ) (decode : List ℕ → Option α) :
    ℕ → List ℕ → Option (List α)
  | 0, bytes => if bytes = [] then some [] else none
  | n + 1, bytes =>
      match decode (bytes.take size), decodeChunks size decode n (bytes.drop size) with
      | some value, some tail => some (value :: tail)
      | _, _ => none

def encodeChunks {α : Type*} (encode : α → List ℕ) (values : List α) : List ℕ :=
  values.flatMap encode

theorem encodeChunks_length {α : Type*} (size : ℕ) (encode : α → List ℕ)
    (hsize : ∀ x, (encode x).length = size) (values : List α) :
    (encodeChunks encode values).length = size * values.length := by
  induction values with
  | nil => simp [encodeChunks]
  | cons x tail ih =>
      change (encode x ++ encodeChunks encode tail).length = size * (tail.length + 1)
      rw [List.length_append, hsize, ih, Nat.mul_succ]
      omega

/-- Successful parsing accounts for every input byte and exact output
length. This is generic code soundness, not a concrete table evaluation. -/
theorem decodeChunks_some_lengths {α : Type*} (size : ℕ) (decode : List ℕ → Option α)
    (hsize : ∀ bytes value, decode bytes = some value → bytes.length = size)
    (n : ℕ) (bytes : List ℕ) (values : List α)
    (h : decodeChunks size decode n bytes = some values) :
    values.length = n ∧ bytes.length = size * n := by
  induction n generalizing bytes values with
  | zero =>
      by_cases hb : bytes = []
      · subst bytes
        simp only [decodeChunks, if_pos rfl, Option.some.injEq] at h
        subst values
        simp
      · simp only [decodeChunks, if_neg hb] at h
        cases h
  | succ n ih =>
      simp only [decodeChunks] at h
      cases hd : decode (bytes.take size) with
      | none => simp only [hd] at h; cases h
      | some x =>
          cases ht : decodeChunks size decode n (bytes.drop size) with
          | none => simp only [hd, ht] at h; cases h
          | some tail =>
              simp only [hd, ht, Option.some.injEq] at h
              subst values
              obtain ⟨htlen, hbytes⟩ := ih _ _ ht
              have hhead := hsize _ _ hd
              have htake : (bytes.take size).length = min size bytes.length := List.length_take
              have hdrop : (bytes.drop size).length = bytes.length - size := List.length_drop
              constructor
              · simp [htlen]
              · rw [Nat.mul_succ]
                omega

/-- Every successful chunk parser retains the byte domain of each block. -/
theorem decodeChunks_some_bytes {α : Type*} (size : ℕ) (decode : List ℕ → Option α)
    (hbound : ∀ bytes value, decode bytes = some value → ∀ b ∈ bytes, b < 256)
    (n : ℕ) (bytes : List ℕ) (values : List α)
    (h : decodeChunks size decode n bytes = some values) : ∀ b ∈ bytes, b < 256 := by
  induction n generalizing bytes values with
  | zero =>
      by_cases hb : bytes = []
      · simp [hb]
      · simp only [decodeChunks, if_neg hb] at h
        cases h
  | succ n ih =>
      simp only [decodeChunks] at h
      cases hd : decode (bytes.take size) with
      | none => simp only [hd] at h; cases h
      | some x =>
          cases ht : decodeChunks size decode n (bytes.drop size) with
          | none => simp only [hd, ht] at h; cases h
          | some tail =>
              intro b hb
              have hmem : b ∈ bytes.take size ++ bytes.drop size := by simpa only [List.take_append_drop] using hb
              rcases List.mem_append.mp hmem with hfirst | hlast
              · exact hbound _ _ hd b hfirst
              · exact ih _ _ ht b hlast

/-- Chunk concatenation roundtrip preserves value order exactly. -/
theorem decodeChunks_encodeChunks {α : Type*} (size : ℕ) (decode : List ℕ → Option α)
    (encode : α → List ℕ) (hsize : ∀ x, (encode x).length = size)
    (values : List α) (hinverse : ∀ x ∈ values, decode (encode x) = some x) :
    decodeChunks size decode values.length (encodeChunks encode values) = some values := by
  induction values with
  | nil => simp [encodeChunks, decodeChunks]
  | cons x tail ih =>
      have hx := hinverse x (by simp)
      have ht := ih (fun y hy => hinverse y (List.mem_cons_of_mem _ hy))
      change decodeChunks size decode tail.length (tail.flatMap encode) = some tail at ht
      simp only [encodeChunks, List.flatMap_cons, List.length_cons, decodeChunks]
      rw [List.take_left' (hsize x), List.drop_left' (hsize x), hx, ht]

def encodeFields (values : List ℤ) : List ℕ := encodeChunks encodeWord8 values

def decodeFields (count : ℕ) (bytes : List ℕ) : Option (List ℤ) :=
  decodeChunks 8 decodeWord8 count bytes

def listColumns (values : List ℤ) : SavedColumns := fun c => values.getD c.val 0

theorem listColumns_ofFn (columns : SavedColumns) : listColumns (List.ofFn columns) = columns := by
  funext c
  fin_cases c <;> simp [listColumns, List.ofFn_succ]

def encodeRow (wire : FifthWireRow) : List ℕ := encodeFields (List.ofFn (wireColumns wire))

def decodeRow80 (bytes : List ℕ) : Option FifthWireRow :=
  (decodeFields 10 bytes).map (fun columns => wireOfColumns (listColumns columns))

theorem encodeRow_length (wire : FifthWireRow) : (encodeRow wire).length = 80 := by
  unfold encodeRow encodeFields
  rw [encodeChunks_length 8 encodeWord8 encodeWord8_length]
  simp

theorem decodeRow80_encodeRow (wire : FifthWireRow)
    (hrange : ∀ c, -(half64 : ℤ) ≤ wireColumns wire c ∧ wireColumns wire c < (half64 : ℤ)) :
    decodeRow80 (encodeRow wire) = some wire := by
  have hfields := decodeChunks_encodeChunks 8 decodeWord8 encodeWord8 encodeWord8_length
    (List.ofFn (wireColumns wire)) (by
      intro z hz
      obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hz
      exact decodeWord8_encodeWord8 _ (hrange c).1 (hrange c).2)
  simp only [List.length_ofFn] at hfields
  unfold decodeRow80 encodeRow encodeFields decodeFields
  rw [hfields]
  simp only [Option.map_some, listColumns_ofFn, wireOfColumns_wireColumns]

theorem decodeRow80_some_length (bytes : List ℕ) (wire : FifthWireRow)
    (h : decodeRow80 bytes = some wire) : bytes.length = 80 := by
  unfold decodeRow80 at h
  cases hf : decodeFields 10 bytes with
  | none => simp only [hf, Option.map_none] at h; cases h
  | some fields => exact (decodeChunks_some_lengths 8 decodeWord8 decodeWord8_some_length 10 bytes fields hf).2

theorem decodeRow80_some_bytes (bytes : List ℕ) (wire : FifthWireRow)
    (h : decodeRow80 bytes = some wire) : ∀ b ∈ bytes, b < 256 := by
  unfold decodeRow80 at h
  cases hf : decodeFields 10 bytes with
  | none => simp only [hf, Option.map_none] at h; cases h
  | some fields => exact decodeChunks_some_bytes 8 decodeWord8 decodeWord8_some_bytes 10 bytes fields hf

def encodeRows (rows : List FifthWireRow) : List ℕ := encodeChunks encodeRow rows

def decodeRowsFuel (count : ℕ) (bytes : List ℕ) : Option (List FifthWireRow) :=
  decodeChunks 80 decodeRow80 count bytes

/-- Reject a residual partial80-byte row before chunk parsing. -/
def decodeRows (bytes : List ℕ) : Option (List FifthWireRow) :=
  if bytes.length % 80 = 0 then decodeRowsFuel (bytes.length / 80) bytes else none

theorem encodeRows_length (rows : List FifthWireRow) : (encodeRows rows).length = 80 * rows.length :=
  encodeChunks_length 80 encodeRow encodeRow_length rows

/-- The first80-byte row is parsed before the rest, with exact prefix and
suffix ownership. The generic branch also rejects malformed byte values. -/
theorem decodeRowsFuel_cons_chunk (count : ℕ) (chunk tail : List ℕ) (hchunk : chunk.length = 80) :
    decodeRowsFuel (count + 1) (chunk ++ tail) =
      match decodeRow80 chunk, decodeRowsFuel count tail with
      | some wire, some rest => some (wire :: rest)
      | _, _ => none := by
  unfold decodeRowsFuel
  rw [decodeChunks, List.take_left' hchunk, List.drop_left' hchunk]

theorem decodeRows_encodeRows (rows : List FifthWireRow)
    (hrange : ∀ wire ∈ rows, ∀ c,
      -(half64 : ℤ) ≤ wireColumns wire c ∧ wireColumns wire c < (half64 : ℤ)) :
    decodeRows (encodeRows rows) = some rows := by
  have hround := decodeChunks_encodeChunks 80 decodeRow80 encodeRow encodeRow_length rows
    (fun wire hw => decodeRow80_encodeRow wire (hrange wire hw))
  unfold decodeRows
  rw [encodeRows_length]
  have hmod : (80 * rows.length) % 80 = 0 := by omega
  have hdiv : (80 * rows.length) / 80 = rows.length := by omega
  rw [if_pos hmod, hdiv]
  exact hround

/-- Successful full payload parsing preserves exact row count and rejects
any leftover bytes. No concrete historical payload is evaluated. -/
theorem decodeRows_some_length (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeRows bytes = some rows) : rows.length * 80 = bytes.length := by
  unfold decodeRows at h
  split_ifs at h with hmod
  · have hlengths := decodeChunks_some_lengths 80 decodeRow80 decodeRow80_some_length
      (bytes.length / 80) bytes rows h
    omega
  · cases h

theorem decodeRows_some_bytes (bytes : List ℕ) (rows : List FifthWireRow)
    (h : decodeRows bytes = some rows) : ∀ b ∈ bytes, b < 256 := by
  unfold decodeRows at h
  split_ifs at h with hmod
  · exact decodeChunks_some_bytes 80 decodeRow80 decodeRow80_some_bytes
      (bytes.length / 80) bytes rows h
  · cases h

/-- The encoder itself always emits byte-domain values, independent of
whether the supplied signed integers are in the injective source range. -/
theorem encodeFields_byte_bound (values : List ℤ) : ∀ b ∈ encodeFields values, b < 256 := by
  intro b hb
  obtain ⟨z, _hz, hzb⟩ := List.mem_flatMap.mp hb
  exact encodeWord8_byte_bound z b hzb

theorem encodeRow_byte_bound (wire : FifthWireRow) : ∀ b ∈ encodeRow wire, b < 256 :=
  encodeFields_byte_bound _

theorem encodeRows_byte_bound (rows : List FifthWireRow) : ∀ b ∈ encodeRows rows, b < 256 := by
  intro b hb
  obtain ⟨wire, _hw, hwb⟩ := List.mem_flatMap.mp hb
  exact encodeRow_byte_bound wire b hwb

/-- A nonmultiple-of80 suffix is rejected explicitly. -/
theorem decodeRows_reject_residual (bytes : List ℕ) (h : bytes.length % 80 ≠ 0) :
    decodeRows bytes = none := if_neg h

theorem decodeRow80_reject_length (bytes : List ℕ) (h : bytes.length ≠ 80) :
    decodeRow80 bytes = none := by
  cases hd : decodeRow80 bytes with
  | none => rfl
  | some wire => exact False.elim (h (decodeRow80_some_length bytes wire hd))

/-- Invalid byte-domain values cannot be accepted in any opaque field. -/
theorem decodeRows_reject_invalid_byte (bytes : List ℕ)
    (hbad : ∃ b ∈ bytes, 256 ≤ b) : decodeRows bytes = none := by
  cases hd : decodeRows bytes with
  | none => rfl
  | some rows =>
      obtain ⟨b, hb, hlarge⟩ := hbad
      exact False.elim ((not_lt_of_ge hlarge) (decodeRows_some_bytes bytes rows hd b hb))

end
end ImbalancedChen.P1HistoricalFifthSigned64Payload



