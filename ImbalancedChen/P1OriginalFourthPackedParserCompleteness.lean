import ImbalancedChen.P1OriginalFourthPackedArithmeticSoundness

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_ACCEPTANCE_CREDIT.

Completeness and the converse lossless round trip for the unmodified
seventeen-byte parser on arbitrary lists. Byte range is a primitive wire
domain condition. No actual historical table is parsed, checked or asserted
to have a certificate here. No geometry or all-table hypothesis occurs.
-/

namespace ImbalancedChen.P1OriginalFourthPackedParserCompleteness
open P1OriginalFourthPackedTable
open P1OriginalFourthPackedArithmeticSoundness

def ValidBytes (bytes : List ℕ) : Prop := ∀ b ∈ bytes, b < 256

private theorem prefix17 (bytes : List ℕ) (hlen : 17 ≤ bytes.length) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : ℕ,
      ∃ rest : List ℕ, bytes = b0::b1::b2::b3::b4::b5::b6::b7::b8::b9::b10::b11::b12::b13::b14::b15::b16::rest := by
  rcases bytes with _ | ⟨b0, bytes⟩
  · simp only [List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b1, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b2, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b3, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b4, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b5, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b6, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b7, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b8, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b9, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b10, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b11, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b12, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b13, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b14, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b15, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  rcases bytes with _ | ⟨b16, bytes⟩
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  exact ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,bytes,rfl⟩

private theorem decodeWireRows_short (bytes : List ℕ) (hne : bytes ≠ [])
    (hlen : bytes.length < 17) : decodeWireRows bytes = none := by
  rcases bytes with _ | ⟨b0, bytes⟩
  · exact False.elim (hne rfl)
  rcases bytes with _ | ⟨b1, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b2, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b3, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b4, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b5, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b6, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b7, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b8, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b9, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b10, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b11, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b12, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b13, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b14, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b15, bytes⟩
  · rfl
  rcases bytes with _ | ⟨b16, bytes⟩
  · rfl
  simp only [List.length_cons] at hlen
  omega

theorem encodeRow_rowFromBytes
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : ℕ)
    (hb : ValidBytes [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16]) :
    encodeRow (rowFromBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16) =
      [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16] := by
  have h0 := hb b0 (by simp)
  have h2 := hb b2 (by simp)
  have h4 := hb b4 (by simp)
  have h6 := hb b6 (by simp)
  have h8 := hb b8 (by simp)
  have h10 := hb b10 (by simp)
  have h12 := hb b12 (by simp)
  have h14 := hb b14 (by simp)
  simp [encodeRow, rowFromBytes, wordLE16_mod, wordLE16_div,
    h0,h2,h4,h6,h8,h10,h12,h14]

private theorem parse_spec_bounded (n : ℕ) :
    ∀ bytes : List ℕ, bytes.length ≤ n → ∀ rows : List FourthWireRow,
    ValidBytes bytes → decodeWireRows bytes = some rows →
      (∀ r ∈ rows, UnsignedRow r) ∧ rows.length * 17 = bytes.length ∧ encodeRows rows = bytes := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro bytes hbound rows hbytes hparse
    by_cases hnil : bytes = []
    · subst bytes
      simp only [decodeWireRows, Option.some.injEq] at hparse
      subst rows
      exact ⟨by simp, by simp, rfl⟩
    by_cases hshort : bytes.length < 17
    · rw [decodeWireRows_short bytes hnil hshort] at hparse
      cases hparse
    obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,rest,rfl⟩ :=
      prefix17 bytes (by omega)
    let head : List ℕ := [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16]
    have hhead : ValidBytes head := by
      intro b hb
      apply hbytes b
      change b ∈ head ++ rest
      exact List.mem_append.mpr (Or.inl hb)
    have hrest : ValidBytes rest := by
      intro b hb
      apply hbytes b
      change b ∈ head ++ rest
      exact List.mem_append.mpr (Or.inr hb)
    have hrestlt : rest.length < n := by
      simp only [List.length_cons] at hbound
      omega
    rw [decodeWireRows_cons17] at hparse
    cases hdec : decodeWireRows rest with
    | none => simp [hdec] at hparse
    | some tail =>
      have heq : rowFromBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 :: tail = rows := by
        simpa [hdec] using hparse
      subst rows
      obtain ⟨hunsigned, hlength, hencode⟩ := ih rest.length hrestlt rest le_rfl tail hrest hdec
      have hrow := rowFromBytes_unsigned b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 hhead
      refine ⟨?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_cons.mp hr with hr | hr
        · subst r
          exact hrow
        · exact hunsigned r hr
      · simp only [List.length_cons]
        omega
      · simpa only [encodeRows,
          encodeRow_rowFromBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 hhead,
          hencode]

/-- Any successful parse on the byte domain produces unsigned row fields,
consumes every byte, and re-encodes to the exact original ordered list. -/
theorem decodeWireRows_sound (bytes : List ℕ) (rows : List FourthWireRow)
    (hbytes : ValidBytes bytes) (hparse : decodeWireRows bytes = some rows) :
    (∀ r ∈ rows, UnsignedRow r) ∧ rows.length * 17 = bytes.length ∧ encodeRows rows = bytes :=
  parse_spec_bounded bytes.length bytes le_rfl rows hbytes hparse

private theorem parse_complete_bounded (n : ℕ) :
    ∀ bytes : List ℕ, bytes.length ≤ n → 17 ∣ bytes.length →
      ∃ rows : List FourthWireRow, decodeWireRows bytes = some rows := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro bytes hbound hdiv
    by_cases hnil : bytes = []
    · subst bytes
      exact ⟨[], rfl⟩
    have hpos : 0 < bytes.length := by
      cases bytes with
      | nil => exact False.elim (hnil rfl)
      | cons b rest => simp
    obtain ⟨k, hk⟩ := hdiv
    have hge : 17 ≤ bytes.length := by omega
    obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,rest,rfl⟩ := prefix17 bytes hge
    have hrestlt : rest.length < n := by
      simp only [List.length_cons] at hbound
      omega
    have hdivRest : 17 ∣ rest.length := by
      refine ⟨k - 1, ?_⟩
      simp only [List.length_cons] at hk
      omega
    obtain ⟨tail, htail⟩ := ih rest.length hrestlt rest le_rfl hdivRest
    refine ⟨rowFromBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 :: tail, ?_⟩
    simpa only [decodeWireRows_cons17, htail]

/-- Format completeness: the old decoder needs exactly a multiple of17
entries. Byte validity is separate and supplies unsigned semantic ranges. -/
theorem decodeWireRows_complete (bytes : List ℕ) (hdiv : 17 ∣ bytes.length) :
    ∃ rows : List FourthWireRow, decodeWireRows bytes = some rows :=
  parse_complete_bounded bytes.length bytes le_rfl hdiv

theorem validBytes_parse_iff_length_dvd (bytes : List ℕ) (hbytes : ValidBytes bytes) :
    (∃ rows : List FourthWireRow, decodeWireRows bytes = some rows) ↔ 17 ∣ bytes.length := by
  constructor
  · rintro ⟨rows, hparse⟩
    have hlength := (decodeWireRows_sound bytes rows hbytes hparse).2.1
    exact ⟨rows.length, by omega⟩
  · exact decodeWireRows_complete bytes

/-- The other round-trip direction, with no filtering, deduplication,
byte loss, padding or sorting. This is conditional only on a valid parse. -/
theorem encodeRows_decoded (bytes : List ℕ) (rows : List FourthWireRow)
    (hbytes : ValidBytes bytes) (hparse : decodeWireRows bytes = some rows) :
    encodeRows rows = bytes :=
  (decodeWireRows_sound bytes rows hbytes hparse).2.2

end ImbalancedChen.P1OriginalFourthPackedParserCompleteness
