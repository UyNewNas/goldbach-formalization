import ImbalancedChen.P2OriginalFourthCapProducerInterface

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_ACCEPTANCE_CREDIT.

Lossless raw fourth-record ABI and a total Option decoder for packed hex.
Each record is 17 bytes: four little-endian unsigned16 lower coordinates,
four little-endian unsigned16 upper coordinates, one unsigned8 winner/mask.
No geometry, numerical check, dynamic parent, epsilon, gain or table claim
is inferred from successful decoding. No entire payload parse is asserted.
-/

namespace ImbalancedChen.P1OriginalFourthPackedTable

structure FourthWireRow where
  lo : Fin 4 → ℕ
  hi : Fin 4 → ℕ
  mask : ℕ

def FourthWireRow.toProducerRow (r : FourthWireRow) :
    P2OriginalFourthCapProducerInterface.ProducerRow := ⟨r.lo, r.hi, r.mask⟩

theorem toProducerRow_lo (r : FourthWireRow) : r.toProducerRow.lo = r.lo := rfl
theorem toProducerRow_hi (r : FourthWireRow) : r.toProducerRow.hi = r.hi := rfl
theorem toProducerRow_mask (r : FourthWireRow) : r.toProducerRow.mask = r.mask := rfl

theorem toProducerRow_lower (r : FourthWireRow) (i : Fin 4) :
    r.toProducerRow.lower i = (r.lo i : ℚ) / 204800 := rfl

theorem toProducerRow_upper (r : FourthWireRow) (i : Fin 4) :
    r.toProducerRow.upper i = (r.hi i : ℚ) / 204800 := rfl

theorem toProducerRow_selected (r : FourthWireRow) (i : Fin 4) :
    i ∈ r.toProducerRow.selected ↔ Nat.testBit r.mask i.val = true := by
  simp [FourthWireRow.toProducerRow, P2OriginalFourthCapProducerInterface.ProducerRow.selected]

def wordLE16 (low high : ℕ) : ℕ := low + 256 * high

def rowFromBytes
    (l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w : ℕ) : FourthWireRow :=
  ⟨![wordLE16 l0 l1, wordLE16 l2 l3, wordLE16 l4 l5, wordLE16 l6 l7],
    ![wordLE16 h0 h1, wordLE16 h2 h3, wordLE16 h4 h5, wordLE16 h6 h7], w⟩

/-- The raw bit-to-integer mapping is explicit and independent of any
particular payload or certificate. These are structural rfl proofs only. -/
theorem rowFromBytes_fields
    (l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w : ℕ) :
    (rowFromBytes l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w).lo =
      ![l0 + 256*l1, l2 + 256*l3, l4 + 256*l5, l6 + 256*l7] ∧
    (rowFromBytes l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w).hi =
      ![h0 + 256*h1, h2 + 256*h3, h4 + 256*h5, h6 + 256*h7] ∧
    (rowFromBytes l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w).mask = w :=
  ⟨rfl, rfl, rfl⟩

def hexDigit (c : Char) : Option ℕ :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else none

theorem hexDigit_bound (c : Char) (n : ℕ) (h : hexDigit c = some n) : n < 16 := by
  unfold hexDigit at h
  split_ifs at h with hd hl hu
  · simp only [Option.some.injEq] at h
    omega
  · simp only [Option.some.injEq] at h
    omega
  · simp only [Option.some.injEq] at h
    omega
  · cases h

def decodeHexChars : List Char → Option (List ℕ)
  | [] => some []
  | a :: b :: rest => do
      let x ← hexDigit a
      let y ← hexDigit b
      let tail ← decodeHexChars rest
      pure ((16*x+y) :: tail)
  | _ => none

theorem decodedByte_bound (a b : Char) (x y : ℕ)
    (ha : hexDigit a = some x) (hb : hexDigit b = some y) : 16*x+y < 256 := by
  have hx := hexDigit_bound a x ha
  have hy := hexDigit_bound b y hb
  omega

theorem decodeHexChars_cons (a b : Char) (rest : List Char) (x y : ℕ) (tail : List ℕ)
    (ha : hexDigit a = some x) (hb : hexDigit b = some y)
    (hr : decodeHexChars rest = some tail) :
    decodeHexChars (a :: b :: rest) = some ((16*x+y) :: tail) := by
  simp [decodeHexChars, ha, hb, hr]

def decodeWireRows : List ℕ → Option (List FourthWireRow)
  | [] => some []
  | l0 :: l1 :: l2 :: l3 :: l4 :: l5 :: l6 :: l7 ::
      h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: w :: rest => do
      let tail ← decodeWireRows rest
      pure (rowFromBytes l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w :: tail)
  | _ => none

def decodePackedHex (payload : String) : Option (List FourthWireRow) := do
  let bytes ← decodeHexChars payload.toList
  decodeWireRows bytes

theorem decodeWireRows_cons17
    (l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w : ℕ) (rest : List ℕ) :
    decodeWireRows (l0 :: l1 :: l2 :: l3 :: l4 :: l5 :: l6 :: l7 ::
      h0 :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: w :: rest) =
      (do let tail ← decodeWireRows rest
          pure (rowFromBytes l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w :: tail)) := rfl

/-- JSON numeric tokens, including diagnostics, remain uninterpreted text.
Object field order and all array positions are retained. -/
inductive RawJson where
  | nullValue
  | boolValue (value : Bool)
  | numberToken (originalLexeme : String)
  | stringValue (value : String)
  | arrayValue (values : List RawJson)
  | objectValue (fields : List (String × RawJson))

end ImbalancedChen.P1OriginalFourthPackedTable
