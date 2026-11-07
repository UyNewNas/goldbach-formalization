import ImbalancedChen.P1OriginalFourthPackedTableDecoder
import ImbalancedChen.P1OriginalPrefixRowFiniteCheckSoundness

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_ACCEPTANCE_CREDIT.

Generic unsigned-byte arithmetic, exact seventeen-byte row encoding, list
round trips, and original-order preservation. Valid byte/word hypotheses
describe only the primitive wire domain. No whole historical payload parse,
geometry checker, certificate calculation, or numerical replay is executed.
The geometry bridge invokes the separately proved common checker soundness;
it does not assert any concrete row has passed that checker.
-/

namespace ImbalancedChen.P1OriginalFourthPackedArithmeticSoundness

open P1OriginalFourthPackedTable

def UnsignedRow (r : FourthWireRow) : Prop :=
  (∀ i, r.lo i < 65536) ∧ (∀ i, r.hi i < 65536) ∧ r.mask < 256

theorem wordLE16_bound (low high : ℕ) (hlow : low < 256) (hhigh : high < 256) :
    wordLE16 low high < 65536 := by
  unfold wordLE16
  omega

theorem wordLE16_mod (low high : ℕ) (hlow : low < 256) :
    wordLE16 low high % 256 = low := by
  unfold wordLE16
  omega

theorem wordLE16_div (low high : ℕ) (hlow : low < 256) :
    wordLE16 low high / 256 = high := by
  unfold wordLE16
  omega

theorem wordLE16_encode (word : ℕ) : wordLE16 (word % 256) (word / 256) = word := by
  exact Nat.mod_add_div word 256

theorem lowByte_bound (word : ℕ) : word % 256 < 256 :=
  Nat.mod_lt word (by norm_num)

theorem highByte_bound (word : ℕ) (hword : word < 65536) : word / 256 < 256 := by
  omega

def encodeRow (r : FourthWireRow) : List ℕ :=
  [r.lo 0 % 256, r.lo 0 / 256, r.lo 1 % 256, r.lo 1 / 256,
   r.lo 2 % 256, r.lo 2 / 256, r.lo 3 % 256, r.lo 3 / 256,
   r.hi 0 % 256, r.hi 0 / 256, r.hi 1 % 256, r.hi 1 / 256,
   r.hi 2 % 256, r.hi 2 / 256, r.hi 3 % 256, r.hi 3 / 256, r.mask]

theorem encodeRow_length (r : FourthWireRow) : (encodeRow r).length = 17 := rfl

theorem encodeRow_bytes (r : FourthWireRow) (hr : UnsignedRow r) :
    ∀ b ∈ encodeRow r, b < 256 := by
  intro b hb
  simp only [encodeRow, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.1 0)
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.1 1)
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.1 2)
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.1 3)
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.2.1 0)
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.2.1 1)
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.2.1 2)
  · exact lowByte_bound _
  · exact highByte_bound _ (hr.2.1 3)
  · exact hr.2.2

/-- The unmodified decoder recovers every field; unsignedness is needed
only to make all encoder outputs physical bytes, not for Nat reconstruction. -/
theorem rowFromBytes_encoded (r : FourthWireRow) :
    rowFromBytes
      (r.lo 0 % 256) (r.lo 0 / 256) (r.lo 1 % 256) (r.lo 1 / 256)
      (r.lo 2 % 256) (r.lo 2 / 256) (r.lo 3 % 256) (r.lo 3 / 256)
      (r.hi 0 % 256) (r.hi 0 / 256) (r.hi 1 % 256) (r.hi 1 / 256)
      (r.hi 2 % 256) (r.hi 2 / 256) (r.hi 3 % 256) (r.hi 3 / 256) r.mask = r := by
  cases r with
  | mk lo hi mask =>
    unfold rowFromBytes
    apply congrArg₂ (fun l h => FourthWireRow.mk l h mask)
    · funext i
      fin_cases i <;> simp [wordLE16_encode]
    · funext i
      fin_cases i <;> simp [wordLE16_encode]

theorem decodeWireRows_encodeRow_append (r : FourthWireRow) (rest : List ℕ) :
    decodeWireRows (encodeRow r ++ rest) =
      (do let tail ← decodeWireRows rest
          pure (r :: tail)) := by
  simp only [encodeRow, List.cons_append, List.nil_append,
    decodeWireRows_cons17, rowFromBytes_encoded]

theorem decodeWireRows_encodeRow (r : FourthWireRow) :
    decodeWireRows (encodeRow r) = some [r] := by
  simpa only [List.append_nil, decodeWireRows] using decodeWireRows_encodeRow_append r []

/-- An arbitrary seventeen valid input bytes produce unsigned endpoint
words and an unsigned mask. No concrete archive row is evaluated here. -/
theorem rowFromBytes_unsigned
    (l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w : ℕ)
    (hbytes : ∀ b ∈ [l0,l1,l2,l3,l4,l5,l6,l7,h0,h1,h2,h3,h4,h5,h6,h7,w], b < 256) :
    UnsignedRow (rowFromBytes l0 l1 l2 l3 l4 l5 l6 l7 h0 h1 h2 h3 h4 h5 h6 h7 w) := by
  refine ⟨?_, ?_, hbytes w (by simp)⟩
  · intro i
    fin_cases i <;>
      exact wordLE16_bound _ _ (hbytes _ (by simp)) (hbytes _ (by simp))
  · intro i
    fin_cases i <;>
      exact wordLE16_bound _ _ (hbytes _ (by simp)) (hbytes _ (by simp))

def encodeRows : List FourthWireRow → List ℕ
  | [] => []
  | r :: rest => encodeRow r ++ encodeRows rest

theorem encodeRows_append (left right : List FourthWireRow) :
    encodeRows (left ++ right) = encodeRows left ++ encodeRows right := by
  induction left with
  | nil => rfl
  | cons r rest ih => simp only [List.cons_append, encodeRows, ih, List.append_assoc]

theorem encodeRows_length (rows : List FourthWireRow) :
    (encodeRows rows).length = 17 * rows.length := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    simp only [encodeRows, List.length_append, encodeRow_length, ih, List.length_cons]
    omega

theorem encodeRows_bytes (rows : List FourthWireRow) :
    (∀ r ∈ rows, UnsignedRow r) → ∀ b ∈ encodeRows rows, b < 256 := by
  induction rows with
  | nil => intro _ b hb; simp only [encodeRows, List.not_mem_nil] at hb
  | cons r rest ih =>
    intro hrows b hb
    simp only [encodeRows, List.mem_append] at hb
    rcases hb with hhead | htail
    · exact encodeRow_bytes r (hrows r (by simp)) b hhead
    · exact ih (fun q hq => hrows q (by simp [hq])) b htail

/-- Full-list equality, rather than a permutation or sorted collection:
all rows, duplicate rows, masks and their original order are preserved. -/
theorem decodeWireRows_encodeRows (rows : List FourthWireRow) :
    decodeWireRows (encodeRows rows) = some rows := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    rw [encodeRows, decodeWireRows_encodeRow_append, ih]
    rfl

theorem decoded_encoded_rows_original_order (rows decoded : List FourthWireRow)
    (h : decodeWireRows (encodeRows rows) = some decoded) : decoded = rows := by
  rw [decodeWireRows_encodeRows] at h
  exact (Option.some.inj h).symm

theorem decoded_encoded_index (rows : List FourthWireRow) (i : ℕ) :
    (decodeWireRows (encodeRows rows)).map (fun decoded => decoded[i]?) = some (rows[i]?) := by
  rw [decodeWireRows_encodeRows]
  rfl

theorem decoded_encoded_producer_order (rows : List FourthWireRow) :
    (decodeWireRows (encodeRows rows)).map (List.map FourthWireRow.toProducerRow) =
      some (rows.map FourthWireRow.toProducerRow) := by
  rw [decodeWireRows_encodeRows]
  rfl

/-- Field-identity bridge to the shared mathematical row ABI. -/
def toCommonRow (r : FourthWireRow) : P1OriginalPrefixRowDecodeSoundness.FourthWireRow :=
  ⟨r.lo, r.hi, r.mask⟩

theorem toCommonRow_producer (r : FourthWireRow) :
    (toCommonRow r).toProducerRow = r.toProducerRow := rfl

/-- The rational finite geometry check is a primitive conditional input.
This theorem does not assert any actual historical row or table passes. -/
theorem common_finite_geometry_check_sound (r : FourthWireRow)
    (hc : P1OriginalPrefixRowFiniteCheckSoundness.fourthGeometryCheck (toCommonRow r) = true) :
    r.toProducerRow.Geometry := by
  have hh := P1OriginalPrefixRowFiniteCheckSoundness.fourthGeometryCheck_sound (toCommonRow r) hc
  simpa only [toCommonRow_producer] using hh

end ImbalancedChen.P1OriginalFourthPackedArithmeticSoundness
