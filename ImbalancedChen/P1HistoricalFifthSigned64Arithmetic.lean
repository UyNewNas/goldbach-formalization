import ImbalancedChen.P1HistoricalFifthTableParser
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
Pure signed-int64 arithmetic and exact ten-column80-byte addressing.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The raw original NPY format is little-endian signed64. This module proves
scalar two's-complement roundtrip, legal8-byte unsigned/signed bounds and
exact contiguous column addressing into the typed FifthWireRow parser.
All gap/A/B fields remain literal signed integers. No NPY header parsing,
full292633-row Lean parse, gate check or payload replay is executed here.
-/

namespace ImbalancedChen.P1HistoricalFifthSigned64Arithmetic
noncomputable section
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser

abbrev Bytes8 := Fin 8 → ℕ
abbrev Bytes80 := Fin 80 → ℕ

def modulus64 : ℕ := 2 ^ 64
def half64 : ℕ := 2 ^ 63

/-- Exact unsigned little-endian value of eight ordered bytes. -/
def unsigned64LE8 (bytes : Bytes8) : ℕ := ∑ i, bytes i * 256 ^ i.val

/-- Original signed64 two's-complement interpretation, with no float cast. -/
def decodeSigned64 (word : ℕ) : ℤ :=
  if word < half64 then (word : ℤ) else (word : ℤ) - (modulus64 : ℤ)

/-- The canonical two's-complement residue; total on all integers. -/
def encodeSigned64 (z : ℤ) : ℕ := (z % (modulus64 : ℤ)).toNat

theorem encodeSigned64_lt (z : ℤ) : encodeSigned64 z < modulus64 := by
  have hnonneg := Int.emod_nonneg z (show (modulus64 : ℤ) ≠ 0 by norm_num [modulus64])
  have hlt := Int.emod_lt_of_pos z (show (0 : ℤ) < modulus64 by norm_num [modulus64])
  unfold encodeSigned64
  omega

/-- Scalar signed64 roundtrip over the complete legal source interval. -/
theorem decodeSigned64_encodeSigned64 (z : ℤ)
    (hlo : -(half64 : ℤ) ≤ z) (hhi : z < (half64 : ℤ)) :
    decodeSigned64 (encodeSigned64 z) = z := by
  by_cases hz : 0 ≤ z
  · have hmod : z % (modulus64 : ℤ) = z := Int.emod_eq_of_lt hz (by
      norm_num [modulus64, half64] at *
      omega)
    have hsmall : z.toNat < half64 := by
      have hcast := Int.toNat_of_nonneg hz
      omega
    unfold encodeSigned64
    rw [hmod, decodeSigned64, if_pos hsmall]
    exact Int.toNat_of_nonneg hz
  · have hlow : 0 ≤ z + (modulus64 : ℤ) := by
      norm_num [modulus64, half64] at *
      omega
    have hupp : z + (modulus64 : ℤ) < (modulus64 : ℤ) := by omega
    have hmod : z % (modulus64 : ℤ) = z + (modulus64 : ℤ) := by
      have h := Int.emod_eq_of_lt hlow hupp
      rw [Int.add_emod_right] at h
      exact h
    have hlarge : ¬ (z + (modulus64 : ℤ)).toNat < half64 := by
      have hcast := Int.toNat_of_nonneg hlow
      norm_num [modulus64, half64] at *
      omega
    unfold encodeSigned64
    rw [hmod, decodeSigned64, if_neg hlarge, Int.toNat_of_nonneg hlow]
    omega

/-- Every unsigned64 word decodes into the exact signed64 interval. -/
theorem decodeSigned64_bounds (word : ℕ) (hword : word < modulus64) :
    -(half64 : ℤ) ≤ decodeSigned64 word ∧ decodeSigned64 word < (half64 : ℤ) := by
  unfold decodeSigned64
  split_ifs with hhalf <;> norm_num [modulus64, half64] at * <;> omega

/-- No valid8-byte column can overflow unsigned64. The endpoint sum is an
exact finite integer identity; no source payload or numerical checker runs. -/
theorem unsigned64LE8_lt (bytes : Bytes8) (hbyte : ∀ i, bytes i < 256) :
    unsigned64LE8 bytes < modulus64 := by
  have hsum : unsigned64LE8 bytes ≤ ∑ i : Fin 8, 255 * 256 ^ i.val := by
    apply Finset.sum_le_sum
    intro i hi
    have hb : bytes i ≤ 255 := by omega
    exact Nat.mul_le_mul_right _ hb
  have htop : (∑ i : Fin 8, 255 * 256 ^ i.val) = modulus64 - 1 := by
    norm_num [Fin.sum_univ_succ, modulus64]
  rw [htop] at hsum
  have hpos : 0 < modulus64 := by norm_num [modulus64]
  omega

theorem decode_bytes8_bounds (bytes : Bytes8) (hbyte : ∀ i, bytes i < 256) :
    -(half64 : ℤ) ≤ decodeSigned64 (unsigned64LE8 bytes) ∧
      decodeSigned64 (unsigned64LE8 bytes) < (half64 : ℤ) :=
  decodeSigned64_bounds _ (unsigned64LE8_lt bytes hbyte)

/-- Source column c occupies exactly bytes8*c,...,8*c+7. -/
def columnByteIndex (column : Fin 10) (byte : Fin 8) : Fin 80 :=
  ⟨8 * column.val + byte.val, by omega⟩

def columnBytes (raw : Bytes80) (column : Fin 10) : Bytes8 :=
  fun byte => raw (columnByteIndex column byte)

/-- Distinct column/byte pairs never alias in the80-byte original row. -/
theorem columnByteIndex_injective :
    Function.Injective (fun p : Fin 10 × Fin 8 => columnByteIndex p.1 p.2) := by
  intro p q h
  have hv := congrArg Fin.val h
  simp only [columnByteIndex] at hv
  have hpb := p.2.isLt
  have hqb := q.2.isLt
  have hc : p.1 = q.1 := by apply Fin.ext; omega
  have hb : p.2 = q.2 := by apply Fin.ext; omega
  exact Prod.ext hc hb

/-- Every original byte is owned by exactly the source quotient/remainder
column pair, with no reversal, padding or omitted opaque statistic. -/
theorem columnByteIndex_surjective :
    Function.Surjective (fun p : Fin 10 × Fin 8 => columnByteIndex p.1 p.2) := by
  intro i
  refine ⟨(⟨i.val / 8, by omega⟩, ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
  apply Fin.ext
  simp only [columnByteIndex]
  omega

def unflattenBytes80 (columns : Fin 10 → Bytes8) : Bytes80 := fun i =>
  columns ⟨i.val / 8, by omega⟩ ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩

theorem columnBytes_unflatten (columns : Fin 10 → Bytes8) (column : Fin 10) :
    columnBytes (unflattenBytes80 columns) column = columns column := by
  funext byte
  change columns (⟨(8 * column.val + byte.val) / 8, by omega⟩ : Fin 10)
      (⟨(8 * column.val + byte.val) % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = columns column byte
  have hc : (⟨(8 * column.val + byte.val) / 8, by omega⟩ : Fin 10) = column := by
    apply Fin.ext
    omega
  have hb : (⟨(8 * column.val + byte.val) % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = byte := by
    apply Fin.ext
    omega
  rw [hc, hb]

/-- Exact original order of all ten signed values. -/
def decodeColumns80 (raw : Bytes80) : SavedColumns :=
  fun column => decodeSigned64 (unsigned64LE8 (columnBytes raw column))

def wireFrom80 (raw : Bytes80) : FifthWireRow := wireOfColumns (decodeColumns80 raw)

theorem decodeColumns80_bounds (raw : Bytes80) (hraw : ∀ i, raw i < 256) (column : Fin 10) :
    -(half64 : ℤ) ≤ decodeColumns80 raw column ∧ decodeColumns80 raw column < (half64 : ℤ) :=
  decode_bytes8_bounds _ (fun byte => hraw (columnByteIndex column byte))

/-- Exact column-to-field assignment, including untouched gap/A/B slots. -/
theorem wireFrom80_fields (raw : Bytes80) :
    (wireFrom80 raw).grid = decodeColumns80 raw 0 ∧
      (∀ i, (wireFrom80 raw).lo i = decodeColumns80 raw (lowerColumn i)) ∧
      (wireFrom80 raw).mask = decodeColumns80 raw 6 ∧
      (wireFrom80 raw).vertexGapSum = decodeColumns80 raw 7 ∧
      (wireFrom80 raw).ratioA = decodeColumns80 raw 8 ∧
      (wireFrom80 raw).ratioB = decodeColumns80 raw 9 := by
  exact ⟨rfl, fun i => wireOfColumns_lo _ i, rfl, rfl, rfl, rfl⟩

/-- Ten scalar two's-complement residues reconstruct all original signed
columns, including opaque statistics, on their signed64 source domain. -/
theorem ten_signed_columns_roundtrip (columns : SavedColumns)
    (hrange : ∀ c, -(half64 : ℤ) ≤ columns c ∧ columns c < (half64 : ℤ)) :
    (fun c => decodeSigned64 (encodeSigned64 (columns c))) = columns := by
  funext c
  exact decodeSigned64_encodeSigned64 (columns c) (hrange c).1 (hrange c).2

/-- The lossless ten-column result plugs into the already proved typed
wire parser. This does not claim that any full NPY payload was evaluated. -/
theorem ten_signed_wire_roundtrip (raw : FifthWireRow)
    (hrange : ∀ c, -(half64 : ℤ) ≤ wireColumns raw c ∧ wireColumns raw c < (half64 : ℤ)) :
    wireOfColumns (fun c => decodeSigned64 (encodeSigned64 (wireColumns raw c))) = raw := by
  rw [ten_signed_columns_roundtrip (wireColumns raw) hrange, wireOfColumns_wireColumns]

end
end ImbalancedChen.P1HistoricalFifthSigned64Arithmetic



