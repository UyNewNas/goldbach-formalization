import ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check

/-!
SOURCEONLY / UNCOMPILED / NO PASS CLAIM.
Proposed module: ImbalancedChen.Certificates.OriginalNodeArraysV1.InitialPrefix

This is the prefix 0..32768 only. The concrete line columns below are compressed
by repetition; their values are NOT premises of the row theorem. This file does
not read the artifact, prove a SHA theorem, or supply an emitter receipt.
See the accompanying CP for the precise remaining external byte identity.
-/

namespace ImbalancedChen.OriginalU2InitialPrefix20261024uSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly

/-- These are ASCII digits only, irrespective of Unicode digit categories. -/
noncomputable def asciiDigit : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

/-- After a nonzero leading digit: accept more ASCII digits and one final LF.
No missing LF, embedded LF, CR, whitespace, sign, or trailing text is accepted. -/
noncomputable def decodeTailLine (acc : Nat) : List Char → Option Nat
  | ['\n'] => some acc
  | c :: cs => do
      let d ← asciiDigit c
      decodeTailLine (10 * acc + d) cs
  | [] => none

/-- Canonical nonnegative manifest line: `0\n` or `[1-9][0-9]*\n`.
This prefix-only Nat decoder intentionally rejects negative update values. -/
noncomputable def decodeCanonicalNatLine (s : String) : Option Nat :=
  match s.toList with
  | ['0', '\n'] => some 0
  | c :: cs => do
      let d ← asciiDigit c
      if d = 0 then none else decodeTailLine d cs
  | [] => none

noncomputable def zeroLine : String := "0\n"
noncomputable def pLine : String := "5192296858534827628530496329220096\n"
noncomputable def prefixCount : Nat := 32769

theorem decode_zeroLine : decodeCanonicalNatLine zeroLine = some 0 := by
  decide

theorem decode_pLine :
    decodeCanonicalNatLine pLine = some 5192296858534827628530496329220096 := by
  decide

/-- Small closed arithmetic goals use kernel-checkable `decide`, never a native
decision procedure. Their successful compilation is NOT claimed here. -/
theorem p_nat_eq_decimal :
    (2 : Nat)^112 = 5192296858534827628530496329220096 := by
  decide

theorem p_int_eq_decimal :
    (2 : Int)^112 = 5192296858534827628530496329220096 := by
  decide

theorem rawInitial_eq_decimal :
    rawInitial =
      (⟨0, 0, 5192296858534827628530496329220096,
        5192296858534827628530496329220096⟩ : RawNode) := by
  simp only [rawInitial, p_int_eq_decimal]

/-- Field order is the actual DataCore order Llo,Lhi,Hlo,Hhi. -/
noncomputable def decodeRowLines (Llo Lhi Hlo Hhi : String) : Option RawNode := do
  let a ← decodeCanonicalNatLine Llo
  let b ← decodeCanonicalNatLine Lhi
  let c ← decodeCanonicalNatLine Hlo
  let d ← decodeCanonicalNatLine Hhi
  pure ⟨Int.ofNat a, Int.ofNat b, Int.ofNat c, Int.ofNat d⟩

theorem decode_initial_row :
    decodeRowLines zeroLine zeroLine pLine pLine = some rawInitial := by
  rw [rawInitial_eq_decimal]
  decide

/-- Transparent compressed line array; no external values enter this definition. -/
noncomputable def repeatedLines : Nat → String → List String
  | 0, _ => []
  | n + 1, line => line :: repeatedLines n line

noncomputable def lineAt : List String → Nat → Option String
  | [], _ => none
  | line :: _, 0 => some line
  | _ :: lines, i + 1 => lineAt lines i

theorem repeatedLines_length (n : Nat) (line : String) :
    (repeatedLines n line).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [repeatedLines, List.length_cons, ih]

theorem lineAt_repeatedLines (line : String) (n i : Nat) (hi : i < n) :
    lineAt (repeatedLines n line) i = some line := by
  induction n generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i =>
          exact ih i (Nat.lt_of_succ_lt_succ hi)

structure PrefixColumns where
  Llo : List String
  Lhi : List String
  Hlo : List String
  Hhi : List String

/-- These are the concrete four columns claimed by the prefix artifact review.
Their identity with external file bytes remains an explicit external obligation. -/
noncomputable def canonicalPrefix : PrefixColumns :=
  ⟨repeatedLines prefixCount zeroLine, repeatedLines prefixCount zeroLine,
   repeatedLines prefixCount pLine, repeatedLines prefixCount pLine⟩

theorem canonicalPrefix_lengths :
    canonicalPrefix.Llo.length = 32769 ∧ canonicalPrefix.Lhi.length = 32769 ∧
    canonicalPrefix.Hlo.length = 32769 ∧ canonicalPrefix.Hhi.length = 32769 := by
  exact ⟨repeatedLines_length prefixCount zeroLine,
    repeatedLines_length prefixCount zeroLine,
    repeatedLines_length prefixCount pLine,
    repeatedLines_length prefixCount pLine⟩

noncomputable def decodeRowAt (columns : PrefixColumns) (i : Nat) : Option RawNode := do
  let a ← lineAt columns.Llo i
  let b ← lineAt columns.Lhi i
  let c ← lineAt columns.Hlo i
  let d ← lineAt columns.Hhi i
  decodeRowLines a b c d

/-- The proof is uniform in count and index; it never expands 32769 rows. -/
theorem decode_repeated_row (count i : Nat) (hi : i < count) :
    decodeRowAt
      ⟨repeatedLines count zeroLine, repeatedLines count zeroLine,
       repeatedLines count pLine, repeatedLines count pLine⟩ i =
      some rawInitial := by
  have hz := lineAt_repeatedLines zeroLine count i hi
  have hp := lineAt_repeatedLines pLine count i hi
  simpa [decodeRowAt, hz, hp] using decode_initial_row

theorem canonicalPrefix_row (i : Nat) (hi : i ≤ 32768) :
    decodeRowAt canonicalPrefix i = some rawInitial := by
  have hlt : i < 32769 := Nat.lt_succ_of_le hi
  exact decode_repeated_row prefixCount i hlt

/-- The existing query carrier agrees with the concrete decoded prefix for any
choice of update blocks. It is the actual DataCore reader, not a new toy reader. -/
theorem assembledRawRead_prefix_correspondence
    (blocks : Nat → Block) (i : Nat) (hi : i ≤ 32768) :
    decodeRowAt canonicalPrefix i = some (assembledRawRead blocks i) := by
  simpa only [assembledRawRead, if_pos hi] using canonicalPrefix_row i hi

/-- Optional entry point for an emitter's reified ordered line columns.
The premise is exact source-data identity; it does not assume decoded row
correctness. No proof of this premise for external artifact files is supplied. -/
theorem reified_prefix_reader_correspondence
    (columns : PrefixColumns) (hcolumns : columns = canonicalPrefix)
    (blocks : Nat → Block) (i : Nat) (hi : i ≤ 32768) :
    decodeRowAt columns i = some (assembledRawRead blocks i) := by
  rw [hcolumns]
  exact assembledRawRead_prefix_correspondence blocks i hi

/-- Exact serialization target for the external byte receipt: concatenate the
already LF-terminated canonical lines in order, without separators or headers.
The receipt must compare each file with the UTF-8 bytes of this String.
All concrete source characters here are ASCII, so UTF-8 is ASCII byte-for-byte. -/
noncomputable def serializeLines : List String → String
  | [] => ""
  | line :: lines => line ++ serializeLines lines

noncomputable def serializedPrefixLlo : String := serializeLines canonicalPrefix.Llo
noncomputable def serializedPrefixLhi : String := serializeLines canonicalPrefix.Lhi
noncomputable def serializedPrefixHlo : String := serializeLines canonicalPrefix.Hlo
noncomputable def serializedPrefixHhi : String := serializeLines canonicalPrefix.Hhi

end ImbalancedChen.OriginalU2InitialPrefix20261024uSourceOnly
