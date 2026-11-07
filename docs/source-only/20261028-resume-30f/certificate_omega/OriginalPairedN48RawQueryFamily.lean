import ImbalancedChen.OriginalPairedN48DirectQuerySoundness
import ImbalancedChen.OriginalPairedN48CanonicalArrayProofProposals
import ImbalancedChen.OriginalPairedN48PreallocatedProducerIdentity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL Omega8192 cell array is reused for every native raw query.
Its first/last indices are not clipped or replaced by a favorable query.
The upper argument can be a grid node: use min(last,floor(s*mesh)) so the
closed right endpoint is covered by the preceding scanned cell if needed.
No supplied uniform omega bound, BridgeValid or QueryCover is assumed.
-/

namespace ImbalancedChen.OriginalPairedN48RawQueryFamily

noncomputable section
open Set
open LiLiuPrereqBuchstab
open OriginalN48Q112LocalProduct
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48DirectQuerySoundness
open OriginalPairedN48CanonicalArrays
open OriginalPairedN48PreallocatedProducerIdentity

def rawFirst (lo : ℚ) : ℕ := ⌊lo * (mesh : ℚ)⌋₊
def rawLast (lo hi : ℚ) : ℕ :=
  max (rawFirst lo) (Int.toNat (⌈hi * (mesh : ℚ)⌉ - 1))

def rawQueryNumerator (p : SourceArrays) (lo hi : ℚ) : ℤ :=
  ((p.cell.drop (rawFirst lo)).take (rawLast lo hi - rawFirst lo + 1)).foldl max 0

def rawQueryToken (p : SourceArrays) (lo hi : ℚ) : Token :=
  ⟨rawQueryNumerator p lo hi, rawQueryNumerator p lo hi⟩

/-- Exact scalar floor/ceil geometry for every native [lo,hi]⊂[2,10).
The actual high-band queries are proved independently to lie in [2,8]. -/
theorem raw_grid_properties (lo hi : ℚ) (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi < 10) :
    rawFirst lo ≤ rawLast lo hi ∧ 2 * mesh ≤ rawFirst lo ∧ rawLast lo hi < cellCount ∧
      (rawFirst lo : ℝ) ≤ (lo : ℝ) * (mesh : ℝ) ∧
      (hi : ℝ) * (mesh : ℝ) ≤ (rawLast lo hi : ℝ) + 1 := by
  have hm : (0 : ℚ) < mesh := by norm_num [mesh]
  have hnonneg : 0 ≤ lo * (mesh : ℚ) := mul_nonneg (by linarith only [hlo]) hm.le
  have hf : (rawFirst lo : ℚ) ≤ lo * (mesh : ℚ) := Nat.floor_le hnonneg
  have hf2 : 2 * mesh ≤ rawFirst lo := by
    apply Nat.le_floor
    have h := mul_le_mul_of_nonneg_right hlo hm.le
    exact_mod_cast h
  let c : ℤ := ⌈hi * (mesh : ℚ)⌉
  let b : ℕ := Int.toNat (c - 1)
  have hcUpper : hi * (mesh : ℚ) ≤ (c : ℚ) := Int.le_ceil _
  have hcLower : (c : ℚ) < hi * (mesh : ℚ) + 1 := Int.ceil_lt_add_one _
  have hc0 : (0 : ℤ) < c := by
    have hx : (0 : ℚ) < hi * (mesh : ℚ) :=
      mul_pos (by linarith only [hlo, horder]) hm
    exact_mod_cast hx.trans_le hcUpper
  have hc1 : 0 ≤ c - 1 := by omega
  have hbZ : (b : ℤ) = c - 1 := Int.toNat_of_nonneg hc1
  have hbQ : (b : ℚ) = (c : ℚ) - 1 := by exact_mod_cast hbZ
  have hbLower : (b : ℚ) < hi * (mesh : ℚ) := by rw [hbQ]; linarith only [hcLower]
  have hbUpper : hi * (mesh : ℚ) ≤ (b : ℚ) + 1 := by rw [hbQ]; linarith only [hcUpper]
  have hiMax : hi * (mesh : ℚ) < (cellCount : ℚ) := by
    have h := mul_lt_mul_of_pos_right hhi hm
    simpa only [cellCount, Nat.cast_mul, Nat.cast_ofNat] using h
  have hfMax : rawFirst lo < cellCount := by
    have h : (rawFirst lo : ℚ) < (cellCount : ℚ) :=
      hf.trans_lt ((mul_le_mul_of_nonneg_right horder hm.le).trans_lt hiMax)
    exact_mod_cast h
  have hbMax : b < cellCount := by exact_mod_cast hbLower.trans hiMax
  have hlastMax : rawLast lo hi < cellCount := max_lt_iff.mpr ⟨hfMax, hbMax⟩
  have hbLast : (b : ℚ) ≤ (rawLast lo hi : ℚ) := by
    exact_mod_cast (le_max_right (rawFirst lo) b)
  refine ⟨le_max_left _ _, hf2, hlastMax, ?_, ?_⟩
  · exact_mod_cast hf
  · have hq : hi * (mesh : ℚ) ≤ (rawLast lo hi : ℚ) + 1 := by
      linarith only [hbUpper, hbLast]
    exact_mod_cast hq

theorem raw_query_cell_cover (lo hi : ℚ) (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi < 10)
    {s : ℝ} (hs : s ∈ Icc (lo : ℝ) (hi : ℝ)) :
    ∃ k : ℕ, rawFirst lo ≤ k ∧ k ≤ rawLast lo hi ∧ 2 * mesh ≤ k ∧ k < cellCount ∧
      s ∈ Icc ((k : ℝ) / (mesh : ℝ)) (((k + 1 : ℕ) : ℝ) / (mesh : ℝ)) := by
  let f : ℕ := ⌊s * (mesh : ℝ)⌋₊
  let k : ℕ := min (rawLast lo hi) f
  have hm : (0 : ℝ) < mesh := by norm_num [mesh]
  have hs0 : 0 ≤ s := by
    have hl : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast (show 0 ≤ lo by linarith only [hlo])
    exact hl.trans hs.1
  have hfLo : (f : ℝ) ≤ s * (mesh : ℝ) := Nat.floor_le (mul_nonneg hs0 hm.le)
  have hfHi : s * (mesh : ℝ) < (f : ℝ) + 1 := Nat.lt_floor_add_one _
  have hp := raw_grid_properties lo hi hlo horder hhi
  have hfirstF : rawFirst lo ≤ f :=
    Nat.le_floor (hp.2.2.2.1.trans (mul_le_mul_of_nonneg_right hs.1 hm.le))
  have hfirstK : rawFirst lo ≤ k := le_min hp.1 hfirstF
  have hkLast : k ≤ rawLast lo hi := min_le_left _ _
  have hkF : k ≤ f := min_le_right _ _
  have hkFReal : (k : ℝ) ≤ (f : ℝ) := by exact_mod_cast hkF
  refine ⟨k, hfirstK, hkLast, hp.2.1.trans hfirstK,
    hkLast.trans_lt hp.2.2.1, ?_, ?_⟩
  · exact (div_le_iff₀ hm).2 (hkFReal.trans hfLo)
  · by_cases hfl : f ≤ rawLast lo hi
    · have he : k = f := min_eq_right hfl
      rw [he]
      apply (le_div_iff₀ hm).2
      push_cast
      exact hfHi.le
    · have he : k = rawLast lo hi := min_eq_left (le_of_not_ge hfl)
      rw [he]
      apply (le_div_iff₀ hm).2
      push_cast
      exact (mul_le_mul_of_nonneg_right hs.2 hm.le).trans hp.2.2.2.2

private theorem fold_max_acc (xs : List ℤ) (a : ℤ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

private theorem fold_max_member (xs : List ℤ) (a x : ℤ) (hx : x ∈ xs) : x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right a y).trans (fold_max_acc ys (max a y))
    · exact ih (max a y) hx

theorem scanned_cell_le_raw_query (p : SourceArrays) (hp : SourceProducerValid p)
    (lo hi : ℚ) (k : ℕ) (hfirst : rawFirst lo ≤ k) (hlast : k ≤ rawLast lo hi)
    (hkc : k < cellCount) : cellAt p k ≤ rawQueryNumerator p lo hi := by
  have hkarray : k < p.cell.length := by rw [hp.2.1]; exact hkc
  let xs := (p.cell.drop (rawFirst lo)).take (rawLast lo hi - rawFirst lo + 1)
  have hjdrop : k - rawFirst lo < (p.cell.drop (rawFirst lo)).length := by
    simp only [List.length_drop]
    omega
  have hj : k - rawFirst lo < xs.length := by
    dsimp [xs]
    simp only [List.length_take]
    omega
  have hmem : cellAt p k ∈ xs := by
    refine List.mem_iff_getElem.mpr ⟨k - rawFirst lo, hj, ?_⟩
    dsimp [xs]
    rw [List.getElem_take, List.getElem_drop]
    have he : rawFirst lo + (k - rawFirst lo) = k := by omega
    simp only [he, cellAt, List.getElem?_eq_getElem hkarray, Option.getD_some]
  exact fold_max_member xs 0 (cellAt p k) hmem

/-- Actual uniform soundness of every original scan on the global array.
The only data premise is the original finite arithmetic producer predicate. -/
theorem original_raw_query_uniform (p : SourceArrays) (hp : SourceProducerValid p)
    (lo hi : ℚ) (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi < 10)
    {s : ℝ} (hs : s ∈ Icc (lo : ℝ) (hi : ℝ)) :
    buchstab s ≤ (rawQueryNumerator p lo hi : ℝ) / (P : ℝ) := by
  obtain ⟨k, hfirst, hlast, hk2, hkc, hcell⟩ := raw_query_cell_cover lo hi hlo horder hhi hs
  have hik : k + 1 < uCount := by dsimp [cellCount, uCount] at *; omega
  have hu := original_sourceCell_sound p hp k hk2 hik hcell
  have he := (hp.2.2.2.2.2.2 ⟨k, hkc⟩).1
  rw [← he] at hu
  have hscan := scanned_cell_le_raw_query p hp lo hi k hfirst hlast hkc
  exact hu.trans (div_le_div_of_nonneg_right (by exact_mod_cast hscan)
    (show (0 : ℝ) ≤ (P : ℝ) by exact_mod_cast P_pos.le))

theorem preallocated_raw_query_identity (lo hi : ℚ) :
    rawQueryNumerator originalFixedFields lo hi = rawQueryNumerator canonicalSourceArrays lo hi := by
  rw [original_fixed_fields_identity]

/-- The point token denotes an upper constant, not a lower enclosure for
all omega values.  This theorem retains exactly that direction. -/
theorem raw_query_token_upper (p : SourceArrays) (hp : SourceProducerValid p)
    (lo hi : ℚ) (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi < 10)
    {s : ℝ} (hs : s ∈ Icc (lo : ℝ) (hi : ℝ)) :
    buchstab s ≤ uniformOmegaUpper (rawQueryToken p lo hi) := by
  simpa only [uniformOmegaUpper, rawQueryToken, decode,
    Rat.cast_div, Rat.cast_intCast] using original_raw_query_uniform p hp lo hi hlo horder hhi hs

end
end ImbalancedChen.OriginalPairedN48RawQueryFamily
