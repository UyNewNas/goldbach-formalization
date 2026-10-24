import ImbalancedChen.ActualThirdOriginalStoredNodeQueryLookup
import ImbalancedChen.ActualThirdOriginalFixedpointClippedChord
import ImbalancedChen.ActualThirdOriginalRoundedNewOperations
import ImbalancedChen.P4AActualSquaredGapDecay
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Literal IndependentSieve.anchors and IndependentSieve.decay, with the SAME
CheckedBlockTable reader, n=16384, P112 nodes, and original 2^48 rescaling.
The source anchor is UP(Hhi[k*n]-Llo[k*n],k)*2^48: Hhi, not Lhi.
No stored integer, recurrence, target decay estimate, or numerical anchor
enclosure is assumed. CheckedBlockTable.encloses supplies actual node bounds.
The prospective P4AActualSquaredGapDecay import is the sibling source in
ordinary_root_first_integral/, not an installed/accepted module here.
No leaf integral, saved table acceptance, or currentK bound is claimed.
-/
namespace ImbalancedChen.P4AOriginalAnchorDecay20261024zSourceOnly

noncomputable section
open scoped Classical
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open P4AActualSquaredGapDecay20261024zSourceOnly

def literalAnchor (table : CheckedBlockTable) (k : ℕ) : ℤ :=
  up ((assembledRead table.blocks (k * 16384)).Hhi -
    (assembledRead table.blocks (k * 16384)).Llo) (k : ℤ) * 2 ^ 48

def anchorIndices (a b : ℤ) : Finset ℕ :=
  (Finset.Icc 3 12).filter fun k => (k : ℤ) * b ≤ a

def literalDecayTerm (table : CheckedBlockTable) (a b : ℤ) (k : ℕ) : ℤ :=
  up (literalAnchor table k * (k : ℤ) ^ 2 * b ^ 2) (a ^ 2)

/-- The unreachable empty branch only makes this a total integer function.
At the original guard a>=3b the minimum is over exactly the original anchors. -/
def literalDecay (table : CheckedBlockTable) (a b : ℤ) : ℤ :=
  if h : (anchorIndices a b).Nonempty then
    (anchorIndices a b).inf' h (literalDecayTerm table a b)
  else 0

theorem anchorIndices_nonempty {a b : ℤ} (h3 : 3 * b ≤ a) :
    (anchorIndices a b).Nonempty := by
  refine ⟨3, ?_⟩
  simp only [anchorIndices, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, by norm_num⟩, by simpa using h3⟩

theorem literalDecay_eq_original_min (table : CheckedBlockTable) (a b : ℤ)
    (h3 : 3 * b ≤ a) :
    literalDecay table a b = (anchorIndices a b).inf'
      (anchorIndices_nonempty h3) (literalDecayTerm table a b) := by
  simp only [literalDecay, dif_pos (anchorIndices_nonempty h3)]

/-- General signed integer UP, with its real comparison proved by the public
literal ceiling API. Neither the numerator nor the output needs a sign premise. -/
theorem real_div_le_original_up (n d : ℤ) (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ≤ (up n d : ℝ) := by
  have h := Int.le_ceil ((n : ℚ) / (d : ℚ))
  rw [query_ceil_div_literal n d hd] at h
  change (n : ℝ) / (d : ℝ) ≤ ((-(-n / d) : ℤ) : ℝ)
  exact_mod_cast h

theorem value_div_le_original_up (n d : ℤ) (hd : 0 < d) :
    value n / (d : ℝ) ≤ value (up n d) := by
  calc
    value n / (d : ℝ) = ((n : ℝ) / (d : ℝ)) / (P160 : ℝ) := by
      unfold value
      ring
    _ ≤ value (up n d) :=
      div_le_div_of_nonneg_right (real_div_le_original_up n d hd) P160_real_pos.le

theorem value_scale112_to160 (n : ℤ) : value (n * 2 ^ 48) = nodeValue n := by
  unfold value P160 nodeValue
  push_cast
  norm_num [originalWeightP] <;> ring

theorem nodeValue_div_le_original_up (n d : ℤ) (hd : 0 < d) :
    nodeValue n / (d : ℝ) ≤ nodeValue (up n d) := by
  have hP : (0 : ℝ) < (originalWeightP : ℝ) := by norm_num [originalWeightP]
  calc
    nodeValue n / (d : ℝ) = ((n : ℝ) / (d : ℝ)) / (originalWeightP : ℝ) := by
      unfold nodeValue
      ring
    _ ≤ nodeValue (up n d) :=
      div_le_div_of_nonneg_right (real_div_le_original_up n d hd) hP.le

/-- Each literal stored anchor bounds the genuine normalized factor gap at k.
The raw node intervals come from the actual checked SAME reader; no numerical
anchor bound is an input and the final node recurrence is never evaluated. -/
theorem normalized_gap_le_literalAnchor (table : CheckedBlockTable) (k : ℕ)
    (hk3 : 3 ≤ k) (hk12 : k ≤ 12) :
    upper (k : ℝ) - lower (k : ℝ) ≤ value (literalAnchor table k) := by
  have hnode := table.encloses (k * 16384) (by omega) (by omega)
  have hgrid : cellLeft (k * 16384) = (k : ℝ) := by
    norm_num [cellLeft, Nat.cast_mul]
  unfold NodeEncloses at hnode
  rw [hgrid] at hnode
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast (show 0 < k by omega)
  let n : ℤ := (assembledRead table.blocks (k * 16384)).Hhi -
    (assembledRead table.blocks (k * 16384)).Llo
  have hraw : upper (k : ℝ) - lower (k : ℝ) ≤ nodeValue n / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    dsimp only [n]
    rw [nodeValue_sub]
    have hh := hnode.2.2
    have hl := hnode.1.1
    dsimp only [H, L] at hh hl
    nlinarith only [hh, hl]
  calc
    upper (k : ℝ) - lower (k : ℝ) ≤ nodeValue n / (k : ℝ) := hraw
    _ ≤ nodeValue (up n (k : ℤ)) := by
      simpa only [Int.cast_natCast] using nodeValue_div_le_original_up n (k : ℤ) hkZ
    _ = value (literalAnchor table k) := by
      rw [literalAnchor, value_scale112_to160]

theorem actual_gap_le_literalAnchor (table : CheckedBlockTable) (k : ℕ)
    (hk3 : 3 ≤ k) (hk12 : k ≤ 12) :
    actualSieveGap (k : ℝ) / (2 * Real.exp Real.eulerMascheroniConstant) ≤
      value (literalAnchor table k) := by
  rw [← normalized_gap_eq_actualSieveGap_div]
  exact normalized_gap_le_literalAnchor table k hk3 hk12

/-- Every admitted original UP term independently bounds the actual gap.
The only extra analytic supplier is genuine squared-gap antitonicity. -/
theorem normalized_gap_le_literalDecayTerm (table : CheckedBlockTable)
    (a b : ℤ) (k : ℕ) (hb : 0 < b) (hk : k ∈ anchorIndices a b) :
    upper ((a : ℝ) / (b : ℝ)) - lower ((a : ℝ) / (b : ℝ)) ≤
      value (literalDecayTerm table a b k) := by
  rcases Finset.mem_filter.mp hk with ⟨hkr, hka⟩
  rcases Finset.mem_Icc.mp hkr with ⟨hk3, hk12⟩
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hkaR : (k : ℝ) * (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hka
  have hks : (k : ℝ) ≤ (a : ℝ) / (b : ℝ) := (le_div_iff₀ hbR).2 hkaR
  have haR : (0 : ℝ) < (a : ℝ) := by nlinarith only [hkR, hbR, hkaR]
  have haZ : 0 < a := by exact_mod_cast haR
  have hfactor : 0 ≤ (k : ℝ) ^ 2 / ((a : ℝ) / (b : ℝ)) ^ 2 := by positivity
  have hgap := normalized_gap_le_anchor_div_sq hkR hks
  have hanchor := normalized_gap_le_literalAnchor table k hk3 hk12
  have hmul := mul_le_mul_of_nonneg_right hanchor hfactor
  have hceil := value_div_le_original_up
    (literalAnchor table k * (k : ℤ) ^ 2 * b ^ 2) (a ^ 2) (sq_pos_of_pos haZ)
  calc
    upper ((a : ℝ) / (b : ℝ)) - lower ((a : ℝ) / (b : ℝ)) ≤
        (upper (k : ℝ) - lower (k : ℝ)) * (k : ℝ) ^ 2 /
          ((a : ℝ) / (b : ℝ)) ^ 2 := hgap
    _ ≤ value (literalAnchor table k) * (k : ℝ) ^ 2 /
        ((a : ℝ) / (b : ℝ)) ^ 2 := by
      simpa only [mul_div_assoc] using hmul
    _ = value (literalAnchor table k * (k : ℤ) ^ 2 * b ^ 2) / ((a ^ 2 : ℤ) : ℝ) := by
      unfold value
      push_cast
      field_simp [haR.ne', hbR.ne'] <;> ring
    _ ≤ value (literalDecayTerm table a b k) := hceil

/-- The original min is nonempty already at a=3b, by its k=3 anchor.
An attaining member transports the real bound through the exact integer min. -/
theorem normalized_gap_le_literalDecay (table : CheckedBlockTable)
    (a b : ℤ) (hb : 0 < b) (h3 : 3 * b ≤ a) :
    upper ((a : ℝ) / (b : ℝ)) - lower ((a : ℝ) / (b : ℝ)) ≤
      value (literalDecay table a b) := by
  have hne := anchorIndices_nonempty h3
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf'
    (s := anchorIndices a b) hne (literalDecayTerm table a b)
  rw [literalDecay_eq_original_min table a b h3, he]
  exact normalized_gap_le_literalDecayTerm table a b k hb hk

theorem actual_gap_le_literalDecay (table : CheckedBlockTable)
    (a b : ℤ) (hb : 0 < b) (h3 : 3 * b ≤ a) :
    actualSieveGap ((a : ℝ) / (b : ℝ)) /
        (2 * Real.exp Real.eulerMascheroniConstant) ≤ value (literalDecay table a b) := by
  rw [← normalized_gap_eq_actualSieveGap_div]
  exact normalized_gap_le_literalDecay table a b hb h3

theorem literalDecay_nonneg (table : CheckedBlockTable)
    (a b : ℤ) (hb : 0 < b) (h3 : 3 * b ≤ a) :
    0 ≤ literalDecay table a b := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h3R : 3 ≤ (a : ℝ) / (b : ℝ) := by
    apply (le_div_iff₀ hbR).2
    exact_mod_cast h3
  have hg := normalized_gap_nonneg (by linarith : 2 ≤ (a : ℝ) / (b : ℝ))
  have hval := hg.trans (normalized_gap_le_literalDecay table a b hb h3)
  apply value_le_iff.mp
  simpa only [value_zero] using hval

end
end ImbalancedChen.P4AOriginalAnchorDecay20261024zSourceOnly
