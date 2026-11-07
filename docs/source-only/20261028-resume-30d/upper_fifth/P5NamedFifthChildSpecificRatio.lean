import ImbalancedChen.P5NamedFifthAllChildren

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The exact two-plane, 32-vertex ratio maxima for ALL 128 actual children.
For these literal mask28 boxes both plane residual ratios are maximized
at the same lower vertex. Real whole-child bounds are proved directly
from positive denominators and coordinate order, not sampled vertices.
The finite statements below are theorem source for later kernel execution;
no checker or numerical total has been run.
-/
namespace ImbalancedChen.P5NamedFifthChildSpecificRatio

open scoped BigOperators
open P5NamedFifthPayloadSemantics P5NamedFifthAllChildren
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord P5OldFifthFiveCoordinateTree
open P5OldFifthChildGapIntegral P5OldFifthPointwiseQ

def qLeft (b : Bool) (c : ChildIndex) (i : Fin 5) : ℚ :=
  (childLeftNumer (namedParent b) c i : ℚ) / 1600

def planeARatioQ (t : Fin 5 → ℚ) : ℚ :=
  (1 / 2 - t 0 - t 1 - (t 2 + t 3 + t 4) / 2) / t 4

def planeCRatioQ (t : Fin 5 → ℚ) : ℚ :=
  (57 / 64 - t 0 - t 1 - 5 * (t 2 + t 3 + t 4) / 2) / t 4

def vertexMaxAQ (b : Bool) (c : ChildIndex) : ℚ :=
  maxQ (Finset.univ : Finset Word)
    (fun w => planeARatioQ (childVertexQ (namedParent b) c (wordChoice w))) 0

def vertexMaxCQ (b : Bool) (c : ChildIndex) : ℚ :=
  maxQ (Finset.univ : Finset Word)
    (fun w => planeCRatioQ (childVertexQ (namedParent b) c (wordChoice w))) 0

/-- The producer's improved b_C=min(max A-residual,max C-residual).
Its canonical rational representation is the exact reduced A/B. -/
def childBQ (b : Bool) (c : ChildIndex) : ℚ :=
  min (planeARatioQ (qLeft b c)) (planeCRatioQ (qLeft b c))

def childEQ (b : Bool) (c : ChildIndex) : ℚ :=
  (sourceChildD (namedParent b) c : ℚ) /
    (1024 * (childRightNumer (namedParent b) c 4 : ℚ))

/-- ALL actual children, with actual two-plane residuals at actual vertices.
The zero seed is harmless because the attained lower-vertex maxima are positive. -/
theorem all_vertex_maxima_at_lower :
    ∀ b : Bool, ∀ c : ChildIndex,
      vertexMaxAQ b c = planeARatioQ (qLeft b c) ∧
      vertexMaxCQ b c = planeCRatioQ (qLeft b c) := by
  decide

theorem all_plane_maxima_nonneg :
    ∀ b : Bool, ∀ c : ChildIndex,
      0 ≤ planeARatioQ (qLeft b c) ∧ 0 ≤ planeCRatioQ (qLeft b c) := by
  decide

/-- The improved value has the paper's strict domain on every actual child.
It never worsens the original parent's bound. -/
theorem all_child_ratio_ranges :
    ∀ b : Bool, ∀ c : ChildIndex,
      2 < childBQ b c ∧ childBQ b c ≤
        ((namedParent b).ratioA : ℚ) / ((namedParent b).ratioB : ℚ) ∧ childBQ b c ≤ 4 := by
  decide

/-- These are actual-data e-domain obligations, not assumed Jensen bounds. -/
theorem all_active_e_ranges :
    ∀ b : Bool, ∀ c : ChildIndex,
      0 ≤ sourceChildD (namedParent b) c →
        0 ≤ childEQ b c ∧ childEQ b c ≤ childBQ b c - 2 := by
  decide

theorem childBQ_eq_producer_minmax (b : Bool) (c : ChildIndex) :
    childBQ b c = min (vertexMaxAQ b c) (vertexMaxCQ b c) := by
  rw [(all_vertex_maxima_at_lower b c).1, (all_vertex_maxima_at_lower b c).2]
  rfl

noncomputable section
open Set
open scoped Classical

theorem cast_qLeft (b : Bool) (c : ChildIndex) (i : Fin 5) :
    (qLeft b c i : ℝ) = childLeft (namedParent b) c i := by
  simp [qLeft, childLeft]

theorem childEQ_eq_actual_scale (b : Bool) (c : ChildIndex) :
    (childEQ b c : ℝ) = (sourceChildD (namedParent b) c : ℝ) /
      (1024 * 1600 * childRight (namedParent b) c 4) := by
  simp [childEQ, childRight]
  ring

private theorem selected_sum_28 (b : Bool) (t : Fin 5 → ℝ) :
    (∑ i ∈ maskSlots 5 (namedParent b).mask.toNat, t i) = t 2 + t 3 + t 4 := by
  have hm : maskSlots 5 (namedParent b).mask.toNat = {2, 3, 4} := by
    cases b <;> decide
  rw [hm]
  simp

private theorem A_minus_sum (b : Bool) (t : Fin 5 → ℝ) :
    VariableEnvelope.A (∑ i ∈ maskSlots 5 (namedParent b).mask.toNat, t i) - sum5 t =
      1 / 2 - t 0 - t 1 - (t 2 + t 3 + t 4) / 2 := by
  rw [selected_sum_28]
  simp [VariableEnvelope.A, sum5, Fin.sum_univ_succ]
  ring

private theorem C_minus_sum (b : Bool) (t : Fin 5 → ℝ) :
    VariableEnvelope.C (∑ i ∈ maskSlots 5 (namedParent b).mask.toNat, t i) - sum5 t =
      57 / 64 - t 0 - t 1 - 5 * (t 2 + t 3 + t 4) / 2 := by
  rw [selected_sum_28]
  simp [VariableEnvelope.C, sum5, Fin.sum_univ_succ]
  ring

/-- The actual linear-fractional expression is decreasing on the positive
orthant above its lower corner, with the checked nonnegative endpoint ratio. -/
private theorem ratio_le_lower (L t : Fin 5 → ℝ) (α k B : ℝ)
    (hL : 0 < L 4) (ht : ∀ i, L i ≤ t i)
    (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hdef : B = (α - L 0 - L 1 - k * (L 2 + L 3 + L 4)) / L 4) :
    (α - t 0 - t 1 - k * (t 2 + t 3 + t 4)) / t 4 ≤ B := by
  have ht4 : 0 < t 4 := hL.trans_le (ht 4)
  apply (div_le_iff₀ ht4).mpr
  have hid : B * L 4 = α - L 0 - L 1 - k * (L 2 + L 3 + L 4) := by
    rw [hdef, div_mul_cancel₀ _ hL.ne']
  have hlast := mul_le_mul_of_nonneg_left (ht 4) (add_nonneg hB hk)
  have h2 := mul_le_mul_of_nonneg_left (ht 2) hk
  have h3 := mul_le_mul_of_nonneg_left (ht 3) hk
  nlinarith [ht 0, ht 1]

/-- Genuine whole-closed-child inequality for the improved b_C, not an
assumed vertex-extremum principle or the inherited parent ratio. -/
theorem actual_child_new_ratio (b : Bool) (c : ChildIndex) (t : Fin 5 → ℝ)
    (ht : t ∈ Icc (childLeft (namedParent b) c) (childRight (namedParent b) c)) :
    residual (rawCandidate 0 (namedParent b) t) t ≤ (childBQ b c : ℝ) := by
  let L := childLeft (namedParent b) c
  have hL : 0 < L 4 := named_childLeft_pos b c 4
  have ht4 : 0 < t 4 := hL.trans_le (ht.1 4)
  have hA0 : (0 : ℝ) ≤ (planeARatioQ (qLeft b c) : ℝ) :=
    Rat.cast_nonneg.mpr (all_plane_maxima_nonneg b c).1
  have hC0 : (0 : ℝ) ≤ (planeCRatioQ (qLeft b c) : ℝ) :=
    Rat.cast_nonneg.mpr (all_plane_maxima_nonneg b c).2
  have hAdef : (planeARatioQ (qLeft b c) : ℝ) =
      (1 / 2 - L 0 - L 1 - (1 / 2 : ℝ) * (L 2 + L 3 + L 4)) / L 4 := by
    simp [planeARatioQ, cast_qLeft, L]
    ring
  have hCdef : (planeCRatioQ (qLeft b c) : ℝ) =
      (57 / 64 - L 0 - L 1 - (5 / 2 : ℝ) * (L 2 + L 3 + L 4)) / L 4 := by
    simp [planeCRatioQ, cast_qLeft, L]
    ring
  have hA := ratio_le_lower L t (1 / 2) (1 / 2)
    (planeARatioQ (qLeft b c)) hL ht.1 (by norm_num) hA0 hAdef
  have hC := ratio_le_lower L t (57 / 64) (5 / 2)
    (planeCRatioQ (qLeft b c)) hL ht.1 (by norm_num) hC0 hCdef
  have hcapA : rawCandidate 0 (namedParent b) t ≤
      VariableEnvelope.A (∑ i ∈ maskSlots 5 (namedParent b).mask.toNat, t i) := by
    simp only [rawCandidate, mul_zero, sub_zero, VariableEnvelope.v_eq_min]
    exact min_le_left _ _
  have hcapC : rawCandidate 0 (namedParent b) t ≤
      VariableEnvelope.C (∑ i ∈ maskSlots 5 (namedParent b).mask.toNat, t i) := by
    simp only [rawCandidate, mul_zero, sub_zero, VariableEnvelope.v_eq_min]
    exact min_le_right _ _
  rw [childBQ, Rat.cast_min]
  apply le_min
  · have h := div_le_div_of_nonneg_right (sub_le_sub_right hcapA (sum5 t)) ht4.le
    rw [A_minus_sum] at h
    exact h.trans (by convert hA using 1 <;> ring)
  · have h := div_le_div_of_nonneg_right (sub_le_sub_right hcapC (sum5 t)) ht4.le
    rw [C_minus_sum] at h
    exact h.trans (by convert hC using 1 <;> ring)

end
end ImbalancedChen.P5NamedFifthChildSpecificRatio
