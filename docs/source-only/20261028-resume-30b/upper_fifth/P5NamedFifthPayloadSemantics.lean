import ImbalancedChen.P1FifthNamedParentActualIntegral
import ImbalancedChen.P5OldFifthChildGapIntegral
import ImbalancedChen.P5OldFifthPointwiseQ

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
Exact payload-to-geometry binding for the two named grid400 parents.

Parent picks are derived once from the original parent midpoint, using
precisely the producer's ordered argmin of its A/C/global-cap scores.
They are held fixed on every grid1600 child. Rational vertex arithmetic
casts to the same real frozenGap used by the actual child integral.

The raw grid400 d fields and grid1600 child d fields have DIFFERENT
normalizations. In particular the all-zero child has d=29824/25152,
whereas the parent fields are 5984/5232. They are never interchanged.
No full adopted J5 or final K is inferred from this local binding.
-/

namespace ImbalancedChen.P5NamedFifthPayloadSemantics

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthExact64ChildTiling
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateTree
open P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ
open P1OriginalFifthRawBoxSelectorEquivalence
open P1OriginalVariableFourthContinuation
open P1LiteralVariableFifthCompactSupplier
open P5OldFifthFrozenGapConcavity

/-- The script uses center2=2*lo+1, with denominator 2*n. -/
def parentCenterQ (raw : FifthWireRow) (i : Fin 5) : ℚ :=
  (2 * (raw.lo i : ℚ) + 1) / (2 * (raw.grid : ℚ))

def parentSumQ (raw : FifthWireRow) (I : OldMask) : ℚ :=
  ∑ i ∈ I, parentCenterQ raw i.castSucc

def planeQ (pick : Fin 3) (s : ℚ) : ℚ :=
  if pick.val = 0 then (1 + s) / 2
  else if pick.val = 1 then 57 / 64 - 3 * s / 2
  else 153 / 256

/-- Ordered first argmin: A wins ties, then C, then the cap. This is the
same tie order as numpy.argmin on the source's three stacked scores. -/
def sourcePick (raw : FifthWireRow) (I : OldMask) : Fin 3 :=
  let s := parentSumQ raw I
  if (1 + s) / 2 ≤ 57 / 64 - 3 * s / 2 ∧
      (1 + s) / 2 ≤ 153 / 256 then 0
  else if 57 / 64 - 3 * s / 2 ≤ 153 / 256 then 1 else 2

/-- Producer picks are fixed at the parent, not recalculated on children. -/
def sourcePicks (raw : FifthWireRow) : ParentPicks := sourcePick raw

/-- The chosen parent plane really is the least of the three source scores. -/
theorem sourcePick_minimizes (raw : FifthWireRow) (I : OldMask) :
    planeQ (sourcePick raw I) (parentSumQ raw I) =
      min ((1 + parentSumQ raw I) / 2)
        (min (57 / 64 - 3 * parentSumQ raw I / 2) (153 / 256)) := by
  unfold sourcePick
  split_ifs with hA hC
  · simpa [planeQ] using (min_eq_left (le_min hA.1 hA.2)).symm
  · have hCA : 57 / 64 - 3 * parentSumQ raw I / 2 ≤
        (1 + parentSumQ raw I) / 2 := by
      by_contra hn
      have hAC : (1 + parentSumQ raw I) / 2 ≤
          57 / 64 - 3 * parentSumQ raw I / 2 := le_of_lt (lt_of_not_ge hn)
      exact hA ⟨hAC, hAC.trans hC⟩
    simp [planeQ, min_eq_left hC, min_eq_right hCA]
  · have hcapC : (153 / 256 : ℚ) ≤ 57 / 64 - 3 * parentSumQ raw I / 2 :=
      le_of_lt (lt_of_not_ge hC)
    have hcapA : (153 / 256 : ℚ) ≤ (1 + parentSumQ raw I) / 2 := by
      by_contra hn
      have hACap : (1 + parentSumQ raw I) / 2 ≤ (153 / 256 : ℚ) :=
        le_of_lt (lt_of_not_ge hn)
      exact hA ⟨hACap.trans hcapC, hACap⟩
    simp [planeQ, min_eq_right hcapC, min_eq_right hcapA]

/-- Multiplying these rational scores by the SAME positive 64*n
produces the literal integer candidate columns of parent_picks. -/
theorem parent_score_alignment (raw : FifthWireRow) (hg : raw.grid = 400)
    (I : OldMask) :
    let z : ℚ := ∑ i ∈ I, (2 * (raw.lo i.castSucc : ℚ) + 1)
    ((1 + parentSumQ raw I) / 2 = (32 * 400 + 16 * z) / (64 * 400)) ∧
    (57 / 64 - 3 * parentSumQ raw I / 2 = (57 * 400 - 48 * z) / (64 * 400)) ∧
    ((153 / 256 : ℚ) = (153 * 400 / 4) / (64 * 400)) := by
  dsimp only
  have hs : parentSumQ raw I =
      (∑ i ∈ I, (2 * (raw.lo i.castSucc : ℚ) + 1)) / 800 := by
    simp [parentSumQ, parentCenterQ, hg, Finset.sum_div]
  rw [hs]
  constructor
  · ring
  constructor <;> ring

def valuesQ {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℚ) (a : ℚ) : Finset ℚ := insert a (S.image f)

def maxQ {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℚ) (a : ℚ) : ℚ :=
  (valuesQ S f a).max' ⟨a, Finset.mem_insert_self _ _⟩

def oldUpperQ (raw : FifthWireRow) (t : Fin 5 → ℚ) : ℚ :=
  maxQ oldMasks (fun I => planeQ (sourcePick raw I)
    (∑ i ∈ I, t i.castSucc)) (153 / 256 - 3 * t 2 / 8)

def gapQ (raw : FifthWireRow) (t : Fin 5 → ℚ) : ℚ :=
  min ((1 + ∑ i ∈ maskSlots 5 raw.mask.toNat, t i) / 2)
      (57 / 64 - 3 * (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) / 2) -
    max (oldUpperQ raw t) ((∑ i : Fin 5, t i) + 2 * t 4)

def childVertexQ (raw : FifthWireRow) (c : ChildIndex)
    (ε : VertexChoice) (i : Fin 5) : ℚ :=
  if ε i then (childRightNumer raw c i : ℚ) / 1600
  else (childLeftNumer raw c i : ℚ) / 1600

def parentVertexQ (raw : FifthWireRow) (ε : VertexChoice) (i : Fin 5) : ℚ :=
  if ε i then raw.upper i else raw.lower i

/-- These are DIFFERENT producer scales. -/
def childDQ (raw : FifthWireRow) (c : ChildIndex) : ℚ :=
  ∑ w : Word, (32 * 1600 : ℚ) * gapQ raw (childVertexQ raw c (wordChoice w))

def parentDQ (raw : FifthWireRow) : ℚ :=
  ∑ w : Word, (32 * 400 : ℚ) * gapQ raw (parentVertexQ raw (wordChoice w))

def zeroChild : ChildIndex := fun i => ⟨0, by unfold divisions; split_ifs <;> omega⟩

/-- Literal finite rational computations, not assumed payload identities.
These small proof terms are written for compiler/kernel evaluation. -/
theorem parent0_saved_d : (selectedParent0.vertexGapSum : ℚ) = parentDQ selectedParent0 := by
  decide

theorem parent1_saved_d : (selectedParent1.vertexGapSum : ℚ) = parentDQ selectedParent1 := by
  decide

theorem parent0_zero_child_d : childDQ selectedParent0 zeroChild = 29824 := by
  decide

theorem parent1_zero_child_d : childDQ selectedParent1 zeroChild = 25152 := by
  decide

noncomputable section
open Set MeasureTheory
open scoped Classical

private theorem cast_planeQ (pick : Fin 3) (s : ℚ) :
    ((planeQ pick s : ℚ) : ℝ) = pickedUpperPlane pick (s : ℝ) := by
  fin_cases pick <;>
    simp [planeQ, pickedUpperPlane, VariableEnvelope.A,
      VariableEnvelope.C, VariableEnvelope.cap] <;> push_cast <;> ring

/-- Exact rational maximum cast; no floating point approximation. -/
theorem cast_maxQ {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℚ) (a : ℚ) :
    (maxQ S f a : ℝ) =
      finiteMax S (fun _ => True) (fun i => (f i : ℝ)) (a : ℝ) := by
  apply le_antisymm
  · have hm : maxQ S f a ∈ valuesQ S f a := Finset.max'_mem _ _
    rcases Finset.mem_insert.mp hm with ha | hf
    · rw [ha]
      exact finiteMax_seed_le S (fun _ => True) (fun i => (f i : ℝ)) (a : ℝ)
    · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hf
      rw [← heq]
      exact finiteMax_row_le S (fun _ => True) (fun i => (f i : ℝ)) (a : ℝ) i hi trivial
  · apply finiteMax_le
    · exact Rat.cast_le.mpr (Finset.le_max' _ a (Finset.mem_insert_self _ _))
    · intro i hi _
      exact Rat.cast_le.mpr (Finset.le_max' _ (f i)
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))

/-- Real vertex gap is the SAME parent-frozen source expression. -/
theorem cast_gapQ (raw : FifthWireRow) (t : Fin 5 → ℚ) :
    (gapQ raw t : ℝ) =
      frozenGap (sourcePicks raw) raw (fun i => (t i : ℝ)) := by
  have hC (s : ℝ) : 3 * s / 2 = (3 / 2 : ℝ) * s := by ring
  have hB (s : ℝ) : 3 * s / 8 = (3 / 8 : ℝ) * s := by ring
  unfold gapQ oldUpperQ
  push_cast
  rw [cast_maxQ]
  simp_rw [cast_planeQ]
  simp [frozenGap, frozenCeiling, frozenParentUpper, sourcePicks,
    rawCandidate, VariableEnvelope.v_eq_min, VariableEnvelope.A,
    VariableEnvelope.C, VariableEnvelope.B, VariableEnvelope.cap,
    ownCubeThreshold, oldSubsetSum, hC, hB]
  <;> ring

theorem cast_childVertexQ (raw : FifthWireRow) (c : ChildIndex)
    (ε : VertexChoice) :
    (fun i => (childVertexQ raw c ε i : ℝ)) = vertexPoint raw c ε := by
  funext i
  by_cases hi : ε i <;>
    simp [childVertexQ, vertexPoint, childLeft, childRight, hi]

/-- Discharge the Jensen theorem's actual hd guard from source geometry. -/
theorem cast_childDQ (raw : FifthWireRow) (c : ChildIndex) :
    (childDQ raw c : ℝ) = vertexD (sourcePicks raw) raw c := by
  unfold childDQ vertexD
  push_cast
  apply Finset.sum_congr rfl
  intro w _
  rw [cast_gapQ, cast_childVertexQ]

theorem parent0_actual_zero_child_hd :
    (29824 : ℝ) = vertexD (sourcePicks selectedParent0) selectedParent0 zeroChild := by
  rw [← cast_childDQ, parent0_zero_child_d]
  norm_num

theorem parent1_actual_zero_child_hd :
    (25152 : ℝ) = vertexD (sourcePicks selectedParent1) selectedParent1 zeroChild := by
  rw [← cast_childDQ, parent1_zero_child_d]
  norm_num

/-- Source ratio payload, kept distinct from the d-scale. -/
def savedRatio (raw : FifthWireRow) : ℝ := (raw.ratioA : ℝ) / (raw.ratioB : ℝ)

theorem parent0_ratio : savedRatio selectedParent0 = 4 := by
  norm_num [savedRatio, selectedParent0]

theorem parent1_ratio : savedRatio selectedParent1 = 399 / 100 := by
  norm_num [savedRatio, selectedParent1]

private theorem selected_sum_28 (raw : FifthWireRow) (hm : raw.mask = 28)
    (t : Fin 5 → ℝ) :
    (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) = t 2 + t 3 + t 4 := by
  have hmask : maskSlots 5 raw.mask.toNat = {2, 3, 4} := by
    rw [hm]
    decide
  rw [hmask]
  simp

/-- Every point above parent0's original lower endpoints obeys its
actual A-plane ratio bound; hence every genuine closed child does. -/
theorem parent0_new_ratio_of_lower (t : Fin 5 → ℝ)
    (ht : ∀ i, (selectedParent0.lower i : ℝ) ≤ t i) :
    residual (rawCandidate 0 selectedParent0 t) t ≤ savedRatio selectedParent0 := by
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  have h3 := ht 3
  have h4 := ht 4
  norm_num [selectedParent0, FifthWireRow.lower] at h0 h1 h2 h3 h4
  have ht4 : 0 < t 4 := by linarith
  rw [parent0_ratio]
  apply (div_le_iff₀ ht4).mpr
  have hcap : rawCandidate 0 selectedParent0 t ≤
      (1 + (t 2 + t 3 + t 4)) / 2 := by
    unfold rawCandidate
    rw [selected_sum_28 selectedParent0 rfl t, VariableEnvelope.v_eq_min]
    simpa [VariableEnvelope.A] using min_le_left
      (VariableEnvelope.A (t 2 + t 3 + t 4))
      (VariableEnvelope.C (t 2 + t 3 + t 4))
  simp [sum5, Fin.sum_univ_succ] at *
  linarith

/-- Parent1 uses the C-plane; this is why its archived A/B is 399/100. -/
theorem parent1_new_ratio_of_lower (t : Fin 5 → ℝ)
    (ht : ∀ i, (selectedParent1.lower i : ℝ) ≤ t i) :
    residual (rawCandidate 0 selectedParent1 t) t ≤ savedRatio selectedParent1 := by
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  have h3 := ht 3
  have h4 := ht 4
  norm_num [selectedParent1, FifthWireRow.lower] at h0 h1 h2 h3 h4
  have ht4 : 0 < t 4 := by linarith
  rw [parent1_ratio]
  apply (div_le_iff₀ ht4).mpr
  have hcap : rawCandidate 0 selectedParent1 t ≤
      57 / 64 - (3 / 2 : ℝ) * (t 2 + t 3 + t 4) := by
    unfold rawCandidate
    rw [selected_sum_28 selectedParent1 rfl t, VariableEnvelope.v_eq_min]
    simpa [VariableEnvelope.C] using min_le_right
      (VariableEnvelope.A (t 2 + t 3 + t 4))
      (VariableEnvelope.C (t 2 + t 3 + t 4))
  simp [sum5, Fin.sum_univ_succ] at *
  linarith

/-- Actual child lower endpoints lie above their original parent lower
endpoints; the same parent-frozen picks therefore apply without rechoice. -/
theorem childLeft_ge_parent_lower (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (c : ChildIndex) (i : Fin 5) :
    (raw.lower i : ℝ) ≤ childLeft raw c i := by
  have hnonneg : 0 ≤ (width i : ℝ) * ((c i).val : ℝ) := by positivity
  simp only [FifthWireRow.lower, childLeft, childLeftNumer, hgrid]
  push_cast
  linarith

theorem parent0_childLeft_pos (c : ChildIndex) (i : Fin 5) :
    0 < childLeft selectedParent0 c i := by
  have hlo : (0 : ℝ) < (selectedParent0.lower i : ℝ) := by
    fin_cases i <;> norm_num [selectedParent0, FifthWireRow.lower]
  exact hlo.trans_le (childLeft_ge_parent_lower selectedParent0 rfl c i)

theorem parent1_childLeft_pos (c : ChildIndex) (i : Fin 5) :
    0 < childLeft selectedParent1 c i := by
  have hlo : (0 : ℝ) < (selectedParent1.lower i : ℝ) := by
    fin_cases i <;> norm_num [selectedParent1, FifthWireRow.lower]
  exact hlo.trans_le (childLeft_ge_parent_lower selectedParent1 rfl c i)

theorem parent0_child_new_ratio (c : ChildIndex) (t : Fin 5 → ℝ)
    (ht : t ∈ Icc (childLeft selectedParent0 c) (childRight selectedParent0 c)) :
    residual (rawCandidate 0 selectedParent0 t) t ≤ savedRatio selectedParent0 :=
  parent0_new_ratio_of_lower t
    (fun i => (childLeft_ge_parent_lower selectedParent0 rfl c i).trans (ht.1 i))

theorem parent1_child_new_ratio (c : ChildIndex) (t : Fin 5 → ℝ)
    (ht : t ∈ Icc (childLeft selectedParent1 c) (childRight selectedParent1 c)) :
    residual (rawCandidate 0 selectedParent1 t) t ≤ savedRatio selectedParent1 :=
  parent1_new_ratio_of_lower t
    (fun i => (childLeft_ge_parent_lower selectedParent1 rfl c i).trans (ht.1 i))

/-- A concrete necessary Jensen input is now discharged, with the exact
actual d. Parent d=5984 is NOT reused at this grid1600 child. -/
theorem parent0_zero_child_gap_integral :
    childVolume selectedParent0 zeroChild * 29824 / (1024 * 1600) ≤
      ∫ t in childBox selectedParent0 zeroChild,
        frozenGap (sourcePicks selectedParent0) selectedParent0 t :=
  integral_frozenGap_ge_saved_integer_d (sourcePicks selectedParent0)
    selectedParent0 zeroChild 29824 parent0_actual_zero_child_hd

theorem parent1_zero_child_gap_integral :
    childVolume selectedParent1 zeroChild * 25152 / (1024 * 1600) ≤
      ∫ t in childBox selectedParent1 zeroChild,
        frozenGap (sourcePicks selectedParent1) selectedParent1 t :=
  integral_frozenGap_ge_saved_integer_d (sourcePicks selectedParent1)
    selectedParent1 zeroChild 25152 parent1_actual_zero_child_hd

end
end ImbalancedChen.P5NamedFifthPayloadSemantics
