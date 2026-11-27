import ImbalancedChen.P5OriginalWireParentPickAlignment
import ImbalancedChen.P5OriginalGenericWireFloorReceiver

/-! Original producer integer d is the SAME rational 32-vertex child sum.
This is algorithm algebra, with no SourceChildFacts or saved-d premise. -/
namespace ImbalancedChen.P5OriginalWireChildDIdentity

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1LiteralVariableFifthCompactSupplier (oldMasks)
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthExact64ChildTiling P5OldFifthChildGapIntegral
open P5OldFifthFiveCoordinateTree
open P5OriginalChildIntegerWireBinding
open P5NamedFifthPayloadSemantics P5NamedFifthAllChildren
open P5OriginalWireParentPickAlignment

private theorem wireWidth_eq_width (i : Fin 5) : wireWidth i = (width i : ℤ) := by
  fin_cases i <;> decide

private theorem wireLo_eq_childLeftNumer (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) :
    wireLo raw c i = childLeftNumer raw c i := by
  simp only [wireLo, childLeftNumer, wireWidth_eq_width]

private theorem vertexNumer_div (raw : FifthWireRow) (c : ChildIndex) (w : Word) :
    (fun i => (vertexNumer raw c w i : ℚ) / 1600) =
      childVertexQ raw c (wordChoice w) := by
  funext i
  have hright : wireLo raw c i + wireWidth i = childRightNumer raw c i :=
    P5OriginalGenericWireFloorReceiver.original_hi_eq_actual raw c i
  have hleft := wireLo_eq_childLeftNumer raw c i
  by_cases h : wordChoice w i
  · simpa only [vertexNumer, childVertexQ, if_pos h] using
      congrArg (fun z : ℤ => (z : ℚ) / 1600) hright
  · simpa only [vertexNumer, childVertexQ, if_neg h, add_zero] using
      congrArg (fun z : ℤ => (z : ℚ) / 1600) hleft

private theorem producerBits_map_sum {α : Type*} [AddCommMonoid α] (f : Word → α) :
    (producerBits.map f).sum = ∑ w : Word, f w := by
  simp [producerBits, Fintype.sum_prod_type, Fintype.sum_bool]
  <;> ac_rfl

private theorem oldMasks_eq_image :
    oldMasks = (Finset.range 15).image (fun k => maskSlots 4 (k + 1)) := by
  decide +kernel

private theorem cast_sum_div {ι : Type*} (S : Finset ι) (v : ι → ℤ) :
    ((∑ i ∈ S, v i : ℤ) : ℚ) / 1600 = ∑ i ∈ S, (v i : ℚ) / 1600 := by
  simp [Finset.sum_div]

private theorem planeNumer_cast (pick : Fin 3) (ss : ℤ) :
    (oldPlaneNumer pick ss : ℚ) = 51200 * planeQ pick ((ss : ℚ) / 1600) := by
  fin_cases pick <;> norm_num [oldPlaneNumer, planeQ] <;> ring

private theorem maxQ_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (f : κ → ℚ) (a : ℚ) :
    maxQ (S.image g) f a = maxQ S (fun i => f (g i)) a := by
  simp only [maxQ, valuesQ, Finset.image_image, Function.comp_def]

/-- Only attained maximum operands and positive scaling are used.
No rational-image enumeration or sorting is performed. -/
private theorem maxQ_scaled_lift {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (fz : ι → ℤ) (fq : ι → ℚ) (az : ℤ) (aq k : ℚ)
    (hk : 0 ≤ k) (ha : (az : ℚ) = k * aq)
    (hf : ∀ i ∈ S, (fz i : ℚ) = k * fq i) :
    (((insert az (S.image fz)).max' ⟨az, Finset.mem_insert_self _ _⟩ : ℤ) : ℚ) =
      k * maxQ S fq aq := by
  let M : ℤ := (insert az (S.image fz)).max' ⟨az, Finset.mem_insert_self _ _⟩
  let q : ℚ := maxQ S fq aq
  change (M : ℚ) = k * q
  have hM : M ∈ insert az (S.image fz) := Finset.max'_mem _ _
  have hq : q ∈ insert aq (S.image fq) := Finset.max'_mem _ _
  have hza : az ≤ M := Finset.le_max' _ az (Finset.mem_insert_self _ _)
  have hzf (i : ι) (hi : i ∈ S) : fz i ≤ M :=
    Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hqa : aq ≤ q := Finset.le_max' _ aq (Finset.mem_insert_self _ _)
  have hqf (i : ι) (hi : i ∈ S) : fq i ≤ q :=
    Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  apply le_antisymm
  · rcases Finset.mem_insert.mp hM with he | he
    · rw [he, ha]
      exact mul_le_mul_of_nonneg_left hqa hk
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp he
      rw [← he, hf i hi]
      exact mul_le_mul_of_nonneg_left (hqf i hi) hk
  · rcases Finset.mem_insert.mp hq with he | he
    · rw [he, ← ha]
      exact Int.cast_le.mpr hza
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp he
      rw [← he, ← hf i hi]
      exact Int.cast_le.mpr (hzf i hi)

private theorem oldNumer_cast (raw : FifthWireRow) (hg : raw.grid = 400)
    (v : Fin 5 → ℤ) :
    (oldNumer raw v : ℚ) =
      51200 * oldUpperQ raw (fun i => (v i : ℚ) / 1600) := by
  unfold oldNumer oldUpperQ
  dsimp only
  rw [oldMasks_eq_image, maxQ_image]
  apply maxQ_scaled_lift
  · norm_num
  · push_cast
    ring
  · intro k _
    rw [originalPick_eq_sourcePick raw hg, planeNumer_cast]
    simp only [cast_sum_div]

private theorem capNumer_cast (raw : FifthWireRow) (v : Fin 5 → ℤ) :
    (capNumer raw v : ℚ) = 51200 *
      min ((1 + ∑ i ∈ maskSlots 5 raw.mask.toNat, (v i : ℚ) / 1600) / 2)
        (57 / 64 - 3 * (∑ i ∈ maskSlots 5 raw.mask.toNat, (v i : ℚ) / 1600) / 2) := by
  unfold capNumer
  rw [Int.cast_min, mul_min_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 51200)]
  simp only [← cast_sum_div, selectedNumer]
  push_cast
  congr 1 <;> ring

private theorem gapNumer_cast (raw : FifthWireRow) (hg : raw.grid = 400)
    (v : Fin 5 → ℤ) :
    (gapNumer raw v : ℚ) =
      51200 * gapQ raw (fun i => (v i : ℚ) / 1600) := by
  have hown : ((32 * ((∑ i : Fin 5, v i) + 2 * v 4) : ℤ) : ℚ) =
      51200 * ((∑ i : Fin 5, (v i : ℚ) / 1600) + 2 * ((v 4 : ℚ) / 1600)) := by
    rw [← cast_sum_div]
    push_cast
    ring
  unfold gapNumer gapQ
  rw [Int.cast_sub, Int.cast_max, capNumer_cast, oldNumer_cast raw hg, hown]
  rw [mul_sub, mul_max_of_nonneg _ _ (by norm_num : (0 : ℚ) ≤ 51200)]

/-- Exact source integer algorithm identity, for arbitrary original mask and
signed data. SourceChildFacts and any saved-d equality are not premises. -/
theorem originalD_cast_eq_childDQ (raw : FifthWireRow) (hg : raw.grid = 400)
    (c : ChildIndex) : (originalD raw c : ℚ) = childDQ raw c := by
  unfold originalD
  calc
    _ = (producerBits.map (fun w => (gapNumer raw (vertexNumer raw c w) : ℚ))).sum := by simp [Function.comp_def]
    _ = ∑ w : Word, (gapNumer raw (vertexNumer raw c w) : ℚ) := producerBits_map_sum _
    _ = childDQ raw c := by
      unfold childDQ
      apply Finset.sum_congr rfl
      intro w _
      rw [gapNumer_cast raw hg, vertexNumer_div]
      norm_num

theorem originalFields_d_cast_eq_childDQ (raw : FifthWireRow) (hg : raw.grid = 400)
    (c : ChildIndex) : ((originalFields raw c).d : ℚ) = childDQ raw c :=
  originalD_cast_eq_childDQ raw hg c

theorem originalD_eq_sourceChildD (raw : FifthWireRow) (hg : raw.grid = 400)
    (c : ChildIndex) : originalD raw c = sourceChildD raw c := by
  unfold sourceChildD
  rw [← originalD_cast_eq_childDQ raw hg c]
  simp

theorem originalD_cast_eq_actual_vertexD (raw : FifthWireRow) (hg : raw.grid = 400)
    (c : ChildIndex) : (originalD raw c : ℝ) = vertexD (sourcePicks raw) raw c := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (originalD_cast_eq_childDQ raw hg c)
  simpa only [Rat.cast_intCast, cast_childDQ] using h

end ImbalancedChen.P5OriginalWireChildDIdentity
