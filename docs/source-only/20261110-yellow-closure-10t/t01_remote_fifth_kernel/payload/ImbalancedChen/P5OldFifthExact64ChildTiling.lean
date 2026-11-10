import ImbalancedChen.P1FifthUnitBoxLiteralGainLower

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED / ZERO FORMAL CREDIT.

The exact saved subdivision (2,2,2,2,4) of a grid400 FifthWireRow
uses grid1600 child lower numerators 4*lo_i + width_i*digit_i,
with widths (2,2,2,2,1). This file proves a half-open 64-child tiling
of one real originalBox and additivity of the actual literalRawKernel
integral after clipping EVERY child by the same original fullCell.

No floor numerator, child enclosure, saved archive row identity, selected
owner list identity, or numerical gain is asserted here.
-/

namespace ImbalancedChen.P5OldFifthExact64ChildTiling

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1FifthUnitBoxGainDecomposition
open P1FifthUnitBoxLiteralGainLower

abbrev Point := Fin 5 → ℝ

/-- Original Python product has two choices in slots 0..3 and four in slot 4. -/
def divisions (i : Fin 5) : ℕ := if i.val < 4 then 2 else 4
def width (i : Fin 5) : ℕ := if i.val < 4 then 2 else 1
abbrev ChildIndex := (i : Fin 5) → Fin (divisions i)

theorem width_mul_divisions (i : Fin 5) : width i * divisions i = 4 := by
  fin_cases i <;> decide

theorem childIndex_card : Fintype.card ChildIndex = 64 := by decide

/-- This is exactly the numerator used by the grid1600 script. -/
def childLeftNumer (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℤ :=
  4 * raw.lo i + (width i : ℤ) * ((c i).val : ℤ)

def childRightNumer (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℤ :=
  childLeftNumer raw c i + (width i : ℤ)

def childBox (raw : FifthWireRow) (c : ChildIndex) : Set Point :=
  {t | ∀ i : Fin 5,
    (childLeftNumer raw c i : ℝ) / 1600 ≤ t i ∧
      t i < (childRightNumer raw c i : ℝ) / 1600}

def childOwnerDomain (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) : Set Point :=
  childBox raw c ∩ P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j

private def scaled (raw : FifthWireRow) (t : Point) (i : Fin 5) : ℝ :=
  1600 * t i - 4 * (raw.lo i : ℝ)

private theorem cast_childLeftNumer (raw : FifthWireRow) (c : ChildIndex)
    (i : Fin 5) :
    (childLeftNumer raw c i : ℝ) =
      4 * (raw.lo i : ℝ) + (width i : ℝ) * ((c i).val : ℝ) := by
  simp [childLeftNumer]

private theorem cast_childRightNumer (raw : FifthWireRow) (c : ChildIndex)
    (i : Fin 5) :
    (childRightNumer raw c i : ℝ) =
      4 * (raw.lo i : ℝ) + (width i : ℝ) * (((c i).val : ℝ) + 1) := by
  rw [childRightNumer, Int.cast_add, cast_childLeftNumer]
  push_cast
  ring

theorem mem_childBox_iff_scaled (raw : FifthWireRow) (c : ChildIndex)
    (t : Point) :
    t ∈ childBox raw c ↔
      ∀ i : Fin 5,
        (width i : ℝ) * ((c i).val : ℝ) ≤ scaled raw t i ∧
          scaled raw t i <
            (width i : ℝ) * (((c i).val : ℝ) + 1) := by
  constructor
  · intro ht i
    have hi := ht i
    rw [cast_childLeftNumer, cast_childRightNumer] at hi
    dsimp [scaled]
    constructor <;> linarith
  · intro ht i
    have hi := ht i
    rw [cast_childLeftNumer, cast_childRightNumer]
    dsimp [scaled] at hi
    constructor <;> linarith

theorem mem_parent_iff_scaled (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (t : Point) :
    t ∈ raw.originalBox ↔
      ∀ i : Fin 5, 0 ≤ scaled raw t i ∧ scaled raw t i < 4 := by
  constructor
  · intro ht i
    have hi : (raw.lo i : ℝ) / 400 ≤ t i ∧
        t i < ((raw.lo i : ℝ) + 1) / 400 := by
      simpa [FifthWireRow.lower, FifthWireRow.upper, hgrid] using ht i
    dsimp [scaled]
    constructor <;> linarith
  · intro ht i
    have hi := ht i
    have hcoord : (raw.lo i : ℝ) / 400 ≤ t i ∧
        t i < ((raw.lo i : ℝ) + 1) / 400 := by
      dsimp [scaled] at hi
      constructor <;> linarith
    simpa [FifthWireRow.lower, FifthWireRow.upper, hgrid] using hcoord

/-- Two and four half-open pieces, including an exact choice at every cut. -/
private theorem binary_cover (u : ℝ) (hu : 0 ≤ u ∧ u < 4) :
    ∃ d : Fin 2, 2 * (d.val : ℝ) ≤ u ∧ u < 2 * ((d.val : ℝ) + 1) := by
  by_cases h : u < 2
  · refine ⟨0, ?_⟩
    simpa using (show 0 ≤ u ∧ u < 2 from ⟨hu.1, h⟩)
  · refine ⟨1, ?_⟩
    simpa using (show 2 ≤ u ∧ u < 4 from ⟨le_of_not_gt h, hu.2⟩)

private theorem quartic_cover (u : ℝ) (hu : 0 ≤ u ∧ u < 4) :
    ∃ d : Fin 4, (d.val : ℝ) ≤ u ∧ u < (d.val : ℝ) + 1 := by
  by_cases h1 : u < 1
  · refine ⟨0, ?_⟩
    simpa using (show 0 ≤ u ∧ u < 1 from ⟨hu.1, h1⟩)
  by_cases h2 : u < 2
  · refine ⟨1, ?_⟩
    simpa using (show 1 ≤ u ∧ u < 2 from ⟨le_of_not_gt h1, h2⟩)
  by_cases h3 : u < 3
  · refine ⟨2, ?_⟩
    simpa using (show 2 ≤ u ∧ u < 3 from ⟨le_of_not_gt h2, h3⟩)
  · refine ⟨3, ?_⟩
    simpa using (show 3 ≤ u ∧ u < 4 from ⟨le_of_not_gt h3, hu.2⟩)

theorem parent_covered_by_child (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (t : Point) (ht : t ∈ raw.originalBox) :
    ∃ c : ChildIndex, t ∈ childBox raw c := by
  have hp := (mem_parent_iff_scaled raw hgrid t).mp ht
  have hcoord : ∀ i : Fin 5, ∃ d : Fin (divisions i),
      (width i : ℝ) * (d.val : ℝ) ≤ scaled raw t i ∧
        scaled raw t i < (width i : ℝ) * ((d.val : ℝ) + 1) := by
    intro i
    by_cases hi : i.val < 4
    · simpa [divisions, width, hi] using binary_cover (scaled raw t i) (hp i)
    · simpa [divisions, width, hi] using quartic_cover (scaled raw t i) (hp i)
  classical
  choose c hc using hcoord
  exact ⟨c, (mem_childBox_iff_scaled raw c t).mpr hc⟩

theorem child_subset_parent (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (c : ChildIndex) : childBox raw c ⊆ raw.originalBox := by
  intro t ht
  apply (mem_parent_iff_scaled raw hgrid t).mpr
  have hc := (mem_childBox_iff_scaled raw c t).mp ht
  intro i
  have hi := hc i
  by_cases hslot : i.val < 4
  · have hd : (c i).val < 2 := by simpa [divisions, hslot] using (c i).isLt
    have hdR : ((c i).val : ℝ) ≤ 1 := by exact_mod_cast (show (c i).val ≤ 1 by omega)
    simp only [width, if_pos hslot] at hi
    constructor
    · nlinarith
    · nlinarith
  · have hd : (c i).val < 4 := by simpa [divisions, hslot] using (c i).isLt
    have hdR : ((c i).val : ℝ) ≤ 3 := by exact_mod_cast (show (c i).val ≤ 3 by omega)
    simp only [width, if_neg hslot] at hi
    constructor
    · nlinarith
    · nlinarith

theorem common_child_point_eq (raw : FifthWireRow) (a b : ChildIndex)
    (t : Point) (ha : t ∈ childBox raw a) (hb : t ∈ childBox raw b) : a = b := by
  funext i
  have hai := (mem_childBox_iff_scaled raw a t).mp ha i
  have hbi := (mem_childBox_iff_scaled raw b t).mp hb i
  by_cases hslot : i.val < 4
  · simp only [width, if_pos hslot] at hai hbi
    have habR : ((a i).val : ℝ) < ((b i).val : ℝ) + 1 := by nlinarith
    have hbaR : ((b i).val : ℝ) < ((a i).val : ℝ) + 1 := by nlinarith
    have habN : (a i).val < (b i).val + 1 := by exact_mod_cast habR
    have hbaN : (b i).val < (a i).val + 1 := by exact_mod_cast hbaR
    apply Fin.ext
    omega
  · simp only [width, if_neg hslot] at hai hbi
    have habR : ((a i).val : ℝ) < ((b i).val : ℝ) + 1 := by linarith
    have hbaR : ((b i).val : ℝ) < ((a i).val : ℝ) + 1 := by linarith
    have habN : (a i).val < (b i).val + 1 := by exact_mod_cast habR
    have hbaN : (b i).val < (a i).val + 1 := by exact_mod_cast hbaR
    apply Fin.ext
    omega

theorem children_pairwise_disjoint (raw : FifthWireRow) :
    Set.PairwiseDisjoint (Set.univ : Set ChildIndex) (childBox raw) := by
  intro a _ b _ hne
  apply Set.disjoint_left.mpr
  intro t ha hb
  exact hne (common_child_point_eq raw a b t ha hb)

theorem parent_eq_union_children (raw : FifthWireRow) (hgrid : raw.grid = 400) :
    raw.originalBox = ⋃ c ∈ (Finset.univ : Finset ChildIndex), childBox raw c := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc⟩ := parent_covered_by_child raw hgrid t ht
    exact mem_iUnion₂.mpr ⟨c, Finset.mem_univ _, hc⟩
  · intro ht
    obtain ⟨c, _hc, hpoint⟩ := mem_iUnion₂.mp ht
    exact child_subset_parent raw hgrid c hpoint

theorem childBox_measurable (raw : FifthWireRow) (c : ChildIndex) :
    MeasurableSet (childBox raw c) := by
  have heq : childBox raw c =
      logPrimeBox (fun i => (childLeftNumer raw c i : ℝ) / 1600)
        (fun i => (childRightNumer raw c i : ℝ) / 1600) := by
    ext t
    exact mem_logPrimeBox.symm
  rw [heq]
  exact measurableSet_logPrimeBox _ _

theorem childOwnerDomain_measurable (raw : FifthWireRow) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) :
    MeasurableSet (childOwnerDomain raw c e chi m omega j) :=
  (childBox_measurable raw c).inter
    (P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j)

theorem childOwnerDomain_subset_rawOwner (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (c : ChildIndex)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) :
    childOwnerDomain raw c e chi m omega j ⊆
      rawOwnerDomain raw e chi m omega j := by
  intro t ht
  exact ⟨child_subset_parent raw hgrid c ht.1, ht.2⟩

theorem rawOwnerDomain_eq_union_children (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (j : Fin 5 → Fin (m + 1)) :
    rawOwnerDomain raw e chi m omega j =
      ⋃ c ∈ (Finset.univ : Finset ChildIndex),
        childOwnerDomain raw c e chi m omega j := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc⟩ := parent_covered_by_child raw hgrid t ht.1
    exact mem_iUnion₂.mpr ⟨c, Finset.mem_univ _, ⟨hc, ht.2⟩⟩
  · intro ht
    obtain ⟨c, _hc, hpoint⟩ := mem_iUnion₂.mp ht
    exact childOwnerDomain_subset_rawOwner raw hgrid c e chi m omega j hpoint

theorem childOwnerDomains_pairwise_disjoint (raw : FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) :
    Set.PairwiseDisjoint (Set.univ : Set ChildIndex)
      (fun c => childOwnerDomain raw c e chi m omega j) := by
  intro a _ b _ hne
  exact ((children_pairwise_disjoint raw) (Set.mem_univ a) (Set.mem_univ b) hne).mono
    inter_subset_left inter_subset_left

/-- Exact additive decomposition of the ORIGINAL literal kernel on its
actual owner domain. The original source's compact integrability theorem
supplies each child integral; no floor or numerical value is inserted. -/
theorem literalRawOwnerIntegral_eq_sum_64_children (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) :
    literalRawOwnerIntegral raw e chi m omega j =
      ∑ c : ChildIndex,
        ∫ t in childOwnerDomain raw c e chi m omega j,
          literalRawKernel (e : ℝ) raw t := by
  unfold literalRawOwnerIntegral
  rw [rawOwnerDomain_eq_union_children raw hgrid]
  have hi := integrableOn_literalRawKernel_rawOwner raw hgrid hpositive
    e chi m omega j
  rw [integral_biUnion_finset (Finset.univ : Finset ChildIndex)
    (fun c _ => childOwnerDomain_measurable raw c e chi m omega j)
    (childOwnerDomains_pairwise_disjoint raw e chi m omega j)
    (fun c _ => hi.mono_set
      (childOwnerDomain_subset_rawOwner raw hgrid c e chi m omega j))]
  simp

end
end ImbalancedChen.P5OldFifthExact64ChildTiling
