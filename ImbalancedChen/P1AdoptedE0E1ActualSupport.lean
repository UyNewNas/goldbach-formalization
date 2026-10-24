import ImbalancedChen.Certificates.PairedV2FullMaskGeometry
import ImbalancedChen.CurrentChenPairedDeletion

/-!
SOURCE ONLY, 2026-10-24. This module has not been compiled or kernel replayed.

The original adopted witness is
verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json,
SHA256 f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7.
Its E0 labels are consecutive terminal u-strips. `e0FirstU` serializes their
actual first u-indices in the already existing FullMask strip order 326..511.
512 means that this strip has no E0 entry. The companion text-only provenance
check binds this data to the literal source labels, without numerical replay.

Two supports are deliberately provided. `fibre` uses the existing strict
four-dimensional integral fibres. `pairCell` uses lower-inclusive,
upper-exclusive outer rectangles, as required for exact arithmetic ownership.
No equality of these different-dimensional objects is asserted.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P1E0E1

open Set
open scoped BigOperators

/-- Literal E0 strip labels, with no gain, floor, or endpoint estimates. -/
def e0FirstU : Fin 186 → ℕ :=
  ![512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512, 512,
    510, 509, 507, 506, 504, 503, 501, 500, 498, 497, 495, 494,
    493, 491, 490, 488, 487, 485, 484, 482, 481, 479, 478, 476,
    475, 473, 472, 470, 469, 467, 466, 464, 463, 461, 460, 458,
    457, 455, 454, 452, 451, 450, 448, 447, 445, 444, 442, 441,
    439, 438, 436, 435, 433, 432, 430, 429, 427, 426, 424, 423,
    421, 420, 418, 417, 415, 414, 412, 411, 409, 408, 407, 405,
    404, 402, 401, 399, 398, 396, 395, 393, 392, 390, 389, 387,
    386, 384, 383, 381, 380, 378]

def IsE0 (r : Row) : Prop := e0FirstU r.1 ≤ (indices r).2

def IsE1 (r : Row) : Prop := (indices r).2 < e0FirstU r.1

theorem row_label_exhaustive (r : Row) : IsE0 r ∨ IsE1 r := by
  exact le_or_gt _ _

theorem row_labels_disjoint (r : Row) : ¬ (IsE0 r ∧ IsE1 r) := by
  intro h
  exact (not_lt_of_ge h.1) h.2

/-- The original strict integral fibre, with its original cutoff. -/
abbrev fibre (r : Row) : Set (Fin 4 → ℝ) := support r

def e0FibreRegion : Set (Fin 4 → ℝ) := {x | ∃ r : Row, IsE0 r ∧ x ∈ fibre r}

def e1FibreRegion : Set (Fin 4 → ℝ) := {x | ∃ r : Row, IsE1 r ∧ x ∈ fibre r}

theorem fibre_region_union : e0FibreRegion ∪ e1FibreRegion = region := by
  ext x
  constructor
  · rintro (⟨r, _, hr⟩ | ⟨r, _, hr⟩) <;>
      exact Set.mem_iUnion.mpr ⟨r, hr⟩
  · intro hx
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    rcases row_label_exhaustive r with h | h
    · exact Or.inl ⟨r, h, hr⟩
    · exact Or.inr ⟨r, h, hr⟩

theorem fibre_regions_disjoint : Disjoint e0FibreRegion e1FibreRegion := by
  apply Set.disjoint_left.mpr
  rintro x ⟨r, hr0, hxr⟩ ⟨s, hs1, hxs⟩
  have hrs : r = s := by
    by_contra hne
    exact Set.disjoint_left.mp (supports_pairwise_disjoint hne) hxr hxs
  subst s
  exact row_labels_disjoint r ⟨hr0, hs1⟩

/-- Exact arithmetic ownership of the outer (t,u) rectangle. -/
def pairCell (r : Row) : Set (ℝ × ℝ) :=
  {x | (tLower (indices r).1 : ℝ) ≤ x.1 ∧ x.1 < (tUpper (indices r).1 : ℝ) ∧
    (uLower (indices r).2 : ℝ) ≤ x.2 ∧ x.2 < (uUpper (indices r).2 : ℝ)}

theorem pairCell_unique_owner {r s : Row} {x : ℝ × ℝ}
    (hr : x ∈ pairCell r) (hs : x ∈ pairCell s) : r = s := by
  apply indices_injective
  apply Prod.ext
  · rcases lt_trichotomy (indices r).1 (indices s).1 with h | h | h
    · have hb : (tUpper (indices r).1 : ℝ) ≤ (tLower (indices s).1 : ℝ) :=
        Rat.cast_le.mpr (tUpper_le_tLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hs.1)) hr.2.1)
    · exact h
    · have hb : (tUpper (indices s).1 : ℝ) ≤ (tLower (indices r).1 : ℝ) :=
        Rat.cast_le.mpr (tUpper_le_tLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hr.1)) hs.2.1)
  · rcases lt_trichotomy (indices r).2 (indices s).2 with h | h | h
    · have hb : (uUpper (indices r).2 : ℝ) ≤ (uLower (indices s).2 : ℝ) :=
        Rat.cast_le.mpr (uUpper_le_uLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hs.2.2.1)) hr.2.2.2)
    · exact h
    · have hb : (uUpper (indices s).2 : ℝ) ≤ (uLower (indices r).2 : ℝ) :=
        Rat.cast_le.mpr (uUpper_le_uLower h)
      exact False.elim ((not_lt_of_ge (hb.trans hr.2.2.1)) hs.2.2.2)

theorem pairCells_pairwise_disjoint : Pairwise (fun r s => Disjoint (pairCell r) (pairCell s)) := by
  intro r s hne
  exact Set.disjoint_left.mpr (fun _ hr hs => hne (pairCell_unique_owner hr hs))

def pairRegion : Set (ℝ × ℝ) := {x | ∃ r : Row, x ∈ pairCell r}

def e0PairRegion : Set (ℝ × ℝ) := {x | ∃ r : Row, IsE0 r ∧ x ∈ pairCell r}

def e1PairRegion : Set (ℝ × ℝ) := {x | ∃ r : Row, IsE1 r ∧ x ∈ pairCell r}

theorem pair_region_unique_owner (x : ℝ × ℝ) :
    x ∈ pairRegion ↔ ∃! r : Row, x ∈ pairCell r := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, hr, fun s hs => pairCell_unique_owner hs hr⟩
  · rintro ⟨r, hr, _⟩
    exact ⟨r, hr⟩

theorem pair_region_union : e0PairRegion ∪ e1PairRegion = pairRegion := by
  ext x
  constructor
  · rintro (⟨r, _, hr⟩ | ⟨r, _, hr⟩) <;> exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    rcases row_label_exhaustive r with h | h
    · exact Or.inl ⟨r, h, hr⟩
    · exact Or.inr ⟨r, h, hr⟩

theorem pair_regions_disjoint : Disjoint e0PairRegion e1PairRegion := by
  apply Set.disjoint_left.mpr
  rintro x ⟨r, hr0, hxr⟩ ⟨s, hs1, hxs⟩
  have hrs : r = s := pairCell_unique_owner hxr hxs
  subst s
  exact row_labels_disjoint r ⟨hr0, hs1⟩

/-- A strict integral fibre projects into its exact arithmetic rectangle. -/
theorem fibre_mem_pairCell {r : Row} {x : Fin 4 → ℝ} (hx : x ∈ fibre r) :
    (x 0, x 1) ∈ pairCell r := by
  exact ⟨hx.1.le, hx.2.1, hx.2.2.1.le, hx.2.2.2.1⟩

theorem fibre_region_projects_pairRegion {x : Fin 4 → ℝ} (hx : x ∈ region) :
    (x 0, x 1) ∈ pairRegion := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  exact ⟨r, fibre_mem_pairCell hr⟩

/-- Literal prime values are increasing; outer coordinates are (larger,smaller). -/
noncomputable def primePairCoordinates (N : ℝ) (p : ℕ × ℕ) : ℝ × ℝ :=
  (Real.log (p.2 : ℝ) / Real.log N, Real.log (p.1 : ℝ) / Real.log N)

def deletionMask (N : ℝ) (p : ℕ × ℕ) : Prop := primePairCoordinates N p ∈ pairRegion

def e0DeletionMask (N : ℝ) (p : ℕ × ℕ) : Prop := primePairCoordinates N p ∈ e0PairRegion

def e1DeletionMask (N : ℝ) (p : ℕ × ℕ) : Prop := primePairCoordinates N p ∈ e1PairRegion

theorem deletionMask_iff (N : ℝ) (p : ℕ × ℕ) :
    deletionMask N p ↔ e0DeletionMask N p ∨ e1DeletionMask N p := by
  change primePairCoordinates N p ∈ pairRegion ↔
    primePairCoordinates N p ∈ e0PairRegion ∪ e1PairRegion
  rw [pair_region_union]

theorem deletionMasks_disjoint (N : ℝ) (p : ℕ × ℕ) :
    ¬ (e0DeletionMask N p ∧ e1DeletionMask N p) := by
  intro h
  exact Set.disjoint_left.mp pair_regions_disjoint h.1 h.2

/-- Pointwise support: there is a unique actual adopted grid rectangle. -/
theorem deletionMask_unique_owner (N : ℝ) (p : ℕ × ℕ) :
    deletionMask N p ↔ ∃! r : Row, primePairCoordinates N p ∈ pairCell r := by
  exact pair_region_unique_owner _

theorem deletion_indicator_split (N : ℝ) (p : ℕ × ℕ) (f : (ℕ × ℕ) → ℝ) :
    {q | deletionMask N q}.indicator f p =
      {q | e0DeletionMask N q}.indicator f p +
        {q | e1DeletionMask N q}.indicator f p := by
  classical
  by_cases h0 : e0DeletionMask N p
  · have h1 : ¬ e1DeletionMask N p := fun h => deletionMasks_disjoint N p ⟨h0, h⟩
    have h : deletionMask N p := (deletionMask_iff N p).2 (Or.inl h0)
    simp [h, h0, h1]
  · by_cases h1 : e1DeletionMask N p
    · have h : deletionMask N p := (deletionMask_iff N p).2 (Or.inr h1)
      simp [h, h0, h1]
    · have h : ¬ deletionMask N p := fun h => Or.elim ((deletionMask_iff N p).1 h) h0 h1
      simp [h, h0, h1]

/-- Exact pointwise row assembly on arithmetic supports. No almost-everywhere
boundary replacement, integral estimate, or geometric coverage assumption is used. -/
theorem deletion_indicator_eq_sum_rows (N : ℝ) (p : ℕ × ℕ) (f : (ℕ × ℕ) → ℝ) :
    {q | deletionMask N q}.indicator f p =
      ∑ r : Row, if primePairCoordinates N p ∈ pairCell r then f p else 0 := by
  classical
  by_cases h : deletionMask N p
  · obtain ⟨r, hr, huniq⟩ := (deletionMask_unique_owner N p).1 h
    rw [Set.indicator_of_mem h]
    symm
    calc
      (∑ s : Row, if primePairCoordinates N p ∈ pairCell s then f p else 0) =
          (if primePairCoordinates N p ∈ pairCell r then f p else 0) := by
        apply Finset.sum_eq_single r
        · intro s _ hsr
          have hs : primePairCoordinates N p ∉ pairCell s := fun hs => hsr (huniq s hs)
          exact if_neg hs
        · intro hrnot
          exact False.elim (hrnot (Finset.mem_univ r))
      _ = f p := if_pos hr
  · rw [Set.indicator_of_notMem h]
    symm
    apply Finset.sum_eq_zero
    intro r _
    have hr : primePairCoordinates N p ∉ pairCell r := by
      intro hr
      exact h ⟨r, hr⟩
    exact if_neg hr

/-- Actual Y6 support uses this same literal outer-pair mask. -/
theorem selectedY6_support (n : ℕ) (A H D N : ℝ) (p : ℕ × ℕ) :
    p ∈ chenY6SelectedTuples n A H D (deletionMask N) ↔
      p ∈ chenY6Tuples n A H D ∧
        ∃! r : Row, primePairCoordinates N p ∈ pairCell r := by
  rw [mem_chenY6SelectedTuples, deletionMask_unique_owner]

/-- Actual Y11 support applies precisely the same mask to the last pair. -/
theorem selectedY11_support (n : ℕ) (A H D N : ℝ)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) :
    p ∈ chenY11SelectedTuples n A H D (deletionMask N) ↔
      p ∈ chenY11FullTuples n A H D ∧
        ∃! r : Row, primePairCoordinates N p.2 ∈ pairCell r := by
  rw [mem_chenY11SelectedTuples, deletionMask_unique_owner]

theorem selectedY6_union (n : ℕ) (A H D N : ℝ) :
    chenY6SelectedTuples n A H D (deletionMask N) =
      chenY6SelectedTuples n A H D (e0DeletionMask N) ∪
        chenY6SelectedTuples n A H D (e1DeletionMask N) := by
  classical
  ext p
  simp only [mem_chenY6SelectedTuples, Finset.mem_union, deletionMask_iff]
  constructor
  · rintro ⟨hp, h0 | h1⟩
    · exact Or.inl ⟨hp, h0⟩
    · exact Or.inr ⟨hp, h1⟩
  · rintro (⟨hp, h0⟩ | ⟨hp, h1⟩)
    · exact ⟨hp, Or.inl h0⟩
    · exact ⟨hp, Or.inr h1⟩

theorem selectedY11_union (n : ℕ) (A H D N : ℝ) :
    chenY11SelectedTuples n A H D (deletionMask N) =
      chenY11SelectedTuples n A H D (e0DeletionMask N) ∪
        chenY11SelectedTuples n A H D (e1DeletionMask N) := by
  classical
  ext p
  simp only [mem_chenY11SelectedTuples, Finset.mem_union, deletionMask_iff]
  constructor
  · rintro ⟨hp, h0 | h1⟩
    · exact Or.inl ⟨hp, h0⟩
    · exact Or.inr ⟨hp, h1⟩
  · rintro (⟨hp, h0⟩ | ⟨hp, h1⟩)
    · exact ⟨hp, Or.inl h0⟩
    · exact ⟨hp, Or.inr h1⟩

theorem selectedY6_disjoint (n : ℕ) (A H D N : ℝ) :
    Disjoint (chenY6SelectedTuples n A H D (e0DeletionMask N))
      (chenY6SelectedTuples n A H D (e1DeletionMask N)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p h0 h1
  exact deletionMasks_disjoint N p
    ⟨(mem_chenY6SelectedTuples.mp h0).2, (mem_chenY6SelectedTuples.mp h1).2⟩

theorem selectedY11_disjoint (n : ℕ) (A H D N : ℝ) :
    Disjoint (chenY11SelectedTuples n A H D (e0DeletionMask N))
      (chenY11SelectedTuples n A H D (e1DeletionMask N)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p h0 h1
  exact deletionMasks_disjoint N p.2
    ⟨(mem_chenY11SelectedTuples.mp h0).2, (mem_chenY11SelectedTuples.mp h1).2⟩

theorem selectedY6_count_split (n : ℕ) (A H D N : ℝ) :
    chenY6Selected n A H D (deletionMask N) =
      chenY6Selected n A H D (e0DeletionMask N) +
        chenY6Selected n A H D (e1DeletionMask N) := by
  classical
  unfold chenY6Selected
  rw [selectedY6_union, Finset.card_union_of_disjoint (selectedY6_disjoint n A H D N)]

theorem selectedY11_count_split (n : ℕ) (A H D N : ℝ) :
    chenY11Selected n A H D (deletionMask N) =
      chenY11Selected n A H D (e0DeletionMask N) +
        chenY11Selected n A H D (e1DeletionMask N) := by
  classical
  unfold chenY11Selected
  rw [selectedY11_union, Finset.card_union_of_disjoint (selectedY11_disjoint n A H D N)]

/-- The concrete adopted arithmetic mask instantiates the existing pointwise theorem. -/
theorem currentPairedWeight_le_four_indicator {n : ℕ} {N : ℝ}
    (hN : 1 ≤ N) (hn : Squarefree n) (hnN : (n : ℝ) ≤ N) :
    currentChenPairedWeight n N (deletionMask N) ≤ if ArithmeticFunction.cardFactors n ≤ 2 then 4 else 0 := by
  exact currentChenPairedWeight_le_four_indicator hN hn hnN (deletionMask N)

end ImbalancedChen.Certificates.PairedV2.FullMask.P1E0E1
