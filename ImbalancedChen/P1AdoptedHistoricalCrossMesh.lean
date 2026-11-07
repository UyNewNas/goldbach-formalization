import ImbalancedChen.HistoricalJointMeshFiniteRefinement
import ImbalancedChen.P1AdoptedE0E1ActualSupport

/-!
The actual adopted pair512 outer rectangles and a historical five-dimensional
uniform mesh have an exact finite common refinement by intersection. The two
meshes need not have common endpoints. Pair ownership reads processing
coordinates zero and one; the increasing prime pair is therefore `(p 1,p 0)`.

This source uses the actual adopted `FullMask.Row` and `P1E0E1.pairCell`.
It does not identify a D cap with an adopted cap, or identify the strict
four-dimensional fibre with its half-open two-dimensional outer mask.
The exact full masked sum below retains the outside-D-cube term.

The first import is a sibling source-only module. The adopted-support import
is the eventual integration name for the separately owned source-only draft.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

open Certificates.PairedV2.FullMask

local notation "AdoptedRow" => Certificates.PairedV2.FullMask.Row
local notation "PairMask" => Certificates.PairedV2.FullMask.P1E0E1.pairRegion
local notation "PairCell" => Certificates.PairedV2.FullMask.P1E0E1.pairCell

/-- The first two processing coordinates, without reordering or sorting. -/
def adoptedCrossPair (t : Fin 5 → ℝ) : ℝ × ℝ := (t 0, t 1)

theorem adoptedCrossPair_actualTuple (N : ℕ) (p : Fin 5 → ℕ) :
    adoptedCrossPair (actualPrimeTupleLog N p) =
      Certificates.PairedV2.FullMask.P1E0E1.primePairCoordinates (N : ℝ) (p 1, p 0) := by
  rfl

/-- The genuine cross-grid intersection: no endpoint alignment is assumed. -/
def adoptedCrossCell (D : HistoricalPrefixCapData) (r : AdoptedRow)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  {t | t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
    adoptedCrossPair t ∈ PairCell r}

theorem adoptedCrossCell_eq_inter (D : HistoricalPrefixCapData) (r : AdoptedRow)
    (j : Fin 5 → Fin (D.m + 1)) :
    D.adoptedCrossCell r j = logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
      adoptedCrossPair ⁻¹' PairCell r := by
  rfl

def adoptedCrossLabels (D : HistoricalPrefixCapData) :
    Finset (AdoptedRow × (Fin 5 → Fin (D.m + 1))) :=
  Finset.univ.product (D.jointMeshCells 5)

def adoptedCrossRegion (D : HistoricalPrefixCapData) : Set (Fin 5 → ℝ) :=
  {t | t ∈ logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ)) ∧
    adoptedCrossPair t ∈ PairMask}

@[simp] theorem mem_adoptedCrossLabels (D : HistoricalPrefixCapData)
    (k : AdoptedRow × (Fin 5 → Fin (D.m + 1))) : k ∈ D.adoptedCrossLabels := by
  simp [adoptedCrossLabels, jointMeshCells]

theorem adoptedCrossCell_unique (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    {k l : AdoptedRow × (Fin 5 → Fin (D.m + 1))} {t : Fin 5 → ℝ}
    (hk : t ∈ D.adoptedCrossCell k.1 k.2)
    (hl : t ∈ D.adoptedCrossCell l.1 l.2) : k = l := by
  apply Prod.ext
  · exact Certificates.PairedV2.FullMask.P1E0E1.pairCell_unique_owner hk.2 hl.2
  · exact logPrimeMeshCell_unique (by exact_mod_cast hab) hk.1 hl.1

theorem adoptedCrossCells_pairwise_disjoint (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) :
    Pairwise (fun k l : AdoptedRow × (Fin 5 → Fin (D.m + 1)) =>
      Disjoint (D.adoptedCrossCell k.1 k.2) (D.adoptedCrossCell l.1 l.2)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro t hk hl
  exact hkl (D.adoptedCrossCell_unique hab hk hl)

theorem adoptedCrossRegion_unique_owner (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (t : Fin 5 → ℝ) :
    t ∈ D.adoptedCrossRegion ↔
      ∃! k : AdoptedRow × (Fin 5 → Fin (D.m + 1)),
        k ∈ D.adoptedCrossLabels ∧ t ∈ D.adoptedCrossCell k.1 k.2 := by
  constructor
  · rintro ⟨ht, r, hr⟩
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m ht
    refine ⟨(r, j), ⟨D.mem_adoptedCrossLabels _, hj, hr⟩, ?_⟩
    intro k hk
    exact D.adoptedCrossCell_unique hab.le hk.2 ⟨hj, hr⟩
  · rintro ⟨k, ⟨_, ht, hr⟩, _⟩
    exact ⟨logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m k.2 ht,
      k.1, hr⟩

theorem adoptedCrossRegion_eq_union (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) :
    D.adoptedCrossRegion =
      ⋃ r : AdoptedRow, ⋃ j ∈ D.jointMeshCells 5, D.adoptedCrossCell r j := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · intro ht
    obtain ⟨k, hk, _⟩ := (D.adoptedCrossRegion_unique_owner hab t).mp ht
    exact ⟨k.1, k.2, D.mem_jointMeshCells 5 _, hk.2⟩
  · rintro ⟨r, j, _, ht, hr⟩
    exact ⟨logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht, r, hr⟩

/-- Cross refinement does not change the D lookup or choose a row cap. -/
theorem exponent5_on_adoptedCrossCell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (r : AdoptedRow) (j : Fin 5 → Fin (D.m + 1))
    (t : Fin 5 → ℝ) (ht : t ∈ D.adoptedCrossCell r j) :
    D.exponent5 t = D.cell5 j := by
  exact D.exponent5_on_cell hab t j ht.1

def adoptedCrossRowsE0 : Finset AdoptedRow :=
  Finset.univ.filter Certificates.PairedV2.FullMask.P1E0E1.IsE0

def adoptedCrossRowsE1 : Finset AdoptedRow :=
  Finset.univ.filter Certificates.PairedV2.FullMask.P1E0E1.IsE1

theorem adoptedCrossRows_union : adoptedCrossRowsE0 ∪ adoptedCrossRowsE1 =
    (Finset.univ : Finset AdoptedRow) := by
  ext r
  simp only [adoptedCrossRowsE0, adoptedCrossRowsE1, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact iff_true_intro (Certificates.PairedV2.FullMask.P1E0E1.row_label_exhaustive r)

theorem adoptedCrossRows_disjoint : Disjoint adoptedCrossRowsE0 adoptedCrossRowsE1 := by
  apply Finset.disjoint_left.mpr
  intro r hr0 hr1
  exact Certificates.PairedV2.FullMask.P1E0E1.row_labels_disjoint r
    ⟨(Finset.mem_filter.mp hr0).2, (Finset.mem_filter.mp hr1).2⟩

theorem sum_adoptedCrossRows_split (w : AdoptedRow → ℝ) :
    (∑ r : AdoptedRow, w r) =
      (∑ r ∈ adoptedCrossRowsE0, w r) + ∑ r ∈ adoptedCrossRowsE1, w r := by
  calc
    _ = ∑ r ∈ adoptedCrossRowsE0 ∪ adoptedCrossRowsE1, w r := by
      rw [adoptedCrossRows_union]
    _ = _ := Finset.sum_union adoptedCrossRows_disjoint

/-- The actual adopted arithmetic mask, in the prime-pair orientation
expected by the source mask. -/
def adoptedMaskedFrontier (D : HistoricalPrefixCapData) (N : ℕ) (carrier : List ℕ) :
    Finset (Fin 5 → ℕ) :=
  (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
    (fun p => Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ) (p 1, p 0))

def adoptedLocalizedMaskedFrontier (D : HistoricalPrefixCapData)
    (N : ℕ) (carrier : List ℕ) : Finset (Fin 5 → ℕ) :=
  (D.adoptedMaskedFrontier N carrier).filter (fun p => actualPrimeTupleLog N p ∈
    logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ)))

def adoptedOutsideMaskedFrontier (D : HistoricalPrefixCapData)
    (N : ℕ) (carrier : List ℕ) : Finset (Fin 5 → ℕ) :=
  (D.adoptedMaskedFrontier N carrier).filter (fun p => actualPrimeTupleLog N p ∉
    logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ)))

def adoptedCrossFrontier (D : HistoricalPrefixCapData) (N : ℕ) (carrier : List ℕ)
    (r : AdoptedRow) (j : Fin 5 → Fin (D.m + 1)) : Finset (Fin 5 → ℕ) :=
  (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
    (fun p => actualPrimeTupleLog N p ∈ D.adoptedCrossCell r j)

@[simp] theorem mem_adoptedMaskedFrontier (D : HistoricalPrefixCapData)
    (N : ℕ) (carrier : List ℕ) (p : Fin 5 → ℕ) :
    p ∈ D.adoptedMaskedFrontier N carrier ↔
      p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier ∧
        adoptedCrossPair (actualPrimeTupleLog N p) ∈ PairMask := by
  simp only [adoptedMaskedFrontier, Finset.mem_filter, adoptedCrossPair_actualTuple,
    Certificates.PairedV2.FullMask.P1E0E1.deletionMask]

theorem adoptedCrossFrontiers_disjoint (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℕ) (carrier : List ℕ)
    {k l : AdoptedRow × (Fin 5 → Fin (D.m + 1))} (hkl : k ≠ l) :
    Disjoint (D.adoptedCrossFrontier N carrier k.1 k.2)
      (D.adoptedCrossFrontier N carrier l.1 l.2) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hkl (D.adoptedCrossCell_unique hab
    (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2)

/-- This is a literal finite partition of the actual localized candidate
set, with the original third-policy parent and fifth candidates. -/
theorem adoptedCrossFrontiers_union (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) :
    D.adoptedCrossLabels.biUnion (fun k => D.adoptedCrossFrontier N carrier k.1 k.2) =
      D.adoptedLocalizedMaskedFrontier N carrier := by
  ext p
  simp only [Finset.mem_biUnion, adoptedCrossFrontier, Finset.mem_filter,
    adoptedLocalizedMaskedFrontier, mem_adoptedMaskedFrontier]
  constructor
  · rintro ⟨k, _, hp, ht, hr⟩
    exact ⟨⟨hp, k.1, hr⟩,
      logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m k.2 ht⟩
  · rintro ⟨⟨hp, r, hr⟩, hbox⟩
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m hbox
    exact ⟨(r, j), D.mem_adoptedCrossLabels _, hp, hj, hr⟩

theorem sum_adoptedLocalizedMaskedFrontier_eq_cross (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) (w : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ D.adoptedLocalizedMaskedFrontier N carrier, w p) =
      ∑ r : AdoptedRow, ∑ j ∈ D.jointMeshCells 5,
        ∑ p ∈ D.adoptedCrossFrontier N carrier r j, w p := by
  have hdisj : (D.adoptedCrossLabels : Set (AdoptedRow × (Fin 5 → Fin (D.m + 1)))).PairwiseDisjoint
      (fun k => D.adoptedCrossFrontier N carrier k.1 k.2) := by
    intro k _ l _ hkl
    exact D.adoptedCrossFrontiers_disjoint hab.le N carrier hkl
  calc
    _ = ∑ p ∈ D.adoptedCrossLabels.biUnion
        (fun k => D.adoptedCrossFrontier N carrier k.1 k.2), w p := by
      rw [D.adoptedCrossFrontiers_union hab N carrier]
    _ = ∑ k ∈ D.adoptedCrossLabels,
        ∑ p ∈ D.adoptedCrossFrontier N carrier k.1 k.2, w p :=
      Finset.sum_biUnion hdisj
    _ = _ := by rw [adoptedCrossLabels, Finset.sum_product]

/-- Original E0/E1 row labels are retained through the cross refinement. -/
theorem sum_adoptedLocalizedMaskedFrontier_split_E0_E1 (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) (w : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ D.adoptedLocalizedMaskedFrontier N carrier, w p) =
      (∑ r ∈ adoptedCrossRowsE0, ∑ j ∈ D.jointMeshCells 5,
        ∑ p ∈ D.adoptedCrossFrontier N carrier r j, w p) +
      ∑ r ∈ adoptedCrossRowsE1, ∑ j ∈ D.jointMeshCells 5,
        ∑ p ∈ D.adoptedCrossFrontier N carrier r j, w p := by
  rw [D.sum_adoptedLocalizedMaskedFrontier_eq_cross hab N carrier w]
  exact sum_adoptedCrossRows_split _

theorem adoptedLocalized_outside_union (D : HistoricalPrefixCapData)
    (N : ℕ) (carrier : List ℕ) :
    D.adoptedLocalizedMaskedFrontier N carrier ∪ D.adoptedOutsideMaskedFrontier N carrier =
      D.adoptedMaskedFrontier N carrier := by
  ext p
  simp only [adoptedLocalizedMaskedFrontier, adoptedOutsideMaskedFrontier,
    Finset.mem_union, Finset.mem_filter]
  tauto

theorem adoptedLocalized_outside_disjoint (D : HistoricalPrefixCapData)
    (N : ℕ) (carrier : List ℕ) :
    Disjoint (D.adoptedLocalizedMaskedFrontier N carrier)
      (D.adoptedOutsideMaskedFrontier N carrier) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2

/-- An untruncated actual adopted-mask sum retains its outside-D-cube
contribution. A finite D mesh alone gives no coverage theorem for that part. -/
theorem sum_adoptedMaskedFrontier_eq_cross_add_outside (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) (w : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ D.adoptedMaskedFrontier N carrier, w p) =
      (∑ r : AdoptedRow, ∑ j ∈ D.jointMeshCells 5,
        ∑ p ∈ D.adoptedCrossFrontier N carrier r j, w p) +
      ∑ p ∈ D.adoptedOutsideMaskedFrontier N carrier, w p := by
  calc
    _ = ∑ p ∈ D.adoptedLocalizedMaskedFrontier N carrier ∪
        D.adoptedOutsideMaskedFrontier N carrier, w p := by
      rw [D.adoptedLocalized_outside_union N carrier]
    _ = (∑ p ∈ D.adoptedLocalizedMaskedFrontier N carrier, w p) +
        ∑ p ∈ D.adoptedOutsideMaskedFrontier N carrier, w p :=
      Finset.sum_union (D.adoptedLocalized_outside_disjoint N carrier)
    _ = _ := by rw [D.sum_adoptedLocalizedMaskedFrontier_eq_cross hab N carrier w]

end HistoricalPrefixCapData

end

end ImbalancedChen
