import ImbalancedChen.P1HistoricalJointMeshOwnershipPartition
import ImbalancedChen.P1AdoptedHistoricalCrossMesh
import ImbalancedChen.P1HistoricalBoundarySafeCellSplit

/-!
Actual fourth residuals on the one original T3 admitted carrier, partitioned
by safe/boundary/fallback fourth owners and the adopted half-open pair rows.
The pair mask is an additional arithmetic localization; it does not replace
the upper policy. The unmasked and no-D-owner contributions are explicit.

All caps, exponents and level checks belong to the original D. In particular
this file does not replace D by a safe-cell restricted table, which could
change the fifth inherited cap. Source-only imports name sibling drafts or
their eventual integration names; no compiler check has been performed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

local notation "AdoptedRow" => Certificates.PairedV2.FullMask.Row
local notation "PairCell" => Certificates.PairedV2.FullMask.P1E0E1.pairCell
local notation "PairMask" => Certificates.PairedV2.FullMask.P1E0E1.pairRegion

def boundaryFourthCarrier (D : HistoricalPrefixCapData) (N cap : ℕ) :
    Finset (Fin 4 → ℕ) :=
  firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))

def boundaryFourthPair (t : Fin 4 → ℝ) : ℝ × ℝ := (t 0, t 1)

def boundaryFourthMasked (D : HistoricalPrefixCapData) (N cap : ℕ) :
    Finset (Fin 4 → ℕ) :=
  (D.boundaryFourthCarrier N cap).filter (fun p =>
    Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ) (p 1, p 0))

def boundaryFourthUnmasked (D : HistoricalPrefixCapData) (N cap : ℕ) :
    Finset (Fin 4 → ℕ) :=
  (D.boundaryFourthCarrier N cap).filter (fun p =>
    ¬ Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ) (p 1, p 0))

@[simp] theorem mem_boundaryFourthMasked (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 4 → ℕ) :
    p ∈ D.boundaryFourthMasked N cap ↔ p ∈ D.boundaryFourthCarrier N cap ∧
      boundaryFourthPair (actualPrimeTupleLog N p) ∈ PairMask := by
  simp only [boundaryFourthMasked, Finset.mem_filter,
    Certificates.PairedV2.FullMask.P1E0E1.deletionMask,
    Certificates.PairedV2.FullMask.P1E0E1.primePairCoordinates,
    boundaryFourthPair, actualPrimeTupleLog]

/-- The actual D owner family J, after arithmetic localization to the pair mask. -/
def boundaryFourthOwned (D : HistoricalPrefixCapData) (N cap : ℕ)
    (J : Finset (Fin 4 → Fin (D.m + 1))) : Finset (Fin 4 → ℕ) :=
  D.jointOwnedTuples N (D.boundaryFourthMasked N cap) J

/-- Outside means no D fourth mesh owner, not just failure of a margin check. -/
def boundaryFourthOutside (D : HistoricalPrefixCapData) (N cap : ℕ) :
    Finset (Fin 4 → ℕ) :=
  D.boundaryFourthMasked N cap \ D.boundaryFourthOwned N cap (D.jointMeshCells 4)

/-- A row is used only as its original half-open pair rectangle. -/
def boundaryFourthCrossTuples (D : HistoricalPrefixCapData) (N cap : ℕ)
    (r : AdoptedRow) (j : Fin 4 → Fin (D.m + 1)) : Finset (Fin 4 → ℕ) :=
  (D.boundaryFourthCarrier N cap).filter (fun p =>
    actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
      boundaryFourthPair (actualPrimeTupleLog N p) ∈ PairCell r)

theorem boundaryFourthCrossTuples_disjoint (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ)
    {k l : AdoptedRow × (Fin 4 → Fin (D.m + 1))} (hkl : k ≠ l) :
    Disjoint (D.boundaryFourthCrossTuples N cap k.1 k.2)
      (D.boundaryFourthCrossTuples N cap l.1 l.2) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hk := (Finset.mem_filter.mp hp).2
  have hl := (Finset.mem_filter.mp hq).2
  apply hkl
  apply Prod.ext
  · exact Certificates.PairedV2.FullMask.P1E0E1.pairCell_unique_owner hk.2 hl.2
  · exact logPrimeMeshCell_unique (by exact_mod_cast hab) hk.1 hl.1

/-- On an arbitrary actual finite fourth family, the cross partition needs
no global cube coverage or margin premise. -/
theorem boundaryFourthCrossTuples_union (D : HistoricalPrefixCapData)
    (N cap : ℕ) (J : Finset (Fin 4 → Fin (D.m + 1))) :
    (Finset.univ.product J).biUnion
      (fun k => D.boundaryFourthCrossTuples N cap k.1 k.2) =
      D.boundaryFourthOwned N cap J := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_univ, true_and,
    boundaryFourthCrossTuples, Finset.mem_filter, boundaryFourthOwned,
    mem_jointOwnedTuples, mem_boundaryFourthMasked]
  constructor
  · rintro ⟨k, hj, hp, ht, hr⟩
    exact ⟨⟨hp, k.1, hr⟩, k.2, hj, ht⟩
  · rintro ⟨⟨hp, r, hr⟩, j, hj, ht⟩
    exact ⟨(r, j), hj, hp, ht, hr⟩

theorem sum_boundaryFourthOwned_eq_cross (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (J : Finset (Fin 4 → Fin (D.m + 1)))
    (w : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ D.boundaryFourthOwned N cap J, w p) =
      ∑ r : AdoptedRow, ∑ j ∈ J, ∑ p ∈ D.boundaryFourthCrossTuples N cap r j, w p := by
  have hdisj : ((Finset.univ.product J :
      Finset (AdoptedRow × (Fin 4 → Fin (D.m + 1)))) : Set _).PairwiseDisjoint
      (fun k => D.boundaryFourthCrossTuples N cap k.1 k.2) := by
    intro k _ l _ hkl
    exact D.boundaryFourthCrossTuples_disjoint hab N cap hkl
  calc
    _ = ∑ p ∈ (Finset.univ.product J).biUnion
        (fun k => D.boundaryFourthCrossTuples N cap k.1 k.2), w p := by
      rw [D.boundaryFourthCrossTuples_union N cap J]
    _ = ∑ k ∈ Finset.univ.product J,
        ∑ p ∈ D.boundaryFourthCrossTuples N cap k.1 k.2, w p :=
      Finset.sum_biUnion hdisj
    _ = _ := Finset.sum_product _ _ _

/-- Cross-localizing a cell keeps exactly its original admitted four-class
signature; the pair mask introduces no policy admission condition. -/
theorem boundaryFourthCross_mem_admittedClass (D : HistoricalPrefixCapData)
    (N cap : ℕ) (σ : Bool × Bool) (r : AdoptedRow)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.jointSelectionOwners4 σ)
    (p : Fin 4 → ℕ) (hp : p ∈ D.boundaryFourthCrossTuples N cap r j) :
    p ∈ D.historicalAdmittedOwnershipClass N
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) σ := by
  obtain ⟨hfront, ht, _⟩ := Finset.mem_filter.mp hp
  exact (D.mem_jointOwnedTuples N _ _ p).mpr ⟨hfront, j, hj, ht⟩

/-- Every boundary or safe family is also partitioned by the previously
constructed four actual admitted ownership classes, on this same D. -/
theorem boundaryFourthOwned_partition_admittedClasses (D : HistoricalPrefixCapData)
    (N cap : ℕ) (J : Finset (Fin 4 → Fin (D.m + 1))) :
    Finset.univ.biUnion (fun σ : Bool × Bool => D.boundaryFourthOwned N cap J ∩
      D.historicalAdmittedOwnershipClass N
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) σ) =
      D.boundaryFourthOwned N cap J := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨_, hp, _⟩
    exact hp
  · intro hp
    obtain ⟨hmask, j, _, ht⟩ := (D.mem_jointOwnedTuples N _ _ p).mp hp
    have hfront := ((D.mem_boundaryFourthMasked N cap p).mp hmask).1
    refine ⟨D.jointSelectionSignature4 j, hp, ?_⟩
    apply (D.mem_jointOwnedTuples N _ _ p).mpr
    refine ⟨hfront, j, ?_, ht⟩
    exact Finset.mem_filter.mpr ⟨D.mem_jointMeshCells 4 j, rfl⟩

theorem sum_boundaryFourthOwned_by_admittedClasses (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (J : Finset (Fin 4 → Fin (D.m + 1)))
    (w : (Fin 4 → ℕ) → ℝ) :
    (∑ σ : Bool × Bool, ∑ p ∈ D.boundaryFourthOwned N cap J ∩
      D.historicalAdmittedOwnershipClass N
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) σ, w p) =
      ∑ p ∈ D.boundaryFourthOwned N cap J, w p := by
  have hdisj : ((Finset.univ : Finset (Bool × Bool)) : Set _).PairwiseDisjoint
      (fun σ => D.boundaryFourthOwned N cap J ∩ D.historicalAdmittedOwnershipClass N
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) σ) := by
    intro σ _ τ _ hστ
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp (D.historicalAdmittedOwnershipClass_disjoint hab N
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) hστ)
        (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hq).2
  rw [← Finset.sum_biUnion hdisj, D.boundaryFourthOwned_partition_admittedClasses N cap J]

/-- The correction is evaluated at the original inherited third owner and
the original fourth value, including unselected fallback cells. -/
theorem boundaryFourthResidual_on_cross (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (r : AdoptedRow)
    (j : Fin 4 → Fin (D.m + 1)) (p : Fin 4 → ℕ)
    (hp : p ∈ D.boundaryFourthCrossTuples N cap r j) :
    D.fourthTupleResidualDifferenceP1 N cap p =
      fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p -
        fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p := by
  have ht := (Finset.mem_filter.mp hp).2.1
  unfold fourthTupleResidualDifferenceP1
  rw [D.exponent4_on_cell hab _ j ht,
    D.exponent3_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)]

def boundaryFourthResidualWeight (D : HistoricalPrefixCapData) (N cap : ℕ)
    (p : Fin 4 → ℕ) : ℝ :=
  (∏ i, 1 / ((p i : ℝ) - 1)) * D.fourthTupleResidualDifferenceP1 N cap p

def boundaryFourthCrossCorrection (D : HistoricalPrefixCapData) (N cap : ℕ)
    (r : AdoptedRow) (j : Fin 4 → Fin (D.m + 1)) : ℝ :=
  ∑ p ∈ D.boundaryFourthCrossTuples N cap r j,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p -
        fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p)

theorem boundaryFourthCrossCorrection_eq_actual_weight (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (r : AdoptedRow)
    (j : Fin 4 → Fin (D.m + 1)) :
    D.boundaryFourthCrossCorrection N cap r j =
      ∑ p ∈ D.boundaryFourthCrossTuples N cap r j, D.boundaryFourthResidualWeight N cap p := by
  apply Finset.sum_congr rfl
  intro p hp
  unfold boundaryFourthResidualWeight
  rw [D.boundaryFourthResidual_on_cross hab N cap r j p hp]

theorem boundaryFourthCrossCorrection_unselected (D : HistoricalPrefixCapData)
    (N cap : ℕ) (r : AdoptedRow) (j : Fin 4 → Fin (D.m + 1))
    (hj : j ∉ D.cells4) : D.boundaryFourthCrossCorrection N cap r j = 0 := by
  unfold boundaryFourthCrossCorrection
  simp only [cell4, if_neg hj, sub_self, mul_zero, Finset.sum_const_zero]

theorem boundaryFourthCrossCorrection_selected (D : HistoricalPrefixCapData)
    (N cap : ℕ) (r : AdoptedRow) (j : Fin 4 → Fin (D.m + 1))
    (hj : j ∈ D.cells4) :
    D.boundaryFourthCrossCorrection N cap r j =
      ∑ p ∈ D.boundaryFourthCrossTuples N cap r j,
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p -
            fourthTuplePlusResidualP1 N cap (D.cap4 j : ℝ) p) := by
  simp only [boundaryFourthCrossCorrection, cell4, if_pos hj]

/-- The existing checked whole-cell safe margin applies on every crossed
prime point with the original levelCheck and original effective old4/cell4. -/
theorem boundaryFourthCross_safe_uniform_gap (D : HistoricalPrefixCapData)
    (hlevels : D.levelCheck = true) (delta rho : ℚ) (N cap : ℕ)
    (r : AdoptedRow) (j : Fin 4 → Fin (D.m + 1))
    (hj : j ∈ D.p1FourthSafeCells delta rho) (p : Fin 4 → ℕ)
    (hp : p ∈ D.boundaryFourthCrossTuples N cap r j) :
    0 < (delta : ℝ) / (2 * (rho : ℝ)) ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.old4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 3 ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.cell4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 3 := by
  exact D.p1_fourthCell_uniform_gap hlevels delta rho j
    (D.p1FourthSafeCells_pass delta rho j hj) _ (Finset.mem_filter.mp hp).2.1

/-- The genuine fourth dictionary on any finite cell family, crossed with
the adopted row mask. Neither residual level is replaced by a row cap. -/
theorem boundaryFourthOwned_residual_eq_cross (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (J : Finset (Fin 4 → Fin (D.m + 1))) :
    (∑ p ∈ D.boundaryFourthOwned N cap J, D.boundaryFourthResidualWeight N cap p) =
      ∑ r : AdoptedRow, ∑ j ∈ J, D.boundaryFourthCrossCorrection N cap r j := by
  rw [D.sum_boundaryFourthOwned_eq_cross hab N cap J]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  exact (D.boundaryFourthCrossCorrection_eq_actual_weight hab N cap r j).symm

/-- The actual boundary-cell dictionary requested by the arithmetic budget. -/
theorem p1BoundaryFamily_masked_residual_eq_cross (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (delta rho : ℚ) :
    (∑ p ∈ D.boundaryFourthOwned N cap (D.p1FourthBoundaryCells delta rho),
      D.boundaryFourthResidualWeight N cap p) =
      ∑ r : AdoptedRow, ∑ j ∈ D.p1FourthBoundaryCells delta rho,
        D.boundaryFourthCrossCorrection N cap r j := by
  exact D.boundaryFourthOwned_residual_eq_cross hab N cap _

theorem p1BoundaryFamily_masked_residual_split_E0_E1 (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (delta rho : ℚ) :
    (∑ p ∈ D.boundaryFourthOwned N cap (D.p1FourthBoundaryCells delta rho),
      D.boundaryFourthResidualWeight N cap p) =
      (∑ r ∈ adoptedCrossRowsE0, ∑ j ∈ D.p1FourthBoundaryCells delta rho,
        D.boundaryFourthCrossCorrection N cap r j) +
      ∑ r ∈ adoptedCrossRowsE1, ∑ j ∈ D.p1FourthBoundaryCells delta rho,
        D.boundaryFourthCrossCorrection N cap r j := by
  rw [D.p1BoundaryFamily_masked_residual_eq_cross hab N cap delta rho]
  exact sum_adoptedCrossRows_split _

theorem boundaryFourthOwned_outside_partition (D : HistoricalPrefixCapData)
    (N cap : ℕ) :
    D.boundaryFourthOwned N cap (D.jointMeshCells 4) ∪ D.boundaryFourthOutside N cap =
      D.boundaryFourthMasked N cap := by
  ext p
  simp only [boundaryFourthOutside, boundaryFourthOwned, mem_jointOwnedTuples,
    Finset.mem_union, Finset.mem_sdiff]
  tauto

theorem boundaryFourthOwned_outside_disjoint (D : HistoricalPrefixCapData)
    (N cap : ℕ) :
    Disjoint (D.boundaryFourthOwned N cap (D.jointMeshCells 4))
      (D.boundaryFourthOutside N cap) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (Finset.mem_sdiff.mp hq).2 hp

theorem boundaryFourthOutside_iff_cube_complement (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N cap : ℕ) (p : Fin 4 → ℕ) :
    p ∈ D.boundaryFourthOutside N cap ↔ p ∈ D.boundaryFourthMasked N cap ∧
      actualPrimeTupleLog N p ∉
        logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ)) := by
  constructor
  · intro hp
    obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp hp
    refine ⟨hm, ?_⟩
    intro hbox
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m hbox
    exact hn ((D.mem_jointOwnedTuples N _ _ p).mpr
      ⟨hm, j, D.mem_jointMeshCells 4 j, hj⟩)
  · rintro ⟨hm, hbox⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hm, ?_⟩
    intro howned
    obtain ⟨_, j, _, ht⟩ := (D.mem_jointOwnedTuples N _ _ p).mp howned
    exact hbox (logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht)

private theorem boundaryFourth_full_cell_sum_eq_selected (D : HistoricalPrefixCapData)
    (N cap : ℕ) (r : AdoptedRow) :
    (∑ j ∈ D.jointMeshCells 4, D.boundaryFourthCrossCorrection N cap r j) =
      ∑ j ∈ D.cells4, D.boundaryFourthCrossCorrection N cap r j := by
  symm
  apply Finset.sum_subset
  · intro j _
    exact D.mem_jointMeshCells 4 j
  · intro j _ hj
    exact D.boundaryFourthCrossCorrection_unselected N cap r j hj

/-- Exact safe/boundary/outside residual split on the ORIGINAL D table.
Unselected in-cube owners vanish by the actual old=new fallback dictionary;
the no-D-owner part is retained explicitly, without a boundary estimate. -/
theorem boundaryFourthMasked_residual_safe_boundary_outside (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) (delta rho : ℚ) :
    (∑ p ∈ D.boundaryFourthMasked N cap, D.boundaryFourthResidualWeight N cap p) =
      (∑ r : AdoptedRow, ∑ j ∈ D.p1FourthSafeCells delta rho,
        D.boundaryFourthCrossCorrection N cap r j) +
      (∑ r : AdoptedRow, ∑ j ∈ D.p1FourthBoundaryCells delta rho,
        D.boundaryFourthCrossCorrection N cap r j) +
      ∑ p ∈ D.boundaryFourthOutside N cap, D.boundaryFourthResidualWeight N cap p := by
  calc
    _ = (∑ p ∈ D.boundaryFourthOwned N cap (D.jointMeshCells 4),
        D.boundaryFourthResidualWeight N cap p) +
        ∑ p ∈ D.boundaryFourthOutside N cap, D.boundaryFourthResidualWeight N cap p := by
      rw [← Finset.sum_union (D.boundaryFourthOwned_outside_disjoint N cap),
        D.boundaryFourthOwned_outside_partition N cap]
    _ = (∑ r : AdoptedRow, ∑ j ∈ D.cells4, D.boundaryFourthCrossCorrection N cap r j) +
        ∑ p ∈ D.boundaryFourthOutside N cap, D.boundaryFourthResidualWeight N cap p := by
      rw [D.boundaryFourthOwned_residual_eq_cross hab N cap]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      exact D.boundaryFourth_full_cell_sum_eq_selected N cap r
    _ = _ := by
      rw [← D.p1FourthSafeBoundary_union delta rho]
      simp only [Finset.sum_union (D.p1FourthSafeBoundary_disjoint delta rho),
        Finset.sum_add_distrib, add_assoc]

/-- The pair mask is a partition of the original correction, never a
replacement of the third-capped upper policy or its admitted carrier. -/
theorem fourthPrimeCorrection_masked_unmasked (D : HistoricalPrefixCapData)
    (N cap : ℕ) :
    D.fourthPrimeCorrectionP1 N cap =
      (∑ p ∈ D.boundaryFourthMasked N cap, D.boundaryFourthResidualWeight N cap p) +
      ∑ p ∈ D.boundaryFourthUnmasked N cap, D.boundaryFourthResidualWeight N cap p := by
  exact (Finset.sum_filter_add_sum_filter_not (D.boundaryFourthCarrier N cap)
    (fun p => Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ) (p 1, p 0))
    (D.boundaryFourthResidualWeight N cap)).symm

theorem fourthPrimeCorrection_safe_boundary_cross_outside_unmasked
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ) (delta rho : ℚ) :
    D.fourthPrimeCorrectionP1 N cap =
      (∑ r : AdoptedRow, ∑ j ∈ D.p1FourthSafeCells delta rho,
        D.boundaryFourthCrossCorrection N cap r j) +
      (∑ r : AdoptedRow, ∑ j ∈ D.p1FourthBoundaryCells delta rho,
        D.boundaryFourthCrossCorrection N cap r j) +
      (∑ p ∈ D.boundaryFourthOutside N cap, D.boundaryFourthResidualWeight N cap p) +
      ∑ p ∈ D.boundaryFourthUnmasked N cap, D.boundaryFourthResidualWeight N cap p := by
  rw [D.fourthPrimeCorrection_masked_unmasked N cap,
    D.boundaryFourthMasked_residual_safe_boundary_outside hab N cap delta rho]

/-- Fifth inheritance continues to read the very same original fourth owner
used in a boundary correction. No safe-table restriction is performed. -/
theorem boundaryFourth_fifth_inheritance_same_owner (D : HistoricalPrefixCapData)
    (delta rho : ℚ) (j4 : Fin 4 → Fin (D.m + 1))
    (_hj4 : j4 ∈ D.p1FourthBoundaryCells delta rho)
    (j5 : Fin 5 → Fin (D.m + 1))
    (hj5 : j5 ∈ D.jointMeshFiber (by omega : 4 ≤ 5) j4) :
    D.old5 j5 = D.cell4 j4 := by
  exact D.old5_on_jointMeshFiber j4 j5 hj5

end HistoricalPrefixCapData

end

end ImbalancedChen
