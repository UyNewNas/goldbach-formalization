import ImbalancedChen.HistoricalUpperFiveCellGeometry

/-!
Finite common refinement of the actual historical cap table.

The carrier is the full label type for the existing `D.m` mesh, not the
selected fifth cells. Thus unselected third, fourth and fifth owners are
retained. Projection fibers are literal `Finset.filter`s. The results here
are exact finite identities; they assert no integral or physical license.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

/-- All owners, including owners at which the stored table falls back. -/
def jointMeshCells (D : HistoricalPrefixCapData) (d : ℕ) :
    Finset (Fin d → Fin (D.m + 1)) := Finset.univ

/-- Literal fibers of coordinate restriction on the one historical mesh. -/
def jointMeshFiber (D : HistoricalPrefixCapData) {r d : ℕ} (hrd : r ≤ d)
    (q : Fin r → Fin (D.m + 1)) : Finset (Fin d → Fin (D.m + 1)) :=
  (D.jointMeshCells d).filter (fun j => historicalPrefixProject hrd j = q)

@[simp] theorem mem_jointMeshCells (D : HistoricalPrefixCapData) (d : ℕ)
    (j : Fin d → Fin (D.m + 1)) : j ∈ D.jointMeshCells d := by
  simp [jointMeshCells]

@[simp] theorem mem_jointMeshFiber (D : HistoricalPrefixCapData)
    {r d : ℕ} (hrd : r ≤ d) (q : Fin r → Fin (D.m + 1))
    (j : Fin d → Fin (D.m + 1)) :
    j ∈ D.jointMeshFiber hrd q ↔ historicalPrefixProject hrd j = q := by
  simp [jointMeshFiber, jointMeshCells]

/-- Selected and unselected fifth owners both occur in the refinement. -/
theorem fifth_cells_and_fallback_retained (D : HistoricalPrefixCapData) :
    D.cells5 ⊆ D.jointMeshCells 5 ∧
      (D.jointMeshCells 5).filter (fun j => j ∉ D.cells5) ⊆ D.jointMeshCells 5 := by
  constructor
  · intro j _
    exact D.mem_jointMeshCells 5 j
  · exact Finset.filter_subset _ _

/-- Restriction to rank three agrees whether rank four is visited or not. -/
theorem jointMesh_ancestor_345 (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    historicalPrefixProject (by omega : 3 ≤ 4)
        (historicalPrefixProject (by omega : 4 ≤ 5) j) =
      historicalPrefixProject (by omega : 3 ≤ 5) j := by
  exact historicalPrefixProject_comp _ _ j

/-- No third fiber is lost by grouping first through the fourth owners. -/
theorem jointMeshFiber_35_eq_biUnion_34_45 (D : HistoricalPrefixCapData)
    (q : Fin 3 → Fin (D.m + 1)) :
    D.jointMeshFiber (by omega : 3 ≤ 5) q =
      (D.jointMeshFiber (by omega : 3 ≤ 4) q).biUnion
        (fun q4 => D.jointMeshFiber (by omega : 4 ≤ 5) q4) := by
  ext j
  simp only [Finset.mem_biUnion, mem_jointMeshFiber]
  constructor
  · intro hj
    refine ⟨historicalPrefixProject (by omega : 4 ≤ 5) j, ?_, rfl⟩
    rw [D.jointMesh_ancestor_345 j]
    exact hj
  · rintro ⟨q4, hq4, hj⟩
    rw [← D.jointMesh_ancestor_345 j, hj]
    exact hq4

/-- Different projected owners give disjoint finite fibers. -/
theorem jointMeshFiber_disjoint (D : HistoricalPrefixCapData)
    {r d : ℕ} (hrd : r ≤ d) {q q' : Fin r → Fin (D.m + 1)} (hqq' : q ≠ q') :
    Disjoint (D.jointMeshFiber hrd q) (D.jointMeshFiber hrd q') := by
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  exact hqq' (((D.mem_jointMeshFiber hrd q j).mp hj).symm.trans
    ((D.mem_jointMeshFiber hrd q' j).mp hj'))

/-- The all-cell fifth refinement covers exactly the original half-open cube. -/
theorem jointMeshCells_five_cover (D : HistoricalPrefixCapData) (hab : D.a < D.b) :
    (⋃ j ∈ D.jointMeshCells 5,
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
      logPrimeBox (fun _ : Fin 5 => (D.a : ℝ)) (fun _ => (D.b : ℝ)) := by
  simpa [jointMeshCells] using
    (logPrimeMeshCells_union (d := 5) (by exact_mod_cast hab) D.m)

/-- Within the ambient cube, a projected ancestor cell is exactly the union
of its literal fine-cell fiber, with no selected-cell condition. -/
theorem jointMeshFiber_region (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    {r d : ℕ} (hrd : r ≤ d) (q : Fin r → Fin (D.m + 1)) :
    (⋃ j ∈ D.jointMeshFiber hrd q,
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
      {t | t ∈ logPrimeBox (fun _ : Fin d => (D.a : ℝ)) (fun _ => (D.b : ℝ)) ∧
        historicalPrefixProject hrd t ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m q} := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, ht⟩
    refine ⟨logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht, ?_⟩
    have hp := mem_logPrimeMeshCell_historicalPrefixProject hrd ht
    rw [(D.mem_jointMeshFiber hrd q j).mp hj] at hp
    exact hp
  · rintro ⟨ht, hq⟩
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m ht
    refine ⟨j, ?_, hj⟩
    apply (D.mem_jointMeshFiber hrd q j).mpr
    exact (historicalPrefixAncestorCell_unique hrd (by exact_mod_cast hab.le) hj hq).symm

/-- Exact finite disintegration over any projected owner. This is valid for
signed weights and includes the entire fallback part of the full carrier. -/
theorem sum_jointMeshFiber (D : HistoricalPrefixCapData)
    {r d : ℕ} (hrd : r ≤ d) {A : Type*} [AddCommMonoid A]
    (w : (Fin d → Fin (D.m + 1)) → A) :
    (∑ q ∈ D.jointMeshCells r, ∑ j ∈ D.jointMeshFiber hrd q, w j) =
      ∑ j ∈ D.jointMeshCells d, w j := by
  simpa only [jointMeshCells, jointMeshFiber] using
    (Finset.sum_fiberwise (D.jointMeshCells d) (historicalPrefixProject hrd) w)

/-- Fiberwise rank-three grouping factors through exactly the same fourth
owner as the historical table. No multiplicity or coefficient is changed. -/
theorem sum_jointMeshFiber_345 (D : HistoricalPrefixCapData)
    {A : Type*} [AddCommMonoid A] (q : Fin 3 → Fin (D.m + 1))
    (w : (Fin 5 → Fin (D.m + 1)) → A) :
    (∑ q4 ∈ D.jointMeshFiber (by omega : 3 ≤ 4) q,
      ∑ j ∈ D.jointMeshFiber (by omega : 4 ≤ 5) q4, w j) =
      ∑ j ∈ D.jointMeshFiber (by omega : 3 ≤ 5) q, w j := by
  have hf := Finset.sum_fiberwise_eq_sum_filter (D.jointMeshCells 5)
    (D.jointMeshFiber (by omega : 3 ≤ 4) q)
    (historicalPrefixProject (by omega : 4 ≤ 5)) w
  simpa only [mem_jointMeshFiber, D.jointMesh_ancestor_345] using hf

/-- The full nested 3→4→5 reindex is an equality of actual finite sums. -/
theorem sum_jointMeshCells_345 (D : HistoricalPrefixCapData)
    {A : Type*} [AddCommMonoid A]
    (w : (Fin 5 → Fin (D.m + 1)) → A) :
    (∑ q3 ∈ D.jointMeshCells 3,
      ∑ q4 ∈ D.jointMeshFiber (by omega : 3 ≤ 4) q3,
        ∑ j ∈ D.jointMeshFiber (by omega : 4 ≤ 5) q4, w j) =
      ∑ j ∈ D.jointMeshCells 5, w j := by
  calc
    _ = ∑ q3 ∈ D.jointMeshCells 3,
        ∑ j ∈ D.jointMeshFiber (by omega : 3 ≤ 5) q3, w j := by
      apply Finset.sum_congr rfl
      intro q3 _
      exact D.sum_jointMeshFiber_345 q3 w
    _ = _ := D.sum_jointMeshFiber (by omega : 3 ≤ 5) w

/-- The inherited fifth value is precisely constant on its fourth fiber. -/
theorem old5_on_jointMeshFiber (D : HistoricalPrefixCapData)
    (q4 : Fin 4 → Fin (D.m + 1)) (j : Fin 5 → Fin (D.m + 1))
    (hj : j ∈ D.jointMeshFiber (by omega : 4 ≤ 5) q4) :
    D.old5 j = D.cell4 q4 := by
  unfold old5
  rw [(D.mem_jointMeshFiber (by omega : 4 ≤ 5) q4 j).mp hj]

/-- Effective fourth values retain the third fallback on the identical
projected owner; this expands the actual pre-existing table definitions. -/
theorem cell5_jointMesh_expansion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    D.cell5 j =
      if j ∈ D.cells5 then D.cap5 j else
      if historicalPrefixProject (by omega : 4 ≤ 5) j ∈ D.cells4 then
        D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
      if historicalPrefixProject (by omega : 3 ≤ 5) j ∈ D.cells3 then
        D.cap3 (historicalPrefixProject (by omega : 3 ≤ 5) j) else D.old := by
  simp only [cell5, old5, cell4, old4, cell3, D.jointMesh_ancestor_345]

/-- The actual fifth fallback is present in the reindexed finite sum,
including when the fourth or third owner is itself unselected. -/
theorem sum_jointMeshCells_cell5_by_fourth (D : HistoricalPrefixCapData)
    (w : (Fin 5 → Fin (D.m + 1)) → ℝ) (f : ℚ → ℝ) :
    (∑ j ∈ D.jointMeshCells 5, w j * f (D.cell5 j)) =
      ∑ q4 ∈ D.jointMeshCells 4,
        ∑ j ∈ D.jointMeshFiber (by omega : 4 ≤ 5) q4,
          w j * f (if j ∈ D.cells5 then D.cap5 j else D.cell4 q4) := by
  rw [← D.sum_jointMeshFiber (by omega : 4 ≤ 5)
    (fun j => w j * f (D.cell5 j))]
  apply Finset.sum_congr rfl
  intro q4 _
  apply Finset.sum_congr rfl
  intro j hj
  rw [cell5, D.old5_on_jointMeshFiber q4 j hj]

/-- The concrete table itself can be summed in ancestral order, retaining
every fifth fallback and its effective third or fourth inherited cap. -/
theorem sum_jointMeshCells_cell5_by_third_fourth (D : HistoricalPrefixCapData)
    (w : (Fin 5 → Fin (D.m + 1)) → ℝ) (f : ℚ → ℝ) :
    (∑ j ∈ D.jointMeshCells 5, w j * f (D.cell5 j)) =
      ∑ q3 ∈ D.jointMeshCells 3,
        ∑ q4 ∈ D.jointMeshFiber (by omega : 3 ≤ 4) q3,
          ∑ j ∈ D.jointMeshFiber (by omega : 4 ≤ 5) q4,
            w j * f (if j ∈ D.cells5 then D.cap5 j else
              if q4 ∈ D.cells4 then D.cap4 q4 else D.cell3 q3) := by
  rw [← D.sum_jointMeshCells_345 (fun j => w j * f (D.cell5 j))]
  apply Finset.sum_congr rfl
  intro q3 _
  apply Finset.sum_congr rfl
  intro q4 hq4
  apply Finset.sum_congr rfl
  intro j hj
  rw [cell5, D.old5_on_jointMeshFiber q4 j hj, cell4, old4,
    (D.mem_jointMeshFiber (by omega : 3 ≤ 4) q3 q4).mp hq4]

/-- All three actual effective exponents are identified on one fifth cell.
This uses the half-open pointwise ownership theorems, including fallback. -/
theorem jointMesh_exponents_on_fifth (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 5) t) =
        D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) ∧
      D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) =
        D.cell4 (historicalPrefixProject (by omega : 4 ≤ 5) j) ∧
      D.exponent5 t = D.cell5 j := by
  exact ⟨D.exponent3_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht),
    D.exponent4_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht),
    D.exponent5_on_cell hab t j ht⟩

end HistoricalPrefixCapData

end

end ImbalancedChen
