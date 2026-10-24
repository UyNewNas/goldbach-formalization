import ImbalancedChen.HistoricalJointMeshFiniteRefinement
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-!
Orthogonal selected/fallback ownership classes on the actual historical
mesh. A rank-four admitted tuple has four classes (third/fourth); a rank-five
next candidate has eight (third/fourth/fifth). No fictitious fifth owner is
assigned to a rank-four tuple, and no own-cube admission is added to a next
candidate. All sums below preserve arbitrary signed real weights.

The sibling source import is intentional: place both draft files on the
same Lean source search path when compilation is authorized.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

def jointSelectionSignature4 (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) : Bool × Bool :=
  (decide (historicalPrefixProject (by omega : 3 ≤ 4) j ∈ D.cells3),
    decide (j ∈ D.cells4))

def jointSelectionSignature5 (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Bool × Bool × Bool :=
  (decide (historicalPrefixProject (by omega : 3 ≤ 5) j ∈ D.cells3),
    decide (historicalPrefixProject (by omega : 4 ≤ 5) j ∈ D.cells4),
    decide (j ∈ D.cells5))

def jointSelectionOwners4 (D : HistoricalPrefixCapData) (σ : Bool × Bool) :
    Finset (Fin 4 → Fin (D.m + 1)) :=
  (D.jointMeshCells 4).filter (fun j => D.jointSelectionSignature4 j = σ)

def jointSelectionOwners5 (D : HistoricalPrefixCapData) (σ : Bool × Bool × Bool) :
    Finset (Fin 5 → Fin (D.m + 1)) :=
  (D.jointMeshCells 5).filter (fun j => D.jointSelectionSignature5 j = σ)

def jointThirdSupport5 (D : HistoricalPrefixCapData) :
    Finset (Fin 5 → Fin (D.m + 1)) :=
  (D.jointMeshCells 5).filter
    (fun j => historicalPrefixProject (by omega : 3 ≤ 5) j ∈ D.cells3)

def jointFourthSupport5 (D : HistoricalPrefixCapData) :
    Finset (Fin 5 → Fin (D.m + 1)) :=
  (D.jointMeshCells 5).filter
    (fun j => historicalPrefixProject (by omega : 4 ≤ 5) j ∈ D.cells4)

/-- A false flag keeps the full relative complement, not just selected
fifth owners whose earlier ancestor happened to be selected. -/
def jointSelectionSide {ι : Type*} [DecidableEq ι]
    (U J : Finset ι) (s : Bool) : Finset ι := if s then J else U \ J

theorem jointThirdSupport5_eq_selected_fibers (D : HistoricalPrefixCapData) :
    D.jointThirdSupport5 = D.cells3.biUnion
      (fun q => D.jointMeshFiber (by omega : 3 ≤ 5) q) := by
  ext j
  simp only [jointThirdSupport5, Finset.mem_filter, mem_jointMeshCells, true_and,
    Finset.mem_biUnion, mem_jointMeshFiber]
  constructor
  · intro hj
    exact ⟨historicalPrefixProject (by omega : 3 ≤ 5) j, hj, rfl⟩
  · rintro ⟨q, hq, hj⟩
    rwa [hj]

theorem jointFourthSupport5_eq_selected_fibers (D : HistoricalPrefixCapData) :
    D.jointFourthSupport5 = D.cells4.biUnion
      (fun q => D.jointMeshFiber (by omega : 4 ≤ 5) q) := by
  ext j
  simp only [jointFourthSupport5, Finset.mem_filter, mem_jointMeshCells, true_and,
    Finset.mem_biUnion, mem_jointMeshFiber]
  constructor
  · intro hj
    exact ⟨historicalPrefixProject (by omega : 4 ≤ 5) j, hj, rfl⟩
  · rintro ⟨q, hq, hj⟩
    rwa [hj]

/-- The eight actual classes are intersections of three independent
selected-or-full-complement supports. -/
theorem jointSelectionOwners5_eq_inter (D : HistoricalPrefixCapData)
    (s3 s4 s5 : Bool) :
    D.jointSelectionOwners5 (s3, s4, s5) =
      jointSelectionSide (D.jointMeshCells 5) D.jointThirdSupport5 s3 ∩
        jointSelectionSide (D.jointMeshCells 5) D.jointFourthSupport5 s4 ∩
        jointSelectionSide (D.jointMeshCells 5) D.cells5 s5 := by
  ext j
  cases s3 <;> cases s4 <;> cases s5 <;>
    simp [jointSelectionOwners5, jointSelectionSignature5, jointSelectionSide,
      jointThirdSupport5, jointFourthSupport5, jointMeshCells, and_assoc]

/-- Neither a selected third nor a selected fifth owner is required to
remain in the unselected fourth support. -/
theorem jointFourthFallback5_mem (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    j ∈ D.jointMeshCells 5 \ D.jointFourthSupport5 ↔
      historicalPrefixProject (by omega : 4 ≤ 5) j ∉ D.cells4 := by
  simp [jointFourthSupport5, jointMeshCells]

theorem jointFifthFallback5_mem (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    j ∈ D.jointMeshCells 5 \ D.cells5 ↔ j ∉ D.cells5 := by
  simp [jointMeshCells]

/-- Actual prime tuples owned by a specified finite family of mesh cells. -/
def jointOwnedTuples (D : HistoricalPrefixCapData) {d : ℕ} (N : ℕ)
    (S : Finset (Fin d → ℕ)) (J : Finset (Fin d → Fin (D.m + 1))) :
    Finset (Fin d → ℕ) :=
  S.filter (fun p => ∃ j ∈ J, actualPrimeTupleLog N p ∈
    logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)

@[simp] theorem mem_jointOwnedTuples (D : HistoricalPrefixCapData) {d : ℕ}
    (N : ℕ) (S : Finset (Fin d → ℕ)) (J : Finset (Fin d → Fin (D.m + 1)))
    (p : Fin d → ℕ) :
    p ∈ D.jointOwnedTuples N S J ↔ p ∈ S ∧
      ∃ j ∈ J, actualPrimeTupleLog N p ∈
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j := by
  simp [jointOwnedTuples]

theorem jointOwnedTuples_disjoint (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    {d : ℕ} (N : ℕ) (S : Finset (Fin d → ℕ))
    {J K : Finset (Fin d → Fin (D.m + 1))} (hJK : Disjoint J K) :
    Disjoint (D.jointOwnedTuples N S J) (D.jointOwnedTuples N S K) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨j, hj, ht⟩ := ((D.mem_jointOwnedTuples N S J p).mp hp).2
  obtain ⟨k, hk, ht'⟩ := ((D.mem_jointOwnedTuples N S K p).mp hp').2
  have hjk := logPrimeMeshCell_unique (by exact_mod_cast hab) ht ht'
  subst k
  exact Finset.disjoint_left.mp hJK hj hk

theorem jointOwnedTuples_union (D : HistoricalPrefixCapData) {d : ℕ}
    (N : ℕ) (S : Finset (Fin d → ℕ)) (J K : Finset (Fin d → Fin (D.m + 1))) :
    D.jointOwnedTuples N S (J ∪ K) =
      D.jointOwnedTuples N S J ∪ D.jointOwnedTuples N S K := by
  ext p
  simp only [mem_jointOwnedTuples, Finset.mem_union]
  aesop

theorem jointOwnedTuples_inter (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    {d : ℕ} (N : ℕ) (S : Finset (Fin d → ℕ))
    (J K : Finset (Fin d → Fin (D.m + 1))) :
    D.jointOwnedTuples N S (J ∩ K) =
      D.jointOwnedTuples N S J ∩ D.jointOwnedTuples N S K := by
  ext p
  simp only [mem_jointOwnedTuples, Finset.mem_inter]
  constructor
  · rintro ⟨hp, j, ⟨hj, hk⟩, ht⟩
    exact ⟨⟨hp, j, hj, ht⟩, hp, j, hk, ht⟩
  · rintro ⟨⟨hp, j, hj, ht⟩, _, k, hk, ht'⟩
    have hjk := logPrimeMeshCell_unique (by exact_mod_cast hab) ht ht'
    subst k
    exact ⟨hp, j, ⟨hj, hk⟩, ht⟩

/-- Relative complement commutes with actual tuple ownership. This uses
pointwise uniqueness, including primes on internal half-open grid faces. -/
theorem jointOwnedTuples_sdiff (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    {d : ℕ} (N : ℕ) (S : Finset (Fin d → ℕ))
    (J K : Finset (Fin d → Fin (D.m + 1))) :
    D.jointOwnedTuples N S (J \ K) =
      D.jointOwnedTuples N S J \ D.jointOwnedTuples N S K := by
  ext p
  simp only [mem_jointOwnedTuples, Finset.mem_sdiff]
  constructor
  · rintro ⟨hp, j, ⟨hj, hjK⟩, ht⟩
    refine ⟨⟨hp, j, hj, ht⟩, ?_⟩
    rintro ⟨_, k, hk, ht'⟩
    have hjk := logPrimeMeshCell_unique (by exact_mod_cast hab) ht ht'
    subst k
    exact hjK hk
  · rintro ⟨⟨hp, j, hj, ht⟩, hK⟩
    refine ⟨hp, j, ⟨hj, ?_⟩, ht⟩
    intro hjK
    exact hK ⟨hp, j, hjK, ht⟩

private theorem jointSignatureOwnerClasses_disjoint (D : HistoricalPrefixCapData)
    {d : ℕ} {Σ : Type*} [DecidableEq Σ]
    (sig : (Fin d → Fin (D.m + 1)) → Σ) {σ τ : Σ} (hστ : σ ≠ τ) :
    Disjoint ((D.jointMeshCells d).filter (fun j => sig j = σ))
      ((D.jointMeshCells d).filter (fun j => sig j = τ)) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  exact hστ ((Finset.mem_filter.mp hj).2.symm.trans (Finset.mem_filter.mp hk).2)

/-- The real tuple partition is finite and exact on the original ambient
cube. Outside-cube tuples are not silently assigned a selected cell. -/
theorem jointSignatureTupleClasses_partition (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) {d : ℕ} {Σ : Type*} [Fintype Σ] [DecidableEq Σ]
    (sig : (Fin d → Fin (D.m + 1)) → Σ)
    (N : ℕ) (S : Finset (Fin d → ℕ)) :
    Finset.univ.biUnion (fun σ => D.jointOwnedTuples N S
      ((D.jointMeshCells d).filter (fun j => sig j = σ))) =
      S.filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ))) := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_jointOwnedTuples, Finset.mem_filter, mem_jointMeshCells]
  constructor
  · rintro ⟨σ, hp, j, _, ht⟩
    exact ⟨hp, logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht⟩
  · rintro ⟨hp, ht⟩
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m ht
    exact ⟨sig j, hp, j, rfl, hj⟩

theorem sum_jointSignatureTupleClasses (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) {d : ℕ} {Σ : Type*} [Fintype Σ] [DecidableEq Σ]
    (sig : (Fin d → Fin (D.m + 1)) → Σ)
    (N : ℕ) (S : Finset (Fin d → ℕ)) (w : (Fin d → ℕ) → ℝ) :
    (∑ σ : Σ, ∑ p ∈ D.jointOwnedTuples N S
      ((D.jointMeshCells d).filter (fun j => sig j = σ)), w p) =
      ∑ p ∈ S.filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ))), w p := by
  have hdisj : ((Finset.univ : Finset Σ) : Set Σ).PairwiseDisjoint
      (fun σ => D.jointOwnedTuples N S
        ((D.jointMeshCells d).filter (fun j => sig j = σ))) := by
    intro σ _ τ _ hστ
    exact D.jointOwnedTuples_disjoint hab.le N S
      (D.jointSignatureOwnerClasses_disjoint sig hστ)
  rw [← Finset.sum_biUnion hdisj, D.jointSignatureTupleClasses_partition hab sig N S]

def historicalFrontierOwnershipClass (D : HistoricalPrefixCapData) (N : ℕ)
    (carrier : List ℕ) (σ : Bool × Bool × Bool) : Finset (Fin 5 → ℕ) :=
  D.jointOwnedTuples N
    (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier)
    (D.jointSelectionOwners5 σ)

def historicalAdmittedOwnershipClass (D : HistoricalPrefixCapData) (N : ℕ)
    (carrier : List ℕ) (σ : Bool × Bool) : Finset (Fin 4 → ℕ) :=
  D.jointOwnedTuples N
    (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier)
    (D.jointSelectionOwners4 σ)

theorem historicalFrontierOwnershipClasses_partition (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) :
    Finset.univ.biUnion (D.historicalFrontierOwnershipClass N carrier) =
      (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ))) := by
  exact D.jointSignatureTupleClasses_partition hab D.jointSelectionSignature5 N _

theorem historicalAdmittedOwnershipClasses_partition (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) :
    Finset.univ.biUnion (D.historicalAdmittedOwnershipClass N carrier) =
      (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ))) := by
  exact D.jointSignatureTupleClasses_partition hab D.jointSelectionSignature4 N _

theorem historicalFrontierOwnershipClass_disjoint (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℕ) (carrier : List ℕ)
    {σ τ : Bool × Bool × Bool} (hστ : σ ≠ τ) :
    Disjoint (D.historicalFrontierOwnershipClass N carrier σ)
      (D.historicalFrontierOwnershipClass N carrier τ) := by
  apply D.jointOwnedTuples_disjoint hab
  exact D.jointSignatureOwnerClasses_disjoint D.jointSelectionSignature5 hστ

theorem historicalAdmittedOwnershipClass_disjoint (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℕ) (carrier : List ℕ)
    {σ τ : Bool × Bool} (hστ : σ ≠ τ) :
    Disjoint (D.historicalAdmittedOwnershipClass N carrier σ)
      (D.historicalAdmittedOwnershipClass N carrier τ) := by
  apply D.jointOwnedTuples_disjoint hab
  exact D.jointSignatureOwnerClasses_disjoint D.jointSelectionSignature4 hστ

/-- All eight classes retain the genuine third-policy next candidates. -/
theorem sum_historicalFrontierOwnershipClasses (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) (w : (Fin 5 → ℕ) → ℝ) :
    (∑ σ : Bool × Bool × Bool,
      ∑ p ∈ D.historicalFrontierOwnershipClass N carrier σ, w p) =
      ∑ p ∈ (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ))), w p := by
  exact D.sum_jointSignatureTupleClasses hab D.jointSelectionSignature5 N _ w

/-- An admitted fourth parent has exactly four ancestor-selection classes. -/
theorem sum_historicalAdmittedOwnershipClasses (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (N : ℕ) (carrier : List ℕ) (w : (Fin 4 → ℕ) → ℝ) :
    (∑ σ : Bool × Bool,
      ∑ p ∈ D.historicalAdmittedOwnershipClass N carrier σ, w p) =
      ∑ p ∈ (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeBox (fun _ => (D.a : ℝ)) (fun _ => (D.b : ℝ))), w p := by
  exact D.sum_jointSignatureTupleClasses hab D.jointSelectionSignature4 N _ w

/-- A next candidate's first four choices really are an admitted parent;
the final candidate's own test is not used to obtain this fact. -/
theorem historicalFrontier_project4_mem_admitted (D : HistoricalPrefixCapData)
    (N : ℕ) (carrier : List ℕ) (p : Fin 5 → ℕ)
    (hp : p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier) :
    historicalPrefixProject (by omega : 4 ≤ 5) p ∈
      firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier := by
  have hh := (mem_firstExitFrontierTuples_iff 4 _ carrier p).mp hp
  have hcoords : List.ofFn (historicalPrefixProject (by omega : 4 ≤ 5) p) =
      (List.ofFn p).dropLast := by
    simp [List.ofFn_succ, historicalPrefixProject]
  apply (mem_firstExitAdmittedTuples_iff 4 _ carrier _).mpr
  rw [hcoords]
  exact ⟨(List.dropLast_sublist (List.ofFn p)).trans hh.1, hh.2⟩

theorem jointSelectionSignature4_project (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    D.jointSelectionSignature4 (historicalPrefixProject (by omega : 4 ≤ 5) j) =
      ((D.jointSelectionSignature5 j).1, (D.jointSelectionSignature5 j).2.1) := by
  simp only [jointSelectionSignature4, jointSelectionSignature5,
    D.jointMesh_ancestor_345]

/-- The eight candidate classes project to their actual four admitted
parent classes. The fifth flag is forgotten without changing a parent flag. -/
theorem historicalFrontierOwnershipClass_project4_mem (D : HistoricalPrefixCapData)
    (N : ℕ) (carrier : List ℕ) (σ : Bool × Bool × Bool) (p : Fin 5 → ℕ)
    (hp : p ∈ D.historicalFrontierOwnershipClass N carrier σ) :
    historicalPrefixProject (by omega : 4 ≤ 5) p ∈
      D.historicalAdmittedOwnershipClass N carrier (σ.1, σ.2.1) := by
  obtain ⟨hfront, j, hj, ht⟩ := (D.mem_jointOwnedTuples N _ _ p).mp hp
  apply (D.mem_jointOwnedTuples N _ _ _).mpr
  refine ⟨D.historicalFrontier_project4_mem_admitted N carrier p hfront,
    historicalPrefixProject (by omega : 4 ≤ 5) j, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨D.mem_jointMeshCells 4 _, ?_⟩
    rw [D.jointSelectionSignature4_project, (Finset.mem_filter.mp hj).2]
  · exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht

theorem cell5_on_jointSelectionOwners (D : HistoricalPrefixCapData)
    (σ : Bool × Bool × Bool) (j : Fin 5 → Fin (D.m + 1))
    (hj : j ∈ D.jointSelectionOwners5 σ) :
    D.cell5 j = if σ.2.2 then D.cap5 j else
      if σ.2.1 then D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
      if σ.1 then D.cap3 (historicalPrefixProject (by omega : 3 ≤ 5) j) else D.old := by
  have hs := (Finset.mem_filter.mp hj).2
  rw [← hs, D.cell5_jointMesh_expansion j]
  simp [jointSelectionSignature5]

theorem old5_on_jointSelectionOwners (D : HistoricalPrefixCapData)
    (σ : Bool × Bool × Bool) (j : Fin 5 → Fin (D.m + 1))
    (hj : j ∈ D.jointSelectionOwners5 σ) :
    D.old5 j =
      if σ.2.1 then D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
      if σ.1 then D.cap3 (historicalPrefixProject (by omega : 3 ≤ 5) j) else D.old := by
  have hs := (Finset.mem_filter.mp hj).2
  rw [← hs]
  simp [old5, cell4, old4, cell3, jointSelectionSignature5, D.jointMesh_ancestor_345]

theorem cell4_on_jointSelectionOwners (D : HistoricalPrefixCapData)
    (σ : Bool × Bool) (j : Fin 4 → Fin (D.m + 1))
    (hj : j ∈ D.jointSelectionOwners4 σ) :
    D.cell4 j = if σ.2 then D.cap4 j else
      if σ.1 then D.cap3 (historicalPrefixProject (by omega : 3 ≤ 4) j) else D.old := by
  have hs := (Finset.mem_filter.mp hj).2
  rw [← hs]
  simp [cell4, old4, cell3, jointSelectionSignature4]

theorem old4_on_jointSelectionOwners (D : HistoricalPrefixCapData)
    (σ : Bool × Bool) (j : Fin 4 → Fin (D.m + 1))
    (hj : j ∈ D.jointSelectionOwners4 σ) :
    D.old4 j =
      if σ.1 then D.cap3 (historicalPrefixProject (by omega : 3 ≤ 4) j) else D.old := by
  have hs := (Finset.mem_filter.mp hj).2
  rw [← hs]
  simp [old4, cell3, jointSelectionSignature4]

/-- An actual finite owned-tuple sum can be written cellwise whenever the
given value has its proved constant value on each owner. -/
theorem sum_jointOwnedTuples_cellwise (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) {d : ℕ} (N : ℕ) (S : Finset (Fin d → ℕ))
    (J : Finset (Fin d → Fin (D.m + 1)))
    (F : (Fin d → ℕ) → ℝ) (G : (Fin d → Fin (D.m + 1)) → (Fin d → ℕ) → ℝ)
    (hFG : ∀ p ∈ S, ∀ j ∈ J,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j →
        F p = G j p) :
    (∑ p ∈ D.jointOwnedTuples N S J, F p) =
      ∑ j ∈ J, ∑ p ∈ S.filter (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j), G j p := by
  simp only [jointOwnedTuples, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hex : ∃ j ∈ J, actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [if_pos ⟨j, hj, ht⟩, hFG p hp j hj ht]
    symm
    calc
      _ = if actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then G j p else 0 := by
        apply Finset.sum_eq_single_of_mem j hj
        intro k _ hkj
        apply if_neg
        intro htk
        exact hkj (logPrimeMeshCell_unique (by exact_mod_cast hab) htk ht)
      _ = _ := if_pos ht
  · rw [if_neg hex]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    apply if_neg
    intro ht
    exact hex ⟨j, hj, ht⟩

/-- Within each one of the eight actual frontier classes, the weighted cap
sum keeps all three fallback branches with their original stored values. -/
theorem sum_historicalFrontierClass_effective_cap (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℕ) (carrier : List ℕ) (σ : Bool × Bool × Bool)
    (w : (Fin 5 → ℕ) → ℝ) (f : ℚ → ℝ) :
    (∑ p ∈ D.historicalFrontierOwnershipClass N carrier σ,
      w p * f (D.exponent5 (actualPrimeTupleLog N p))) =
      ∑ j ∈ D.jointSelectionOwners5 σ,
        ∑ p ∈ (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
          (fun p => actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j),
          w p * f (if σ.2.2 then D.cap5 j else
            if σ.2.1 then D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
            if σ.1 then D.cap3 (historicalPrefixProject (by omega : 3 ≤ 5) j) else
              D.old) := by
  apply D.sum_jointOwnedTuples_cellwise hab
  intro p _ j hj ht
  rw [D.exponent5_on_cell hab _ j ht, D.cell5_on_jointSelectionOwners σ j hj]

theorem sum_historicalAdmittedClass_effective_cap (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℕ) (carrier : List ℕ) (σ : Bool × Bool)
    (w : (Fin 4 → ℕ) → ℝ) (f : ℚ → ℝ) :
    (∑ p ∈ D.historicalAdmittedOwnershipClass N carrier σ,
      w p * f (D.exponent4 (actualPrimeTupleLog N p))) =
      ∑ j ∈ D.jointSelectionOwners4 σ,
        ∑ p ∈ (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
          (fun p => actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j),
          w p * f (if σ.2 then D.cap4 j else
            if σ.1 then D.cap3 (historicalPrefixProject (by omega : 3 ≤ 4) j) else
              D.old) := by
  apply D.sum_jointOwnedTuples_cellwise hab
  intro p _ j hj ht
  rw [D.exponent4_on_cell hab _ j ht, D.cell4_on_jointSelectionOwners σ j hj]

/-- The old fifth residual in each class reads the full effective fourth
owner. Its fifth flag is irrelevant, including a restored old exit. -/
theorem sum_historicalFrontierClass_inherited_cap (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℕ) (carrier : List ℕ) (σ : Bool × Bool × Bool)
    (w : (Fin 5 → ℕ) → ℝ) (f : ℚ → ℝ) :
    (∑ p ∈ D.historicalFrontierOwnershipClass N carrier σ,
      w p * f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5)
        (actualPrimeTupleLog N p)))) =
      ∑ j ∈ D.jointSelectionOwners5 σ,
        ∑ p ∈ (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
          (fun p => actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j),
          w p * f (if σ.2.1 then
            D.cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) else
            if σ.1 then D.cap3 (historicalPrefixProject (by omega : 3 ≤ 5) j) else
              D.old) := by
  apply D.sum_jointOwnedTuples_cellwise hab
  intro p _ j hj ht
  have he := D.exponent4_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)
  change w p * f (D.exponent4 _) = _
  rw [he]
  change w p * f (D.old5 j) = _
  rw [D.old5_on_jointSelectionOwners σ j hj]

/-- The fourth old value uses its effective third owner, in every one of
the four actual admitted-parent classes. -/
theorem sum_historicalAdmittedClass_inherited_cap (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℕ) (carrier : List ℕ) (σ : Bool × Bool)
    (w : (Fin 4 → ℕ) → ℝ) (f : ℚ → ℝ) :
    (∑ p ∈ D.historicalAdmittedOwnershipClass N carrier σ,
      w p * f (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4)
        (actualPrimeTupleLog N p)))) =
      ∑ j ∈ D.jointSelectionOwners4 σ,
        ∑ p ∈ (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ)) carrier).filter
          (fun p => actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j),
          w p * f (if σ.1 then
            D.cap3 (historicalPrefixProject (by omega : 3 ≤ 4) j) else D.old) := by
  apply D.sum_jointOwnedTuples_cellwise hab
  intro p _ j hj ht
  have he := D.exponent3_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)
  change w p * f (D.exponent3 _) = _
  rw [he]
  change w p * f (D.old4 j) = _
  rw [D.old4_on_jointSelectionOwners σ j hj]

end HistoricalPrefixCapData

end

end ImbalancedChen
