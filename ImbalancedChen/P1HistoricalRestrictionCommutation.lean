import ImbalancedChen.P1HistoricalLevelCheckPreservation

/-!
# Composing restrictions and partitioning actual fifth corrections

Integration import map: the sibling source-only preservation draft is to
be installed as `ImbalancedChen/P1HistoricalLevelCheckPreservation.lean`.
No such installation or compilation is performed by this draft.

The support assertions below include the earlier ancestor selections.
The correction is defined from the actual exponent lookup, and its finite
partition uses the same inherited fourth value in both pieces.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

section Composition

variable (D : HistoricalPrefixCapData)
variable (J3 K3 : Finset (Fin 3 → Fin (D.m + 1)))
variable (J4 K4 : Finset (Fin 4 → Fin (D.m + 1)))
variable (J5 K5 : Finset (Fin 5 → Fin (D.m + 1)))

theorem p1RestrictSelections_comp :
    (D.p1RestrictSelections J3 J4 J5).p1RestrictSelections K3 K4 K5 =
      D.p1RestrictSelections (J3 ∩ K3) (J4 ∩ K4) (J5 ∩ K5) := by
  simp only [p1RestrictSelections, Finset.inter_assoc]

theorem p1RestrictSelections_idempotent :
    (D.p1RestrictSelections J3 J4 J5).p1RestrictSelections J3 J4 J5 =
      D.p1RestrictSelections J3 J4 J5 := by
  rw [D.p1RestrictSelections_comp (J3 := J3) (K3 := J3)
    (J4 := J4) (K4 := J4) (J5 := J5) (K5 := J5)]
  simp only [Finset.inter_self]

theorem p1RestrictSelections_commute :
    (D.p1RestrictSelections J3 J4 J5).p1RestrictSelections K3 K4 K5 =
      (D.p1RestrictSelections K3 K4 K5).p1RestrictSelections J3 J4 J5 := by
  rw [D.p1RestrictSelections_comp (J3 := J3) (K3 := K3)
      (J4 := J4) (K4 := K4) (J5 := J5) (K5 := K5),
    D.p1RestrictSelections_comp (J3 := K3) (K3 := J3)
      (J4 := K4) (K4 := J4) (J5 := K5) (K5 := J5)]
  simp only [Finset.inter_comm]

/-- Both successive restrictions retain the original, unmodified check. -/
theorem p1RestrictSelections_comp_levelCheck (hcheck : D.levelCheck = true) :
    ((D.p1RestrictSelections J3 J4 J5).p1RestrictSelections K3 K4 K5).levelCheck = true := by
  exact (D.p1RestrictSelections J3 J4 J5).p1RestrictSelections_levelCheck K3 K4 K5
    (D.p1RestrictSelections_levelCheck J3 J4 J5 hcheck)

theorem p1RestrictFifth_comp :
    (D.p1RestrictFifth J5).p1RestrictFifth K5 = D.p1RestrictFifth (J5 ∩ K5) := by
  simp only [p1RestrictFifth, Finset.inter_assoc]

theorem p1RestrictFifth_idempotent :
    (D.p1RestrictFifth J5).p1RestrictFifth J5 = D.p1RestrictFifth J5 := by
  rw [D.p1RestrictFifth_comp J5 J5, Finset.inter_self]

theorem p1RestrictFifth_commute :
    (D.p1RestrictFifth J5).p1RestrictFifth K5 =
      (D.p1RestrictFifth K5).p1RestrictFifth J5 := by
  rw [D.p1RestrictFifth_comp J5 K5, D.p1RestrictFifth_comp K5 J5,
    Finset.inter_comm J5 K5]

theorem p1RestrictFifth_comp_levelCheck (hcheck : D.levelCheck = true) :
    ((D.p1RestrictFifth J5).p1RestrictFifth K5).levelCheck = true := by
  exact (D.p1RestrictFifth J5).p1RestrictFifth_levelCheck K5
    (D.p1RestrictFifth_levelCheck J5 hcheck)

end Composition

/-- Only selected owners in the symmetric difference can change a lookup. -/
def p1RestrictionDifferenceCells {d m : ℕ}
    (S J K : Finset (Fin d → Fin (m + 1))) : Finset (Fin d → Fin (m + 1)) :=
  ((S ∩ J) \ (S ∩ K)) ∪ ((S ∩ K) \ (S ∩ J))

theorem p1RestrictedMembership_iff_of_outside {d m : ℕ} (a b : ℚ)
    (S J K : Finset (Fin d → Fin (m + 1))) (t : Fin d → ℝ)
    (hout : ∀ j ∈ p1RestrictionDifferenceCells S J K,
      t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j)
    (j : Fin d → Fin (m + 1))
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    j ∈ S ∩ J ↔ j ∈ S ∩ K := by
  constructor
  · intro hJ
    by_contra hK
    exact hout j (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hJ, hK⟩))) ht
  · intro hK
    by_contra hJ
    exact hout j (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hK, hJ⟩))) ht

/-- This statement includes points outside the mesh and all internal faces. -/
theorem p1HistoricalLookup_eq_of_owner_membership {d m : ℕ} (a b : ℚ)
    (hab : a ≤ b) (J K : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (hagree : ∀ j, t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j →
      (j ∈ J ↔ j ∈ K)) :
    historicalPrefixLookup a b m J cap fallback t =
      historicalPrefixLookup a b m K cap fallback t := by
  by_cases hex : ∃ j ∈ J, t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [historicalPrefixLookup_on_cell a b hab m J cap fallback t j hj ht,
      historicalPrefixLookup_on_cell a b hab m K cap fallback t j ((hagree j ht).mp hj) ht]
  · have hJ : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j := by
      intro j hj ht
      exact hex ⟨j, hj, ht⟩
    have hK : ∀ j ∈ K, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j := by
      intro j hj ht
      exact hJ j ((hagree j ht).mpr hj) ht
    rw [historicalPrefixLookup_outside a b m J cap fallback t hJ,
      historicalPrefixLookup_outside a b m K cap fallback t hK]

section Support

variable (D : HistoricalPrefixCapData)
variable (J3 K3 : Finset (Fin 3 → Fin (D.m + 1)))
variable (J4 K4 : Finset (Fin 4 → Fin (D.m + 1)))
variable (J5 K5 : Finset (Fin 5 → Fin (D.m + 1)))

theorem p1RestrictSelections_exponent3_eq_off_difference (hab : D.a ≤ D.b)
    (t : Fin 3 → ℝ)
    (hout : ∀ j ∈ p1RestrictionDifferenceCells D.cells3 J3 K3,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictSelections J3 J4 J5).exponent3 t =
      (D.p1RestrictSelections K3 K4 K5).exponent3 t := by
  apply p1HistoricalLookup_eq_of_owner_membership D.a D.b hab
    (D.cells3 ∩ J3) (D.cells3 ∩ K3) D.cap3 D.old t
  exact p1RestrictedMembership_iff_of_outside D.a D.b D.cells3 J3 K3 t hout

theorem p1RestrictSelections_exponent4_eq_off_difference (hab : D.a ≤ D.b)
    (t : Fin 4 → ℝ)
    (h3 : ∀ j ∈ p1RestrictionDifferenceCells D.cells3 J3 K3,
      historicalPrefixProject (by omega : 3 ≤ 4) t ∉
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (h4 : ∀ j ∈ p1RestrictionDifferenceCells D.cells4 J4 K4,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictSelections J3 J4 J5).exponent4 t =
      (D.p1RestrictSelections K3 K4 K5).exponent4 t := by
  change historicalPrefixLookup D.a D.b D.m (D.cells4 ∩ J4) D.cap4
      ((D.p1RestrictSelections J3 J4 J5).exponent3
        (historicalPrefixProject (by omega : 3 ≤ 4) t)) t =
    historicalPrefixLookup D.a D.b D.m (D.cells4 ∩ K4) D.cap4
      ((D.p1RestrictSelections K3 K4 K5).exponent3
        (historicalPrefixProject (by omega : 3 ≤ 4) t)) t
  rw [D.p1RestrictSelections_exponent3_eq_off_difference
    (J3 := J3) (K3 := K3) (J4 := J4) (K4 := K4) (J5 := J5) (K5 := K5) hab _ h3]
  apply p1HistoricalLookup_eq_of_owner_membership D.a D.b hab
  exact p1RestrictedMembership_iff_of_outside D.a D.b D.cells4 J4 K4 t h4

/-- Fifth support includes the pullbacks of both earlier difference
families, since those families can change the fifth fallback. -/
theorem p1RestrictSelections_exponent5_eq_off_difference (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ)
    (h3 : ∀ j ∈ p1RestrictionDifferenceCells D.cells3 J3 K3,
      historicalPrefixProject (by omega : 3 ≤ 4)
        (historicalPrefixProject (by omega : 4 ≤ 5) t) ∉
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (h4 : ∀ j ∈ p1RestrictionDifferenceCells D.cells4 J4 K4,
      historicalPrefixProject (by omega : 4 ≤ 5) t ∉
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (h5 : ∀ j ∈ p1RestrictionDifferenceCells D.cells5 J5 K5,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictSelections J3 J4 J5).exponent5 t =
      (D.p1RestrictSelections K3 K4 K5).exponent5 t := by
  change historicalPrefixLookup D.a D.b D.m (D.cells5 ∩ J5) D.cap5
      ((D.p1RestrictSelections J3 J4 J5).exponent4
        (historicalPrefixProject (by omega : 4 ≤ 5) t)) t =
    historicalPrefixLookup D.a D.b D.m (D.cells5 ∩ K5) D.cap5
      ((D.p1RestrictSelections K3 K4 K5).exponent4
        (historicalPrefixProject (by omega : 4 ≤ 5) t)) t
  rw [D.p1RestrictSelections_exponent4_eq_off_difference
    (J3 := J3) (K3 := K3) (J4 := J4) (K4 := K4) (J5 := J5) (K5 := K5) hab _ h3 h4]
  apply p1HistoricalLookup_eq_of_owner_membership D.a D.b hab
  exact p1RestrictedMembership_iff_of_outside D.a D.b D.cells5 J5 K5 t h5

theorem p1RestrictSelections_level4_eq_off_difference (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ)
    (h3 : ∀ j ∈ p1RestrictionDifferenceCells D.cells3 J3 K3,
      historicalPrefixProject (by omega : 3 ≤ 4)
        (primeHistoryLogCoordinates N 4 history) ∉
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (h4 : ∀ j ∈ p1RestrictionDifferenceCells D.cells4 J4 K4,
      primeHistoryLogCoordinates N 4 history ∉
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictSelections J3 J4 J5).level4 N history =
      (D.p1RestrictSelections K3 K4 K5).level4 N history := by
  unfold level4
  rw [D.p1RestrictSelections_exponent4_eq_off_difference
    (J3 := J3) (K3 := K3) (J4 := J4) (K4 := K4) (J5 := J5) (K5 := K5) hab _ h3 h4]

theorem p1RestrictSelections_level5_eq_off_difference (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ)
    (h3 : ∀ j ∈ p1RestrictionDifferenceCells D.cells3 J3 K3,
      historicalPrefixProject (by omega : 3 ≤ 4)
        (historicalPrefixProject (by omega : 4 ≤ 5)
          (primeHistoryLogCoordinates N 5 history)) ∉
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (h4 : ∀ j ∈ p1RestrictionDifferenceCells D.cells4 J4 K4,
      historicalPrefixProject (by omega : 4 ≤ 5)
        (primeHistoryLogCoordinates N 5 history) ∉
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (h5 : ∀ j ∈ p1RestrictionDifferenceCells D.cells5 J5 K5,
      primeHistoryLogCoordinates N 5 history ∉
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.p1RestrictSelections J3 J4 J5).level5 N history =
      (D.p1RestrictSelections K3 K4 K5).level5 N history := by
  unfold level5
  rw [D.p1RestrictSelections_exponent5_eq_off_difference
    (J3 := J3) (K3 := K3) (J4 := J4) (K4 := K4) (J5 := J5) (K5 := K5) hab _ h3 h4 h5]

end Support

/-- The actual lookup correction, before rewriting it as a finite sum. -/
def p1RestrictedFifthCorrection (D : HistoricalPrefixCapData)
    (J : Finset (Fin 5 → Fin (D.m + 1))) (t : Fin 5 → ℝ) (f : ℚ → ℝ) : ℝ :=
  f ((D.p1RestrictFifth J).exponent5 t) -
    f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t))

theorem p1RestrictedFifthCorrection_eq_sum (D : HistoricalPrefixCapData)
    (J : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    D.p1RestrictedFifthCorrection J t f =
      ∑ j ∈ D.cells5 ∩ J,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0 := by
  exact D.p1RestrictFifth_apply_sub J hab t f

/-- Disjoint actual selected subfamilies partition the real correction.
The hypothesis permits J and K to overlap on unselected cells. -/
theorem p1RestrictedFifthCorrection_union (D : HistoricalPrefixCapData)
    (J K : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (hdisj : Disjoint (D.cells5 ∩ J) (D.cells5 ∩ K))
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    D.p1RestrictedFifthCorrection (J ∪ K) t f =
      D.p1RestrictedFifthCorrection J t f + D.p1RestrictedFifthCorrection K t f := by
  rw [D.p1RestrictedFifthCorrection_eq_sum (J ∪ K) hab t f,
    D.p1RestrictedFifthCorrection_eq_sum J hab t f,
    D.p1RestrictedFifthCorrection_eq_sum K hab t f]
  have hfamily : D.cells5 ∩ (J ∪ K) = (D.cells5 ∩ J) ∪ (D.cells5 ∩ K) := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_union, and_or_left]
  rw [hfamily, Finset.sum_union hdisj]

/-- Any retained family splits into an intersection and a deletion part.
Both pieces are actual restricted fifth lookups with the same old4. -/
theorem p1RestrictedFifthCorrection_partition (D : HistoricalPrefixCapData)
    (J K : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    D.p1RestrictedFifthCorrection J t f =
      D.p1RestrictedFifthCorrection (J ∩ K) t f +
        D.p1RestrictedFifthCorrection (J \ K) t f := by
  have hfamily : (J ∩ K) ∪ (J \ K) = J := by
    ext j
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint (D.cells5 ∩ (J ∩ K)) (D.cells5 ∩ (J \ K)) := by
    apply Finset.disjoint_left.mpr
    intro j hjI hjD
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hjD).2).2
      (Finset.mem_inter.mp (Finset.mem_inter.mp hjI).2).2
  have h := D.p1RestrictedFifthCorrection_union (J ∩ K) (J \ K) hab hdisj t f
  rw [hfamily] at h
  exact h

/-- The two real pieces in the preceding partition each retain the
original levelCheck; no new checked-cap assumption is introduced. -/
theorem p1RestrictedFifthCorrection_partition_checks (D : HistoricalPrefixCapData)
    (J K : Finset (Fin 5 → Fin (D.m + 1))) (hcheck : D.levelCheck = true) :
    (D.p1RestrictFifth (J ∩ K)).levelCheck = true ∧
      (D.p1RestrictFifth (J \ K)).levelCheck = true := by
  exact ⟨D.p1RestrictFifth_levelCheck (J ∩ K) hcheck,
    D.p1RestrictFifth_levelCheck (J \ K) hcheck⟩

/-- Further restriction removes exactly the complementary correction. -/
theorem p1RestrictedFifthCorrection_removed (D : HistoricalPrefixCapData)
    (J K : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    D.p1RestrictedFifthCorrection J t f -
        D.p1RestrictedFifthCorrection (J ∩ K) t f =
      D.p1RestrictedFifthCorrection (J \ K) t f := by
  rw [D.p1RestrictedFifthCorrection_partition J K hab t f]
  ring

/-- The same partition applies to the two literal own-cube gated lower
densities at an actual five-entry history. Each density keeps its gate. -/
theorem p1RestrictedFifthGatedCorrection_partition (D : HistoricalPrefixCapData)
    (J K : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (N cap : ℕ) (history : List ℕ) (hlen : history.length = 5) :
    actualOwnCubeGatedMinusDensity N cap ((D.p1RestrictFifth J).level5 (N : ℝ)) history -
        actualOwnCubeGatedMinusDensity N cap
          (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history =
      (actualOwnCubeGatedMinusDensity N cap
          ((D.p1RestrictFifth (J ∩ K)).level5 (N : ℝ)) history -
        actualOwnCubeGatedMinusDensity N cap
          (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history) +
      (actualOwnCubeGatedMinusDensity N cap
          ((D.p1RestrictFifth (J \ K)).level5 (N : ℝ)) history -
        actualOwnCubeGatedMinusDensity N cap
          (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history) := by
  have h := D.p1RestrictedFifthCorrection_partition J K hab
    (primeHistoryLogCoordinates (N : ℝ) 5 history)
    (fun q : ℚ =>
      if (history.prod : ℝ) * (history.headD 0 : ℝ) ^ 2 < (N : ℝ) ^ (q : ℝ) then
        actualSmallRosserMinusDensity N cap (history.headD 0 : ℝ)
          ((N : ℝ) ^ (q : ℝ) / (history.prod : ℝ)) else 0)
  simpa only [p1RestrictedFifthCorrection, actualOwnCubeGatedMinusDensity, level5, level4,
    primeHistoryLogCoordinates_eq_historicalPrefixProject (N : ℝ)
      (by omega : 4 ≤ 5) hlen] using h

private theorem p1List_sum_map_partition {α : Type*} (L : List α) (f g h : α → ℝ) :
    (∀ x ∈ L, f x = g x + h x) →
      (L.map f).sum = (L.map g).sum + (L.map h).sum := by
  induction L with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro hsum
      have hx := hsum x (by simp)
      have ht := ih (fun y hy => hsum y (by simp only [List.mem_cons]; exact Or.inr hy))
      simp only [List.map_cons, List.sum_cons]
      rw [hx, ht]
      ring

/-- Finite additive partition of the actual historical fifth saving on
the common third-capped rank-four frontier. No candidate is discarded by
an old own-cube filter, and the exact fourth fallback is shared. -/
theorem p1ActualHistoricalFifthSaving_partition (D : HistoricalPrefixCapData)
    (J K : Finset (Fin 5 → Fin (D.m + 1))) (hab : D.a ≤ D.b)
    (base : Bool → List ℕ → Bool) (N cap : ℕ) (z : ℝ) :
    actualHistoricalFifthSaving base (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        ((D.p1RestrictFifth J).level5 (N : ℝ)) N cap z =
      actualHistoricalFifthSaving base (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        ((D.p1RestrictFifth (J ∩ K)).level5 (N : ℝ)) N cap z +
      actualHistoricalFifthSaving base (D.level3 (N : ℝ)) (D.level4 (N : ℝ))
        ((D.p1RestrictFifth (J \ K)).level5 (N : ℝ)) N cap z := by
  unfold actualHistoricalFifthSaving
  apply p1List_sum_map_partition
  intro frontier hfrontier
  apply p1List_sum_map_partition
  intro candidate hcandidate
  have hlen4 := firstExitDepthFrontier_selected_length 4
    (thirdCappedUpperPolicy base (D.level3 (N : ℝ)))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z)
    true 1 (by simp) frontier hfrontier
  have hlen5 : candidate.selectedPrefix.length = 5 := by
    obtain ⟨_before, q, _after, _hremaining, rfl⟩ :=
      (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ candidate).mp hcandidate
    simp only [List.length_cons, hlen4]
  rw [D.p1RestrictedFifthGatedCorrection_partition J K hab N cap
    candidate.selectedPrefix hlen5]
  ring

end HistoricalPrefixCapData

end

end ImbalancedChen
