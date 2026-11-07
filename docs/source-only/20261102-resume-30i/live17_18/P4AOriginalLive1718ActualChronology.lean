import ImbalancedChen.P4AOriginalLive19ActualChronology

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original LIVE17/18 navigation, source exclusions and slots15--19.
The incoming source is G's original whole-box prime bank on E's common
constructor. No claim about held PhysicalRows, its existential selector,
or exhaustive58/87 coverage is made here.
-/
namespace ImbalancedChen.P4AOriginalLive1718ActualChronology
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P4AOriginalLive171819Atlas P4AOriginalLive171819CommonParent
open P4AOriginalLive171819PrimeBank

abbrev UnequalCell := P4AOriginalSeed7Unequal15Literal.UnequalCell
abbrev Data := P5OriginalCommonRefinedConstructor.OriginalData

/-- A strict original nonwinning branch bounds the actual tent, whichever
affine half its independently supplied navigation selected. -/
private theorem tent_le_plane (c : LiveCell) (m : Fin 64) (t : Point) :
    v (subset6 m t) ≤ plane c m t := by
  rw [v_eq_min]
  unfold plane
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

private theorem unequal_old6_strict (u : UnequalCell) (t : Point)
    (hs : sourceRows (.unequal18 u) t) :
    v (subset6 6 t) < oldCap (.unequal18 u) t := by
  exact (tent_le_plane (.unequal18 u) 6 t).trans_lt
    (source_plane_strict (.unequal18 u) t hs 6 (by norm_num)
      (by cases u <;> norm_num [winner]))

private theorem descending_subset_tent (i : Fin 15) (m : Fin 64) (t : Point)
    (hd : OriginalDescendingFifteenCellOwnership.StrictRows i t)
    (h0 : m ≠ 0) (h6 : m ≠ 6) :
    v (subset6 m t) < P2OriginalDescendingEighthLogSemantics.oldRaw t := by
  have hm : m.val ∈ Finset.Icc 1 63 := by
    apply Finset.mem_Icc.mpr
    constructor
    · have hmv : m.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    · omega
  have hb := hd.branches m.val hm (fun h => h6 (Fin.ext h))
  have heq : OriginalDescendingFifteenCellOwnership.subsetSum m.val t = subset6 m t := by
    simp [OriginalDescendingFifteenCellOwnership.subsetSum,
      OriginalDescendingFifteenCellOwnership.maskSlots, subset6,
      Finset.sum_filter, Fin.sum_univ_succ]
  have hle : v (subset6 m t) ≤
      OriginalDescendingFifteenCellOwnership.branchPlane i m.val t := by
    rw [v_eq_min]
    unfold OriginalDescendingFifteenCellOwnership.branchPlane
    rw [heq]
    split_ifs
    · exact min_le_left _ _
    · exact min_le_right _ _
  exact hle.trans_lt hb

private theorem ascending_fifty_tent (i : Fin 13) (t : Point)
    (ha : OriginalAscendingThirteenCellOwnership.StrictRows i t) :
    v (subset6 50 t) < P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t := by
  have hb := ha.branches 50 (by norm_num) (by norm_num)
  have heq : OriginalAscendingThirteenCellOwnership.subsetSum 50 t = subset6 50 t := by
    norm_num [OriginalAscendingThirteenCellOwnership.subsetSum,
      OriginalAscendingThirteenCellOwnership.maskSlots, subset6,
      Finset.sum_filter, Fin.sum_univ_succ]
  have hle : v (subset6 50 t) ≤
      OriginalAscendingThirteenCellOwnership.branchPlane i 50 t := by
    rw [v_eq_min]
    unfold OriginalAscendingThirteenCellOwnership.branchPlane
    rw [heq]
    split_ifs
    · exact min_le_left _ _
    · exact min_le_right _ _
  exact hle.trans_lt hb

/-- The seed's actual mask9 or mask50 row, rather than its stage tag. -/
private theorem seed_unequal_winner (u : UnequalCell) (t : Point)
    (hseed : P4AOriginalSeed7Unequal15Literal.seed7SourceRows t) :
    v (subset6 (winner (.unequal18 u)) t) <
      P4AOriginalSeed7Unequal15Literal.D23 t := by
  cases u with
  | nine i =>
      have hr := hseed (41 : Fin 96)
      norm_num [P4AOriginalSeed7Unequal15Literal.seed7Rows,
        P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hr
      rw [winner]
      have hle := min_le_right (A (subset6 9 t)) (C (subset6 9 t))
      rw [← v_eq_min] at hle
      apply hle.trans_lt
      norm_num [subset6, C, P4AOriginalSeed7Unequal15Literal.D23,
        P4AOriginalSeed7Unequal15Literal.D, Fin.sum_univ_succ]
      linarith
  | fiftyAsc =>
      have hr := hseed (82 : Fin 96)
      norm_num [P4AOriginalSeed7Unequal15Literal.seed7Rows,
        P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hr
      rw [winner]
      have hle := min_le_left (A (subset6 50 t)) (C (subset6 50 t))
      rw [← v_eq_min] at hle
      apply hle.trans_lt
      norm_num [subset6, A, P4AOriginalSeed7Unequal15Literal.D23,
        P4AOriginalSeed7Unequal15Literal.D, Fin.sum_univ_succ]
      linarith
  | fiftyDesc =>
      have hr := hseed (82 : Fin 96)
      norm_num [P4AOriginalSeed7Unequal15Literal.seed7Rows,
        P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hr
      rw [winner]
      have hle := min_le_left (A (subset6 50 t)) (C (subset6 50 t))
      rw [← v_eq_min] at hle
      apply hle.trans_lt
      norm_num [subset6, A, P4AOriginalSeed7Unequal15Literal.D23,
        P4AOriginalSeed7Unequal15Literal.D, Fin.sum_univ_succ]
      linarith

theorem live17_not_seed7 (i : Fin 15) (t : Point)
    (hs : sourceRows (.descending17 i) t) :
    ¬ P4AOriginalSeed7Unequal15Literal.seed7SourceRows t := by
  intro hseed
  have hd := (source17_guard i t hs).descending
  have ha := hseed (17 : Fin 96)
  norm_num [P4AOriginalSeed7Unequal15Literal.seed7Rows,
    P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at ha
  dsimp [P2OriginalDescendingEighthLogSemantics.selectedSum, mu] at hd
  linarith

theorem live17_not_ascending14 (i : Fin 15) (t : Point)
    (hs : sourceRows (.descending17 i) t) :
    ¬ P4AOriginalAscending14Literal42.ascending14Owns t := by
  intro ha
  exact P4AOriginalAscending14Literal42.ascending14_disjoint_descending15
    t ha i (source17_guard i t hs)

theorem live17_not_unequal15 (i : Fin 15) (t : Point)
    (hs : sourceRows (.descending17 i) t) (u : UnequalCell) :
    ¬ P4AOriginalSeed7Unequal15Literal.unequalSourceRows u t := by
  intro hu
  have hu' : sourceRows (.unequal18 u) t := by cases u <;> exact hu
  have heq := live_owner_unique (.descending17 i) (.unequal18 u) t hs hu'
  cases heq

theorem live17_not_ascending13 (i : Fin 15) (t : Point)
    (hs : sourceRows (.descending17 i) t) :
    ¬ ∃ j : Fin 13, OriginalAscendingThirteenCellOwnership.StrictRows j t := by
  rintro ⟨j, ha⟩
  have hd := (source17_guard i t hs).oldWinner
  have hh := ha.ascendingThird
  dsimp [P2OriginalDescendingEighthLogSemantics.d] at hd
  linarith

theorem live18_not_seed7 (u : UnequalCell) (t : Point)
    (hs : sourceRows (.unequal18 u) t) :
    ¬ P4AOriginalSeed7Unequal15Literal.seed7SourceRows t := by
  intro hseed
  have hwin := seed_unequal_winner u t hseed
  rw [source_winner_active (.unequal18 u) t hs] at hwin
  have h6 := unequal_old6_strict u t hs
  have hside := hseed (14 : Fin 96)
  norm_num [P4AOriginalSeed7Unequal15Literal.seed7Rows,
    P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hside
  have hmu : mu ≤ t 1 + t 2 := by dsimp [mu]; linarith
  have heq : v (subset6 6 t) = P4AOriginalSeed7Unequal15Literal.D23 t := by
    simpa [subset6, P4AOriginalSeed7Unequal15Literal.D23,
      P4AOriginalSeed7Unequal15Literal.D, C, Fin.sum_univ_succ] using v_eq_C hmu
  rw [heq] at h6
  exact (lt_asymm h6 hwin)

/-- Original ascending14 supplies all old subset planes. Its old winner6
cannot coexist with the strict unequal winner9/50, even at closed planes. -/
theorem live18_not_ascending14 (u : UnequalCell) (t : Point)
    (hs : sourceRows (.unequal18 u) t) :
    ¬ P4AOriginalAscending14Literal42.ascending14Owns t := by
  rintro ⟨i, _hi, ha⟩
  have h6 := unequal_old6_strict u t hs
  have heq : v (subset6 6 t) = P2OriginalAscendingEighthCapDictionary.R t := by
    rw [v_eq_min]
    norm_num [subset6, Fin.sum_univ_succ]
    exact min_eq_right ha.old_descending.le
  rw [heq] at h6
  have hupper : oldCap (.unequal18 u) t ≤ P2OriginalAscendingEighthCapDictionary.R t := by
    have hwin := source_winner_active (.unequal18 u) t hs
    rw [← hwin]
    cases u with
    | nine j =>
        simpa [winner, subset6, P2OriginalAscendingEighthCapDictionary.subsetSum,
          Fin.sum_univ_succ] using
          P2OriginalAscendingEighthCapDictionary.old_tents_below_R _ t ha.old_planes
            ({0,3} : Finset (Fin 6)) (by simp [P2OriginalAscendingEighthCapDictionary.oldMasks])
    | fiftyAsc =>
        simpa [winner, subset6, P2OriginalAscendingEighthCapDictionary.subsetSum,
          Fin.sum_univ_succ, add_assoc] using
          P2OriginalAscendingEighthCapDictionary.old_tents_below_R _ t ha.old_planes
            ({1,4,5} : Finset (Fin 6)) (by simp [P2OriginalAscendingEighthCapDictionary.oldMasks])
    | fiftyDesc =>
        simpa [winner, subset6, P2OriginalAscendingEighthCapDictionary.subsetSum,
          Fin.sum_univ_succ, add_assoc] using
          P2OriginalAscendingEighthCapDictionary.old_tents_below_R _ t ha.old_planes
            ({1,4,5} : Finset (Fin 6)) (by simp [P2OriginalAscendingEighthCapDictionary.oldMasks])
  exact (not_lt_of_ge hupper) h6

theorem live18_not_descending15 (u : UnequalCell) (t : Point)
    (hs : sourceRows (.unequal18 u) t) :
    ¬ ∃ j : Fin 15, OriginalDescendingFifteenCellOwnership.StrictRows j t := by
  rintro ⟨j, hd⟩
  have h6 := unequal_old6_strict u t hs
  have heq : v (subset6 6 t) = P2OriginalDescendingEighthLogSemantics.oldRaw t := by
    simpa [subset6, P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, Fin.sum_univ_succ] using v_eq_C hd.oldWinner.le
  rw [heq] at h6
  have hw := descending_subset_tent j (winner (.unequal18 u)) t hd
    (by cases u <;> norm_num [winner]) (by cases u <;> norm_num [winner])
  rw [source_winner_active (.unequal18 u) t hs] at hw
  exact lt_asymm h6 hw

theorem live18_not_ascending13 (u : UnequalCell) (t : Point)
    (hs : sourceRows (.unequal18 u) t) :
    ¬ ∃ j : Fin 13, OriginalAscendingThirteenCellOwnership.StrictRows j t := by
  rintro ⟨j, ha⟩
  cases u with
  | nine i =>
      have hr := hs (16 : Fin 97)
      fin_cases i <;>
        norm_num [rows, P4AOriginalSeed7Unequal15Literal.nineRows,
          eval, P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hr <;>
        have hside := ha.ascendingThird <;> dsimp [mu] at hside <;> linarith
  | fiftyAsc =>
      have h9 := (tent_le_plane (.unequal18 .fiftyAsc) 9 t).trans_lt
        (source_plane_strict (.unequal18 .fiftyAsc) t hs 9 (by norm_num) (by norm_num [winner]))
      have h9eq : v (subset6 9 t) =
          P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t := by
        simpa [subset6, P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,
          Fin.sum_univ_succ] using v_eq_A ha.oldWinner.le
      rw [h9eq] at h9
      have h50 := ascending_fifty_tent j t ha
      have hw := source_winner_active (.unequal18 .fiftyAsc) t hs
      change v (subset6 50 t) = _ at hw
      rw [hw] at h50
      exact lt_asymm h9 h50
  | fiftyDesc =>
      have h9 := (tent_le_plane (.unequal18 .fiftyDesc) 9 t).trans_lt
        (source_plane_strict (.unequal18 .fiftyDesc) t hs 9 (by norm_num) (by norm_num [winner]))
      have h9eq : v (subset6 9 t) =
          P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t := by
        simpa [subset6, P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,
          Fin.sum_univ_succ] using v_eq_A ha.oldWinner.le
      rw [h9eq] at h9
      have h50 := ascending_fifty_tent j t ha
      have hw := source_winner_active (.unequal18 .fiftyDesc) t hs
      change v (subset6 50 t) = _ at hw
      rw [hw] at h50
      exact lt_asymm h9 h50

/-- Exact original source navigation for any active unequal action. -/
theorem unequal_active_owner (u v : UnequalCell) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (hs : sourceRows (.unequal18 u) (point8 N pre))
    (hv : P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 v pre) : v = u := by
  have hv' : sourceRows (.unequal18 v) (point8 N pre) := by
    cases v <;> exact hv.2.1
  have heq := live_owner_unique (.unequal18 v) (.unequal18 u) _ hv' hs
  cases heq
  rfl

/-- Derives the actual action guard from rows, the real retained sixth
history and the genuine sixth upper bound. H7<lambda3 is not used. -/
theorem unequal_actual (u : UnequalCell) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 8)
    (hs : sourceRows (.unequal18 u) (point8 N pre))
    (hh : P2OriginalDescendingEighthLogSemantics.history7 (point8 N pre) <
      lambda6 (rosserAncestor 6 pre))
    (hc : lambda6 (rosserAncestor 6 pre) ≤ oldCap (.unequal18 u) (point8 N pre)) :
    P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 u pre := by
  refine ⟨hlen, ?_, ?_, hc, source_improvement (.unequal18 u) _ hs⟩
  · cases u <;> exact hs
  · simpa only [P4AOriginalSeed7Unequal15Literal.H7,
      P4AOriginalSeed7Unequal15Literal.currentSixth,
      P2OriginalDescendingEighthLogSemantics.history7] using hh

/-- The finite supremum has exactly the source's cap. Every possible
active witness is the real original owner; inactive terms are the parent. -/
theorem unequalRaised_eq_source (u : UnequalCell) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (hs : sourceRows (.unequal18 u) (point8 N pre))
    (ha : P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 u pre) :
    P4AOriginalSeed7Unequal15Literal.unequalRaised N lambda6 pre =
      newCap (.unequal18 u) (point8 N pre) := by
  have hle : P4AOriginalSeed7Unequal15Literal.currentSixth lambda6 pre ≤
      newCap (.unequal18 u) (point8 N pre) := ha.2.2.2.1.trans ha.2.2.2.2.le
  unfold P4AOriginalSeed7Unequal15Literal.unequalRaised
  dsimp only
  apply le_antisymm
  · apply Finset.sup'_le
    intro v _
    by_cases hv : P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 v pre
    · have hvu := unequal_active_owner u v N lambda6 pre hs hv
      subst v
      simpa only [if_pos ha] using
        (le_refl (newCap (.unequal18 u) (point8 N pre)))
    · simpa only [if_neg hv] using hle
  · have hmem : u ∈ (Finset.univ : Finset UnequalCell) := Finset.mem_univ _
    have hl := Finset.le_sup'
      (f := fun v => if P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 v pre
        then P4AOriginalSeed7Unequal15Literal.newCap v (point8 N pre)
        else P4AOriginalSeed7Unequal15Literal.currentSixth lambda6 pre) hmem
    simpa only [if_pos ha] using hl

/-- Original LIVE17 branch, including preservation through both later
source actions. The two displayed parent facts are discharged below. -/
theorem live17_slots1519 (i : Fin 15) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (hs : sourceRows (.descending17 i) (point8 N pre))
    (hh : P2OriginalDescendingEighthLogSemantics.history7 (point8 N pre) <
      lambda6 (rosserAncestor 6 pre))
    (hc : lambda6 (rosserAncestor 6 pre) ≤ oldCap (.descending17 i) (point8 N pre)) :
    P4AOriginalPrior58Chronology.slot15 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot16 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot17 N lambda6 pre = newCap (.descending17 i) (point8 N pre) ∧
    P4AOriginalPrior58Chronology.slot18 N lambda6 pre = newCap (.descending17 i) (point8 N pre) ∧
    P4AOriginalPrior58Chronology.slot19 N lambda6 pre = newCap (.descending17 i) (point8 N pre) := by
  have hseed : ¬ P4AOriginalSeed7Unequal15Literal.ActualSeed7 N lambda6 pre :=
    fun h => live17_not_seed7 i _ hs h.2.1
  have h15 : P4AOriginalPrior58Chronology.slot15 N lambda6 pre = lambda6 (rosserAncestor 6 pre) := by
    simp [P4AOriginalPrior58Chronology.slot15, P4AOriginalSeed7Unequal15Literal.seed7Raised,
      hseed, P4AOriginalSeed7Unequal15Literal.currentSixth]
  have h16src : P4AOriginalAscending14Literal42.literal16Exponent N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    have hout := live17_not_ascending14 i _ hs
    change (if P4AOriginalAscending14Literal42.ascending14Owns (point8 N pre) ∧
      P2OriginalAscendingEighthCapDictionary.CurrentParentGuard (point8 N pre)
        (lambda6 (rosserAncestor 6 pre)) then
      P2OriginalAscendingEighthCapDictionary.M (point8 N pre)
      else lambda6 (rosserAncestor 6 pre)) = lambda6 (rosserAncestor 6 pre)
    exact if_neg (fun h => hout h.1)
  have h16 : P4AOriginalPrior58Chronology.slot16 N lambda6 pre = lambda6 (rosserAncestor 6 pre) := by
    simp only [P4AOriginalPrior58Chronology.slot16, h15, h16src, max_self]
  have h17src := OriginalDescendingFifteenCellOwnership.ownedRaisedExponent_eq_selected_cap
    N lambda6 pre i (source17_guard i _ hs) hh hc
  have hle := hc.trans (source_improvement (.descending17 i) _ hs).le
  have h17 : P4AOriginalPrior58Chronology.slot17 N lambda6 pre = newCap (.descending17 i) (point8 N pre) := by
    simpa only [P4AOriginalPrior58Chronology.slot17, h16, h17src, max_eq_right hle]
  have hu : ∀ u, ¬ P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 u pre :=
    fun u h => live17_not_unequal15 i _ hs u h.2.1
  have h18src : P4AOriginalSeed7Unequal15Literal.unequalRaised N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp [P4AOriginalSeed7Unequal15Literal.unequalRaised, hu,
      P4AOriginalSeed7Unequal15Literal.currentSixth]
  have h18 : P4AOriginalPrior58Chronology.slot18 N lambda6 pre = newCap (.descending17 i) (point8 N pre) := by
    simp only [P4AOriginalPrior58Chronology.slot18, h17, h18src, max_eq_left hle]
  have h19src := OriginalAscendingThirteenCellOwnership.ownedRaisedExponent_inherits_outside
    N lambda6 pre (fun j hj => live17_not_ascending13 i _ hs ⟨j,hj⟩)
  have h19 : P4AOriginalPrior58Chronology.slot19 N lambda6 pre = newCap (.descending17 i) (point8 N pre) := by
    simpa only [P4AOriginalPrior58Chronology.slot19, h18, h19src,
      P4ASlot19ChargedFrontierSourceOnly.inheritedSixth,
      P2OriginalAscendingEighthCapDictionary.inheritedExponent, max_eq_left hle]
  exact ⟨h15,h16,h17,h18,h19⟩

theorem live18_slots1519 (u : UnequalCell) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 8)
    (hs : sourceRows (.unequal18 u) (point8 N pre))
    (hh : P2OriginalDescendingEighthLogSemantics.history7 (point8 N pre) <
      lambda6 (rosserAncestor 6 pre))
    (hc : lambda6 (rosserAncestor 6 pre) ≤ oldCap (.unequal18 u) (point8 N pre)) :
    P4AOriginalPrior58Chronology.slot15 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot16 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot17 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot18 N lambda6 pre = newCap (.unequal18 u) (point8 N pre) ∧
    P4AOriginalPrior58Chronology.slot19 N lambda6 pre = newCap (.unequal18 u) (point8 N pre) := by
  have hseed : ¬ P4AOriginalSeed7Unequal15Literal.ActualSeed7 N lambda6 pre :=
    fun h => live18_not_seed7 u _ hs h.2.1
  have h15 : P4AOriginalPrior58Chronology.slot15 N lambda6 pre = lambda6 (rosserAncestor 6 pre) := by
    simp [P4AOriginalPrior58Chronology.slot15, P4AOriginalSeed7Unequal15Literal.seed7Raised,
      hseed, P4AOriginalSeed7Unequal15Literal.currentSixth]
  have h16src : P4AOriginalAscending14Literal42.literal16Exponent N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    have hout := live18_not_ascending14 u _ hs
    change (if P4AOriginalAscending14Literal42.ascending14Owns (point8 N pre) ∧
      P2OriginalAscendingEighthCapDictionary.CurrentParentGuard (point8 N pre)
        (lambda6 (rosserAncestor 6 pre)) then
      P2OriginalAscendingEighthCapDictionary.M (point8 N pre)
      else lambda6 (rosserAncestor 6 pre)) = lambda6 (rosserAncestor 6 pre)
    exact if_neg (fun h => hout h.1)
  have h16 : P4AOriginalPrior58Chronology.slot16 N lambda6 pre = lambda6 (rosserAncestor 6 pre) := by
    simp only [P4AOriginalPrior58Chronology.slot16, h15, h16src, max_self]
  have h17src := OriginalDescendingFifteenCellOwnership.ownedRaisedExponent_eq_parent_outside
    N lambda6 pre (fun j hj => live18_not_descending15 u _ hs ⟨j,hj⟩)
  have h17 : P4AOriginalPrior58Chronology.slot17 N lambda6 pre = lambda6 (rosserAncestor 6 pre) := by
    simpa only [P4AOriginalPrior58Chronology.slot17, h16, h17src,
      P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth,
      P2OriginalAscendingEighthCapDictionary.inheritedExponent, max_self]
  have ha := unequal_actual u N lambda6 pre hlen hs hh hc
  have h18src := unequalRaised_eq_source u N lambda6 pre hs ha
  have hle := hc.trans (source_improvement (.unequal18 u) _ hs).le
  have h18 : P4AOriginalPrior58Chronology.slot18 N lambda6 pre = newCap (.unequal18 u) (point8 N pre) := by
    simp only [P4AOriginalPrior58Chronology.slot18, h17, h18src, max_eq_right hle]
  have h19src := OriginalAscendingThirteenCellOwnership.ownedRaisedExponent_inherits_outside
    N lambda6 pre (fun j hj => live18_not_ascending13 u _ hs ⟨j,hj⟩)
  have h19 : P4AOriginalPrior58Chronology.slot19 N lambda6 pre = newCap (.unequal18 u) (point8 N pre) := by
    simpa only [P4AOriginalPrior58Chronology.slot19, h18, h19src,
      P4ASlot19ChargedFrontierSourceOnly.inheritedSixth,
      P2OriginalAscendingEighthCapDictionary.inheritedExponent, max_eq_left hle]
  exact ⟨h15,h16,h17,h18,h19⟩

private theorem selected_length (c : LiveCell) (d : Data) (N cap : ℕ)
    (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) : s.selectedPrefix.length = 8 := by
  have hf := (List.mem_filter.mp hs).1
  exact firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse N cap w z) true 1 (by simp) s hf

/-- Actual common-frontier LIVE17 consumer. Both parent facts are proved
by the independent constructor and this same selected source bank. -/
theorem actual_common_live17 (i : Fin 15) (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.descending17 i) d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    OriginalDescendingFifteenCellOwnership.StrictRows i (point8 (N : ℝ) s.selectedPrefix) ∧
    HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m (N : ℝ) (rosserAncestor 1 s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot16 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
      P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
      P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex (.descending17 i))
        (point8 (N : ℝ) s.selectedPrefix) := by
  obtain ⟨hr,hstop,hh,hc⟩ := shared_frontier_live_guard (.descending17 i) d he N cap hN w z s hs
  obtain ⟨_,h16,_,_,h19⟩ := live17_slots1519 i (N : ℝ)
    (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix hr hh hc
  rw [source_newCap_dictionary (.descending17 i) _ hr] at h19
  exact ⟨source17_guard i _ hr,hstop,h16,h19⟩

/-- Actual source navigation, including both independently original
winner50 branches. Every active unequal witness is precisely this u. -/
theorem actual_common_live18 (u : UnequalCell) (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.unequal18 u) d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    P4AOriginalSeed7Unequal15Literal.ActualUnequalCell (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) u s.selectedPrefix ∧
    HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m (N : ℝ) (rosserAncestor 1 s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot17 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
      P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
      P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex (.unequal18 u))
        (point8 (N : ℝ) s.selectedPrefix) ∧
    (∀ v : UnequalCell, P4AOriginalSeed7Unequal15Literal.ActualUnequalCell (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) v s.selectedPrefix ↔ v = u) := by
  obtain ⟨hr,hstop,hh,hc⟩ := shared_frontier_live_guard (.unequal18 u) d he N cap hN w z s hs
  have hlen := selected_length (.unequal18 u) d N cap w z s hs
  have ha := unequal_actual u (N : ℝ) (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ))
    s.selectedPrefix hlen hr hh hc
  obtain ⟨_,_,h17,_,h19⟩ := live18_slots1519 u (N : ℝ)
    (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix hlen hr hh hc
  rw [source_newCap_dictionary (.unequal18 u) _ hr] at h19
  refine ⟨ha,hstop,h17,h19,?_⟩
  intro v
  constructor
  · exact unequal_active_owner u v _ _ _ hr
  · intro hv
    simpa only [hv] using ha

/-- Literal descending navigation determines every possible existential
owner. Its original action cap is already independent of that witness. -/
theorem actual_common_live17_owner (i : Fin 15) (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.descending17 i) d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) (j : Fin 15) :
    OriginalDescendingFifteenCellOwnership.StrictRows j
      (point8 (N : ℝ) s.selectedPrefix) ↔ j = i := by
  have hi := (actual_common_live17 i d he N cap hN w z s hs).1
  constructor
  · intro hj
    exact OriginalDescendingFifteenCellOwnership.owner_unique hj hi
  · intro hji
    simpa only [hji] using hi

/-- Uniform actual final-cap identity on all43 original live banks.
This combines the two new branches with H's thirteen LIVE19 branches. -/
theorem actual_common_live_cap (c : LiveCell) (d : Data) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
      P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c)
        (point8 (N : ℝ) s.selectedPrefix) := by
  cases c with
  | descending17 i => exact (actual_common_live17 i d he N cap hN w z s hs).2.2.2
  | unequal18 u => exact (actual_common_live18 u d he N cap hN w z s hs).2.2.2.1
  | ascending19 i => exact
      (P4AOriginalLive19ActualChronology.actual_common_live19 i d he N cap hN w z s hs).2.2.2

end
end ImbalancedChen.P4AOriginalLive1718ActualChronology
