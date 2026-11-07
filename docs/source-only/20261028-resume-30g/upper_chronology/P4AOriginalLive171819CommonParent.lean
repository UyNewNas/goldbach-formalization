import ImbalancedChen.P4AOriginalLive171819Atlas

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual old plane licences on all43 LIVE sources bound the independent
common constructor, including the genuinely re-tested sixth candidates.
A clipped sixth candidate is bounded through BOTH selected tent licences;
it is never falsely treated as a tent definition.
-/
namespace ImbalancedChen.P4AOriginalLive171819CommonParent
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse
open P4AOriginalLive171819Atlas
open P1OriginalVariableFourthContinuation P1OriginalVariableFifthContinuation
abbrev point8 (N : ℝ) (pre : List ℕ) := primeHistoryLogCoordinates N 8 pre

abbrev nineLeft := P4AOriginalSeed7Unequal15Literal.nineLeft

def unequalLeft : P4AOriginalSeed7Unequal15Literal.UnequalCell → Finset ℕ
  | .nine i => nineLeft i
  | .fiftyAsc => P4AOriginalSeed7Unequal15Literal.fiftyAscLeft
  | .fiftyDesc => P4AOriginalSeed7Unequal15Literal.fiftyDescLeft

def winner : LiveCell → Fin 64
  | .descending17 _ => 6
  | .unequal18 (.nine _) => 9
  | .unequal18 .fiftyAsc => 50
  | .unequal18 .fiftyDesc => 50
  | .ascending19 _ => 9

def left : LiveCell → Finset ℕ
  | .descending17 i => OriginalDescendingFifteenCellOwnership.leftMasks i
  | .unequal18 u => unequalLeft u
  | .ascending19 i => OriginalAscendingThirteenCellOwnership.leftMasks i

def subset6 (m : Fin 64) (t : Point) : ℝ :=
  ∑ i : Fin 6, if m.val.testBit i.val then t ⟨i.val,by omega⟩ else 0

def plane (c : LiveCell) (m : Fin 64) (t : Point) : ℝ :=
  if m.val ∈ left c then A (subset6 m t) else C (subset6 m t)

private def unequalPlaneIndex (u : P4AOriginalSeed7Unequal15Literal.UnequalCell)
    (m : Fin 64) : Fin (rowCount (.unequal18 u)) :=
  match u with
  | .nine _ => ⟨if m.val<9 then 34+m.val else 33+m.val,by split_ifs <;> omega⟩
  | .fiftyAsc => ⟨if m.val<50 then 16+m.val else 15+m.val,by split_ifs <;> omega⟩
  | .fiftyDesc => ⟨if m.val<50 then 16+m.val else 15+m.val,by split_ifs <;> omega⟩

private theorem unequal_plane_eval (u : P4AOriginalSeed7Unequal15Literal.UnequalCell)
    (m : Fin 64) (h0 : m ≠ 0) (hw : m ≠ winner (.unequal18 u)) (t : Point) :
    eval (rows (.unequal18 u) (unequalPlaneIndex u m)) t =
      oldCap (.unequal18 u) t - plane (.unequal18 u) m t := by
  cases u with
  | nine i =>
      fin_cases i <;> fin_cases m <;>
        norm_num [winner] at h0 hw ⊢ <;>
        norm_num [unequalPlaneIndex, rows, oldCap, plane, left, unequalLeft, nineLeft,
          subset6, P4AOriginalSeed7Unequal15Literal.nineRows,
          P4AOriginalSeed7Unequal15Literal.oldCap,
          P4AOriginalSeed7Unequal15Literal.A, P4AOriginalSeed7Unequal15Literal.D,
          eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
          A, C, Fin.sum_univ_succ] <;> ring
  | fiftyAsc =>
      fin_cases m <;> norm_num [winner] at h0 hw ⊢ <;>
        norm_num [unequalPlaneIndex, rows, oldCap, plane, left, unequalLeft, P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
          P4AOriginalSeed7Unequal15Literal.fiftyDescLeft, subset6, P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
          P4AOriginalSeed7Unequal15Literal.oldCap,
          P4AOriginalSeed7Unequal15Literal.A, P4AOriginalSeed7Unequal15Literal.D,
          eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
          A, C, Fin.sum_univ_succ] <;> ring
  | fiftyDesc =>
      fin_cases m <;> norm_num [winner] at h0 hw ⊢ <;>
        norm_num [unequalPlaneIndex, rows, oldCap, plane, left, unequalLeft, P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
          P4AOriginalSeed7Unequal15Literal.fiftyDescLeft, subset6, P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
          P4AOriginalSeed7Unequal15Literal.oldCap,
          P4AOriginalSeed7Unequal15Literal.A, P4AOriginalSeed7Unequal15Literal.D,
          eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
          A, C, Fin.sum_univ_succ] <;> ring

/-- Strict chosen-plane licence on every nonwinning original old mask. -/
theorem source_plane_strict (c : LiveCell) (t : Point) (hs : sourceRows c t)
    (m : Fin 64) (h0 : m ≠ 0) (hw : m ≠ winner c) : plane c m t < oldCap c t := by
  cases c with
  | descending17 i =>
      have h := (source17_guard i t hs).branches m.val
        (Finset.mem_Icc.mpr ⟨by apply Nat.pos_of_ne_zero; exact_mod_cast h0,by omega⟩)
        (by exact_mod_cast hw)
      simpa [plane,left,oldCap,subset6,
        OriginalDescendingFifteenCellOwnership.branchPlane,
        OriginalDescendingFifteenCellOwnership.subsetSum,
        OriginalDescendingFifteenCellOwnership.maskSlots,
        Finset.sum_filter,Fin.sum_univ_succ] using h
  | unequal18 u =>
      have h := hs (unequalPlaneIndex u m)
      rw [unequal_plane_eval u m h0 hw] at h
      linarith
  | ascending19 i =>
      have h := (source19_guard i t hs).branches m.val
        (Finset.mem_Icc.mpr ⟨by apply Nat.pos_of_ne_zero; exact_mod_cast h0,by omega⟩)
        (by exact_mod_cast hw)
      simpa [plane,left,oldCap,subset6,
        OriginalAscendingThirteenCellOwnership.branchPlane,
        OriginalAscendingThirteenCellOwnership.subsetSum,
        OriginalAscendingThirteenCellOwnership.maskSlots,
        Finset.sum_filter,Fin.sum_univ_succ] using h

theorem source_order_positive (c : LiveCell) (t : Point) (hs : sourceRows c t) :
    StrictAnti t ∧ (∀ j, 0<t j) ∧ t 0<mu := by
  have hcommon (k : Fin 10) : 0 < eval (common17 ⟨k.val,by omega⟩).2 t := by
    have heq : rows c ⟨k.val,by cases c <;> try {rename_i u; cases u} <;> simp [rowCount] <;> omega⟩ =
        (common17 ⟨k.val,by omega⟩).2 := by
      cases c with
      | descending17 i => simp [rows,rows17,show k.val<34 by omega]
      | unequal18 u => cases u with
        | nine i => fin_cases i <;> fin_cases k <;> decide
        | fiftyAsc => fin_cases k <;> decide
        | fiftyDesc => fin_cases k <;> decide
      | ascending19 i => fin_cases k <;> decide
    simpa only [heq] using hs ⟨k.val,by cases c <;> try {rename_i u; cases u} <;> simp [rowCount] <;> omega⟩
  have h0 := hcommon 0
  have hp := hcommon 2
  have h01 := hcommon 3
  have h12 := hcommon 4
  have h23 := hcommon 5
  have h34 := hcommon 6
  have h45 := hcommon 7
  have h56 := hcommon 8
  have h67 := hcommon 9
  norm_num [common17,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h0 hp h01 h12 h23 h34 h45 h56 h67
  refine ⟨?_,?_,?_⟩
  · intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith
  · intro j; fin_cases j <;> norm_num <;> linarith
  · dsimp [mu]; linarith

theorem source_winner_active (c : LiveCell) (t : Point) (hs : sourceRows c t) :
    v (subset6 (winner c) t) = oldCap c t := by
  cases c with
  | descending17 i =>
      have h := (source17_guard i t hs).oldWinner
      simpa [winner,subset6,oldCap,P2OriginalDescendingEighthLogSemantics.oldRaw,
        P2OriginalDescendingEighthLogSemantics.d,Fin.sum_univ_succ] using v_eq_C h.le
  | unequal18 u => cases u with
      | nine i =>
          have h := hs (15 : Fin 97)
          fin_cases i <;> norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.nineRows,Fin.sum_univ_succ] at h <;>
            rw [v_eq_min] <;>
            norm_num [winner,subset6,oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
              P4AOriginalSeed7Unequal15Literal.A,A,C,Fin.sum_univ_succ] <;>
            apply min_eq_left <;> linarith
      | fiftyAsc =>
          have h := hs (15 : Fin 95)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyAscRows,Fin.sum_univ_succ] at h
          rw [v_eq_min]
          norm_num [winner,subset6,oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.A,A,C,Fin.sum_univ_succ]
          apply min_eq_left; linarith
      | fiftyDesc =>
          have h := hs (15 : Fin 96)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyDescRows,Fin.sum_univ_succ] at h
          rw [v_eq_min]
          norm_num [winner,subset6,oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.D,A,C,Fin.sum_univ_succ]
          apply min_eq_right; linarith
  | ascending19 i =>
      have h := (source19_guard i t hs).oldWinner
      simpa [winner,subset6,oldCap,
        P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,
        Fin.sum_univ_succ] using v_eq_A h.le

private theorem tent_le_plane (c : LiveCell) (m : Fin 64) (t : Point) :
    v (subset6 m t) ≤ plane c m t := by
  rw [v_eq_min]; unfold plane; split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem source_old_tents (c : LiveCell) (t : Point) (hs : sourceRows c t)
    (m : Fin 64) : v (subset6 m t) ≤ oldCap c t := by
  by_cases hw : m=winner c
  · rw [hw,source_winner_active c t hs]
  by_cases h0 : m=0
  · subst m
    have h1 := source_plane_strict c t hs (1 : Fin 64) (by decide)
      (by cases c <;> try {rename_i u; cases u} <;> decide)
    have heq : plane c 1 t = A (t 0) := by
      cases c with
      | descending17 i => fin_cases i <;> norm_num [plane,left,subset6,
          OriginalDescendingFifteenCellOwnership.leftMasks,Fin.sum_univ_succ]
      | unequal18 u => cases u with
        | nine i => fin_cases i <;> norm_num [plane,left,unequalLeft,nineLeft,P4AOriginalSeed7Unequal15Literal.nineLeft,
          P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,subset6,Fin.sum_univ_succ]
        | fiftyAsc => norm_num [plane,left,unequalLeft,P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
          P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,subset6,Fin.sum_univ_succ]
        | fiftyDesc => norm_num [plane,left,unequalLeft,P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
          P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,subset6,Fin.sum_univ_succ]
      | ascending19 i => fin_cases i <;> norm_num [plane,left,subset6,
          OriginalAscendingThirteenCellOwnership.leftMasks,Fin.sum_univ_succ]
    rw [heq] at h1
    have hp := (source_order_positive c t hs).2.1 0
    norm_num [subset6,Fin.sum_univ_succ,v_eq_min,A,C]
    dsimp [A] at h1
    linarith
  · exact (tent_le_plane c m t).trans (source_plane_strict c t hs m h0 hw).le

/-- Every real subset of the actual first six coordinates is licensed;
this is a derived literal-source result, not a requested cap premise. -/
theorem source_subset_tent (c : LiveCell) (t : Point) (hs : sourceRows c t)
    (I : Finset (Fin 6)) : v (∑ i ∈ I,t ⟨i.val,by omega⟩) ≤ oldCap c t := by
  let m : Fin 64 := ⟨P4AOriginalAscending14Literal42.sixMask I,by fin_cases I <;> decide⟩
  have heq : subset6 m t = ∑ i ∈ I,t ⟨i.val,by omega⟩ := by
    fin_cases I <;> norm_num [m,subset6,P4AOriginalAscending14Literal42.sixMask,Fin.sum_univ_succ]
  rw [←heq]
  exact source_old_tents c t hs m

theorem source_old_W (c : LiveCell) (t : Point) (hs : sourceRows c t) :
    B (t 2) ≤ oldCap c t := by
  cases c with
  | descending17 i => simpa [B,oldCap] using (source17_guard i t hs).oldW.le
  | ascending19 i => simpa [B,oldCap] using (source19_guard i t hs).oldW.le
  | unequal18 u => cases u with
      | nine i =>
          have h := hs (17 : Fin 97)
          fin_cases i <;> norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.nineRows,Fin.sum_univ_succ] at h <;>
            dsimp [B,cap,oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
              P4AOriginalSeed7Unequal15Literal.A] <;> linarith
      | fiftyAsc =>
          have h := hs (16 : Fin 95)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyAscRows,Fin.sum_univ_succ] at h
          dsimp [B,cap,oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.A]; linarith
      | fiftyDesc =>
          have h := hs (16 : Fin 96)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyDescRows,Fin.sum_univ_succ] at h
          dsimp [B,cap,oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.D]; linarith

/-- Transport of the literal six-coordinate licence to every actual
third/fourth/fifth/sixth frozen ancestor of the same prefix. -/
theorem ancestor_subset_tent (c : LiveCell) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length=8) (hs : sourceRows c (point8 N pre))
    (k : ℕ) (hk : k≤6) (I : Finset (Fin k)) :
    v (∑ i∈I,primeHistoryLogCoordinates N k (rosserAncestor k pre) i) ≤
      oldCap c (point8 N pre) := by
  let emb : Fin k ↪ Fin 6 := ⟨fun i=>i.castLE hk,by intro i j h;exact Fin.ext (congrArg Fin.val h)⟩
  let J := I.map emb
  have heq : (∑ i∈I,primeHistoryLogCoordinates N k (rosserAncestor k pre) i) =
      ∑ i∈J,(point8 N pre) ⟨i.val,by omega⟩ := by
    simp only [J,Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : k≤8) i
  rw [heq]
  exact source_subset_tent c _ hs J

/-- The actual supported historical third seed is bounded using its real
Gamma enclosure and all source old planes, without identifying a minorant
with the true third cap. -/
theorem supported_seed_le_old (c : LiveCell)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ) (he : 0≤e)
    (pre : List ℕ) (hlen : pre.length=8) (hs : sourceRows c (point8 N pre))
    (hsup : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre)) :
    P1CoarseFirstCubeFallbackMargin.effectiveExponent (e : ℝ) chi m omega N
      (rosserAncestor 3 pre) ≤ oldCap c (point8 N pre) := by
  obtain ⟨j,hj,hjt⟩ := hsup.2
  have hg := source_order_positive c _ hs
  have heR : (0 : ℝ)≤e := by exact_mod_cast he
  have hcoords (i : Fin 3) := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3≤8) i
  have hord : Ordered
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) := by
    simp only [hcoords]
    exact ⟨(hg.2.1 2).le,(hg.1 (by decide : (1 : Fin 8)<2)).le,
      (hg.1 (by decide : (0 : Fin 8)<1)).le,hg.2.2.le⟩
  have hgamma := gamma_le_endpoint (e : ℝ) (box m j) heR (inBox_of_cell hjt)
    hord.1 hord.2.1 hord.2.2.1
  have hend : endpoint
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) ≤ oldCap c (point8 N pre) := by
    rw [endpoint,if_pos hord.2.2.2,original_eq_six hord]
    have h0 := ancestor_subset_tent c N pre hlen hs 3 (by decide) ({0} : Finset (Fin 3))
    have h01 := ancestor_subset_tent c N pre hlen hs 3 (by decide) ({0,1} : Finset (Fin 3))
    have h012 := ancestor_subset_tent c N pre hlen hs 3 (by decide) ({0,1,2} : Finset (Fin 3))
    have h02 := ancestor_subset_tent c N pre hlen hs 3 (by decide) ({0,2} : Finset (Fin 3))
    have h12 := ancestor_subset_tent c N pre hlen hs 3 (by decide) ({1,2} : Finset (Fin 3))
    have hW := source_old_W c _ hs
    simp [hcoords] at h0 h01 h012 h02 h12
    simp only [six,hcoords]
    apply max_le h0
    apply max_le h01
    apply max_le h012
    exact max_le hW (max_le h02 h12)
  rw [P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hsup,
    exponent_on_cell (e : ℝ) chi m _ j hj hjt]
  dsimp [levelExponent]
  linarith

theorem common_lambda3_le_old (c : LiveCell)
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (he : 0≤d.e)
    (pre : List ℕ) (hlen : pre.length=8) (hs : sourceRows c (point8 N pre))
    (hsup : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    P5OriginalCommonRefinedConstructor.lambda3 d N (rosserAncestor 4 pre) ≤
      oldCap c (point8 N pre) := by
  have hold : P5OriginalCommonRefinedConstructor.originalSeed d N (rosserAncestor 4 pre) ≤
      oldCap c (point8 N pre) := by
    simpa only [P5OriginalCommonRefinedConstructor.originalSeed,seedExponent,
      rosserAncestor_nested 3 4 (by decide)] using
      supported_seed_le_old c d.e d.chi d.m d.omega N he pre hlen hs hsup
  unfold P5OriginalCommonRefinedConstructor.lambda3
  apply max_le hold
  unfold P5OriginalCommonRefinedConstructor.fallbackSeed
  split_ifs
  · have h := ancestor_subset_tent c N pre hlen hs 3 (by decide) ({1,2} : Finset (Fin 3))
    simpa [rosserAncestor_nested 3 4 (by decide)] using h
  · have h := ancestor_subset_tent c N pre hlen hs 2 (by decide) ({1} : Finset (Fin 2))
    simpa [rosserAncestor_nested 2 4 (by decide)] using h
  · exact hold

theorem common_actual_fifth_le_old (c : LiveCell)
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (he : 0≤d.e)
    (pre : List ℕ) (hlen : pre.length=8) (hs : sourceRows c (point8 N pre))
    (hsup : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    P5OriginalCommonRefinedConstructor.actualParent5 d N (rosserAncestor 6 pre) ≤
      oldCap c (point8 N pre) := by
  have heR : (0 : ℝ)≤d.e := by exact_mod_cast he
  have hseed := common_lambda3_le_old c d N he pre hlen hs hsup
  have h4len : (rosserAncestor 4 pre).length=4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length=5 := by simp [hlen]
  have h4 : P5OriginalCommonRefinedConstructor.exponent4 d N (rosserAncestor 4 pre) ≤
      oldCap c (point8 N pre) := by
    rw [P5OriginalCommonRefinedConstructor.exponent4,if_pos h4len]
    apply finiteMax_le
    · exact hseed
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have hr := ancestor_subset_tent c N pre hlen hs 4 (by decide) r.selected
      linarith
  change P5OriginalCommonRefinedConstructor.exponent5 d N
    (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _
  rw [rosserAncestor_nested 5 6 (by decide),P5OriginalCommonRefinedConstructor.exponent5,
    if_pos h5len,rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le
  · exact h4
  · intro r _ _
    have hr := ancestor_subset_tent c N pre hlen hs 5 (by decide) r.selected
    rw [candidate,envelope_eq_v]
    linarith

/-- Sixth candidates may be clipped affine caps. Their actual selected
ascending AND descending licences put them below a real subset tent. -/
theorem common_sixth_le_old (c : LiveCell)
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (he : 0≤d.e)
    (pre : List ℕ) (hlen : pre.length=8) (hs : sourceRows c (point8 N pre))
    (hsup : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    P5OriginalCommonRefinedConstructor.lambda6 d N (rosserAncestor 6 pre) ≤
      oldCap c (point8 N pre) := by
  unfold P5OriginalCommonRefinedConstructor.lambda6
  apply finiteMax_le
  · exact common_actual_fifth_le_old c d N he pre hlen hs hsup
  · intro sc _ helig
    have hp := helig.2.1
    let I : Finset (Fin 6) := Finset.univ.filter
      (fun i => Certificates.P2OriginalSixthElevenLogSemantics.bit sc.selectedMask i.val = true)
    have htent := ancestor_subset_tent c N pre hlen hs 6 (by decide) I
    have hsum : (∑ i∈I,primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) i) =
        Certificates.P2OriginalSixthElevenLogSemantics.selectedSum sc.selectedMask
          (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
      simp [I,Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,Finset.sum_filter]
    rw [hsum,v_eq_min] at htent
    have hnew := le_min hp.selectedAscending.le hp.selectedDescending.le
    exact hnew.trans htent

theorem source_improvement (c : LiveCell) (t : Point) (hs : sourceRows c t) :
    oldCap c t < newCap c t := by
  cases c with
  | descending17 i => exact (source17_guard i t hs).improvement
  | ascending19 i => exact (source19_guard i t hs).improvement
  | unequal18 u => cases u with
      | nine i =>
          have h := hs (18 : Fin 97)
          fin_cases i <;> norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.nineRows,Fin.sum_univ_succ] at h <;>
            dsimp [oldCap,newCap,P4AOriginalSeed7Unequal15Literal.oldCap,
              P4AOriginalSeed7Unequal15Literal.newCap,P4AOriginalSeed7Unequal15Literal.A] <;> linarith
      | fiftyAsc =>
          have h := hs (79 : Fin 95)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyAscRows,Fin.sum_univ_succ] at h
          dsimp [oldCap,newCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.newCap,P4AOriginalSeed7Unequal15Literal.A]; linarith
      | fiftyDesc =>
          have h := hs (79 : Fin 96)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyDescRows,Fin.sum_univ_succ] at h
          dsimp [oldCap,newCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.newCap,P4AOriginalSeed7Unequal15Literal.D]; linarith

theorem source_old_lt_peak (c : LiveCell) (t : Point) (hs : sourceRows c t) :
    oldCap c t < cap := by
  cases c with
  | descending17 i =>
      have h := (source17_guard i t hs).oldWinner
      dsimp [oldCap,P2OriginalDescendingEighthLogSemantics.oldRaw,
        P2OriginalDescendingEighthLogSemantics.d,C,mu,cap] at *
      linarith
  | ascending19 i =>
      have h := (source19_guard i t hs).oldWinner
      dsimp [oldCap,P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,A,mu,cap] at *
      linarith
  | unequal18 u => cases u with
      | nine i =>
          have h := hs (15 : Fin 97)
          fin_cases i <;> norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.nineRows,Fin.sum_univ_succ] at h <;>
            dsimp [oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
              P4AOriginalSeed7Unequal15Literal.A,cap] <;> linarith
      | fiftyAsc =>
          have h := hs (15 : Fin 95)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyAscRows,Fin.sum_univ_succ] at h
          dsimp [oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.A,cap]; linarith
      | fiftyDesc =>
          have h := hs (15 : Fin 96)
          norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
            P4AOriginalSeed7Unequal15Literal.fiftyDescRows,Fin.sum_univ_succ] at h
          dsimp [oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
            P4AOriginalSeed7Unequal15Literal.D,cap]; linarith

/-- Distinct actual old winners cannot both be the strict winner on the
same original history. This compares genuine source tent expressions. -/
theorem distinct_winner_disjoint (c c' : LiveCell) (t : Point)
    (h : sourceRows c t) (h' : sourceRows c' t) (hw : winner c ≠ winner c') : False := by
  have hn (a : LiveCell) : winner a ≠ 0 := by
    cases a <;> try {rename_i u;cases u} <;> decide
  have hl := (tent_le_plane c (winner c') t).trans_lt
    (source_plane_strict c t h (winner c') (hn c') hw.symm)
  have hr := (tent_le_plane c' (winner c) t).trans_lt
    (source_plane_strict c' t h' (winner c) (hn c) hw)
  rw [source_winner_active c' t h'] at hl
  rw [source_winner_active c t h] at hr
  linarith

private theorem nine_separator : ∀ (i j : Fin 13), i≠j →
    ∃ m : Fin 64, m≠0 ∧ m≠9 ∧ ((m.val∈nineLeft i) ≠ (m.val∈nineLeft j)) := by decide

private theorem nine_unique (i j : Fin 13) (t : Point)
    (h : sourceRows (.unequal18 (.nine i)) t)
    (h' : sourceRows (.unequal18 (.nine j)) t) : i=j := by
  by_contra hn
  obtain ⟨m,hm0,hm9,hdiff⟩ := nine_separator i j hn
  have hi := source_plane_strict (.unequal18 (.nine i)) t h m hm0 hm9
  have hj := source_plane_strict (.unequal18 (.nine j)) t h' m hm0 hm9
  have hp := source_old_lt_peak (.unequal18 (.nine i)) t h
  dsimp [plane,left,unequalLeft] at hi hj
  by_cases hmi : m.val∈nineLeft i <;> by_cases hmj : m.val∈nineLeft j
  all_goals simp only [hmi,hmj,if_true,if_false] at hi hj hdiff
  all_goals try contradiction
  all_goals dsimp [oldCap,P4AOriginalSeed7Unequal15Literal.oldCap,
    P4AOriginalSeed7Unequal15Literal.A,A,C,cap] at hi hj hp
  all_goals linarith

private theorem ascending_nine_disjoint (i j : Fin 13) (t : Point)
    (h : sourceRows (.ascending19 i) t) (h' : sourceRows (.unequal18 (.nine j)) t) : False := by
  have hl := (source19_guard i t h).ascendingThird
  have hr := h' (16 : Fin 97)
  fin_cases j <;> norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
    P4AOriginalSeed7Unequal15Literal.nineRows,Fin.sum_univ_succ] at hr <;>
    dsimp [mu] at hl <;> linarith

private theorem fifty_disjoint (t : Point)
    (h : sourceRows (.unequal18 .fiftyAsc) t)
    (h' : sourceRows (.unequal18 .fiftyDesc) t) : False := by
  have ha := h (15 : Fin 95)
  have hd := h' (15 : Fin 96)
  norm_num [rows,eval,P4AOriginalSeed7Unequal15Literal.evalAffine,
    P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
    P4AOriginalSeed7Unequal15Literal.fiftyDescRows,Fin.sum_univ_succ] at ha hd
  linarith

/-- Complete owner uniqueness for all43 live original sources. Different
stage tags alone do not establish disjointness: actual winners and the
original third-half selectors are used. -/
theorem live_owner_unique (c c' : LiveCell) (t : Point)
    (h : sourceRows c t) (h' : sourceRows c' t) : c=c' := by
  cases c with
  | descending17 i => cases c' with
    | descending17 j =>
        exact congrArg LiveCell.descending17
          (OriginalDescendingFifteenCellOwnership.owner_unique
            (source17_guard i t h) (source17_guard j t h'))
    | unequal18 u =>
        exfalso; apply distinct_winner_disjoint _ _ t h h'
        cases u <;> decide
    | ascending19 j =>
        exfalso; exact distinct_winner_disjoint _ _ t h h' (by decide)
  | ascending19 i => cases c' with
    | ascending19 j =>
        exact congrArg LiveCell.ascending19
          (OriginalAscendingThirteenCellOwnership.owner_unique
            (source19_guard i t h) (source19_guard j t h'))
    | descending17 j =>
        exfalso; exact distinct_winner_disjoint _ _ t h h' (by decide)
    | unequal18 u => cases u with
      | nine j => exact (ascending_nine_disjoint i j t h h').elim
      | fiftyAsc => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
      | fiftyDesc => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
  | unequal18 u => cases c' with
    | descending17 j =>
        exfalso; apply distinct_winner_disjoint _ _ t h h'
        cases u <;> decide
    | ascending19 j => cases u with
      | nine i => exact (ascending_nine_disjoint j i t h' h).elim
      | fiftyAsc => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
      | fiftyDesc => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
    | unequal18 v => cases u with
      | nine i => cases v with
        | nine j => exact congrArg (fun x=>LiveCell.unequal18 (.nine x)) (nine_unique i j t h h')
        | fiftyAsc => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
        | fiftyDesc => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
      | fiftyAsc => cases v with
        | nine j => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
        | fiftyAsc => rfl
        | fiftyDesc => exact (fifty_disjoint t h h').elim
      | fiftyDesc => cases v with
        | nine j => exact (distinct_winner_disjoint _ _ t h h' (by decide)).elim
        | fiftyAsc => exact (fifty_disjoint t h' h).elim
        | fiftyDesc => rfl

end
end ImbalancedChen.P4AOriginalLive171819CommonParent
