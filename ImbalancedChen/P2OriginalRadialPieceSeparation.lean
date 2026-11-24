import ImbalancedChen.P2OriginalRadialStaircaseGraph

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Hierarchical nonoverlap of the original radial stairs: different endpoint
selectors, original max-pulled outer rows, radial panels, then stairs.
Only the original primitive widths/selectors/face incidence are finite
checks. No all-pairs geometric disjointness check is accepted or executed.
-/
namespace ImbalancedChen.P2OriginalRadialPieceSeparation
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSaving15RadialArchive
open P2OriginalSaving15RadialProfile (actualPieceRow)
open P2OriginalSaving16OriginalArchive (QPoint castPoint evalQ edgeMatrix)
open P2OriginalRadialBasePulling (Affine7 eval7 lift7 vertexId)
open P2OriginalPhysicalSimplexMomentRow (Point Row rowSupport)
open P2OriginalRadialRealWall
open P2OriginalRadialStaircaseGraph (height_mono graphWall graphWall_proper
  same_staircase_nonneg later_staircase_nonpos radialUnit)

abbrev Index := Σ c : Fin 4, Σ s : BaseRow c, Fin 4 × Fin 8
def indexVertices (i : Index) : Fin 9 → QPoint := pieceVertices i.1 i.2.1 i.2.2.1 i.2.2.2
abbrev Piece := {i : Index // (edgeMatrix (indexVertices i)).det ≠ 0}
def pieceRow (i : Piece) : Row := actualPieceRow i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2 i.property
def pieceSupport (i : Piece) : Set Point := rowSupport (pieceRow i)

theorem lift7_eval_liftPoint (a : Affine7) (x : Fin 7 → ℚ) (q : ℚ) :
    evalQ (lift7 a) (liftPoint x q) = eval7 a x := by
  rw [P2OriginalRadialBasePulling.eval_lift7]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem lift7_eval_cast (a : Affine7) (x : Fin 7 → ℚ) (q : ℚ) :
    (fromQ (lift7 a)).eval (castPoint (liftPoint x q)) = (eval7 a x : ℝ) := by
  rw [fromQ_cast,lift7_eval_liftPoint]

theorem nonpos_at_piece_of_base (a : Affine7) (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8)
    (h : ∀ i : Fin 8, eval7 a (baseVertex c s i) ≤ 0) (i : Fin 9) :
    (fromQ (lift7 a)).eval (castPoint (pieceVertices c s p k i)) ≤ 0 := by
  unfold pieceVertices
  split_ifs
  all_goals rw [lift7_eval_cast]; exact_mod_cast h _
theorem nonneg_at_piece_of_base (a : Affine7) (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8)
    (h : ∀ i : Fin 8, 0 ≤ eval7 a (baseVertex c s i)) (i : Fin 9) :
    0 ≤ (fromQ (lift7 a)).eval (castPoint (pieceVertices c s p k i)) := by
  unfold pieceVertices
  split_ifs
  all_goals rw [lift7_eval_cast]; exact_mod_cast h _

theorem eval7_sub (a b : Affine7) (x : Fin 7 → ℚ) :
    eval7 (fun j => a j-b j) x = eval7 a x-eval7 b x := by
  simp only [eval7,sub_mul,Finset.sum_sub_distrib]
  ring

private theorem selector_injective : Function.Injective (fun c : Fin 4 => (lowerId c,upperId c)) := by decide
private theorem lower_difference_proper (i j : Fin 2) (hij : i ≠ j) :
    ∃ t : Point, (fromQ (lift7 (fun a => lowerAffine j a-lowerAffine i a))).eval t ≠ 0 := by
  refine ⟨0,?_⟩
  rw [fromQ_eval]
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerAffine,lift7,P2OriginalSaving19OwnedSource.eval,
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients] at *
private theorem upper_difference_proper (i j : Fin 2) (hij : i ≠ j) :
    ∃ t : Point, (fromQ (lift7 (fun a => upperAffine i a-upperAffine j a))).eval t ≠ 0 := by
  refine ⟨0,?_⟩
  rw [fromQ_eval]
  fin_cases i <;> fin_cases j <;>
    norm_num [upperAffine,lift7,P2OriginalSaving19OwnedSource.eval,
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients] at *

theorem different_chambers_null (c d : Fin 4) (hcd : c ≠ d)
    (s : BaseRow c) (t : BaseRow d) (p q : Fin 4) (k l : Fin 8)
    (hs : (edgeMatrix (pieceVertices c s p k)).det ≠ 0)
    (ht : (edgeMatrix (pieceVertices d t q l)).det ≠ 0) :
    volume (rowSupport (actualPieceRow c s p k hs) ∩ rowSupport (actualPieceRow d t q l ht)) = 0 := by
  have hlo (c : Fin 4) (s : BaseRow c) (i : Fin 8) (j : Fin 2) :
      eval7 (lowerAffine j) (baseVertex c s i) ≤ lowerAt c (baseVertex c s i) := by
    have hv := (original_base_checks c).2.1 s
    exact (original_widths_and_selectors c ⟨vertexId (data c) s i,hv.2 i⟩).2.1 j
  have hup (c : Fin 4) (s : BaseRow c) (i : Fin 8) (j : Fin 2) :
      upperAt c (baseVertex c s i) ≤ eval7 (upperAffine j) (baseVertex c s i) := by
    have hv := (original_base_checks c).2.1 s
    exact (original_widths_and_selectors c ⟨vertexId (data c) s i,hv.2 i⟩).2.2 j
  by_cases hlow : lowerId c = lowerId d
  · have hupper : upperId c ≠ upperId d := fun h => hcd (selector_injective (Prod.ext hlow h))
    let a : Affine7 := fun j => upperAffine (upperId c) j-upperAffine (upperId d) j
    apply Wall.separated_supports_null (fromQ (lift7 a))
    · exact nonpos_at_piece_of_base a c s p k (fun i => by
        rw [eval7_sub]; exact sub_nonpos.mpr (hup c s i (upperId d)))
    · exact nonneg_at_piece_of_base a d t q l (fun i => by
        rw [eval7_sub]; exact sub_nonneg.mpr (hup d t i (upperId c)))
    · exact upper_difference_proper _ _ hupper
  · let a : Affine7 := fun j => lowerAffine (lowerId d) j-lowerAffine (lowerId c) j
    apply Wall.separated_supports_null (fromQ (lift7 a))
    · exact nonpos_at_piece_of_base a c s p k (fun i => by
        rw [eval7_sub]; exact sub_nonpos.mpr (hlo c s i (lowerId d)))
    · exact nonneg_at_piece_of_base a d t q l (fun i => by
        rw [eval7_sub]; exact sub_nonneg.mpr (hlo d t i (lowerId c)))
    · exact lower_difference_proper _ _ hlow

theorem different_outer_rows_null (c : Fin 4) (s t : BaseRow c) (hst : s ≠ t)
    (p q : Fin 4) (k l : Fin 8)
    (hs : (edgeMatrix (pieceVertices c s p k)).det ≠ 0)
    (ht : (edgeMatrix (pieceVertices c t q l)).det ≠ 0) :
    volume (rowSupport (actualPieceRow c s p k hs) ∩ rowSupport (actualPieceRow c t q l ht)) = 0 := by
  obtain ⟨a,ha,hb,v,hv⟩ := P2OriginalRadialBasePulling.separated (original_base_checks c) s t hst
  apply Wall.separated_supports_null (fromQ (lift7 a))
  · exact nonpos_at_piece_of_base a c s p k ha
  · exact nonneg_at_piece_of_base a c t q l hb
  · refine ⟨castPoint (liftPoint (P2OriginalRadialBasePulling.vertex (data c) v.val) 0),?_⟩
    rw [lift7_eval_cast]
    exact_mod_cast hv

def heightAffine (c : Fin 4) (n : ℕ) : Affine7 := fun j =>
  lowerAffine (lowerId c) j+(n:ℚ)/4*(upperAffine (upperId c) j-lowerAffine (lowerId c) j)
def sliceRow (c : Fin 4) (n : ℕ) : Fin 9 → ℚ :=
  ![-heightAffine c n 0,-heightAffine c n 1,-heightAffine c n 2,-heightAffine c n 3,
    -heightAffine c n 4,-heightAffine c n 5,-heightAffine c n 6,-heightAffine c n 7,1]
theorem heightAffine_eval (c : Fin 4) (n : ℕ) (x : Fin 7 → ℚ) :
    eval7 (heightAffine c n) x = height c x n := by
  simp only [eval7,heightAffine,height,lowerAt,upperAt,add_mul,sub_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum]
  ring
theorem slice_eval (c : Fin 4) (n : ℕ) (x : Fin 7 → ℚ) (r : ℚ) :
    (fromQ (sliceRow c n)).eval (castPoint (liftPoint x r)) = (r-height c x n : ℚ) := by
  rw [fromQ_cast]
  have he : evalQ (sliceRow c n) (liftPoint x r) = r-eval7 (heightAffine c n) x := by
    norm_num [evalQ,sliceRow,liftPoint,eval7,Fin.sum_univ_succ] <;> ring
  rw [he,heightAffine_eval]
theorem slice_proper (c : Fin 4) (n : ℕ) : ∃ t : Point, (fromQ (sliceRow c n)).eval t ≠ 0 := by
  apply Wall.proper_of_linear_ne_zero
  intro h
  have he := congrArg (fun L : Point →L[ℝ] ℝ => L radialUnit) h
  norm_num [fromQ,P2OriginalSaving19OwnedSource.linearPart,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,sliceRow,radialUnit,Pi.single_apply] at he

theorem panel_left_nonpos (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (i : Fin 9) :
    (fromQ (sliceRow c (p.val+1))).eval (castPoint (pieceVertices c s p k i)) ≤ 0 := by
  unfold pieceVertices
  split_ifs
  · rw [slice_eval]
    exact_mod_cast sub_nonpos.mpr (height_mono c s _ (Nat.le_succ p.val))
  · rw [slice_eval]
    simp
theorem panel_right_nonneg (c : Fin 4) (s : BaseRow c) (p q : Fin 4) (hpq : p < q)
    (k : Fin 8) (i : Fin 9) :
    0 ≤ (fromQ (sliceRow c (p.val+1))).eval (castPoint (pieceVertices c s q k i)) := by
  unfold pieceVertices
  split_ifs
  all_goals rw [slice_eval]
  all_goals exact_mod_cast sub_nonneg.mpr (height_mono c s _ (by have := hpq; omega))

theorem different_panels_null (c : Fin 4) (s : BaseRow c) (p q : Fin 4) (hpq : p ≠ q)
    (k l : Fin 8) (hs : (edgeMatrix (pieceVertices c s p k)).det ≠ 0)
    (ht : (edgeMatrix (pieceVertices c s q l)).det ≠ 0) :
    volume (rowSupport (actualPieceRow c s p k hs) ∩ rowSupport (actualPieceRow c s q l ht)) = 0 := by
  rcases lt_or_gt_of_ne hpq with h | h
  · exact Wall.separated_supports_null (fromQ (sliceRow c (p.val+1))) _ _
      (panel_left_nonpos c s p k) (panel_right_nonneg c s p q h l) (slice_proper c (p.val+1))
  · rw [Set.inter_comm]
    exact Wall.separated_supports_null (fromQ (sliceRow c (q.val+1))) _ _
      (panel_left_nonpos c s q l) (panel_right_nonneg c s q p h k) (slice_proper c (q.val+1))

theorem different_stairs_null (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k l : Fin 8) (hkl : k ≠ l)
    (hs : (edgeMatrix (pieceVertices c s p k)).det ≠ 0)
    (ht : (edgeMatrix (pieceVertices c s p l)).det ≠ 0) :
    volume (rowSupport (actualPieceRow c s p k hs) ∩ rowSupport (actualPieceRow c s p l ht)) = 0 := by
  rcases lt_or_gt_of_ne hkl with h | h
  · rw [Set.inter_comm]
    exact Wall.separated_supports_null (graphWall c s p k) _ _
      (later_staircase_nonpos c s p k l h) (same_staircase_nonneg c s p k) (graphWall_proper c s p k)
  · exact Wall.separated_supports_null (graphWall c s p l) _ _
      (later_staircase_nonpos c s p l k h) (same_staircase_nonneg c s p l) (graphWall_proper c s p l)

theorem piece_pairwise_null : Pairwise (fun i j : Piece => volume (pieceSupport i ∩ pieceSupport j) = 0) := by
  rintro ⟨⟨c,s,p,k⟩,hi⟩ ⟨⟨d,t,q,l⟩,hj⟩ hne
  by_cases hcd : c = d
  · subst d
    by_cases hst : s = t
    · subst t
      by_cases hpq : p = q
      · subst q
        have hkl : k ≠ l := fun h => hne (by subst l; rfl)
        exact different_stairs_null c s p k l hkl hi hj
      · exact different_panels_null c s p q hpq k l hi hj
    · exact different_outer_rows_null c s t hst p q k l hi hj
  · exact different_chambers_null c d hcd s t p q k l hi hj

end
end ImbalancedChen.P2OriginalRadialPieceSeparation
