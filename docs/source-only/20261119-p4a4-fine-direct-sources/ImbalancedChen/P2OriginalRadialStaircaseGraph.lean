import ImbalancedChen.P2OriginalRadialRealWall

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The separating graph between adjacent original staircase simplices.
It is affine in the actual seven base coordinates and has coefficient
one on the radial coordinate. No rational inverse-matrix replay or
precomputed geometric overlap field is needed.
-/
namespace ImbalancedChen.P2OriginalRadialStaircaseGraph
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSaving15RadialArchive
open P2OriginalRadialBasePulling (vertexId vertex)
open P2OriginalSaving16OriginalArchive (castPoint edgeMatrix)
open P2OriginalSaving16SimplexBinding (edgeEquiv edge_vertices)
open P2OriginalPhysicalSimplexMomentRow (Point)
open P2OriginalRadialRealWall
namespace Bary
export P2OriginalSaving19SimplexMoments (bary interpolate vertices)
end Bary

def projectionMap (c : Fin 4) (s : BaseRow c) : Point ≃L[ℝ] Point :=
  edgeEquiv (extendedVertices c s) (original_extended_determinants c s)
def projectionBase (c : Fin 4) (s : BaseRow c) : Point := castPoint (extendedVertices c s 0)
def radialUnit : Point := Pi.single 7 1
def boundaryValue (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k i : Fin 8) : ℚ :=
  if i.val ≤ k.val then height c (baseVertex c s i) p.val
  else height c (baseVertex c s i) (p.val+1)
def graphValues (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (i : Fin 9) : ℝ :=
  if h : i.val < 8 then (boundaryValue c s p k ⟨i.val,h⟩ : ℝ)
  else (boundaryValue c s p k 0 : ℝ)
def graphLinear (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) : Point →L[ℝ] ℝ :=
  ∑ j : Fin 8, (graphValues c s p k j.succ-graphValues c s p k 0) •
    ((ContinuousLinearMap.proj j).comp (projectionMap c s).symm.toContinuousLinearMap)
def graphFunction (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (t : Point) : ℝ :=
  Bary.interpolate (graphValues c s p k) ((projectionMap c s).symm (t-projectionBase c s))
def graphWall (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) : Wall where
  linear := ContinuousLinearMap.proj 7-graphLinear c s p k
  constant := -(graphValues c s p k 0-graphLinear c s p k (projectionBase c s))

theorem interpolate_eq_affine (y : Fin 9 → ℝ) (x : Point) :
    Bary.interpolate y x = y 0+∑ j : Fin 8, (y j.succ-y 0)*x j := by
  have hs : (∑ j : Fin 8, (y j.succ-y 0)*x j) =
      (∑ j : Fin 8, x j*y j.succ)-(∑ j : Fin 8, x j)*y 0 := by
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [Bary.interpolate,Fin.sum_univ_succ,Bary.bary,Fin.cases_zero,Fin.cases_succ]
  rw [hs]
  ring

theorem graphLinear_apply (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (t : Point) :
    graphLinear c s p k t = ∑ j : Fin 8,
      (graphValues c s p k j.succ-graphValues c s p k 0)*((projectionMap c s).symm t) j := by
  simp [graphLinear,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]

theorem graphFunction_affine (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (t : Point) :
    graphFunction c s p k t = graphValues c s p k 0+
      graphLinear c s p k t-graphLinear c s p k (projectionBase c s) := by
  rw [graphFunction,interpolate_eq_affine]
  rw [graphLinear_apply,graphLinear_apply]
  simp only [map_sub,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  ring

theorem graphWall_eval (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (t : Point) :
    (graphWall c s p k).eval t = t 7-graphFunction c s p k t := by
  rw [graphFunction_affine]
  simp [graphWall,Wall.eval]
  ring

theorem projectionMap_radialUnit (c : Fin 4) (s : BaseRow c) :
    projectionMap c s radialUnit = radialUnit := by
  have hv := congrFun (edge_vertices (extendedVertices c s) (original_extended_determinants c s)) (8 : Fin 9)
  have he : castPoint (extendedVertices c s 8) = projectionBase c s+radialUnit := by
    ext j
    fin_cases j <;> norm_num [extendedVertices,liftPoint,projectionBase,castPoint,radialUnit,Pi.single_apply]
  change projectionBase c s+projectionMap c s radialUnit = castPoint (extendedVertices c s 8) at hv
  exact add_left_cancel (hv.trans he)
theorem projectionSymm_radialUnit (c : Fin 4) (s : BaseRow c) :
    (projectionMap c s).symm radialUnit = radialUnit := by
  apply (projectionMap c s).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,projectionMap_radialUnit]
theorem graphLinear_radialUnit (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) :
    graphLinear c s p k radialUnit = 0 := by
  rw [graphLinear_apply,projectionSymm_radialUnit]
  simp [radialUnit,Pi.single_apply,graphValues]

theorem graphWall_proper (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) :
    ∃ t : Point, (graphWall c s p k).eval t ≠ 0 := by
  apply Wall.proper_of_linear_ne_zero
  intro h
  have h1 : (graphWall c s p k).linear radialUnit = 1 := by
    simp [graphWall,graphLinear_radialUnit,radialUnit]
  rw [h] at h1
  norm_num at h1

theorem interpolate_at_vertex (L : Point ≃L[ℝ] Point) (b : Point) (y : Fin 9 → ℝ) (i : Fin 9) :
    Bary.interpolate y (L.symm (Bary.vertices L b i-b)) = y i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Bary.vertices,Bary.interpolate,Bary.bary,Fin.sum_univ_succ]
  · simp [Bary.vertices,Bary.interpolate,Bary.bary,Fin.sum_univ_succ,Pi.single_apply]

theorem graphFunction_base_vertex (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k i : Fin 8) :
    graphFunction c s p k (castPoint (extendedVertices c s i.castSucc)) =
      (boundaryValue c s p k i : ℝ) := by
  have hv := congrFun (edge_vertices (extendedVertices c s) (original_extended_determinants c s)) i.castSucc
  rw [← hv]
  unfold graphFunction
  rw [interpolate_at_vertex]
  simp [graphValues,i.isLt]

theorem lift_vertex_eq (c : Fin 4) (s : BaseRow c) (i : Fin 8) (q : ℚ) :
    castPoint (liftPoint (baseVertex c s i) q) =
      castPoint (extendedVertices c s i.castSucc)+(q:ℝ) • radialUnit := by
  ext j
  fin_cases j <;> simp [extendedVertices,liftPoint,castPoint,radialUnit,Pi.single_apply,i.isLt]

theorem graphWall_lift_vertex (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k i : Fin 8) (q : ℚ) :
    (graphWall c s p k).eval (castPoint (liftPoint (baseVertex c s i) q)) =
      (q:ℝ)-(boundaryValue c s p k i : ℝ) := by
  rw [graphWall_eval,lift_vertex_eq,graphFunction_affine]
  have hb := graphFunction_base_vertex c s p k i
  rw [graphFunction_affine] at hb
  simp only [map_add,map_smul,smul_eq_mul,graphLinear_radialUnit,mul_zero,add_zero]
  have hr : (castPoint (extendedVertices c s i.castSucc)) 7 = 0 := by
    simp [extendedVertices,liftPoint,castPoint,i.isLt]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,radialUnit,Pi.single_eq_same,hr,zero_add,mul_one]
  linarith

theorem width_nonneg (c : Fin 4) (s : BaseRow c) (i : Fin 8) :
    lowerAt c (baseVertex c s i) ≤ upperAt c (baseVertex c s i) := by
  have hv := (original_base_checks c).2.1 s
  exact (original_widths_and_selectors c ⟨vertexId (data c) s i,hv.2 i⟩).1
theorem height_mono (c : Fin 4) (s : BaseRow c) (i : Fin 8) {n m : ℕ} (hnm : n ≤ m) :
    height c (baseVertex c s i) n ≤ height c (baseVertex c s i) m := by
  have hw := sub_nonneg.mpr (width_nonneg c s i)
  have hnmQ : (n:ℚ)/4 ≤ (m:ℚ)/4 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hnm) (by norm_num)
  exact add_le_add_left (mul_le_mul_of_nonneg_right hnmQ hw) _

theorem same_staircase_nonneg (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (i : Fin 9) :
    0 ≤ (graphWall c s p k).eval (castPoint (pieceVertices c s p k i)) := by
  unfold pieceVertices
  split_ifs with hi
  · rw [graphWall_lift_vertex]
    simp [boundaryValue,hi]
  · rw [graphWall_lift_vertex]
    unfold boundaryValue
    split_ifs
    · exact sub_nonneg.mpr (by exact_mod_cast height_mono c s ⟨i.val-1,by omega⟩ (Nat.le_succ p.val))
    · simp

theorem later_staircase_nonpos (c : Fin 4) (s : BaseRow c) (p : Fin 4)
    (k l : Fin 8) (hkl : k < l) (i : Fin 9) :
    (graphWall c s p k).eval (castPoint (pieceVertices c s p l i)) ≤ 0 := by
  unfold pieceVertices
  split_ifs with hi
  · rw [graphWall_lift_vertex]
    unfold boundaryValue
    split_ifs
    · simp
    · exact sub_nonpos.mpr (by exact_mod_cast height_mono c s ⟨i.val,by omega⟩ (Nat.le_succ p.val))
  · rw [graphWall_lift_vertex]
    have hj : ¬ i.val-1 ≤ k.val := by have := hkl; omega
    simp [boundaryValue,hj]

end
end ImbalancedChen.P2OriginalRadialStaircaseGraph
