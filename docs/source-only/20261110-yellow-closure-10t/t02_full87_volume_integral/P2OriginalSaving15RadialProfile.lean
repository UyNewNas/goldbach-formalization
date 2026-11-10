import ImbalancedChen.P2OriginalSaving15RadialArchive
import ImbalancedChen.P4AOriginalFull87KernelPositiveWitness

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The staircase vertices retain the actual seed7 source and its actual
A(t1+t8)-eta versus D(t2+t3) residual. Weak source membership is derived
from the original lifted endpoint rows. No source/integral licence or
old saving19 physical guard is accepted as an input.
-/
namespace ImbalancedChen.P2OriginalSaving15RadialProfile
noncomputable section
open Set MeasureTheory VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSaving15RadialArchive
open P2OriginalRadialBasePulling (QPoint7 eval7 vertex vertexId)
open P2OriginalSaving16OriginalArchive (QPoint castPoint evalQ edgeMatrix)
open P2OriginalSaving16SimplexBinding (edgeEquiv edge_vertices)
open P2OriginalPhysicalSimplexMomentRow (Row)
namespace Bary
export P2OriginalSaving19SimplexMoments
  (interpolate pointInterpolate interpolate_const interpolate_sub interpolate_add
   interpolate_div interpolate_sum pointInterpolate_apply vertices_interpolate)
end Bary
abbrev Point := Fin 8 → ℝ
def R (t : Point) : ℝ := C (t 1 + t 2)
def M (t : Point) : ℝ := A (t 0 + t 7) - 1/1000000
def total (t : Point) : ℝ := ∑ i, t i
def gap (t : Point) : ℝ := M t - R t
def factors (t : Point) : Fin 10 → ℝ :=
  ![R t-total t,M t-total t,t 0,t 1,t 2,t 3,t 4,t 5,t 6,t 7]
def comparisonQ (t : QPoint) : ℚ := 57/64-(3/2)*(t 1+t 2)
def capQ (t : QPoint) : ℚ := (1+(t 0+t 7))/2-1/1000000
def gapQ (t : QPoint) : ℚ := capQ t-comparisonQ t
def factorsQ (t : QPoint) : Fin 10 → ℚ :=
  ![comparisonQ t-∑ i,t i,capQ t-∑ i,t i,t 0,t 1,t 2,t 3,t 4,t 5,t 6,t 7]
def seedCell : P4AOriginalFull87SourceDictionary.Cell := .remaining .seed

theorem gapQ_cast (t : QPoint) : (gapQ t : ℝ) = gap (castPoint t) := by
  norm_num [gapQ,capQ,comparisonQ,gap,M,R,A,C,castPoint] <;> ring
theorem factorsQ_cast (t : QPoint) (j : Fin 10) : (factorsQ t j : ℝ) = factors (castPoint t) j := by
  fin_cases j <;> norm_num [factorsQ,capQ,comparisonQ,factors,M,R,total,A,C,castPoint] <;> ring

theorem seed_profile_dictionary (t : Point) :
    P4AOriginalFull87SourceDictionary.newCap seedCell t = M t ∧
    P4AOriginalFull87SourceDictionary.comparison seedCell t = R t := by
  constructor
  · simp [seedCell,P4AOriginalFull87SourceDictionary.newCap,
      P4AOriginalRemainingEighthSources.newCap,P4AOriginalRemainingEighthSources.descendingNew,
      P4AOriginalRemainingEighthSources.selectedSum,P4AOriginalRemainingEighthSources.selected,
      P4AOriginalRemainingEighthSources.eta,M]
  · rfl

theorem seed_kernel_dictionary (t : Point) :
    4 * gap t / ∏ j, factors t j = P4AOriginalFull87EighthKernelControl.kernel seedCell t := by
  rw [P4AOriginalFull87EighthKernelControl.kernel,P4AOriginalFull87EighthKernelControl.residual,
    (seed_profile_dictionary t).1,(seed_profile_dictionary t).2]
  norm_num [gap,factors,Fin.prod_univ_succ,P4AOriginalFull87EighthKernelControl.total,
    P4AOriginalFull87EighthKernelControl.product,total] <;> ring

theorem evalQ_height (a : Fin 9 → ℚ) (c : Fin 4) (x : QPoint7) (n : ℕ) :
    evalQ a (liftPoint x (height c x n)) =
      (1-(n:ℚ)/4) * evalQ a (liftPoint x (lowerAt c x)) +
        ((n:ℚ)/4) * evalQ a (liftPoint x (upperAt c x)) := by
  norm_num [evalQ,liftPoint,height,Fin.sum_univ_succ] <;> ring

theorem height_closed_rows (c : Fin 4) (v : Fin (data c).vertices.size)
    (n : ℕ) (hn : n ≤ 4) (g : Fin 96) :
    0 ≤ evalQ (seedRows g)
      (liftPoint (vertex (data c) v.val) (height c (vertex (data c) v.val) n)) := by
  rw [evalQ_height]
  have he := original_endpoint_source_rows c v g
  have hnQ : (n : ℚ) ≤ 4 := by exact_mod_cast hn
  exact add_nonneg (mul_nonneg (by linarith : (0:ℚ) ≤ 1-(n:ℚ)/4) he.1)
    (mul_nonneg (by positivity) he.2)

theorem piece_vertex_closed_rows (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8)
    (i : Fin 9) (g : Fin 96) : 0 ≤ evalQ (seedRows g) (pieceVertices c s p k i) := by
  unfold pieceVertices
  split_ifs with hi
  · have hv := (original_base_checks c).2.1 s
    exact height_closed_rows c ⟨vertexId (data c) s ⟨i.val,by omega⟩,hv.2 _⟩ p.val (by omega) g
  · have hv := (original_base_checks c).2.1 s
    exact height_closed_rows c ⟨vertexId (data c) s ⟨i.val-1,by omega⟩,hv.2 _⟩ (p.val+1) (by omega) g

abbrev evalRow := P2OriginalSaving16FourteenPhysicalAtlas.evalRow
theorem evalQ_cast (a : Fin 9 → ℚ) (t : QPoint) : evalRow a (castPoint t) = (evalQ a t : ℝ) :=
  P2OriginalSaving16OriginalArchive.evalQ_cast a t

theorem weak_rows_mem_closure {t : Point} (ht : ∀ g : Fin 96, 0 ≤ evalRow (seedRows g) t) :
    t ∈ closure (P4AOriginalFull87StrictActionTrim.sourceSet seedCell) := by
  let z := P4AOriginalFull87KernelPositiveWitness.originalCentre seedCell
  have hz : P4AOriginalFull87SourceDictionary.Source seedCell z :=
    P4AOriginalFull87KernelPositiveWitness.originalCentre_mem_source _
  let f : ℝ → Point := fun a => a • z + (1-a) • t
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hp : ∀ a ∈ Ioo (0:ℝ) 1, f a ∈ P4AOriginalFull87StrictActionTrim.sourceSet seedCell := by
    intro a ha g
    rw [show f a = a • z+(1-a) • t from rfl,
      P2OriginalSaving16FourteenPhysicalAtlas.evalRow_convexCombination _ _ _ _ _ (by ring)]
    exact add_pos_of_pos_of_nonneg (mul_pos ha.1 (hz g))
      (mul_nonneg (sub_nonneg.mpr ha.2.le) (ht g))
  have h0 : (0:ℝ) ∈ closure (Ioo (0:ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]
    exact ⟨le_rfl,by norm_num⟩
  have hm := image_closure_subset_closure_image hf ⟨0,h0,rfl⟩
  have hs : f '' Ioo (0:ℝ) 1 ⊆ P4AOriginalFull87StrictActionTrim.sourceSet seedCell := by
    rintro _ ⟨a,ha,rfl⟩
    exact hp a ha
  simpa [f] using closure_mono hs hm

theorem piece_vertex_mem_closure (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (i : Fin 9) :
    castPoint (pieceVertices c s p k i) ∈ closure (P4AOriginalFull87StrictActionTrim.sourceSet seedCell) := by
  apply weak_rows_mem_closure
  intro g
  rw [evalQ_cast]
  exact_mod_cast piece_vertex_closed_rows c s p k i g

theorem continuous_gap : Continuous gap := by unfold gap,M,R,A,C; fun_prop
theorem continuous_factor (j : Fin 10) : Continuous (fun t => factors t j) := by
  fin_cases j <;> simp only [factors,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals dsimp [M,R,total,A,C] <;> fun_prop

theorem closure_gap_nonneg {t : Point}
    (ht : t ∈ closure (P4AOriginalFull87StrictActionTrim.sourceSet seedCell)) : 0 ≤ gap t := by
  apply (closure_minimal (s := P4AOriginalFull87StrictActionTrim.sourceSet seedCell)
    (t := {x | 0 ≤ gap x}) ?_ (isClosed_le continuous_const continuous_gap)) ht
  intro x hx
  have h := (P4AOriginalFull87SourceDictionary.source_improvement_terminal hx).1
  rw [(seed_profile_dictionary x).1,(seed_profile_dictionary x).2] at h
  exact (sub_pos.mpr h).le

theorem closure_factor_floor {t : Point}
    (ht : t ∈ closure (P4AOriginalFull87StrictActionTrim.sourceSet seedCell)) (j : Fin 10) :
    P2OriginalPhysicalSimplexMomentRow.cutoff ≤ factors t j := by
  apply (closure_minimal (s := P4AOriginalFull87StrictActionTrim.sourceSet seedCell)
    (t := {x | P2OriginalPhysicalSimplexMomentRow.cutoff ≤ factors x j}) ?_
    (isClosed_le continuous_const (continuous_factor j))) ht
  intro x hx
  have hr := P4AOriginalFull87EighthKernelControl.source_residual_range hx
  have hc := P4AOriginalFull87EighthKernelControl.source_coordinate_lower hx
  have hp := hr.1.trans hr.2.1
  have hm := hr.2.2.1
  rw [(seed_profile_dictionary x).1,(seed_profile_dictionary x).2] at hp hm
  fin_cases j <;> simp only [factors,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact hp.le
  · change P4AOriginalFull87EighthKernelControl.cutoff < R x - total x at hp
    change R x < M x at hm
    change P4AOriginalFull87EighthKernelControl.cutoff ≤ M x-total x
    linarith
  all_goals exact (hc _).le

theorem interpolate_mul_const (v : Fin 9 → ℝ) (a : ℝ) (x : Point) :
    Bary.interpolate (fun i => a*v i) x = a*Bary.interpolate v x :=
  P2OriginalSaving16JensenFloor.interpolate_mul_const v a x
theorem R_interpolate (v : Fin 9 → Point) (x : Point) :
    R (Bary.pointInterpolate v x) = Bary.interpolate (fun i => R (v i)) x := by
  simp only [R,C,Bary.interpolate_sub,Bary.interpolate_const,Bary.interpolate_add,
    interpolate_mul_const,Bary.pointInterpolate_apply]
theorem M_interpolate (v : Fin 9 → Point) (x : Point) :
    M (Bary.pointInterpolate v x) = Bary.interpolate (fun i => M (v i)) x := by
  simp only [M,A,Bary.interpolate_sub,Bary.interpolate_const,Bary.interpolate_add,
    Bary.interpolate_div,Bary.pointInterpolate_apply]
theorem total_interpolate (v : Fin 9 → Point) (x : Point) :
    total (Bary.pointInterpolate v x) = Bary.interpolate (fun i => total (v i)) x := by
  simp only [total,Bary.pointInterpolate_apply,Bary.interpolate_sum]
theorem gap_interpolate (v : Fin 9 → Point) (x : Point) :
    gap (Bary.pointInterpolate v x) = Bary.interpolate (fun i => gap (v i)) x := by
  simp only [gap,M_interpolate,R_interpolate,Bary.interpolate_sub]
theorem factors_interpolate (v : Fin 9 → Point) (x : Point) (j : Fin 10) :
    factors (Bary.pointInterpolate v x) j = Bary.interpolate (fun i => factors (v i) j) x := by
  fin_cases j <;> simp only [factors,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · rw [R_interpolate,total_interpolate,Bary.interpolate_sub]
  · rw [M_interpolate,total_interpolate,Bary.interpolate_sub]
  all_goals exact Bary.pointInterpolate_apply v x _

theorem vertices_gap_sum_pos (v : Fin 9 → QPoint) (hd : (edgeMatrix v).det ≠ 0)
    (hv : ∀ i, castPoint (v i) ∈ closure (P4AOriginalFull87StrictActionTrim.sourceSet seedCell)) :
    0 < ∑ i, gapQ (v i) := by
  have hn (i : Fin 9) : 0 ≤ gap (castPoint (v i)) := closure_gap_nonneg (hv i)
  have hs : 0 ≤ ∑ i, gap (castPoint (v i)) := Finset.sum_nonneg (fun i _ => hn i)
  have hcast : (∑ i, (gapQ (v i) : ℝ)) = ∑ i, gap (castPoint (v i)) := by simp_rw [gapQ_cast]
  suffices hp : 0 < ∑ i, gap (castPoint (v i)) by
    have hq : 0 < ∑ i, (gapQ (v i) : ℝ) := by rw [hcast]; exact hp
    exact_mod_cast hq
  by_contra hp
  have he : (∑ i, gap (castPoint (v i))) = 0 := le_antisymm (le_of_not_gt hp) hs
  have hz (i : Fin 9) : gap (castPoint (v i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 9))) => hn i)).mp he i (Finset.mem_univ i)
  let L := edgeEquiv v hd
  let b := castPoint (v 0)
  let z := P4AOriginalFull87KernelPositiveWitness.originalCentre seedCell
  let x := L.symm (z-b)
  have hrec : Bary.pointInterpolate (fun i => castPoint (v i)) x = z := by
    rw [← edge_vertices v hd,Bary.vertices_interpolate]
    simp [x,L,b]
  have hg : gap z = 0 := by
    rw [← hrec,gap_interpolate]
    simp_rw [hz]
    exact Bary.interpolate_const 0 x
  have hstrict := (P4AOriginalFull87SourceDictionary.source_improvement_terminal
    (P4AOriginalFull87KernelPositiveWitness.originalCentre_mem_source seedCell)).1
  rw [(seed_profile_dictionary z).1,(seed_profile_dictionary z).2] at hstrict
  exact (sub_pos.mpr hstrict).ne' hg

def actualPieceRow (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8)
    (hd : (edgeMatrix (pieceVertices c s p k)).det ≠ 0) : Row where
  verticesQ := pieceVertices c s p k
  gapsQ := fun i => gapQ (pieceVertices c s p k i)
  factorsQ := fun i j => factorsQ (pieceVertices c s p k i) j
  determinant_ne_zero := hd
  gap_nonneg := fun i => by
    have h := closure_gap_nonneg (piece_vertex_mem_closure c s p k i)
    rw [← gapQ_cast] at h
    exact_mod_cast h
  gapTotal_pos := vertices_gap_sum_pos _ hd (piece_vertex_mem_closure c s p k)
  factor_floor := fun i j => by
    have h := closure_factor_floor (piece_vertex_mem_closure c s p k i) j
    rw [← factorsQ_cast,← P2OriginalPhysicalSimplexMomentRow.cutoffQ_cast] at h
    exact_mod_cast h

theorem actual_piece_density (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8)
    (hd : (edgeMatrix (pieceVertices c s p k)).det ≠ 0) (t : Point) :
    P2OriginalPhysicalSimplexMomentRow.rowDensity (actualPieceRow c s p k hd) t =
      P4AOriginalFull87EighthKernelControl.kernel seedCell t := by
  let r := actualPieceRow c s p k hd
  have hg : P2OriginalPhysicalSimplexMomentRow.rowGap r t = gap t := by
    unfold P2OriginalPhysicalSimplexMomentRow.rowGap
    simp_rw [show ∀ i, (r.gapsQ i : ℝ) = gap (castPoint (r.verticesQ i)) from fun i => gapQ_cast _]
    rw [← gap_interpolate,P2OriginalPhysicalSimplexMomentRow.row_pointInterpolate_coordinates]
  have hf (j : Fin 10) : P2OriginalPhysicalSimplexMomentRow.rowFactors r t j = factors t j := by
    unfold P2OriginalPhysicalSimplexMomentRow.rowFactors
    simp_rw [show ∀ i, (r.factorsQ i j : ℝ) = factors (castPoint (r.verticesQ i)) j from fun i => factorsQ_cast _ j]
    rw [← factors_interpolate,P2OriginalPhysicalSimplexMomentRow.row_pointInterpolate_coordinates]
  change P2OriginalPhysicalSimplexMomentRow.rowDensity r t = _
  rw [P2OriginalPhysicalSimplexMomentRow.rowDensity,hg]
  simp_rw [hf]
  exact seed_kernel_dictionary t

end
end ImbalancedChen.P2OriginalSaving15RadialProfile
