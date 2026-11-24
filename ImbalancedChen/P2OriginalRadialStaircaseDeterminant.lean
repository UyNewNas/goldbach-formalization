import ImbalancedChen.P2OriginalSaving15RadialArchive
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
An exact identity for the ORIGINAL vertical staircase vertex order.
Subtract the lower-pivot edge from the upper-pivot edge, then expand
along that vertical row. The remaining minor is the original 7D edge
matrix, in its original order. No determinant is evaluated here.
This separate resource supplement does not change the frozen packet.
-/
namespace ImbalancedChen.P2OriginalRadialStaircaseDeterminant
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped BigOperators
open P2OriginalSaving15RadialArchive
open P2OriginalSaving16OriginalArchive (QPoint edgeMatrix physicalVolumeQ)
open P2OriginalRadialBasePulling (QPoint7)

def baseEdge (v : Fin 8 → QPoint7) : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => v i.succ j - v 0 j

def stairs (v : Fin 8 → QPoint7) (lo hi : Fin 8 → ℚ) (k : Fin 8) : Fin 9 → QPoint :=
  fun i => if h : i.val ≤ k.val then
    let j : Fin 8 := ⟨i.val,by omega⟩
    liftPoint (v j) (lo j)
  else
    let j : Fin 8 := ⟨i.val-1,by omega⟩
    liftPoint (v j) (hi j)

def clearedEdge (v : Fin 8 → QPoint7) (lo hi : Fin 8 → ℚ) (k : Fin 8) :
    Matrix (Fin 8) (Fin 8) ℚ :=
  if h : k.val = 0 then edgeMatrix (stairs v lo hi k)
  else
    let j : Fin 8 := ⟨k.val-1,by omega⟩
    (edgeMatrix (stairs v lo hi k)).updateRow k
      ((edgeMatrix (stairs v lo hi k)) k - (edgeMatrix (stairs v lo hi k)) j)

theorem clearedEdge_det (v : Fin 8 → QPoint7) (lo hi : Fin 8 → ℚ) (k : Fin 8) :
    (clearedEdge v lo hi k).det = (edgeMatrix (stairs v lo hi k)).det := by
  unfold clearedEdge
  split_ifs with hk
  · rfl
  · have hkj : k ≠ (⟨k.val-1,by omega⟩ : Fin 8) := by
      intro he
      have hv := congrArg Fin.val he
      omega
    simpa only [sub_eq_add_neg,neg_one_smul] using
      Matrix.det_updateRow_add_smul_self (edgeMatrix (stairs v lo hi k)) hkj (-1 : ℚ)

theorem clearedEdge_pivot (v : Fin 8 → QPoint7) (lo hi : Fin 8 → ℚ) (k j : Fin 8) :
    clearedEdge v lo hi k k j = if j = 7 then hi k-lo k else 0 := by
  fin_cases k <;> fin_cases j <;>
    norm_num [clearedEdge,stairs,edgeMatrix,liftPoint,Matrix.updateRow_apply] <;> ring

theorem clearedEdge_minor (v : Fin 8 → QPoint7) (lo hi : Fin 8 → ℚ) (k : Fin 8) :
    (clearedEdge v lo hi k).submatrix k.succAbove (7 : Fin 8).succAbove = baseEdge v := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.submatrix,clearedEdge,stairs,edgeMatrix,liftPoint,baseEdge,
      Matrix.updateRow_apply,Fin.succAbove] <;> ring

/-- Signed row expansion; its sign is retained before taking absolute values. -/
theorem stairs_det (v : Fin 8 → QPoint7) (lo hi : Fin 8 → ℚ) (k : Fin 8) :
    (edgeMatrix (stairs v lo hi k)).det =
      (-1 : ℚ)^(k.val+7) * (hi k-lo k) * (baseEdge v).det := by
  rw [← clearedEdge_det,Matrix.det_succ_row _ k]
  rw [Finset.sum_eq_single (7 : Fin 8)]
  · rw [clearedEdge_pivot,if_pos rfl,clearedEdge_minor]
  · intro j _ hj
    rw [clearedEdge_pivot,if_neg hj]
    ring
  · simp

def width (c : Fin 4) (s : BaseRow c) (k : Fin 8) : ℚ :=
  upperAt c (baseVertex c s k)-lowerAt c (baseVertex c s k)

theorem panel_height_difference (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) :
    height c (baseVertex c s k) (p.val+1)-height c (baseVertex c s k) p.val =
      width c s k/4 := by
  simp only [height,width,Nat.cast_add,Nat.cast_one]
  ring

theorem piece_det (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) :
    (edgeMatrix (pieceVertices c s p k)).det =
      (-1 : ℚ)^(k.val+7) * (width c s k/4) * (baseEdge (baseVertex c s)).det := by
  change (edgeMatrix (stairs (baseVertex c s)
    (fun i => height c (baseVertex c s i) p.val)
    (fun i => height c (baseVertex c s i) (p.val+1)) k)).det = _
  rw [stairs_det,panel_height_difference]

theorem width_nonneg (c : Fin 4) (s : BaseRow c) (k : Fin 8) : 0 ≤ width c s k := by
  have hv := (original_base_checks c).2.1 s
  exact sub_nonneg.mpr (original_widths_and_selectors c
    ⟨P2OriginalRadialBasePulling.vertexId (data c) s k,hv.2 k⟩).1

theorem piece_abs_det (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) :
    |(edgeMatrix (pieceVertices c s p k)).det| =
      |(baseEdge (baseVertex c s)).det| * width c s k/4 := by
  rw [piece_det]
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  rw [abs_of_nonneg (div_nonneg (width_nonneg c s k) (by norm_num : (0 : ℚ) ≤ 4))]
  ring

end
end ImbalancedChen.P2OriginalRadialStaircaseDeterminant
