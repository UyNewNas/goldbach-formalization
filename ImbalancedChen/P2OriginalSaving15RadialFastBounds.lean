import ImbalancedChen.P2OriginalRadialStaircaseDeterminant
import ImbalancedChen.P2OriginalRadialPieceSeparation
import Mathlib.Data.Fintype.BigOperators

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Resource conversion only: one original 7D volume witness per outer row,
then the exact staircase determinant identity supplies all 32 physical
pieces. The closed panel check contains no 8D determinant or Row value.
The same original Q96 panel is floored once; pieces remain unrounded.
-/
namespace ImbalancedChen.P2OriginalSaving15RadialFastBounds
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped BigOperators
open P2OriginalSaving15RadialArchive
open P2OriginalRadialStaircaseDeterminant
open P2OriginalRadialPieceSeparation (Index indexVertices Piece pieceRow)
open P2OriginalSaving15RadialProfile (actualPieceRow gapQ factorsQ)
open P2OriginalSaving16OriginalArchive (edgeMatrix physicalVolumeQ)
open P2OriginalPhysicalSimplexMomentRow (Row rowMassQ rowMeansQ)
open P2OriginalPhysicalSimplexJensenRow (rowJensenQ)
open P2OriginalLogMomentQ96CheckerSourceOnly (oldEvaluator)

def outerVolume (c : Fin 4) (s : BaseRow c) : ℚ :=
  ((chamber c).rows.getD s.val default).outerVolume

/-- These are the 2847 ORIGINAL stored outer-volume witnesses. Their
determinants are 7D, and are checked once, rather than once per piece. -/
theorem original_outer_volume_checks : ∀ (c : Fin 4) (s : BaseRow c),
    0 < outerVolume c s ∧
    |(baseEdge (baseVertex c s)).det| = outerVolume c s * (7.factorial : ℚ) := by decide

theorem base_det_ne_zero (c : Fin 4) (s : BaseRow c) :
    (baseEdge (baseVertex c s)).det ≠ 0 := by
  apply abs_pos.mp
  rw [(original_outer_volume_checks c s).2]
  exact mul_pos (original_outer_volume_checks c s).1 (by norm_num)

theorem piece_det_ne_zero_iff (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) :
    (edgeMatrix (pieceVertices c s p k)).det ≠ 0 ↔ width c s k ≠ 0 := by
  constructor
  · intro hd hw
    apply hd
    apply abs_eq_zero.mp
    rw [piece_abs_det,hw]
    ring
  · intro hw hd
    have hb := abs_pos.mpr (base_det_ne_zero c s)
    have hwpos : 0 < width c s k :=
      lt_of_le_of_ne (width_nonneg c s k) (Ne.symm hw)
    have hp : 0 < |(edgeMatrix (pieceVertices c s p k)).det| := by
      rw [piece_abs_det]
      exact div_pos (mul_pos hb hwpos) (by norm_num)
    rw [hd,abs_zero] at hp
    exact (lt_irrefl 0) hp

theorem piece_volume (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) :
    physicalVolumeQ (pieceVertices c s p k) = outerVolume c s * width c s k/32 := by
  rw [physicalVolumeQ,piece_abs_det,(original_outer_volume_checks c s).2]
  norm_num [Nat.factorial] <;> ring

def gapSum (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) : ℚ :=
  ∑ i : Fin 9, gapQ (pieceVertices c s p k i)
def means (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) (j : Fin 10) : ℚ :=
  ((∑ i : Fin 9, factorsQ (pieceVertices c s p k i) j) +
    (∑ i : Fin 9, gapQ (pieceVertices c s p k i) * factorsQ (pieceVertices c s p k i) j) /
      gapSum c s p k)/10
def unroundedBound (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) : ℚ :=
  oldEvaluator ((outerVolume c s * width c s k/32) * gapSum c s p k/9) (means c s p k)

theorem rowJensen_eq_unrounded (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8)
    (hd : (edgeMatrix (pieceVertices c s p k)).det ≠ 0) :
    rowJensenQ (actualPieceRow c s p k hd) = unroundedBound c s p k := by
  change oldEvaluator (physicalVolumeQ (pieceVertices c s p k) * gapSum c s p k/9)
    (means c s p k) = unroundedBound c s p k
  rw [piece_volume] <;> rfl

def indexWidth (i : Index) : ℚ := width i.1 i.2.1 i.2.2.2
abbrev FastPiece := {i : Index // indexWidth i ≠ 0}
def toOriginal (i : FastPiece) : Piece :=
  ⟨i.val,(piece_det_ne_zero_iff i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2).mpr i.property⟩
def pieceEquiv : FastPiece ≃ Piece where
  toFun := toOriginal
  invFun := fun i => ⟨i.val,
    (piece_det_ne_zero_iff i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2).mp i.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
def fastRow (i : FastPiece) : Row := pieceRow (toOriginal i)

/-- The executable arithmetic expression has only the original outer
volume, pivot width, and original affine vertex values. In particular
it does not reduce the proof-valued construction of fastRow. -/
def indexedFastQ (i : Index) : ℚ :=
  dite (indexWidth i ≠ 0)
    (fun _ => unroundedBound i.1 i.2.1 i.2.2.1 i.2.2.2) (fun _ => 0)
def pieceFastQ (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) : ℚ :=
  indexedFastQ ⟨c,s,p,k⟩

/-- Original once-per-panel Q96 floor; the right side uses no determinant. -/
theorem original_fast_panel_floor_checks : ∀ (c : Fin 4) (s : BaseRow c) (p : Fin 4),
    ((panelRecord c s p).floor : ℚ)/(2 : ℚ)^96 ≤ ∑ k : Fin 8, pieceFastQ c s p k := by decide

theorem indexedFast_eq_original_expression (i : Index) :
    indexedFastQ i =
      if hd : (edgeMatrix (indexVertices i)).det ≠ 0 then rowJensenQ (pieceRow ⟨i,hd⟩) else 0 := by
  by_cases hw : indexWidth i ≠ 0
  · have hd := (piece_det_ne_zero_iff i.1 i.2.1 i.2.2.1 i.2.2.2).mpr hw
    rw [indexedFastQ,dif_pos hw,dif_pos hd]
    exact (rowJensen_eq_unrounded i.1 i.2.1 i.2.2.1 i.2.2.2 hd).symm
  · have hd : ¬ (edgeMatrix (indexVertices i)).det ≠ 0 :=
      fun hd => hw ((piece_det_ne_zero_iff i.1 i.2.1 i.2.2.1 i.2.2.2).mp hd)
    rw [indexedFastQ,dif_neg hw,dif_neg hd]

theorem flattened_fast_sum :
    (∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4, ∑ k : Fin 8, pieceFastQ c s p k) =
      ∑ i : FastPiece, rowJensenQ (fastRow i) := by
  have he : (∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4, ∑ k : Fin 8, pieceFastQ c s p k) =
      ∑ i : Index, indexedFastQ i := by
    simp only [Index,Fintype.sum_sigma,Fintype.sum_prod_type,pieceFastQ]
  rw [he,indexedFastQ,Fintype.sum_dite]
  simp only [Finset.sum_const_zero,add_zero]
  apply Finset.sum_congr rfl
  intro i _
  exact (rowJensen_eq_unrounded i.val.1 i.val.2.1 i.val.2.2.1 i.val.2.2.2
    (toOriginal i).property).symm

theorem original_saved_floor_le_fast_jensen_sum :
    (savedNumerator : ℚ)/(2 : ℚ)^96 ≤ ∑ i : FastPiece, rowJensenQ (fastRow i) := by
  calc
    _ = ∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4,
        ((panelRecord c s p).floor : ℚ)/(2 : ℚ)^96 := by simp [savedNumerator,Finset.sum_div]
    _ ≤ ∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4, ∑ k : Fin 8, pieceFastQ c s p k :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun s _ =>
        Finset.sum_le_sum (fun p _ => original_fast_panel_floor_checks c s p)))
    _ = _ := flattened_fast_sum

end
end ImbalancedChen.P2OriginalSaving15RadialFastBounds
