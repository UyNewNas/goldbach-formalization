import ImbalancedChen.P1OriginalFourthFourSubintervals
import ImbalancedChen.P1OriginalFourthAllRowsAdmission

/-! The actual integer R0, R1 and four upward-rounded indices on every
original 17-byte row. All comparisons are on the row's physical
coordinates and the actual six-component old cap and selected new cap. -/
namespace ImbalancedChen.P1OriginalFourthRowSubintervals
noncomputable section
open Set
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P2OriginalFourthCapProducerInterface
open P1OriginalFourthIntegerGapSemantics P1OriginalFourthIntegerGeometryAdmission
open OriginalU2CoupledRecurrenceSourceOnly (upper)
open P1OriginalFourthFourSubintervals P1OriginalFourthN8193
open P5OriginalFourthFifthSourceInputs P1OriginalFourthAllRowsAdmission

def R0 (raw : FourthWireRow) : ℚ := (integerR0 raw:ℚ)/6553600
def R1 (raw : FourthWireRow) : ℚ := (integerR1 raw:ℚ)/6553600
def qBlend (A B : ℚ) (j : ℕ) : ℚ := (1-(j:ℚ)/4)*A+((j:ℚ)/4)*B
def argument (raw : FourthWireRow) (k : Fin 4) : ℚ :=
  qBlend (R0 raw) (R1 raw) (k.val+1)/raw.toProducerRow.lower 3

theorem qBlend_cast (A B : ℚ) (j : ℕ) :
    (qBlend A B j:ℝ) = blend (A:ℝ) (B:ℝ) j := by simp [qBlend,blend]

private theorem real_upper (raw : FourthWireRow) (a : IntegerAffine) :
    (a.toAffine.upper raw.toProducerRow.lower raw.toProducerRow.upper:ℝ) =
      (integerUpper a raw.lo raw.hi:ℝ)/6553600 := by
  have hh := congrArg (fun x : ℚ => (x:ℝ)) (upper_scaled a raw.lo raw.hi)
  simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using hh

private theorem old_piece_scaled (raw : FourthWireRow) (j : Fin 6) :
    min (((oldPiece j false).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper:ℝ)
      (((oldPiece j true).sub sumAffine).upper raw.toProducerRow.lower raw.toProducerRow.upper:ℝ) =
        (commonOldResidualPiece raw j:ℝ)/6553600 := by
  have hp (s : Bool) := real_upper raw ((sourceOld j s).sub sourceSum)
  simp only [toAffine_sub,sourceOld_toAffine,sourceSum_toAffine] at hp
  simp only [hp,commonOldResidualPiece,Int.cast_min,min_div_div_right (by norm_num : (0:ℝ)≤6553600)]

private theorem new_piece_scaled (raw : FourthWireRow) :
    min (((tentPlane raw.toProducerRow.selected false).sub sumAffine).upper
        raw.toProducerRow.lower raw.toProducerRow.upper:ℝ)
      (((tentPlane raw.toProducerRow.selected true).sub sumAffine).upper
        raw.toProducerRow.lower raw.toProducerRow.upper:ℝ) =
      (integerNewResidualPiece raw:ℝ)/6553600 := by
  have hp (s : Bool) := real_upper raw ((sourceTent raw.toProducerRow.selected s).sub sourceSum)
  simp only [toAffine_sub,sourceTent_toAffine,sourceSum_toAffine] at hp
  simp only [hp,integerNewResidualPiece,Int.cast_min,min_div_div_right (by norm_num : (0:ℝ)≤6553600)]

theorem residual_le_R0 (raw : FourthWireRow) (t : Point) (ht : t ∈ raw.toProducerRow.box) :
    oldCap t - total t ≤ (R0 raw:ℝ) := by
  refine (old_residual_le_upper _ _ t ht.1 ht.2).trans ?_
  unfold oldResidualUpper
  apply Finset.sup'_le
  intro j _hj
  rw [old_piece_scaled]
  have h := Finset.le_sup' (programOldResidualPiece raw) (Finset.mem_univ (commonToPython j))
  have hj : commonOldResidualPiece raw j ≤ integerR0 raw := by
    simpa only [programOldResidualPiece,pythonToCommon_commonToPython] using h
  simp only [R0,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hj) (by norm_num)

theorem residual_le_R1 (raw : FourthWireRow) (t : Point) (ht : t ∈ raw.toProducerRow.box) :
    raw.toProducerRow.candidate t - total t ≤ (R1 raw:ℝ) := by
  have h0 := ((tentPlane raw.toProducerRow.selected false).sub sumAffine).eval_le_upper
    _ _ t ht.1 ht.2
  have h1 := ((tentPlane raw.toProducerRow.selected true).sub sumAffine).eval_le_upper
    _ _ t ht.1 ht.2
  rw [Affine.eval_sub,sumAffine_eval] at h0 h1
  have h := min_le_min h0 h1
  rw [← min_sub,new_piece_scaled] at h
  refine h.trans ?_
  simp only [R1,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast (le_max_right (integerR0 raw) (integerNewResidualPiece raw))

theorem R_range (raw : FourthWireRow) (hr : raw ∈ originalFourthWireRows) :
    0 < R0 raw ∧ R0 raw ≤ R1 raw ∧ R1 raw < 5*raw.toProducerRow.lower 3 := by
  obtain ⟨_,_,_,_,hr0,hr1⟩ := (integerGeometryAccept_iff raw).mp (all_original_rows_pass raw hr)
  have h0 : (0:ℚ) < (integerR0 raw:ℚ) := by exact_mod_cast hr0
  have h1 : (integerR1 raw:ℚ) < 160*(raw.lo 3:ℚ) := by exact_mod_cast hr1
  have h2 : (integerR0 raw:ℚ) ≤ (integerR1 raw:ℚ) := by
    exact_mod_cast (le_max_left (integerR0 raw) (integerNewResidualPiece raw))
  simp only [R0,R1,fourth_lower]
  exact ⟨by positivity,by linarith only [h2],by linarith only [h1]⟩

theorem argument_le_five (raw : FourthWireRow) (hr : raw ∈ originalFourthWireRows) (k : Fin 4) :
    argument raw k ≤ 5 := by
  obtain ⟨h0,h01,h5⟩ := R_range raw hr
  have hl : 0 < raw.toProducerRow.lower 3 := by linarith
  have h : qBlend (R0 raw) (R1 raw) (k.val+1) ≤ R1 raw := by
    have hk : ((k.val+1:ℕ):ℚ) ≤ 4 := by exact_mod_cast (show k.val+1 ≤ 4 by omega)
    unfold qBlend
    nlinarith only [mul_nonneg (show 0 ≤ 1-((k.val+1:ℕ):ℚ)/4 by linarith) (sub_nonneg.mpr h01)]
  exact (div_le_iff₀ hl).mpr (h.trans h5.le)

def rowIndex (raw : FourthWireRow) (hr : raw ∈ originalFourthWireRows) (k : Fin 4) : Fin 8193 :=
  ⟨ceilIndex (argument raw k),ceilIndex_lt (argument_le_five raw hr k)⟩

/-- The pointwise four-ceiling bound on every original row, with the
true factor 4 and the true four reciprocal coordinates. -/
theorem original_row_density (raw : FourthWireRow) (hr : raw ∈ originalFourthWireRows)
    (t : Point) (ht : t ∈ raw.toProducerRow.box) :
    4*(raw.toProducerRow.candidate t-oldCap t)/(t 0*t 1*t 2*t 3)*
        (∑ k, segmentWeight (R0 raw:ℝ) (R1 raw:ℝ) (rowIndex raw hr) k) ≤
      4*(upper ((oldCap t-total t)/t 3)-upper ((raw.toProducerRow.candidate t-total t)/t 3))/
        (t 0*t 1*t 2*(t 3)^2) := by
  have hg := all_original_rows_geometry raw hr
  have ho := raw.toProducerRow.ordered hg t ht
  have harg := raw.toProducerRow.residual_range hg t ht
  obtain ⟨hr0,hr01,hr5⟩ := R_range raw hr
  have hw := ho.2.1
  have hz := hw.trans_le ho.2.2
  have hy := hz.trans_le ho.1.2.1
  have hx := hy.trans_le ho.1.2.2.1
  have hlow : (0:ℝ) < (raw.toProducerRow.lower 3:ℝ) := by
    exact_mod_cast (show 0 < raw.toProducerRow.lower 3 by linarith)
  have hi (k : Fin 4) :
      blend (R0 raw:ℝ) (R1 raw:ℝ) (k.val+1)/t 3 ≤ node ((rowIndex raw hr k).val) := by
    have hb := (blend_bounds (show (R0 raw:ℝ) ≤ (R1 raw:ℝ) by exact_mod_cast hr01)
      (show k.val+1 ≤ 4 by omega)).1
    refine (div_le_div_of_nonneg_left ((show (0:ℝ) < (R0 raw:ℝ) by exact_mod_cast hr0).le.trans hb)
      hlow (ht.1 3)).trans ?_
    simpa only [argument,Rat.cast_div,qBlend_cast,rowIndex] using ceilIndex_upper (argument raw k)
  have h := fourth_density hx hy hz hw ((one_lt_div hw).mp harg.1)
    ((div_lt_div_iff_of_pos_right hw).mp harg.2.1).le (residual_le_R0 raw t ht)
    (residual_le_R1 raw t ht) (rowIndex raw hr) hi
  rwa [show raw.toProducerRow.candidate t-total t-(oldCap t-total t) =
    raw.toProducerRow.candidate t-oldCap t by ring] at h

end
end ImbalancedChen.P1OriginalFourthRowSubintervals
