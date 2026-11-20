import ImbalancedChen.P2OriginalSixthMomentRow
import ImbalancedChen.P2OriginalSixthElevenLogSemantics

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The row density below is the original physical G7 savingKernel, with
the source chart decoded before any determinant is taken. Affine factors
are reconstructed from the original seven physical vertices. No integral,
weighted-moment or numerical-floor premise is accepted by PhysicalRow.
-/
namespace ImbalancedChen.P2OriginalSixthPhysicalRow
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthSimplexBinding (QPoint castPoint edgeMatrix)
open P2OriginalSixthMomentRow
open P2OriginalSixthSimplexMoments (pointInterpolate interpolate
  pointInterpolate_apply interpolate_add interpolate_sub interpolate_div interpolate_const)
def physicalQ (q : QPoint) : QPoint :=
  ![q 0,q 1,q 2,(1-q 0)/2-q 1-q 2-3*q 3/2+q 4/2,(q 3-q 4)/2,q 5]
def decodeQ (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (q : QPoint) : QPoint :=
  if c.family = .pair12 then q else physicalQ q
def totalQ (t : QPoint) : ℚ := t 0+t 1+t 2+t 3+t 4+t 5
def oldCapQ (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : QPoint) : ℚ :=
  match c.family with
  | .singleton | .tent33 => (1+t 0)/2
  | .pair17 => 57/64-3*(t 0+t 4)/2
  | .pair12 => (1+t 2+t 3)/2
def newCapQ (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : QPoint) : ℚ :=
  if c.family = .tent33 then (1+t 0+t 5)/2-1/1000000
  else t 0+t 1+t 2+t 3+t 4+4*t 5-1/1000000
def gapQ (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : QPoint) : ℚ := newCapQ c t-oldCapQ c t
def factorsQ (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : QPoint) : Fin 8 → ℚ :=
  ![oldCapQ c t-totalQ t,newCapQ c t-totalQ t,t 0,t 1,t 2,t 3,t 4,t 5]

theorem decodeQ_cast (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (q : QPoint) :
    castPoint (decodeQ c q) = ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.decode c (castPoint q) := by
  cases c <;> ext j <;> fin_cases j <;>
    norm_num [decodeQ,physicalQ,castPoint,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.decode,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.physical,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family]

theorem gapQ_cast (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : QPoint) :
    (gapQ c t : ℝ) = ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.gap c (castPoint t) := by
  cases c <;>
    norm_num [gapQ,newCapQ,oldCapQ,castPoint,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.gap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S5,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.eta,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family]

theorem factorsQ_cast (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : QPoint) (j : Fin 8) :
    (factorsQ c t j : ℝ) = ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factors c (castPoint t) j := by
  cases c <;> fin_cases j <;>
    norm_num [factorsQ,newCapQ,oldCapQ,totalQ,castPoint,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factors,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldResidual,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newResidual,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S6,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S5,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.eta,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family]

theorem gap_interpolate (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (v : Fin 7 → Point) (x : Point) :
    ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.gap c (pointInterpolate v x) = interpolate (fun i => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.gap c (v i)) x := by
  cases c <;>
    simp only [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.gap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,ite_true,ite_false,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S5,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.eta,pointInterpolate_apply,
      interpolate_add,interpolate_sub,interpolate_div,interpolate_const]
  all_goals simp [interpolate,Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.sum_div] <;> ring

theorem factors_interpolate (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (v : Fin 7 → Point) (x : Point) (j : Fin 8) :
    ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factors c (pointInterpolate v x) j =
      interpolate (fun i => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factors c (v i) j) x := by
  cases c <;> fin_cases j <;>
    simp only [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factors,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldResidual,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newResidual,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,ite_true,ite_false,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S6,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S5,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.eta,Matrix.cons_val_zero,Matrix.cons_val_succ,pointInterpolate_apply,
      interpolate_add,interpolate_sub,interpolate_div,interpolate_const]
  all_goals simp [interpolate,Finset.mul_sum,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.sum_div] <;> ring

structure PhysicalRow (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) where
  verticesQ : Fin 7 → QPoint
  determinant_ne_zero : (edgeMatrix verticesQ).det ≠ 0
  gap_nonneg : ∀ i, 0 ≤ gapQ c (verticesQ i)
  gapTotal_pos : 0 < ∑ i, gapQ c (verticesQ i)
  factor_floor : ∀ i j, cutoffQ ≤ factorsQ c (verticesQ i) j

def PhysicalRow.toRow {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} (r : PhysicalRow c) : Row where
  verticesQ := r.verticesQ
  gapsQ := fun i => gapQ c (r.verticesQ i)
  factorsQ := fun i => factorsQ c (r.verticesQ i)
  determinant_ne_zero := r.determinant_ne_zero
  gap_nonneg := r.gap_nonneg
  gapTotal_pos := r.gapTotal_pos
  factor_floor := r.factor_floor

theorem rowGap_eq {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} (r : PhysicalRow c) (t : Point) :
    rowGap r.toRow t = ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.gap c t := by
  have h := gap_interpolate c (fun i => castPoint (r.verticesQ i)) (rowCoordinates r.toRow t)
  rw [row_pointInterpolate_coordinates] at h
  simpa only [rowGap,PhysicalRow.toRow,gapQ_cast] using h.symm

theorem rowFactors_eq {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} (r : PhysicalRow c) (t : Point) (j : Fin 8) :
    rowFactors r.toRow t j = ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factors c t j := by
  have h := factors_interpolate c (fun i => castPoint (r.verticesQ i))
    (rowCoordinates r.toRow t) j
  rw [row_pointInterpolate_coordinates] at h
  simpa only [rowFactors,PhysicalRow.toRow,factorsQ_cast] using h.symm

theorem rowDensity_eq {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} (r : PhysicalRow c) (t : Point) :
    rowDensity r.toRow t = ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel c t := by
  simp only [rowDensity,rowGap_eq,rowFactors_eq,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factorProduct]

theorem original_physical_row_floor {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} (r : PhysicalRow c) (stored : ℤ)
    (h : checkStoredRowFloor r.toRow stored = true) :
    (stored : ℝ)/(2:ℝ)^96 ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral c (rowSupport r.toRow) := by
  have hrow := stored_row_floor_sound r.toRow stored h
  simpa only [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral,rowDensity_eq] using hrow

end
end ImbalancedChen.P2OriginalSixthPhysicalRow
