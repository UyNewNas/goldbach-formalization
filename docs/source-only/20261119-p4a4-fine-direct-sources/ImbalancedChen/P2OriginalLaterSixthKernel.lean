import ImbalancedChen.P4AOriginalNonsingletonComparison
import ImbalancedChen.P2OriginalSixthMomentRow

/-! The original nineteen later sixth actions and the two comparison
corrections have twenty-one distinct integral pieces. Both correction
pieces end at D33 while the already-adopted A34/D34 action remains in
force on their source. G14 starts each of its four kernels at R17. -/
namespace ImbalancedChen.P2OriginalLaterSixthKernel
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSixthSimplexBinding (QPoint castPoint edgeMatrix)
open P2OriginalSixthMomentRow (Row rowSupport rowDensity rowCoordinates rowGap rowFactors
  row_pointInterpolate_coordinates rowFloorQ row_floor_sound rowMassQ rowMeansQ cutoffQ)
open P2OriginalSixthSimplexMoments (Point pointInterpolate interpolate pointInterpolate_apply
  interpolate_add interpolate_const interpolate_sum)
open P2OriginalLogMomentQ96CheckerSourceOnly (oldFloorQ96)

abbrev Piece := Fin 21
abbrev Plane := Fin 7 → ℚ
def action : Piece → P4AOriginalSixthLaterLiteral.Cell :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,3,5]
def slot : Piece → Fin 7 := ![0,0,1,1,2,2,3,4,5,5,5,5,5,5,5,6,6,6,6,5,5]
def correction (i : Piece) : Bool := decide (19≤i.val)
def charted (i : Piece) := P4AOriginalSixthLaterLiteral.mapped (action i)

def constP (a : ℚ) : Plane := ![a,0,0,0,0,0,0]
def xP (j : Fin 6) : Plane := fun k => if k.val=j.val+1 then 1 else 0
def totalP : Plane := ![0,1,1,1,1,1,1]
def r0 : Plane := ![1/2,1/2,0,0,0,0,0]
def r17 : Plane := ![57/64,-3/2,0,0,0,-3/2,0]
def d33 : Plane := ![57/64,-3/2,0,0,0,0,-3/2]
def a33 : Plane := ![1/2,1/2,0,0,0,0,1/2]
def a34 : Plane := ![1/2,0,1/2,0,0,0,1/2]
def d34 : Plane := ![57/64,0,-3/2,0,0,0,-3/2]
def a50 : Plane := ![1/2,0,1/2,0,0,1/2,1/2]
def d50 : Plane := ![57/64,0,-3/2,0,0,-3/2,-3/2]

def lower : Piece → Plane :=
  ![r0,r0,r0,d33,r0,d33,r0,r0,r0,r0,r0,r0,r0,r0,a34,r17,r17,r17,r17,r0,r0]
def upper (i : Piece) : Plane :=
  if correction i then d33 else
    (![d33,d33,a34,a34,d34,d34,a34,d34,d33,d33,a50,a50,d50,d50,d33,a33,d33,a33,d33,d33,d33] i)
      - constP (1/1000000)
def gapPlane (i : Piece) := upper i-lower i
def factorPlane (i : Piece) : Fin 8 → Plane :=
  ![lower i-totalP,upper i-totalP,xP 0,xP 1,xP 2,xP 3,xP 4,xP 5]

def evalQ (a : Plane) (t : QPoint) : ℚ := a 0+∑ j,a j.succ*t j
def eval (a : Plane) (t : Point) : ℝ := (a 0:ℝ)+∑ j,(a j.succ:ℝ)*t j
def kernel (i : Piece) (t : Point) : ℝ := 4*eval (gapPlane i) t/∏ j,eval (factorPlane i j) t
def sourceIntegral (i : Piece) (D : Set Point) : ℝ := ∫ t in D,kernel i t

theorem eval_cast (a : Plane) (t : QPoint) : eval a (castPoint t)=(evalQ a t:ℝ) := by
  simp [eval,evalQ,castPoint]

theorem eval_interpolate (a : Plane) (v : Fin 7 → Point) (x : Point) :
    eval a (pointInterpolate v x) = interpolate (fun k => eval a (v k)) x := by
  simp only [eval,pointInterpolate_apply]
  rw [interpolate_add,interpolate_const,interpolate_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [interpolate,Finset.mul_sum,mul_assoc,mul_left_comm]

theorem eval_lower (i : Piece) (t : Point) : eval (lower i) t =
    if correction i then Certificates.P2OriginalSixthElevenLogSemantics.R0 t
    else P4AOriginalSixthLaterSemantics.comparison (action i) t := by
  fin_cases i <;>
    norm_num [lower,eval,action,correction,r0,r17,d33,a34,
      P4AOriginalSixthLaterSemantics.comparison,P4AOriginalSixthLaterLiteral.comparisonChart,
      P4AOriginalSixthLaterSemantics.R17,Certificates.P2OriginalSixthElevenLogSemantics.R0,
      Certificates.P2OriginalSixthElevenLogSemantics.descending33,
      Certificates.P2OriginalSixthElevenLogSemantics.ascending34,Fin.sum_univ_succ] <;> ring

theorem eval_upper (i : Piece) (t : Point) : eval (upper i) t =
    if correction i then Certificates.P2OriginalSixthElevenLogSemantics.descending33 t
    else P4AOriginalSixthLaterSemantics.endpoint (action i) t := by
  fin_cases i <;>
    norm_num [upper,eval,action,correction,constP,d33,a33,a34,d34,a50,d50,
      P4AOriginalSixthLaterSemantics.endpoint,P4AOriginalSixthLaterSemantics.selectedSum,
      P4AOriginalSixthLaterLiteral.descending,P4AOriginalSixthLaterLiteral.mask,
      Certificates.P2OriginalSixthElevenLogSemantics.descending33,
      Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit,Certificates.P2OriginalSixthElevenLogSemantics.eta,
      Fin.sum_univ_succ] <;> ring

structure PhysicalRow (i : Piece) where
  vertices : Fin 7 → QPoint
  nonsingular : (edgeMatrix vertices).det≠0
  gap_nonneg : ∀ j,0≤evalQ (gapPlane i) (vertices j)
  gap_positive : 0<∑ j,evalQ (gapPlane i) (vertices j)
  floor : ∀ j k,cutoffQ≤evalQ (factorPlane i k) (vertices j)

def PhysicalRow.toRow {i : Piece} (r : PhysicalRow i) : Row where
  verticesQ := r.vertices
  gapsQ := fun j => evalQ (gapPlane i) (r.vertices j)
  factorsQ := fun j k => evalQ (factorPlane i k) (r.vertices j)
  determinant_ne_zero := r.nonsingular
  gap_nonneg := r.gap_nonneg
  gapTotal_pos := r.gap_positive
  factor_floor := r.floor

theorem physical_eval {i : Piece} (r : PhysicalRow i) (a : Plane) (t : Point) :
    interpolate (fun j => (evalQ a (r.vertices j):ℝ)) (rowCoordinates r.toRow t) = eval a t := by
  have h := eval_interpolate a (fun j => castPoint (r.vertices j)) (rowCoordinates r.toRow t)
  rw [row_pointInterpolate_coordinates] at h
  simpa only [eval_cast] using h.symm

theorem row_density {i : Piece} (r : PhysicalRow i) (t : Point) :
    rowDensity r.toRow t=kernel i t := by
  have hg : rowGap r.toRow t=eval (gapPlane i) t := physical_eval r _ _
  have hf (k : Fin 8) : rowFactors r.toRow t k=eval (factorPlane i k) t := physical_eval r _ _
  simp only [rowDensity,kernel,hg,hf]

/-- These later sources use the original arithmetic Jensen floor. The
general simplex theorem bounds it by its physical six-dimensional integral. -/
theorem original_row_floor {i : Piece} (r : PhysicalRow i) (z : ℤ)
    (hz : z=oldFloorQ96 (rowMassQ r.toRow) (rowMeansQ r.toRow)) :
    (z:ℝ)/(2:ℝ)^96 ≤ sourceIntegral i (rowSupport r.toRow) := by
  have hq : (z:ℚ)/(2:ℚ)^96 ≤ rowFloorQ r.toRow := by
    rw [hz]
    unfold rowFloorQ
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (le_max_left (oldFloorQ96 (rowMassQ r.toRow) (rowMeansQ r.toRow))
      (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96 (rowMassQ r.toRow) (rowMeansQ r.toRow)
        (P2OriginalSixthMomentRow.rowMomentsQ r.toRow)))
  have hr : (z:ℝ)/(2:ℝ)^96 ≤ (rowFloorQ r.toRow:ℝ) := by exact_mod_cast hq
  exact hr.trans (by simpa only [sourceIntegral,row_density] using row_floor_sound r.toRow)

end
end ImbalancedChen.P2OriginalLaterSixthKernel
