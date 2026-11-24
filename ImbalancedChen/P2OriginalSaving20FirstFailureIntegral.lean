import ImbalancedChen.P2OriginalPhysicalSimplexMomentRow
import ImbalancedChen.P2OriginalFull87PullingCell
import ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Actual stage20: all12 H3,7 H5,10 H7 original first-failure cells,
their78777 physical simplices and unchanged degree6/Q80/exp3/Q96 floors.
No old saving19 PhysicalRows or integral/floor/ownership hypothesis.
Loaders emit only the original58 String literals at root compilation.
All closed finite proof bodies remain UNEVALUATED.
-/
namespace ImbalancedChen.P2OriginalSaving20FirstFailureIntegral
open Lean Elab Term

private def loaderLabel (c : ℕ) : String :=
  let first := if c < 12 then "h3-" else if c < 19 then "h5-" else "h7-"
  let n := if c < 12 then c else if c < 19 then c - 12 else c - 19
  first ++ (if n < 10 then "0" else "") ++ toString n

elab "originalSaving20GeometryText% " n:num : term => do
  let c := n.getNat
  unless c < 29 do throwError "saving20 selects the original29 first-failure cells"
  let path := "../goldbach-research/eighth-history-first-failure-20261009-" ++
    loaderLabel c ++ "-cell.witness.json"
  let raw ← liftIO <| IO.FS.readFile path
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

elab "originalSaving20MomentText% " n:num : term => do
  let c := n.getNat
  unless c < 29 do throwError "saving20 selects the original29 first-failure cells"
  let path := "../goldbach-research/eighth-history-moment-refinement-20261009-" ++
    loaderLabel c ++ ".witness.json"
  let raw ← liftIO <| IO.FS.readFile path
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Set MeasureTheory
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim (sourceSet)
open P4AOriginalFull87EighthKernelControl (kernel)
open P2OriginalSaving19Archive
  (SourceJson Geometry Moments decodeGeometry decodeMoments GeometryRow MomentRecord)
open P2OriginalSaving16OriginalArchive (QPoint castPoint edgeMatrix physicalVolumeQ)
namespace Moment
export P2OriginalPhysicalSimplexMomentRow
  (Row rowMap rowBase rowSupport rowGap rowFactors rowDensity rowMassQ rowMeansQ rowTopsQ rowMomentsQ
   rowFloorQ checkStoredRowFloor stored_row_floor_sound row_pointInterpolate_coordinates)
end Moment
namespace Pull
export P2OriginalFull87PullingCell (Data Checks rowVertices row_det rowSupport sum_support_integrals_le)
end Pull

def sourceCell (c : Fin 29) : Cell :=
  if h : c.val < 12 then .h3 ⟨c.val,h⟩
  else if h' : c.val < 19 then .remaining (.h5 ⟨c.val - 12,by omega⟩)
  else .remaining (.h7 ⟨c.val - 19,by omega⟩)

def geometryText : Fin 29 → String :=
  ![originalSaving20GeometryText% 0, originalSaving20GeometryText% 1, originalSaving20GeometryText% 2,
    originalSaving20GeometryText% 3, originalSaving20GeometryText% 4, originalSaving20GeometryText% 5,
    originalSaving20GeometryText% 6, originalSaving20GeometryText% 7, originalSaving20GeometryText% 8,
    originalSaving20GeometryText% 9, originalSaving20GeometryText% 10, originalSaving20GeometryText% 11,
    originalSaving20GeometryText% 12, originalSaving20GeometryText% 13, originalSaving20GeometryText% 14,
    originalSaving20GeometryText% 15, originalSaving20GeometryText% 16, originalSaving20GeometryText% 17,
    originalSaving20GeometryText% 18, originalSaving20GeometryText% 19, originalSaving20GeometryText% 20,
    originalSaving20GeometryText% 21, originalSaving20GeometryText% 22, originalSaving20GeometryText% 23,
    originalSaving20GeometryText% 24, originalSaving20GeometryText% 25, originalSaving20GeometryText% 26,
    originalSaving20GeometryText% 27, originalSaving20GeometryText% 28]
def momentText : Fin 29 → String :=
  ![originalSaving20MomentText% 0, originalSaving20MomentText% 1, originalSaving20MomentText% 2,
    originalSaving20MomentText% 3, originalSaving20MomentText% 4, originalSaving20MomentText% 5,
    originalSaving20MomentText% 6, originalSaving20MomentText% 7, originalSaving20MomentText% 8,
    originalSaving20MomentText% 9, originalSaving20MomentText% 10, originalSaving20MomentText% 11,
    originalSaving20MomentText% 12, originalSaving20MomentText% 13, originalSaving20MomentText% 14,
    originalSaving20MomentText% 15, originalSaving20MomentText% 16, originalSaving20MomentText% 17,
    originalSaving20MomentText% 18, originalSaving20MomentText% 19, originalSaving20MomentText% 20,
    originalSaving20MomentText% 21, originalSaving20MomentText% 22, originalSaving20MomentText% 23,
    originalSaving20MomentText% 24, originalSaving20MomentText% 25, originalSaving20MomentText% 26,
    originalSaving20MomentText% 27, originalSaving20MomentText% 28]

def parsedGeometry (c : Fin 29) : Except String Geometry :=
  SourceJson.parse (geometryText c) >>= decodeGeometry
def parsedMoments (c : Fin 29) : Except String Moments :=
  SourceJson.parse (momentText c) >>= decodeMoments
def geometry (c : Fin 29) : Geometry := (parsedGeometry c).toOption.getD default
def moments (c : Fin 29) : Moments := (parsedMoments c).toOption.getD default
def geometrySuccess (c : Fin 29) : Bool := match parsedGeometry c with | .ok _ => true | .error _ => false
def momentSuccess (c : Fin 29) : Bool := match parsedMoments c with | .ok _ => true | .error _ => false
theorem original_parse_success_tags : ∀ c : Fin 29, geometrySuccess c = true ∧ momentSuccess c = true := by decide
theorem original_geometry_parse (c : Fin 29) : parsedGeometry c = .ok (geometry c) := by
  cases h : parsedGeometry c with
  | error msg => have hs := (original_parse_success_tags c).1; simp [geometrySuccess,h] at hs
  | ok g => simp [geometry,h]
theorem original_moment_parse (c : Fin 29) : parsedMoments c = .ok (moments c) := by
  cases h : parsedMoments c with
  | error msg => have hs := (original_parse_success_tags c).2; simp [momentSuccess,h] at hs
  | ok g => simp [moments,h]

def pullingData (c : Fin 29) : Pull.Data where
  vertices := (geometry c).vertices
  facets := (geometry c).facetVertices
  faces := (geometry c).faces
  rows := (geometry c).rows.map (fun r => r.vertexIds)

def HeaderChecks (c : Fin 29) : Prop :=
  let g := geometry c
  let m := moments c
  g.dimension = 8 ∧ g.physicalJacobian = 1 ∧ m.rows.size = (pullingData c).rows.size ∧
  m.cellId = (if c.val < 12 then c.val else if c.val < 19 then c.val - 12 else c.val - 19) ∧
  m.sourceWitness = "eighth-history-first-failure-20261009-" ++ loaderLabel c.val ++ "-cell.witness.json" ∧
  m.dimension = 8 ∧ m.verticesPerSimplex = 9 ∧ m.factorCount = 10 ∧ m.logDegree = 6 ∧
  m.expDegree = 3 ∧ m.logDenominator = 2^80 ∧ m.finalDenominator = 2^96
instance (c : Fin 29) : Decidable (HeaderChecks c) := by unfold HeaderChecks; infer_instance
theorem original_headers : ∀ c : Fin 29, HeaderChecks c := by decide
theorem original_geometry_checks : ∀ c : Fin 29, Pull.Checks (sourceCell c) (pullingData c) := by decide

def comparisonQ (t : QPoint) : ℚ := (1 + (t 0 + t 3)) / 2
def capQ (t : QPoint) : ℚ := (1 + (t 1 + t 3 + t 7)) / 2 - 1 / 1000000
def gapQ (t : QPoint) : ℚ := capQ t - comparisonQ t
def factorsQ (t : QPoint) : Fin 10 → ℚ :=
  ![comparisonQ t - ∑ i, t i, capQ t - ∑ i, t i,
    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]
def PrimitiveChecks (c : Fin 29) (s : Fin (pullingData c).rows.size) : Prop :=
  (∀ i, 0 ≤ gapQ (Pull.rowVertices (pullingData c) s i)) ∧
  0 < ∑ i, gapQ (Pull.rowVertices (pullingData c) s i) ∧
  ∀ i j, P2OriginalPhysicalSimplexMomentRow.cutoffQ ≤ factorsQ (Pull.rowVertices (pullingData c) s i) j
instance (c : Fin 29) (s : Fin (pullingData c).rows.size) : Decidable (PrimitiveChecks c s) := by
  unfold PrimitiveChecks
  infer_instance
theorem original_primitive_checks : ∀ (c : Fin 29) (s : Fin (pullingData c).rows.size),
    PrimitiveChecks c s := by decide

def actualRow (c : Fin 29) (s : Fin (pullingData c).rows.size) : Moment.Row where
  verticesQ := Pull.rowVertices (pullingData c) s
  gapsQ := fun i => gapQ (Pull.rowVertices (pullingData c) s i)
  factorsQ := fun i j => factorsQ (Pull.rowVertices (pullingData c) s i) j
  determinant_ne_zero := Pull.row_det (original_geometry_checks c) s
  gap_nonneg := (original_primitive_checks c s).1
  gapTotal_pos := (original_primitive_checks c s).2.1
  factor_floor := (original_primitive_checks c s).2.2

def rawGeometryRow (c : Fin 29) (s : Fin (pullingData c).rows.size) : GeometryRow :=
  (geometry c).rows.getD s.val default
def rawMomentRow (c : Fin 29) (s : Fin (pullingData c).rows.size) : MomentRecord :=
  (moments c).rows.getD s.val default

/-- Original saved intermediary fields are matched to independently
defined rational operations on the actual ordered physical vertices.
There is no archive PASS/integral bound in this finite certificate. -/
def RowChecks (c : Fin 29) (s : Fin (pullingData c).rows.size) : Prop :=
  let r := actualRow c s
  let g := rawGeometryRow c s
  let m := rawMomentRow c s
  g.simplexId = s.val ∧ m.simplexId = s.val ∧
  g.physicalVolume = physicalVolumeQ r.verticesQ ∧ g.meanGap = (∑ i, r.gapsQ i) / 9 ∧
  g.gapWeightedMeans.size = 10 ∧ g.factorMaxima.size = 10 ∧ m.factorFloorsQ80.size = 10 ∧
  (∀ j : Fin 10, g.gapWeightedMeans.getD j.val 0 = Moment.rowMeansQ r j ∧
    g.factorMaxima.getD j.val 0 = Moment.rowTopsQ r j ∧
    m.factorFloorsQ80.getD j.val 0 =
      P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 (Moment.rowMomentsQ r j)) ∧
  m.oldFloorQ96 = P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (Moment.rowMassQ r) (Moment.rowMeansQ r) ∧
  Moment.checkStoredRowFloor r m.newFloorQ96 = true
instance (c : Fin 29) (s : Fin (pullingData c).rows.size) : Decidable (RowChecks c s) := by
  unfold RowChecks
  infer_instance
theorem original_row_checks : ∀ (c : Fin 29) (s : Fin (pullingData c).rows.size), RowChecks c s := by decide

theorem original_stored_floor_checks (c : Fin 29) (s : Fin (pullingData c).rows.size) :
    Moment.checkStoredRowFloor (actualRow c s) (rawMomentRow c s).newFloorQ96 = true :=
  (original_row_checks c s).2.2.2.2.2.2.2.2.2

open P2OriginalThirdMinorantLogDictionarySourceOnly

theorem gapQ_cast (t : QPoint) : (gapQ t : ℝ) = gap (castPoint t) := by
  norm_num [gapQ,capQ,comparisonQ,gap,newCap,comparisonCap,selectedSum,eta,
    VariableEnvelope.A,castPoint] <;> ring
theorem factorsQ_cast (t : QPoint) (j : Fin 10) : (factorsQ t j : ℝ) = factors (castPoint t) j := by
  fin_cases j <;> norm_num [factorsQ,capQ,comparisonQ,factors,newCap,comparisonCap,
    selectedSum,eta,total,VariableEnvelope.A,castPoint] <;> ring

theorem source_kernel_dictionary (c : Fin 29) (t : Point) :
    kernel (sourceCell c) t = conservativeDensity t := by
  fin_cases c <;>
    norm_num [sourceCell,kernel,P4AOriginalFull87EighthKernelControl.residual,
      P4AOriginalFull87SourceDictionary.comparison,P4AOriginalFull87SourceDictionary.newCap,
      P4AOriginalRemainingEighthSources.comparison,P4AOriginalRemainingEighthSources.newCap,
      P4AOriginalRemainingEighthSources.descendingNew,P4AOriginalRemainingEighthSources.selectedSum,
      P4AOriginalRemainingEighthSources.selected,P4AOriginalRemainingEighthSources.eta,
      P4AOriginalFirstFailureH3Literal.R6,P4AOriginalFirstFailureH3Literal.M8,
      P4AOriginalFirstFailureH3Literal.A,P4AOriginalFirstFailureH3Literal.eta,
      P4AOriginalFull87EighthKernelControl.total,P4AOriginalFull87EighthKernelControl.product,
      conservativeDensity,gap,newCap,comparisonCap,selectedSum,eta,total,VariableEnvelope.A]
    <;> ring

theorem actual_row_density (c : Fin 29) (s : Fin (pullingData c).rows.size) (t : Point) :
    Moment.rowDensity (actualRow c s) t = kernel (sourceCell c) t := by
  have hg : Moment.rowGap (actualRow c s) t = gap t := by
    unfold Moment.rowGap
    simp_rw [show ∀ i, ((actualRow c s).gapsQ i : ℝ) = gap (castPoint ((actualRow c s).verticesQ i))
      from fun i => gapQ_cast _]
    rw [← P2OriginalSaving19SimplexMoments.gap_interpolate,
      Moment.row_pointInterpolate_coordinates]
  have hf (j : Fin 10) : Moment.rowFactors (actualRow c s) t j = factors t j := by
    unfold Moment.rowFactors
    simp_rw [show ∀ i, ((actualRow c s).factorsQ i j : ℝ) =
      factors (castPoint ((actualRow c s).verticesQ i)) j from fun i => factorsQ_cast _ j]
    rw [← P2OriginalSaving19SimplexMoments.factors_interpolate,
      Moment.row_pointInterpolate_coordinates]
  rw [Moment.rowDensity,hg]
  simp_rw [hf]
  rw [← density_factor_dictionary,source_kernel_dictionary]

theorem actual_row_support (c : Fin 29) (s : Fin (pullingData c).rows.size) :
    Moment.rowSupport (actualRow c s) =
      Pull.rowSupport (pullingData c) s (Pull.row_det (original_geometry_checks c) s) := rfl

theorem original_row_floor_le_kernel_integral (c : Fin 29) (s : Fin (pullingData c).rows.size) :
    ((rawMomentRow c s).newFloorQ96 : ℝ) / (2 : ℝ)^96 ≤
      ∫ t in Pull.rowSupport (pullingData c) s (Pull.row_det (original_geometry_checks c) s),
        kernel (sourceCell c) t := by
  have h := Moment.stored_row_floor_sound (actualRow c s) (rawMomentRow c s).newFloorQ96
    (original_stored_floor_checks c s)
  simp_rw [actual_row_density] at h
  rw [actual_row_support] at h
  exact h

def cellNumerator (c : Fin 29) : ℤ := ∑ s : Fin (pullingData c).rows.size, (rawMomentRow c s).newFloorQ96
theorem original_selected_records : ∀ c : Fin 29,
    (P4AOriginalFull87ArchiveSourceIndex.archivedRecordForOriginalCell (sourceCell c)).2 =
      (cellNumerator c : ℚ) / (2 : ℚ)^96 := by decide
theorem original_aggregate : (∑ c : Fin 29, cellNumerator c) = 29501230015891355325630 := by decide
theorem original_row_count : (∑ c : Fin 29, (pullingData c).rows.size) = 78777 := by decide

theorem original_cell_floor_le_source_integral (c : Fin 29) :
    (cellNumerator c : ℝ) / (2 : ℝ)^96 ≤ ∫ t in sourceSet (sourceCell c), kernel (sourceCell c) t := by
  have he : (cellNumerator c : ℝ) / (2 : ℝ)^96 =
      ∑ s : Fin (pullingData c).rows.size, ((rawMomentRow c s).newFloorQ96 : ℝ) / (2 : ℝ)^96 := by
    simp [cellNumerator,Finset.sum_div]
  rw [he]
  exact (Finset.sum_le_sum (fun s _ => original_row_floor_le_kernel_integral c s)).trans
    (Pull.sum_support_integrals_le (sourceCell c) (pullingData c) (original_geometry_checks c))

/-- Each original archived Cell record, not only the global total, is
attached to its own original full87 kernel integral for the86-cell join. -/
theorem original_archived_cell_le_source_integral (c : Fin 29) :
    ((P4AOriginalFull87ArchiveSourceIndex.archivedRecordForOriginalCell (sourceCell c)).2 : ℝ) ≤
      ∫ t in sourceSet (sourceCell c), kernel (sourceCell c) t := by
  rw [original_selected_records]
  exact_mod_cast original_cell_floor_le_source_integral c

/-- Actual original stage20 full saved endpoint, on its29 true full87
Source integrals. No missing moment, floor or ownership premise. -/
theorem original_stage20_floor_le_sum_full87_integrals :
    (14750615007945677662815 : ℝ) / (2 : ℝ)^95 ≤
      ∑ c : Fin 29, ∫ t in sourceSet (sourceCell c), kernel (sourceCell c) t := by
  have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin 29))) =>
    original_cell_floor_le_source_integral c)
  rw [← Finset.sum_div, ← Int.cast_sum, original_aggregate] at h
  convert h using 1 <;> norm_num

end
end ImbalancedChen.P2OriginalSaving20FirstFailureIntegral
