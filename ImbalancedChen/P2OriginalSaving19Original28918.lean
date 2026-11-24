import ImbalancedChen.P2OriginalSaving19Archive
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
SOURCE ONLY / UNCOMPILED / ALL CLOSED GUARDS UNEVALUATED / CREDIT 0.
Actual original13-cell/28918 primitive family. No assumptions assert
geometry, a saved-field equality, guard success, or an integral estimate.
The finite proof terms are closed over the original text literals.
-/

namespace ImbalancedChen.P2OriginalSaving19Original28918

set_option maxRecDepth 1000000

open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalLogMomentQ96CheckerSourceOnly
open P2OriginalSaving19Archive

abbrev QPoint := Fin 8 → ℚ
abbrev rawVertex := P2OriginalSaving19Archive.rawVertex

def comparisonQ (t : QPoint) : ℚ := (1 + t 0 + t 3) / 2
def newQ (t : QPoint) : ℚ := (1 + t 1 + t 3 + t 7) / 2 - 1 / 1000000
def thirdQ (t : QPoint) : ℚ := (1 + t 1 + t 2) / 2
def totalQ (t : QPoint) : ℚ := ∑ i, t i
def gapQ (t : QPoint) : ℚ := newQ t - comparisonQ t
def factorsQ (t : QPoint) : Fin 10 → ℚ :=
  ![comparisonQ t - totalQ t, newQ t - totalQ t,
    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]
def realPoint (t : QPoint) : Point := fun j => (t j : ℝ)

def PhysicalQ (t : QPoint) : Prop :=
  (∀ i j : Fin 8, i ≤ j → t j ≤ t i) ∧
  53 / 13824 ≤ t 7 ∧ 1 / 100 ≤ t 2 ∧ t 0 ≤ 25 / 128 ∧
  t 1 + t 2 ≤ 25 / 128 ∧ t 0 + t 3 ≤ 25 / 128 ∧
  t 1 + t 3 + t 7 ≤ 25 / 128 ∧
  3 * t 0 ≤ thirdQ t ∧ t 0 + t 1 + 3 * t 2 ≤ thirdQ t ∧
  t 0 + t 1 + t 2 + t 3 + 3 * t 4 ≤ thirdQ t ∧
  t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + 3 * t 6 ≤ thirdQ t ∧
  thirdQ t ≤ comparisonQ t ∧ comparisonQ t ≤ newQ t ∧
  newQ t - totalQ t ≤ 3 * t 7

instance (t : QPoint) : Decidable (PhysicalQ t) := by unfold PhysicalQ; infer_instance

theorem comparison_cast (t : QPoint) :
    (comparisonQ t : ℝ) = comparisonCap (realPoint t) := by
  norm_num [comparisonQ, comparisonCap, VariableEnvelope.A, realPoint]
  <;> ring

theorem new_cast (t : QPoint) : (newQ t : ℝ) = newCap (realPoint t) := by
  norm_num [newQ, newCap, selectedSum, VariableEnvelope.A, eta, realPoint]
  <;> ring

theorem third_cast (t : QPoint) : (thirdQ t : ℝ) = thirdMinorant (realPoint t) := by
  norm_num [thirdQ, thirdMinorant, VariableEnvelope.A, realPoint]
  <;> ring

theorem total_cast (t : QPoint) : (totalQ t : ℝ) = total (realPoint t) := by
  simp [totalQ, total, realPoint]

theorem gap_cast (t : QPoint) : (gapQ t : ℝ) = gap (realPoint t) := by
  simp only [gapQ, Rat.cast_sub, comparison_cast, new_cast, gap]

theorem factors_cast (t : QPoint) (j : Fin 10) :
    (factorsQ t j : ℝ) = factors (realPoint t) j := by
  fin_cases j <;>
    simp [factorsQ, factors, realPoint, Rat.cast_sub, comparison_cast, new_cast, total_cast]

theorem physical_cast {t : QPoint} (h : PhysicalQ t) : PhysicalRows (realPoint t) := by
  rcases h with ⟨ho, h8, h3, hm, ha3, haR, haM, h1, hh3, hh5, hh7, hBR, hRM, hres⟩
  constructor
  · intro i j hij
    exact_mod_cast ho i j hij
  · exact_mod_cast h8
  · exact_mod_cast h3
  · change (t 0 : ℝ) ≤ 25 / 128
    exact_mod_cast hm
  · change (t 1 : ℝ) + (t 2 : ℝ) ≤ 25 / 128
    exact_mod_cast ha3
  · change (t 0 : ℝ) + (t 3 : ℝ) ≤ 25 / 128
    exact_mod_cast haR
  · change (t 1 : ℝ) + (t 3 : ℝ) + (t 7 : ℝ) ≤ 25 / 128
    exact_mod_cast haM
  · rw [← third_cast]
    exact_mod_cast h1
  · rw [← third_cast]
    dsimp only [history3, realPoint]
    exact_mod_cast hh3
  · rw [← third_cast]
    dsimp only [history5, realPoint]
    exact_mod_cast hh5
  · rw [← third_cast]
    dsimp only [history7, realPoint]
    exact_mod_cast hh7
  · rw [← third_cast, ← comparison_cast]
    exact_mod_cast hBR
  · rw [← comparison_cast, ← new_cast]
    exact_mod_cast hRM
  · rw [← new_cast, ← total_cast]
    exact_mod_cast hres

def edgeQ (r : OriginalRowIndex) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => rawVertex r j.succ i - rawVertex r 0 i

def gapSumQ (r : OriginalRowIndex) : ℚ := ∑ i : Fin 9, gapQ (rawVertex r i)
def volumeQ (r : OriginalRowIndex) : ℚ := (rawGeometryRow r).physicalVolume
def massQ (r : OriginalRowIndex) : ℚ := volumeQ r * (rawGeometryRow r).meanGap
def meansQ (r : OriginalRowIndex) (j : Fin 10) : ℚ :=
  (rawGeometryRow r).gapWeightedMeans[j.val]!
def topsQ (r : OriginalRowIndex) (j : Fin 10) : ℚ :=
  (rawGeometryRow r).factorMaxima[j.val]!

def computedMeanQ (r : OriginalRowIndex) (j : Fin 10) : ℚ :=
  ((∑ i : Fin 9, factorsQ (rawVertex r i) j) +
    (∑ i : Fin 9, gapQ (rawVertex r i) * factorsQ (rawVertex r i) j) / gapSumQ r) / 10

/-- All finite checks refer to literal original coordinates, never a
synthetic rational simplex. Maxima use attainment plus domination. -/
structure RowDataGuard (r : OriginalRowIndex) : Prop where
  det_ne_zero : (edgeQ r).det ≠ 0
  physical : ∀ i, PhysicalQ (rawVertex r i)
  gap_pos : 0 < gapSumQ r
  volume_eq : volumeQ r = |(edgeQ r).det| / (8.factorial : ℚ)
  mean_gap_eq : (rawGeometryRow r).meanGap = gapSumQ r / 9
  means_eq : ∀ j, meansQ r j = computedMeanQ r j
  tops_dominate : ∀ i j, factorsQ (rawVertex r i) j ≤ topsQ r j
  tops_attained : ∀ j, ∃ i : Fin 9, factorsQ (rawVertex r i) j = topsQ r j
  jensen_eq : (rawGeometryRow r).jensenBound = oldEvaluator (massQ r) (meansQ r)
  geometry_floor_eq : (rawGeometryRow r).jensenFloorQ96 = oldFloorQ96 (massQ r) (meansQ r)

def RowDataChecks (r : OriginalRowIndex) : Prop :=
  (edgeQ r).det ≠ 0 ∧
  (∀ i, PhysicalQ (rawVertex r i)) ∧
  0 < gapSumQ r ∧
  volumeQ r = |(edgeQ r).det| / (8.factorial : ℚ) ∧
  (rawGeometryRow r).meanGap = gapSumQ r / 9 ∧
  (∀ j, meansQ r j = computedMeanQ r j) ∧
  (∀ i j, factorsQ (rawVertex r i) j ≤ topsQ r j) ∧
  (∀ j, ∃ i : Fin 9, factorsQ (rawVertex r i) j = topsQ r j) ∧
  (rawGeometryRow r).jensenBound = oldEvaluator (massQ r) (meansQ r) ∧
  (rawGeometryRow r).jensenFloorQ96 = oldFloorQ96 (massQ r) (meansQ r)

instance (r : OriginalRowIndex) : Decidable (RowDataChecks r) := by
  unfold RowDataChecks
  infer_instance

/-- This is a closed pure proofterm request, NOT a hypothesis and NOT an
executed successful certificate. Resource feasibility is also untested. -/
theorem original_data_checks : ∀ r, RowDataChecks r := by decide

theorem original_data_guard (r : OriginalRowIndex) : RowDataGuard r := by
  rcases original_data_checks r with ⟨hd, hp, hg, hv, hmg, hm, ht, ha, hj, hf⟩
  exact ⟨hd, hp, hg, hv, hmg, hm, ht, ha, hj, hf⟩

def VertexValueGuard (c : Fin 13) : Prop :=
  ∀ v : Fin (geometry c).vertices.size,
    let t : QPoint := fun j => ((geometry c).vertices[v.val]!)[j.val]!
    let saved := (geometry c).vertexValues[v.val]!
    saved.gap = gapQ t ∧ ∀ j : Fin 10, saved.factors[j.val]! = factorsQ t j

instance (c : Fin 13) : Decidable (VertexValueGuard c) := by
  unfold VertexValueGuard
  infer_instance

theorem original_saved_vertex_values : ∀ c, VertexValueGuard c := by decide

noncomputable section

def edgeR (r : OriginalRowIndex) : Matrix (Fin 8) (Fin 8) ℝ :=
  (edgeQ r).map (algebraMap ℚ ℝ)

def edgeMap (r : OriginalRowIndex) : Point →L[ℝ] Point :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (edgeR r))

theorem edgeMap_det (r : OriginalRowIndex) :
    (edgeMap r).det = ((edgeQ r).det : ℝ) := by
  change LinearMap.det (Matrix.toLin' (edgeR r)) = _
  rw [LinearMap.det_toLin']
  exact ((algebraMap ℚ ℝ).map_det (edgeQ r)).symm

theorem edgeMap_det_ne_zero (r : OriginalRowIndex) : (edgeMap r).det ≠ 0 := by
  rw [edgeMap_det]
  exact_mod_cast (original_data_guard r).det_ne_zero

def rowLinear (r : OriginalRowIndex) : Point ≃L[ℝ] Point :=
  (edgeMap r).toContinuousLinearEquivOfDetNeZero (edgeMap_det_ne_zero r)

def rowBase (r : OriginalRowIndex) : Point := realPoint (rawVertex r 0)

theorem row_vertices (r : OriginalRowIndex) (i : Fin 9) :
    vertices (rowLinear r) (rowBase r) i = realPoint (rawVertex r i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · ext k
    simp [vertices, rowBase, rowLinear, edgeMap, Matrix.toLin'_apply,
      Matrix.mulVec_single_one, edgeR, edgeQ, realPoint]

theorem row_physicalVertices (r : OriginalRowIndex) :
    ∀ i, PhysicalRows (vertices (rowLinear r) (rowBase r) i) := by
  intro i
  rw [row_vertices]
  exact physical_cast ((original_data_guard r).physical i)

theorem row_gapsEncoding (r : OriginalRowIndex) (i : Fin 9) :
    (gapQ (rawVertex r i) : ℝ) = gap (vertices (rowLinear r) (rowBase r) i) := by
  rw [row_vertices]
  exact gap_cast _

theorem row_factorsEncoding (r : OriginalRowIndex) (i : Fin 9) (j : Fin 10) :
    (factorsQ (rawVertex r i) j : ℝ) = factors (vertices (rowLinear r) (rowBase r) i) j := by
  rw [row_vertices]
  exact factors_cast _ _

theorem row_gapSumEncoding (r : OriginalRowIndex) :
    (gapSumQ r : ℝ) = gapTotal (vertices (rowLinear r) (rowBase r)) := by
  simp only [gapSumQ, Rat.cast_sum, gapTotal, row_gapsEncoding]

theorem row_positiveGapTotal (r : OriginalRowIndex) :
    0 < gapTotal (vertices (rowLinear r) (rowBase r)) := by
  rw [← row_gapSumEncoding]
  exact_mod_cast (original_data_guard r).gap_pos

theorem row_volumeEncoding (r : OriginalRowIndex) :
    (volumeQ r : ℝ) = physicalVolume (rowLinear r) := by
  rw [(original_data_guard r).volume_eq]
  simp only [physicalVolume, jacobian, rowLinear,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, edgeMap_det]
  push_cast
  rfl

theorem row_massEncoding (r : OriginalRowIndex) :
    (massQ r : ℝ) = physicalVolume (rowLinear r) *
      gapTotal (vertices (rowLinear r) (rowBase r)) / 9 := by
  simp only [massQ, (original_data_guard r).mean_gap_eq, Rat.cast_mul,
    Rat.cast_div, Rat.cast_natCast, row_volumeEncoding, row_gapSumEncoding]
  ring

theorem row_meansEncoding (r : OriginalRowIndex) (j : Fin 10) :
    (meansQ r j : ℝ) = factorMean (vertices (rowLinear r) (rowBase r)) j := by
  rw [(original_data_guard r).means_eq]
  simp only [computedMeanQ, factorMean, Rat.cast_div, Rat.cast_add,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, row_gapsEncoding,
    row_factorsEncoding, row_gapSumEncoding]

theorem row_topsEncoding (r : OriginalRowIndex) (j : Fin 10) :
    (topsQ r j : ℝ) = vertexTop (vertices (rowLinear r) (rowBase r)) j := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := (original_data_guard r).tops_attained j
    rw [← hi, row_factorsEncoding]
    exact factor_le_vertexTop _ i j
  · apply Finset.sup'_le
    intro i _
    rw [← row_factorsEncoding]
    exact_mod_cast (original_data_guard r).tops_dominate i j

/-- Stable primitive interface for actual-cell ownership. -/
structure PrimitiveRow where
  linear : Point ≃L[ℝ] Point
  base : Point
  physicalVertices : ∀ i, PhysicalRows (vertices linear base i)
  positiveGapTotal : 0 < gapTotal (vertices linear base)

def primitiveRow (r : OriginalRowIndex) : PrimitiveRow where
  linear := rowLinear r
  base := rowBase r
  physicalVertices := row_physicalVertices r
  positiveGapTotal := row_positiveGapTotal r

end

end ImbalancedChen.P2OriginalSaving19Original28918
