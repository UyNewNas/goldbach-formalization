import ImbalancedChen.P2Winner9SelectedRowRealJacobian
import ImbalancedChen.P2Winner9Row21SourceBridge
import ImbalancedChen.P2Winner9Row22Arithmetic
import ImbalancedChen.P2Winner9MixedKOneFiniteCollapse

/-!
The original row21 and row22 physical vertex formulas agree with the exact
integer scales of their nine-vertex certificate inputs. Both rows retain the
literal saved means and separate signed transverse deviations.
-/

namespace ImbalancedChen.P2Winner9SelectedRowIntegerScales

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
open ImbalancedChen.P2Winner9MixedKOneFiniteCollapse

namespace Row21

abbrev data : SimplexData := P2Winner9Row21SourceBridge.row21
abbrev gapDen : Nat := P2Winner9Row21Arithmetic.gapCommonDen

/-- Actual stored gap-weighted means, in the source's ten-factor order. -/
def means (j : Fin 10) : ℚ := P2Winner9Row21RawVertexData.storedMeans[j.val]!

def upper : ℚ := (data.U : ℚ) / data.L

end Row21

export P2Winner9Row22Arithmetic
  (rawR rawM rawSum rawGap rawFactor rawP rawY rawDeviation VertexNormalization)

namespace Row22

export P2Winner9Row22Arithmetic (data gapDen means upper means_match_source)

end Row22

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- The actual row21 values supply all normalization fields; this is a
closed source proposition, not a new assumed normalization hypothesis. -/
theorem row21_vertex_normalization :
    VertexNormalization row21 Row21.means Row21.upper Row21.data Row21.gapDen := by
  unfold VertexNormalization
  decide +kernel

/-- The reconstructed row22 inputs carry the original vertex normalization. -/
theorem row22_vertex_normalization :
    VertexNormalization row22 Row22.means Row22.upper Row22.data Row22.gapDen :=
  P2Winner9Row22Arithmetic.row22_vertex_normalization

/-- Rational embedding of the actual physical formulas. -/
theorem rawR_cast (v : RationalVertices) (i : Fin 9) :
    (rawR v i : ℝ) = physicalR (realVertices v i) := by
  simp [rawR, physicalR, realVertices]

theorem rawM_cast (v : RationalVertices) (i : Fin 9) :
    (rawM v i : ℝ) = physicalM (realVertices v i) := by
  simp [rawM, physicalM, realVertices]

theorem rawSum_cast (v : RationalVertices) (i : Fin 9) :
    (rawSum v i : ℝ) = coordinateSum (realVertices v i) := by
  simp [rawSum, coordinateSum, realVertices]

theorem rawGap_cast (v : RationalVertices) (i : Fin 9) :
    (rawGap v i : ℝ) = physicalGap (realVertices v i) := by
  simp only [rawGap, Rat.cast_sub, rawM_cast, rawR_cast, physicalGap]

theorem rawFactor_cast (v : RationalVertices) (i : Fin 9) (j : Fin 10) :
    (rawFactor v i j : ℝ) = physicalFactor j (realVertices v i) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [rawFactor, Fin.cases_zero, Rat.cast_sub, rawR_cast,
      rawSum_cast, physicalFactor_zero]
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp only [rawFactor, Fin.cases_succ, Fin.cases_zero, Rat.cast_sub,
        rawM_cast, rawSum_cast]
      exact (physicalFactor_one (realVertices v i)).symm
    · simp only [rawFactor, Fin.cases_succ, physicalFactor_succ_succ,
        realVertices]

theorem rawP_cast (v : RationalVertices) (means : Fin 10 → ℚ) (i : Fin 9) :
    (rawP v means i : ℝ) =
      physicalP (fun j => (means j : ℝ)) (realVertices v i) := by
  simp [rawP, physicalP, normalizedFactor, rawFactor_cast]

theorem rawY_cast (v : RationalVertices) (means : Fin 10 → ℚ) (U : ℚ)
    (i : Fin 9) :
    (rawY v means U i : ℝ) =
      physicalY (fun j => (means j : ℝ)) (U : ℝ) (realVertices v i) := by
  simp [rawY, physicalY, rawP_cast]

theorem rawDeviation_cast (v : RationalVertices) (means : Fin 10 → ℚ)
    (i : Fin 9) (j : Fin 10) :
    (rawDeviation v means i j : ℝ) =
      physicalDeviation (fun k => (means k : ℝ)) j (realVertices v i) := by
  simp [rawDeviation, physicalDeviation, normalizedFactor, rawFactor_cast, rawP_cast]

/-- The real vertex arrays follow from the exact finite arithmetic
normalization. Both selected rows below supply this normalization by a
closed source proof; the target integral is not among its fields. -/
theorem real_vertex_arrays (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (gd : Nat)
    (h : VertexNormalization v means upper d gd) :
    (fun i => physicalGap (realVertices v i)) =
        (fun i => gapVertices d i / (gd : ℝ)) ∧
      (fun i => physicalY (fun j => (means j : ℝ)) (upper : ℝ) (realVertices v i)) =
        yVertices d ∧
      ∀ j : Fin 10,
        (fun i => physicalDeviation (fun k => (means k : ℝ)) j (realVertices v i)) =
          bVertices d j := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    rw [← rawGap_cast, (h.2 i).1]
    simp [gapVertices]
  · funext i
    rw [← rawY_cast, (h.2 i).2.1]
    simp [yVertices]
  · intro j
    funext i
    rw [← rawDeviation_cast, (h.2 i).2.2 j]
    simp [bVertices]

/-- The source maximum has the same scale in the real kernel. -/
theorem row21_upper_cast :
    (Row21.upper : ℝ) = (Row21.data.U : ℝ) / (Row21.data.L : ℝ) := by
  simp only [Row21.upper, Rat.cast_div, Rat.cast_natCast]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- These exact ratios also retain the original normalized factor numerators. -/
theorem row21_rational_P_and_factor_scales : ∀ i : Fin 9,
    rawP row21 Row21.means i = (P2Winner9Row21Arithmetic.pv i : ℚ) / Row21.data.L ∧
    ∀ j : Fin 10, rawFactor row21 i j / Row21.means j =
      (P2Winner9Row21Arithmetic.ai i j : ℚ) / Row21.data.L := by
  decide +kernel

/-- The gap, Y and signed deviations have the original integer scales at
every point of the affine chart. -/
theorem row21_affine_weight_scales (x : Ambient) :
    let z := vertexMap (realVertices row21) x
    physicalGap z = affine (gapVertices Row21.data) x / (Row21.gapDen : ℝ) ∧
    physicalY (fun j => (Row21.means j : ℝ)) (Row21.upper : ℝ) z =
      affine (yVertices Row21.data) x ∧
    ∀ j : Fin 10, physicalDeviation (fun k => (Row21.means k : ℝ)) j z =
      affine (bVertices Row21.data j) x := by
  dsimp only
  obtain ⟨hg, hy, hb⟩ :=
    real_vertex_arrays row21 Row21.means Row21.upper Row21.data Row21.gapDen
      row21_vertex_normalization
  refine ⟨?_, ?_, ?_⟩
  · rw [physicalGap_vertexMap, hg, affine_div]
  · rw [physicalY_vertexMap, hy]
  · intro j
    rw [physicalDeviation_vertexMap, hb j]

/-- The same chart interpolates the original scaled P and all ten normalized
factors of row21. -/
theorem row21_affine_P_and_factor_scales (x : Ambient) :
    let z := vertexMap (realVertices row21) x
    physicalP (fun j => (Row21.means j : ℝ)) z =
      affine (fun i => (P2Winner9Row21Arithmetic.pv i : ℝ)) x / (Row21.data.L : ℝ) ∧
    ∀ j : Fin 10, normalizedFactor (fun k => (Row21.means k : ℝ)) j z =
      affine (fun i => (P2Winner9Row21Arithmetic.ai i j : ℝ)) x / (Row21.data.L : ℝ) := by
  dsimp only
  constructor
  · have hp (i : Fin 9) :
        physicalP (fun j => (Row21.means j : ℝ)) (realVertices row21 i) =
          (P2Winner9Row21Arithmetic.pv i : ℝ) / (Row21.data.L : ℝ) := by
      rw [← rawP_cast]
      have h := congrArg (fun q : ℚ => (q : ℝ)) (row21_rational_P_and_factor_scales i).1
      simpa only [Rat.cast_div, Rat.cast_natCast] using h
    rw [physicalP_vertexMap]
    simp only [hp, affine_div]
  · intro j
    have ha (i : Fin 9) :
        normalizedFactor (fun k => (Row21.means k : ℝ)) j (realVertices row21 i) =
          (P2Winner9Row21Arithmetic.ai i j : ℝ) / (Row21.data.L : ℝ) := by
      change physicalFactor j (realVertices row21 i) / (Row21.means j : ℝ) = _
      rw [← rawFactor_cast]
      have h := congrArg (fun q : ℚ => (q : ℝ)) ((row21_rational_P_and_factor_scales i).2 j)
      simpa only [Rat.cast_div, Rat.cast_natCast] using h
    rw [normalizedFactor_vertexMap]
    simp only [ha, affine_div]

/-- Normalization of the genuine measured canonical numerator to the
pinned signed integer mixed coefficient. This reuses the already drafted
actual Δ8/finite-partition theorem rather than assuming moment identity M. -/
theorem actualMixedNumerator_integer (d : SimplexData) (j : Fin 10) :
    actualMixedNumerator d j =
      (mixedNumerator d j 1 : ℝ) /
        (((12 : ℕ).factorial : ℝ) * d.U * (d.L : ℝ)^2) := by
  have hG : (gapTotal d.gaps : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.gapsPos)
  have hU : (d.U : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.UPos)
  have hL : (d.L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.LPos)
  have hMass : actualGapMass d ≠ 0 := ne_of_gt (actualGapMass_pos d)
  calc
    actualMixedNumerator d j = actualMixedExpectation d j * actualGapMass d := by
      rw [actualMixedExpectation]
      field_simp [hMass]
    _ = _ := by
      rw [actualMixedExpectation_eq_candidate, actualGapMass_eq]
      norm_num
      field_simp [hG, hU, hL]; ring

/-- Actual physical measured mixed numerator, with the gap's original
common denominator retained. This is then instantiated at the two real
raw rows, with no normalization premise left in the concrete results. -/
theorem physical_mixed_integer (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (gd : Nat)
    (h : VertexNormalization v means upper d gd) (j : Fin 10) :
    (∫ y in sourceSupport v,
      physicalMixedIntegrand (fun k => (means k : ℝ)) (upper : ℝ) j y) =
      (|((edgeMatrix v).det : ℝ)| / (gd : ℝ)) *
        ((mixedNumerator d j 1 : ℝ) /
          (((12 : ℕ).factorial : ℝ) * d.U * (d.L : ℝ)^2)) := by
  obtain ⟨hg, hy, hb⟩ := real_vertex_arrays v means upper d gd h
  rw [source_mixed_integral v hv, hg, hy, hb j]
  simp_rw [affine_div]
  have hfactor : (fun x : Ambient =>
      (affine (gapVertices d) x / (gd : ℝ)) *
        affine (yVertices d) x * (affine (bVertices d j) x)^2) =
      (fun x => (1 / (gd : ℝ)) *
        (affine (gapVertices d) x * affine (yVertices d) x *
          (affine (bVertices d j) x)^2)) := by
    funext x
    ring
  rw [hfactor, integral_const_mul]
  change |((edgeMatrix v).det : ℝ)| *
    ((1 / (gd : ℝ)) * actualMixedNumerator d j) = _
  rw [actualMixedNumerator_integer]
  ring

/-- Concrete original row21 physical mixed numerator. Its gap scale,
stored mean vector, U/L and signed-deviation normalization are all supplied
by the actual finite vertex reconstruction, not premises. -/
theorem row21_physical_mixed_numerator (j : Fin 10) :
    (∫ y in sourceSupport row21,
      physicalMixedIntegrand (fun k => (Row21.means k : ℝ))
        (Row21.upper : ℝ) j y) =
      ((((8 : ℕ).factorial : ℝ) * (P2Winner9Row21RawVertexData.physicalVolume : ℝ)) /
        (Row21.gapDen : ℝ)) *
      ((mixedNumerator Row21.data j 1 : ℝ) /
        (((12 : ℕ).factorial : ℝ) * Row21.data.U * (Row21.data.L : ℝ)^2)) := by
  rw [physical_mixed_integer row21 row21_det_ne_zero Row21.means Row21.upper
    Row21.data Row21.gapDen row21_vertex_normalization]
  congr 2
  exact_mod_cast row21_abs_det_volume

/-- Concrete original row22 physical mixed numerator. The row22 integer
data is reconstructed from its own distinct final two source vertices. -/
theorem row22_physical_mixed_numerator (j : Fin 10) :
    (∫ y in sourceSupport row22,
      physicalMixedIntegrand (fun k => (Row22.means k : ℝ))
        (Row22.upper : ℝ) j y) =
      ((((8 : ℕ).factorial : ℝ) * (row22Volume : ℝ)) / (Row22.gapDen : ℝ)) *
      ((mixedNumerator Row22.data j 1 : ℝ) /
        (((12 : ℕ).factorial : ℝ) * Row22.data.U * (Row22.data.L : ℝ)^2)) := by
  rw [physical_mixed_integer row22 row22_det_ne_zero Row22.means Row22.upper
    Row22.data Row22.gapDen row22_vertex_normalization]
  congr 2
  exact_mod_cast row22_abs_det_volume

end

end ImbalancedChen.P2Winner9SelectedRowIntegerScales
