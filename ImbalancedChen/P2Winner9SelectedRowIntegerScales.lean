import ImbalancedChen.P2Winner9SelectedRowRealJacobian
import ImbalancedChen.P2Winner9Row21PrimitiveBinding
import ImbalancedChen.P2Winner9MixedKOneFiniteCollapse
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This source binds the actual physical vertex functions to the integer
SimplexData normalization for the two selected physical rows. Row21 reuses
its earlier typed source; row22 is reconstructed from the ordered rational
vertices by the original denominator-lcm, gap-weighted-mean, P/Y and signed
transverse formulas. Its stored means are literal witness fields.

All closed finite rational normalization bodies are unevaluated. No Lean,
checker, producer, determinant, integer-floor or numeric replay ran.
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

abbrev data : SimplexData := P2Winner9Row21PrimitiveBinding.row21SimplexData
abbrev gapDen : Nat := P2Winner9Row21PrimitiveBinding.gapCommonDen

/-- Actual stored gap-weighted means, in the source's ten-factor order. -/
def means (j : Fin 10) : ℚ := P2Winner9Row21RawVertexData.storedMeans[j.val]!

def upper : ℚ := (data.U : ℚ) / data.L

end Row21

def rawR (v : RationalVertices) (i : Fin 9) : ℚ :=
  (1 + v i 0 + v i 3) / 2

def rawM (v : RationalVertices) (i : Fin 9) : ℚ :=
  (1 + v i 1 + v i 3 + v i 7) / 2 - 1 / 1000000

def rawSum (v : RationalVertices) (i : Fin 9) : ℚ := ∑ k : Fin 8, v i k

def rawGap (v : RationalVertices) (i : Fin 9) : ℚ := rawM v i - rawR v i

def rawFactor (v : RationalVertices) (i : Fin 9) (j : Fin 10) : ℚ :=
  Fin.cases (rawR v i - rawSum v i)
    (Fin.cases (rawM v i - rawSum v i) (fun k : Fin 8 => v i k)) j

def rawP (v : RationalVertices) (means : Fin 10 → ℚ) (i : Fin 9) : ℚ :=
  (∑ j : Fin 10, rawFactor v i j / means j) / 10

def rawY (v : RationalVertices) (means : Fin 10 → ℚ) (U : ℚ)
    (i : Fin 9) : ℚ := 1 - rawP v means i / U

def rawDeviation (v : RationalVertices) (means : Fin 10 → ℚ)
    (i : Fin 9) (j : Fin 10) : ℚ :=
  rawFactor v i j / means j - rawP v means i

namespace Row22

/-- The source's `ints` construction on the nine actual gap values. -/
def gapDen : Nat :=
  (List.ofFn (fun i : Fin 9 => (rawGap row22 i).den)).foldl Nat.lcm 1

def g (i : Fin 9) : Nat :=
  (rawGap row22 i).num.toNat * (gapDen / (rawGap row22 i).den)

def G : Nat := ∑ i : Fin 9, g i

def columnDen (j : Fin 10) : Nat :=
  (List.ofFn (fun i : Fin 9 => (rawFactor row22 i j).den)).foldl Nat.lcm 1

def ellInt (i : Fin 9) (j : Fin 10) : Nat :=
  (rawFactor row22 i j).num.toNat * (columnDen j / (rawFactor row22 i j).den)

def meanNum (j : Fin 10) : Nat :=
  G * (∑ i : Fin 9, ellInt i j) + ∑ i : Fin 9, g i * ellInt i j

def computedMeans (j : Fin 10) : ℚ := (meanNum j : ℚ) / (10 * G * columnDen j)

/-- Literal row22 `gap_weighted_means` values; data transcription only. -/
def means : Fin 10 → ℚ :=
  ![((577637705887096607 : ℚ) / 11578849671480000000), ((2247037326827454443 : ℚ) / 38596165571600000000), ((234767748712392229153 : ℚ) / 2084192940866400000000), ((27938293278857716721 : ℚ) / 260524117608300000000), ((108089626526730803819 : ℚ) / 1042096470433200000000), ((18072940253656771157 : ℚ) / 297741848695200000000), ((901094636466229069 : ℚ) / 15438466228640000000), ((1929335299193979307 : ℚ) / 42534549813600000000), ((882788654227555807 : ℚ) / 33082427632800000000), ((5110669782824725501 : ℚ) / 231576993429600000000)]

def L : Nat := (List.ofFn (fun j : Fin 10 => meanNum j)).foldl Nat.lcm 1

def pv (i : Fin 9) : Nat :=
  G * ∑ j : Fin 10, ellInt i j * (L / meanNum j)

def U : Nat := (List.ofFn (fun i : Fin 9 => pv i)).foldl max 0

def y (i : Fin 9) : Nat := U - pv i

def ai (i : Fin 9) (j : Fin 10) : Nat :=
  10 * G * ellInt i j * (L / meanNum j)

/-- The transverse numerator stays in ℤ; there is no Nat truncation. -/
def b (j : Fin 10) (i : Fin 9) : ℤ := (ai i j : ℤ) - pv i

def vmax (j : Fin 10) : Nat :=
  max U ((List.ofFn (fun i : Fin 9 => ai i j)).foldl max 0)

def reconstructedJensen : ℚ :=
  4 * row22Volume * ((G : ℚ) / (9 * gapDen)) / ∏ j : Fin 10, computedMeans j

/-- The same typed primitive data as the pinned producer's reconstruction.
Every closed proof field below remains unexecuted. -/
def data : SimplexData := {
  gaps := g
  y := y
  L := L
  U := U
  deviations := b
  maxima := vmax
  jensenNum := reconstructedJensen.num.toNat
  jensenDen := reconstructedJensen.den
  gapsPos := by decide +kernel
  LPos := by decide +kernel
  UPos := by decide +kernel
  maximaPos := by decide +kernel
  jensenDenPos := by decide +kernel
}

def upper : ℚ := (data.U : ℚ) / data.L

/-- This actual stored/source mean equality is a finite rational check
proposal; it has not been evaluated. -/
theorem means_match_source : ∀ j : Fin 10, computedMeans j = means j := by
  decide +kernel

end Row22

/-- Exact finite vertex normalization obligations, independent of any
integral, mixed identity, cap, row floor or certificate conclusion. -/
def VertexNormalization (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (gapDen : Nat) : Prop :=
  0 < gapDen ∧
    ∀ i : Fin 9,
      rawGap v i = (d.gaps i : ℚ) / gapDen ∧
      rawY v means upper i = (d.y i : ℚ) / d.U ∧
      ∀ j : Fin 10, rawDeviation v means i j = (d.deviations j i : ℚ) / d.L

/-- The actual row21 values supply all normalization fields; this is a
closed source proposition, not a new assumed normalization hypothesis. -/
theorem row21_vertex_normalization :
    VertexNormalization row21 Row21.means Row21.upper Row21.data Row21.gapDen := by
  decide +kernel

/-- The actual row22 vertices and literal means supply the same fields.
The maxima-derived U is used in U/L, and the deviations remain signed. -/
theorem row22_vertex_normalization :
    VertexNormalization row22 Row22.means Row22.upper Row22.data Row22.gapDen := by
  decide +kernel

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
        rawM_cast, rawSum_cast, physicalFactor_one]
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

/-- Normalization of the genuine measured canonical numerator to the
pinned signed integer mixed coefficient. This reuses the already drafted
actual Δ8/finite-partition theorem rather than assuming moment identity M. -/
theorem actualMixedNumerator_integer (d : SimplexData) (j : Fin 10) :
    actualMixedNumerator d j =
      (mixedNumerator d j 1 : ℝ) /
        ((12.factorial : ℝ) * d.U * (d.L : ℝ)^2) := by
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
      field_simp [hG, hU, hL] <;> ring

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
          ((12.factorial : ℝ) * d.U * (d.L : ℝ)^2)) := by
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
      (((8.factorial : ℝ) * (P2Winner9Row21RawVertexData.physicalVolume : ℝ)) /
        (Row21.gapDen : ℝ)) *
      ((mixedNumerator Row21.data j 1 : ℝ) /
        ((12.factorial : ℝ) * Row21.data.U * (Row21.data.L : ℝ)^2)) := by
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
      (((8.factorial : ℝ) * (row22Volume : ℝ)) / (Row22.gapDen : ℝ)) *
      ((mixedNumerator Row22.data j 1 : ℝ) /
        ((12.factorial : ℝ) * Row22.data.U * (Row22.data.L : ℝ)^2)) := by
  rw [physical_mixed_integer row22 row22_det_ne_zero Row22.means Row22.upper
    Row22.data Row22.gapDen row22_vertex_normalization]
  congr 2
  exact_mod_cast row22_abs_det_volume

end

end ImbalancedChen.P2Winner9SelectedRowIntegerScales
