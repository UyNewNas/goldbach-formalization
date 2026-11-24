import ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
import ImbalancedChen.P2Winner9SelectedAllMixedMoments
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Independent rational polynomial decoder of ALL original physical rows.
No source row is copied or filtered. Closed finite source proof terms below
are deliberately NOT executed. Their evaluation feasibility is not claimed.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedMomentDecoder

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedAllMixedMoments
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne

abbrev vertices (i : RowIndex) := physicalVertices i
abbrev means (i : RowIndex) := (entry i).means

def upper (i : RowIndex) : ℚ :=
  (List.ofFn (rawP (vertices i) (means i))).foldl max 0

def pLower (i : RowIndex) : ℚ :=
  (List.ofFn (rawP (vertices i) (means i))).foldl min 1

def transverseUpper (i : RowIndex) (j : Fin 10) : ℚ :=
  (List.ofFn (fun k : Fin 9 => rawFactor (vertices i) k j / means i j)).foldl max (upper i)

def yUpper (i : RowIndex) : ℚ := 1 - pLower i / upper i

def gapPoly (i : RowIndex) : Poly := affinePoly (rawGap (vertices i))
def factorPoly (i : RowIndex) (j : Fin 10) : Poly :=
  affinePoly (fun k => rawFactor (vertices i) k j)
def yPoly (i : RowIndex) : Poly := affinePoly (rawY (vertices i) (means i) (upper i))
def bPoly (i : RowIndex) (j : Fin 10) : Poly :=
  affinePoly (fun k => rawDeviation (vertices i) (means i) k j)
def powerPoly (i : RowIndex) (k : ℕ) : Poly := gapPoly i * (yPoly i)^k

def powerMoment (i : RowIndex) (k : ℕ) : ℚ :=
  polynomialMoment (powerPoly i k) / polynomialMoment (gapPoly i)
def mixedMoment (i : RowIndex) (j : Fin 10) (k : ℕ) : ℚ :=
  polynomialMoment (gapPoly i * (yPoly i)^k * (bPoly i j)^2) /
    polynomialMoment (gapPoly i)

def t10 (i : RowIndex) : ℚ := (1 / (upper i)^10) *
  ∑ k ∈ Finset.range 11, ((9 + k).choose k : ℚ) *
    (powerMoment i k - (powerMoment i 1)^k)
def mixedTerm (i : RowIndex) (j : Fin 10) (k : Fin 7) : ℚ :=
  ((9 + k.val).choose k.val : ℚ) * mixedMoment i j k.val /
    (2 * (transverseUpper i j)^2 * (upper i)^10)
def q6 (i : RowIndex) : ℚ := ∑ j : Fin 10, ∑ k : Fin 7, mixedTerm i j k
def q0 (i : RowIndex) : ℚ := ∑ j : Fin 10, mixedTerm i j 0

def q80 : ℚ := 2^80
def q96 : ℚ := 2^96
/-- Exact directed rounding, including the upper endpoint. -/
def FloorAt (scale x : ℚ) (n : ℕ) : Prop :=
  (n : ℚ) / scale ≤ x ∧ x < ((n : ℚ) + 1) / scale

/-- Every guard is rational source arithmetic, independent of real integrals.
In particular neither a row enclosure nor a selected-floor bound occurs. -/
structure SourceFacts (i : RowIndex) : Prop where
  det_ne : (edgeMatrix (vertices i)).det ≠ 0
  volume_eq : |(edgeMatrix (vertices i)).det| = (8.factorial : ℚ) * (entry i).physicalVolume
  gap_pos : 0 < polynomialMoment (gapPoly i)
  gap_mean : polynomialMoment (gapPoly i) = (entry i).meanGap / (8.factorial : ℚ)
  factor_mean : ∀ j : Fin 10, polynomialMoment (gapPoly i * factorPoly i j) =
    means i j * polynomialMoment (gapPoly i)
  y_mean : powerMoment i 1 = 1 - 1 / upper i
  jensen_eq : (entry i).jensen = 4 * |(edgeMatrix (vertices i)).det| *
    polynomialMoment (gapPoly i) / ∏ j : Fin 10, means i j
  upper_pos : 0 < upper i
  lower_pos : 0 < pLower i
  vertex_caps : ∀ k : Fin 9,
    pLower i ≤ rawP (vertices i) (means i) k ∧
    rawP (vertices i) (means i) k ≤ upper i ∧
    ∀ j : Fin 10,
      rawFactor (vertices i) k j / means i j ≤ transverseUpper i j ∧
      rawP (vertices i) (means i) k ≤ transverseUpper i j

/-- Closed source proof proposal over the genuine Fin11026. NOT EXECUTED. -/
theorem all_source_facts : ∀ i : RowIndex, SourceFacts i := by
  intro i
  constructor <;> revert i <;> decide +kernel

/-- Each original stored Q80/Q96 field is compared with an independently
integrated rational polynomial, never with the real integral to be bounded.
The seven term fields are sums over factors, not sums of rounded moments. -/
structure FieldFacts (i : RowIndex) : Prop where
  moments : ∀ j : Fin 10, ∀ k : Fin 7,
    FloorAt q80 (mixedMoment i j k.val) (((entry i).mixedMomentFloors[j.val]!)[k.val]!)
  terms : ∀ k : Fin 7, FloorAt q80 (∑ j : Fin 10, mixedTerm i j k)
    ((entry i).mixedTermFloors[k.val]!)
  correction : FloorAt q80 (q6 i) (entry i).mixedCorrectionQ80
  curvature_diagnostic : FloorAt q80 (q0 i) (entry i).curvatureDiagnosticQ80
  curvature_total : FloorAt q80 (t10 i + q0 i) (entry i).curvatureTotalQ80
  curvature_raw : FloorAt q96
    ((entry i).jensen * (1 + ((entry i).curvatureTotalQ80 : ℚ) / q80))
    (entry i).curvatureRaw
  mixed_total : FloorAt q80 (t10 i + q6 i) (entry i).mixedTotalQ80
  mixed_raw : FloorAt q96
    ((entry i).jensen * (1 + ((entry i).mixedTotalQ80 : ℚ) / q80)) (entry i).mixedRaw
  raw_monotone : (entry i).curvatureRaw ≤ (entry i).mixedRaw

/-- No checker/decision execution was performed; this body is source only. -/
theorem all_field_facts : ∀ i : RowIndex, FieldFacts i := by
  intro i
  constructor <;> revert i <;> simp only [FloorAt] <;> decide +kernel

def jacobian (i : RowIndex) : ℝ := |((edgeMatrix (vertices i)).det : ℝ)|
def gapMass (i : RowIndex) : ℝ := ∫ z in actualSupport i, physicalGap z

theorem jacobian_pos (i : RowIndex) : 0 < jacobian i := by
  apply abs_pos.mpr
  exact_mod_cast (all_source_facts i).det_ne

theorem gapPoly_eval (i : RowIndex) (x : Ambient) :
    (gapPoly i).eval₂ (Rat.castHom ℝ) x =
      physicalGap (vertexMap (realVertices (vertices i)) x) := by
  simp only [gapPoly, affinePoly_eval, rawGap_cast, physicalGap_vertexMap]

theorem factorPoly_eval (i : RowIndex) (j : Fin 10) (x : Ambient) :
    (factorPoly i j).eval₂ (Rat.castHom ℝ) x =
      physicalFactor j (vertexMap (realVertices (vertices i)) x) := by
  simp only [factorPoly, affinePoly_eval, rawFactor_cast, physicalFactor_vertexMap]

theorem yPoly_eval (i : RowIndex) (x : Ambient) :
    (yPoly i).eval₂ (Rat.castHom ℝ) x =
      physicalY (fun j => (means i j : ℝ)) (upper i : ℝ)
        (vertexMap (realVertices (vertices i)) x) := by
  simp only [yPoly, affinePoly_eval, rawY_cast, physicalY_vertexMap]

theorem bPoly_eval (i : RowIndex) (j : Fin 10) (x : Ambient) :
    (bPoly i j).eval₂ (Rat.castHom ℝ) x =
      physicalDeviation (fun k => (means i k : ℝ)) j
        (vertexMap (realVertices (vertices i)) x) := by
  simp only [bPoly, affinePoly_eval, rawDeviation_cast, physicalDeviation_vertexMap]

theorem gapMass_eq (i : RowIndex) :
    gapMass i = jacobian i * (polynomialMoment (gapPoly i) : ℝ) := by
  rw [gapMass, actualSupport, source_integral (vertices i) (all_source_facts i).det_ne]
  simp_rw [← gapPoly_eval]
  rw [canonical_polynomial_integral]
  rfl

theorem gapMass_pos (i : RowIndex) : 0 < gapMass i := by
  rw [gapMass_eq]
  exact mul_pos (jacobian_pos i) (by exact_mod_cast (all_source_facts i).gap_pos)

/-- Reusable polynomial transport: real measured expectation from a
polynomial pullback, with the actual positive Jacobian cancelled. -/
theorem measured_polynomial (i : RowIndex) (p : Poly) (f : Ambient → ℝ)
    (hf : ∀ x, p.eval₂ (Rat.castHom ℝ) x = f (vertexMap (realVertices (vertices i)) x)) :
    (∫ z in actualSupport i, physicalGap z * f z) / gapMass i =
      ((polynomialMoment (gapPoly i * p) / polynomialMoment (gapPoly i) : ℚ) : ℝ) := by
  rw [actualSupport, source_integral (vertices i) (all_source_facts i).det_ne]
  have he (x : Ambient) :
      physicalGap (vertexMap (realVertices (vertices i)) x) *
          f (vertexMap (realVertices (vertices i)) x) =
        (gapPoly i * p).eval₂ (Rat.castHom ℝ) x := by
    rw [MvPolynomial.eval₂_mul, gapPoly_eval, hf]
  simp_rw [he]
  rw [canonical_polynomial_integral, gapMass_eq]
  have hJ := (jacobian_pos i).ne'
  have hG : (polynomialMoment (gapPoly i) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast (all_source_facts i).gap_pos)
  change jacobian i * _ / (jacobian i * _) = _
  push_cast
  field_simp [hJ, hG] <;> ring

/-- All ten literal means now denote actual physical expectations. -/
theorem actual_factor_mean (i : RowIndex) (j : Fin 10) :
    (∫ z in actualSupport i, physicalGap z * physicalFactor j z) / gapMass i =
      (means i j : ℝ) := by
  rw [measured_polynomial i (factorPoly i j) _ (factorPoly_eval i j),
    (all_source_facts i).factor_mean j]
  have hg := ne_of_gt (all_source_facts i).gap_pos
  simp [hg]

theorem actual_power_mean (i : RowIndex) (k : ℕ) :
    (∫ z in actualSupport i, physicalGap z *
      (physicalY (fun j => (means i j : ℝ)) (upper i : ℝ) z)^k) / gapMass i =
        (powerMoment i k : ℝ) := by
  apply measured_polynomial i ((yPoly i)^k)
  intro x
  rw [MvPolynomial.eval₂_pow, yPoly_eval]

theorem actual_mixed_mean (i : RowIndex) (j : Fin 10) (k : ℕ) :
    (∫ z in actualSupport i, physicalGap z *
      ((physicalY (fun l => (means i l : ℝ)) (upper i : ℝ) z)^k *
        (physicalDeviation (fun l => (means i l : ℝ)) j z)^2)) / gapMass i =
          (mixedMoment i j k : ℝ) := by
  have h := measured_polynomial i ((yPoly i)^k * (bPoly i j)^2)
    (fun z => (physicalY (fun l => (means i l : ℝ)) (upper i : ℝ) z)^k *
      (physicalDeviation (fun l => (means i l : ℝ)) j z)^2)
    (fun x => by simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      yPoly_eval, bPoly_eval])
  simpa only [mixedMoment, mul_assoc] using h

theorem actual_Jensen_factor (i : RowIndex) :
    ((entry i).jensen : ℝ) = 4 * gapMass i / ∏ j : Fin 10, (means i j : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (all_source_facts i).jensen_eq
  push_cast at h
  rw [gapMass_eq]
  convert h using 1 <;> ring

/-- The archive volume is proved to be the volume of its own support. -/
theorem actual_volume (i : RowIndex) :
    (∫ _z in actualSupport i, (1 : ℝ)) = ((entry i).physicalVolume : ℝ) := by
  rw [actualSupport, source_volume (vertices i) (all_source_facts i).det_ne]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (all_source_facts i).volume_eq
  push_cast at h
  rw [h]
  norm_num

end
end ImbalancedChen.P2Winner9CompleteSeedMomentDecoder

