import ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
import ImbalancedChen.P2AffineSimplexMomentLaw
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The selected winner9 parents have eight physical coordinates and nine
vertices. This source gives the actual measurable affine image of the
canonical closed Δ8 and the Lebesgue integral transport with the
absolute eight-dimensional determinant. It also states the exact
physical R, M, gap and ten factors used by the pinned producer and
records the distinct row21/row22 vertex-ID orders.

The equality of those witness vertices with a particular invertible
affine map, their exact gap/mean/deviation values, and their row cap
remain separate source checks. No physical row floor is asserted.
-/

namespace ImbalancedChen.P2Winner9PhysicalAffineTransfer

noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9SimplexCoordinateSlice
open ImbalancedChen.P2Winner9ActualEightSimplexMoment
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.Certificates.P2AffineSimplexMomentLaw
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly

abbrev Ambient := Fin 8 → ℝ

def canonicalSupport : Set Ambient := standardSimplex 8 (1 : ℝ)

theorem canonicalSupport_measurable : MeasurableSet canonicalSupport :=
  (isClosed_standardSimplex (1 : ℝ)).measurableSet

theorem canonicalSupport_compact : IsCompact canonicalSupport :=
  isCompact_standardSimplex (by norm_num)

def affinePoint (L : Ambient ≃L[ℝ] Ambient) (b x : Ambient) : Ambient :=
  b + L x

def physicalSupport (L : Ambient ≃L[ℝ] Ambient) (b : Ambient) : Set Ambient :=
  (affinePoint L b) '' canonicalSupport

theorem physicalSupport_compact (L : Ambient ≃L[ℝ] Ambient) (b : Ambient) :
    IsCompact (physicalSupport L b) := by
  exact canonicalSupport_compact.image
    (continuous_const.add L.continuous)

theorem physicalSupport_measurable (L : Ambient ≃L[ℝ] Ambient) (b : Ambient) :
    MeasurableSet (physicalSupport L b) :=
  (physicalSupport_compact L b).isClosed.measurableSet

/-- The actual eight-dimensional change of variables. The Jacobian is
the absolute determinant of the map from canonical coordinates to
physical coordinates. There is no ordering factorial in this step. -/
theorem physical_integral (L : Ambient ≃L[ℝ] Ambient) (b : Ambient)
    (f : Ambient → ℝ) :
    (∫ y in physicalSupport L b, f y) =
      |L.toContinuousLinearMap.det| *
        ∫ x in canonicalSupport, f (affinePoint L b x) := by
  simpa only [physicalSupport, canonicalSupport, affinePoint]
    using integral_affine_image volume L b
      (standardSimplex 8 (1 : ℝ)) canonicalSupport_measurable f

def pullback (L : Ambient ≃L[ℝ] Ambient) (b : Ambient)
    (f : Ambient → ℝ) (y : Ambient) : ℝ :=
  f (L.symm (y - b))

theorem pullback_affinePoint (L : Ambient ≃L[ℝ] Ambient)
    (b x : Ambient) (f : Ambient → ℝ) :
    pullback L b f (affinePoint L b x) = f x := by
  simp [pullback, affinePoint]

/-- Transport of an arbitrary canonical integrand, including every
actual Δ8 moment. -/
theorem physical_pullback_integral (L : Ambient ≃L[ℝ] Ambient)
    (b : Ambient) (f : Ambient → ℝ) :
    (∫ y in physicalSupport L b, pullback L b f y) =
      |L.toContinuousLinearMap.det| * ∫ x in canonicalSupport, f x := by
  rw [physical_integral]
  simp only [pullback_affinePoint]

theorem canonical_volume :
    (∫ _x in canonicalSupport, (1 : ℝ)) =
      1 / (8.factorial : ℝ) := by
  have h := actual_eight_factorial 0 (fun _ : Fin 8 => 0)
    (s := (1 : ℝ)) (by norm_num)
  simpa [canonicalSupport, factorialProduct, List.ofFn] using h

/-- Actual physical volume, with no inserted ordering factorial. -/
theorem physical_volume (L : Ambient ≃L[ℝ] Ambient) (b : Ambient) :
    (∫ _y in physicalSupport L b, (1 : ℝ)) =
      |L.toContinuousLinearMap.det| / (8.factorial : ℝ) := by
  rw [physical_integral, canonical_volume]
  ring

theorem physical_mixed_degree_one (L : Ambient ≃L[ℝ] Ambient)
    (b : Ambient) (d : SimplexData) (j : Fin 10) :
    (∫ y in physicalSupport L b,
      pullback L b (fun x =>
        affine (gapVertices d) x * affine (yVertices d) x *
          (affine (bVertices d j) x)^2) y) =
      |L.toContinuousLinearMap.det| * actualMixedNumerator d j := by
  rw [physical_pullback_integral]
  rfl

theorem physical_gap_mass (L : Ambient ≃L[ℝ] Ambient)
    (b : Ambient) (d : SimplexData) :
    (∫ y in physicalSupport L b,
      pullback L b (affine (gapVertices d)) y) =
      |L.toContinuousLinearMap.det| *
        ((gapTotal d.gaps : ℝ) / (9.factorial : ℝ)) := by
  rw [physical_pullback_integral]
  exact congrArg (|L.toContinuousLinearMap.det| * ·)
    (actualGapMass_eq d)

/-- The physical weighted expectation cancels the common Jacobian.
The explicit positive determinant guard is a geometric nondegeneracy
fact to check for a selected witness row, not a moment assumption. -/
theorem physical_pullback_mixed_ratio
    (L : Ambient ≃L[ℝ] Ambient) (b : Ambient)
    (d : SimplexData) (j : Fin 10)
    (hJac : 0 < |L.toContinuousLinearMap.det|) :
    (∫ y in physicalSupport L b,
      pullback L b (fun x =>
        affine (gapVertices d) x * affine (yVertices d) x *
          (affine (bVertices d j) x)^2) y) /
      (∫ y in physicalSupport L b,
        pullback L b (affine (gapVertices d)) y) =
      actualMixedExpectation d j := by
  rw [physical_mixed_degree_one, physical_gap_mass]
  rw [actualMixedExpectation, actualGapMass_eq]
  have hG : (gapTotal d.gaps : ℝ) / (9.factorial : ℝ) ≠ 0 :=
    ne_of_gt (by simpa only [actualGapMass_eq] using actualGapMass_pos d)
  field_simp [hJac.ne', hG]

/-- Exact physical variables used by the author source. These are
affine functions on the original eight physical coordinates. -/
def coordinateSum (v : Ambient) : ℝ := ∑ i : Fin 8, v i
def physicalR (v : Ambient) : ℝ := (1 + v 0 + v 3) / 2
def physicalM (v : Ambient) : ℝ :=
  (1 + v 1 + v 3 + v 7) / 2 - 1 / 1000000
def physicalGap (v : Ambient) : ℝ := physicalM v - physicalR v
def physicalFactor (j : Fin 10) (v : Ambient) : ℝ :=
  Fin.cases (physicalR v - coordinateSum v)
    (Fin.cases (physicalM v - coordinateSum v)
      (fun i : Fin 8 => v i)) j

theorem physicalFactor_zero (v : Ambient) :
    physicalFactor 0 v = physicalR v - coordinateSum v := rfl

theorem physicalFactor_one (v : Ambient) :
    physicalFactor 1 v = physicalM v - coordinateSum v := rfl

theorem physicalFactor_succ_succ (i : Fin 8) (v : Ambient) :
    physicalFactor i.succ.succ v = v i := rfl

def physicalUpperIntegrand (v : Ambient) : ℝ :=
  4 * physicalGap v / ∏ j : Fin 10, physicalFactor j v

def normalizedFactor (means : Fin 10 → ℝ) (j : Fin 10)
    (v : Ambient) : ℝ := physicalFactor j v / means j

def physicalP (means : Fin 10 → ℝ) (v : Ambient) : ℝ :=
  (∑ j : Fin 10, normalizedFactor means j v) / 10

def physicalY (means : Fin 10 → ℝ) (U : ℝ) (v : Ambient) : ℝ :=
  1 - physicalP means v / U

def physicalDeviation (means : Fin 10 → ℝ) (j : Fin 10)
    (v : Ambient) : ℝ :=
  normalizedFactor means j v - physicalP means v

def physicalMixedIntegrand (means : Fin 10 → ℝ) (U : ℝ)
    (j : Fin 10) (v : Ambient) : ℝ :=
  physicalGap v * physicalY means U v *
    (physicalDeviation means j v)^2

/-- The original upper integrand is transported as written, with its
factor 4 and all ten actual factors. This is an equality of integrals,
not a numerical enclosure or positivity claim. -/
theorem physical_upper_integral (L : Ambient ≃L[ℝ] Ambient)
    (b : Ambient) :
    (∫ v in physicalSupport L b, physicalUpperIntegrand v) =
      |L.toContinuousLinearMap.det| *
        ∫ x in canonicalSupport,
          physicalUpperIntegrand (affinePoint L b x) :=
  physical_integral L b physicalUpperIntegrand

/-- The original mixed polynomial on the physical cell also transports
to canonical coordinates. Matching its vertex values to PhaseB2's
integer `SimplexData` is the separate exact row reconstruction step. -/
theorem physical_mixed_integral (L : Ambient ≃L[ℝ] Ambient)
    (b : Ambient) (means : Fin 10 → ℝ) (U : ℝ) (j : Fin 10) :
    (∫ v in physicalSupport L b,
      physicalMixedIntegrand means U j v) =
      |L.toContinuousLinearMap.det| *
        ∫ x in canonicalSupport,
          physicalMixedIntegrand means U j (affinePoint L b x) :=
  physical_integral L b (physicalMixedIntegrand means U j)

/-- Frozen source orders. They are IDs of vertices in the raw witness;
they are not coordinate values or a proof of the Jacobian. -/
def row21VertexIds : Fin 9 → Nat :=
  ![200, 188, 58, 49, 48, 21, 7, 6, 0]

def row22VertexIds : Fin 9 → Nat :=
  ![200, 188, 58, 49, 48, 21, 7, 2, 1]

def selectedVertices (lookup : Nat → Ambient) (ids : Fin 9 → Nat) :
    Fin 9 → Ambient := fun i => lookup (ids i)

def selectedPhysicalSupport (L : Ambient ≃L[ℝ] Ambient)
    (lookup : Nat → Ambient) (ids : Fin 9 → Nat) : Set Ambient :=
  physicalSupport L (lookup (ids 0))

/-- A selected row's affine coordinate map is bound to its source
ordered vertices one by one. This is a checkable geometry guard, never
an asserted row21/row22 witness success. -/
def selectedVertexMatch (L : Ambient ≃L[ℝ] Ambient)
    (lookup : Nat → Ambient) (ids : Fin 9 → Nat) : Prop :=
  ∀ i : Fin 8,
    affinePoint L (lookup (ids 0)) (Pi.single i (1 : ℝ)) =
      lookup (ids i.succ)

private theorem canonical_zero_mem : (0 : Ambient) ∈ canonicalSupport := by
  simp [canonicalSupport, standardSimplex]

private theorem canonical_single_mem (i : Fin 8) :
    Pi.single i (1 : ℝ) ∈ canonicalSupport := by
  have hcoord : ∀ k : Fin 8, 0 ≤ Pi.single i (1 : ℝ) k := by
    intro k
    by_cases h : k = i <;> simp [Pi.single_apply, h]
  have hsum : (∑ k : Fin 8, Pi.single i (1 : ℝ) k) = 1 := by simp
  change (∀ k : Fin 8, 0 ≤ Pi.single i (1 : ℝ) k) ∧
    (∑ k : Fin 8, Pi.single i (1 : ℝ) k) ≤ 1
  exact ⟨hcoord, by rw [hsum]⟩

/-- Under the exact vertex-order guard, every named selected vertex
belongs to the measurable physical parent support. This does not prove
that the raw witness lookup satisfies the guard. -/
theorem selectedVertices_mem (L : Ambient ≃L[ℝ] Ambient)
    (lookup : Nat → Ambient) (ids : Fin 9 → Nat)
    (hMatch : selectedVertexMatch L lookup ids) (i : Fin 9) :
    lookup (ids i) ∈ selectedPhysicalSupport L lookup ids := by
  refine Fin.cases ?_ ?_ i
  · change lookup (ids 0) ∈ physicalSupport L (lookup (ids 0))
    refine ⟨0, canonical_zero_mem, ?_⟩
    simp [affinePoint]
  · intro k
    change lookup (ids k.succ) ∈ physicalSupport L (lookup (ids 0))
    refine ⟨Pi.single k (1 : ℝ), canonical_single_mem k, ?_⟩
    exact hMatch k

end

end ImbalancedChen.P2Winner9PhysicalAffineTransfer
