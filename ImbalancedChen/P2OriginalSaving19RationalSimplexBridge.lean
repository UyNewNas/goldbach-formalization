import ImbalancedChen.P2OriginalSaving19HigherMoments
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Rat.Cast.Order

/-! Candidate bridge from the original rational vertices and finite row
checks to an actual affine simplex. No integration assertion is a premise. -/
namespace ImbalancedChen.P2OriginalSaving19RationalSimplexBridge
noncomputable section
open scoped BigOperators Matrix
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SourceMeasure
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19RowNumericsPure

def realPoint (v : QPoint) : Point := fun j => (v j : ℝ)

theorem comparison_cast (v : QPoint) : (comparisonQ v : ℝ) = comparisonCap (realPoint v) := by
  norm_num [comparisonQ, comparisonCap, realPoint, VariableEnvelope.A]
  ; ring

theorem new_cast (v : QPoint) : (newQ v : ℝ) = newCap (realPoint v) := by
  norm_num [newQ, newCap, selectedSum, realPoint, VariableEnvelope.A, eta]
  ; ring

theorem third_cast (v : QPoint) : (thirdQ v : ℝ) = thirdMinorant (realPoint v) := by
  norm_num [thirdQ, thirdMinorant, realPoint, VariableEnvelope.A]
  ; ring

theorem total_cast (v : QPoint) : (totalQ v : ℝ) = total (realPoint v) := by
  simp [totalQ, total, realPoint]

theorem gap_cast (v : QPoint) : (gapQ v : ℝ) = gap (realPoint v) := by
  simp only [gapQ, gap, Rat.cast_sub, comparison_cast, new_cast]

theorem factors_cast (v : QPoint) (j : Fin 10) :
    (factorsQ v j : ℝ) = factors (realPoint v) j := by
  fin_cases j <;> simp [factorsQ, factors, comparison_cast, new_cast, total_cast, realPoint]

theorem physical_cast (v : QPoint) (hv : PhysicalQ v) : PhysicalRows (realPoint v) := by
  rcases hv with ⟨ho, h8, h3, h0, ha3, hao, han, hh1, hh3, hh5, hh7, hc, hi, hr⟩
  constructor
  · intro i j hij
    change (v j : ℝ) ≤ (v i : ℝ)
    exact_mod_cast ho i j hij
  · change (53 : ℝ) / 13824 ≤ (v 7 : ℝ)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h8
  · change (1 : ℝ) / 100 ≤ (v 2 : ℝ)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h3
  · change (v 0 : ℝ) ≤ 25 / 128
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h0
  · change (v 1 : ℝ) + (v 2 : ℝ) ≤ 25 / 128
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).2 ha3
  · change (v 0 : ℝ) + (v 3 : ℝ) ≤ 25 / 128
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).2 hao
  · change (v 1 : ℝ) + (v 3 : ℝ) + (v 7 : ℝ) ≤ 25 / 128
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).2 han
  · rw [← third_cast]
    change 3 * (v 0 : ℝ) ≤ (thirdQ v : ℝ)
    exact_mod_cast hh1
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
    exact_mod_cast hc
  · rw [← comparison_cast, ← new_cast]
    exact_mod_cast hi
  · rw [← new_cast, ← total_cast]
    change (newQ v : ℝ) - (totalQ v : ℝ) ≤ 3 * (v 7 : ℝ)
    exact_mod_cast hr

def realEdge (v : Fin 9 → QPoint) : Matrix (Fin 8) (Fin 8) ℝ :=
  (algebraMap ℚ ℝ).mapMatrix (edgeOf v)

theorem realEdge_det (v : Fin 9 → QPoint) :
    (realEdge v).det = ((edgeOf v).det : ℝ) := by
  exact (RingHom.map_det (algebraMap ℚ ℝ) (edgeOf v)).symm

def linear (v : Fin 9 → QPoint) (h : (edgeOf v).det ≠ 0) : Point ≃L[ℝ] Point :=
  ((realEdge v).toLinearEquiv (Pi.basisFun ℝ (Fin 8))
    (isUnit_iff_ne_zero.mpr (by rw [realEdge_det]; exact_mod_cast h))).toContinuousLinearEquiv

theorem linear_apply (v : Fin 9 → QPoint) (h : (edgeOf v).det ≠ 0) (x : Point) :
    linear v h x = realEdge v *ᵥ x := by
  change Matrix.toLin (Pi.basisFun ℝ (Fin 8)) (Pi.basisFun ℝ (Fin 8)) (realEdge v) x = _
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

theorem original_vertices (v : Fin 9 → QPoint) (h : (edgeOf v).det ≠ 0) :
    vertices (linear v h) (realPoint (v 0)) = fun i => realPoint (v i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · ext k
    simp only [vertices, Fin.cons_succ, Pi.add_apply, linear_apply,
      Matrix.mulVec_single_one]
    change (v 0 k : ℝ) + ((v j.succ k - v 0 k : ℚ) : ℝ) = (v j.succ k : ℝ)
    push_cast
    ring

theorem physicalVolume_cast (v : Fin 9 → QPoint) (h : (edgeOf v).det ≠ 0) :
    physicalVolume (linear v h) = (|(edgeOf v).det| / (Nat.factorial 8 : ℚ) : ℚ) := by
  unfold physicalVolume jacobian
  change |LinearMap.det (Matrix.toLin (Pi.basisFun ℝ (Fin 8))
    (Pi.basisFun ℝ (Fin 8)) (realEdge v))| / ((8 : ℕ).factorial : ℝ) = _
  rw [LinearMap.det_toLin, realEdge_det]
  push_cast
  rfl

theorem gapTotal_cast (v : Fin 9 → QPoint) :
    (gapSumOf v : ℝ) = gapTotal (fun i => realPoint (v i)) := by
  simp only [gapSumOf, gapTotal, Rat.cast_sum, gap_cast]

/-- Every semantic field is produced from rational vertex algebra. The
two moment identities are finite equalities, with no integral premise. -/
def algebraicRow (v : Fin 9 → QPoint) (g : P2OriginalSaving19Archive.GeometryRow)
    (moments : Fin 10 → ℕ → ℚ) (h : RowDataChecksFor v g)
    (hfirst : ∀ j, moments j 1 = 1 - meansOf g j / topsOf g j)
    (hhigher : ∀ j k, 2 ≤ k → k ≤ 6 → moments j k =
      P2OriginalSaving19HigherMoments.rationalMoment (fun i => gapQ (v i))
        (fun i => 1 - factorsQ (v i) j / topsOf g j) k) :
    P2OriginalSaving19HigherMoments.AlgebraicMomentRow where
  linear := linear v h.1
  base := realPoint (v 0)
  physicalVertices := by
    rw [original_vertices]
    intro i
    exact physical_cast (v i) (h.2.1 i)
  positiveGapTotal := by
    rw [original_vertices, ← gapTotal_cast]
    exact_mod_cast h.2.2.1
  massQ := massOf g
  meansQ := meansOf g
  topsQ := topsOf g
  momentsQ := moments
  gapsQ := fun i => gapQ (v i)
  factorsQ := fun i j => factorsQ (v i) j
  massEncoding := by
    rw [physicalVolume_cast, original_vertices, ← gapTotal_cast,
      massOf, h.2.2.2.1, h.2.2.2.2.1]
    push_cast
    ring
  meansEncoding := by
    intro j
    rw [h.2.2.2.2.2.1 j, original_vertices]
    simp [computedMeanOf, factorMean, gapTotal, gapSumOf, ← gap_cast, ← factors_cast]
  topsEncoding := by
    intro j
    rw [original_vertices]
    apply le_antisymm
    · obtain ⟨i, hi⟩ := h.2.2.2.2.2.2.2.1 j
      calc
        (topsOf g j : ℝ) = factors (realPoint (v i)) j := by rw [← hi, factors_cast]
        _ ≤ vertexTop (fun i => realPoint (v i)) j :=
          factor_le_vertexTop (fun i => realPoint (v i)) i j
    · apply Finset.sup'_le
      intro i _
      rw [← factors_cast]
      exact_mod_cast h.2.2.2.2.2.2.1 i j
  gapsEncoding := by
    intro i
    rw [original_vertices]
    exact gap_cast (v i)
  factorsEncoding := by
    intro i j
    rw [original_vertices]
    exact factors_cast (v i) j
  firstMomentEncoding := hfirst
  higherMomentEncoding := hhigher

#print axioms physical_cast
#print axioms original_vertices
#print axioms physicalVolume_cast
#print axioms algebraicRow
end
end ImbalancedChen.P2OriginalSaving19RationalSimplexBridge
