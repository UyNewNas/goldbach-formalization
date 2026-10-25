import ImbalancedChen.Part3ActualResolventGlobalHilbertSum
import ImbalancedChen.Part3ActualResolventCyclicIntertwining
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual completed-energy weak resolvent is unitarily represented by
coordinate multiplication on the unrestricted Hilbert sum of its actual
scalar measures. The diagonal operator is built from genuine pointwise
scalar multiplication, uniformly bounded by one. The intertwining passes
through the actual convergent orthogonal sum using continuity of actualR.
No abstract unitary, totality, or diagonalization hypothesis occurs.
-/

namespace ImbalancedChen.Part3.ActualResolventGlobalDiagonalization20261025a

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a
open ImbalancedChen.Part3.ActualResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.ActualResolventCyclicIntertwining20261025a
open ImbalancedChen.Part3.ActualResolventGlobalHilbertSum20261025a

/-- Uniformly bounded actual coordinate multiplication on every actual
scalar-measure fiber. No countability restriction on the family is needed. -/
def actualDiagonalResolvent : ActualSpectralSum →L[ℂ] ActualSpectralSum :=
  lp.mapCLM 2 (fun i : ActualSpectralIndex => coordinateMultiplier (i : HyperbolicL2))
    zero_le_one (fun i => coordinateMultiplier_opNorm_le_one (i : HyperbolicL2))

theorem actualDiagonalResolvent_apply (ξ : ActualSpectralSum) (i : ActualSpectralIndex) :
    actualDiagonalResolvent ξ i = coordinateMultiplier (i : HyperbolicL2) (ξ i) := rfl

theorem actualDiagonalResolvent_opNorm_le_one : ‖actualDiagonalResolvent‖ ≤ 1 :=
  lp.norm_mapCLM_le 2
    (fun i : ActualSpectralIndex => coordinateMultiplier (i : HyperbolicL2))
    zero_le_one (fun i => coordinateMultiplier_opNorm_le_one (i : HyperbolicL2))

/-- The diagonal entries are actual multiplication by the spectral
coordinate, almost everywhere for the actual RMK scalar measures. -/
theorem actualDiagonalResolvent_coordinate_ae (ξ : ActualSpectralSum)
    (i : ActualSpectralIndex) :
    actualDiagonalResolvent ξ i =ᵐ[scalarMeasure (i : HyperbolicL2)]
      (fun t : ResolventSpectrum => (t : ℂ) * (ξ i) t) :=
  coordinateMultiplier_coe_ae (i : HyperbolicL2) (ξ i)

theorem actualFiberEmbedding_intertwine (i : ActualSpectralIndex)
    (ξ : ActualSpectralFiber i) :
    actualFiberEmbedding i (coordinateMultiplier (i : HyperbolicL2) ξ) =
      actualWeakResolvent (actualFiberEmbedding i ξ) :=
  cyclicExtension_intertwine (i : HyperbolicL2) ξ

/-- Global intertwining follows from two actual convergent sums and the
proved cyclic intertwining. No summation or diagonalization supplier. -/
theorem actualSpectralUnitary_intertwine (ξ : ActualSpectralSum) :
    actualSpectralUnitary (actualDiagonalResolvent ξ) =
      actualWeakResolvent (actualSpectralUnitary ξ) := by
  have hleft := actualSpectralUnitary_hasSum (actualDiagonalResolvent ξ)
  have hright := actualWeakResolvent.hasSum (actualSpectralUnitary_hasSum ξ)
  have hterms :
      (fun i : ActualSpectralIndex => actualFiberEmbedding i (actualDiagonalResolvent ξ i)) =
        (fun i : ActualSpectralIndex => actualWeakResolvent (actualFiberEmbedding i (ξ i))) := by
    funext i
    rw [actualDiagonalResolvent_apply]
    exact actualFiberEmbedding_intertwine i (ξ i)
  rw [hterms] at hleft
  exact hleft.unique hright

/-- The actual resolvent in the whole-space scalar spectral coordinates. -/
theorem actualResolvent_spectral_coordinates (f : HyperbolicL2) :
    actualSpectralUnitary.symm (actualWeakResolvent f) =
      actualDiagonalResolvent (actualSpectralUnitary.symm f) := by
  apply actualSpectralUnitary.injective
  rw [actualSpectralUnitary.apply_symm_apply, actualSpectralUnitary_intertwine,
    actualSpectralUnitary.apply_symm_apply]

/-- Operator-level conjugacy, for the original actual weak resolvent. -/
theorem actualResolvent_unitary_conjugacy :
    actualWeakResolvent =
      actualSpectralUnitary.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (actualDiagonalResolvent.comp
          actualSpectralUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext f
  change actualWeakResolvent f =
    actualSpectralUnitary (actualDiagonalResolvent (actualSpectralUnitary.symm f))
  rw [actualSpectralUnitary_intertwine, actualSpectralUnitary.apply_symm_apply]

end
end ImbalancedChen.Part3.ActualResolventGlobalDiagonalization20261025a
