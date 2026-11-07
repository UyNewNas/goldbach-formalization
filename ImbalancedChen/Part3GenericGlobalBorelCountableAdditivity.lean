import ImbalancedChen.Part3GenericSpectralSumDominatedConvergence
import ImbalancedChen.Part3GenericCyclicBorelCountableAdditivity

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Strong countable additivity of the constructed global Borel projections.
The Borel family may have any countable index type. The spectral Hilbert
sum itself is unrestricted: Tannery is applied to squared coordinate
errors bounded by four times the summable coordinate norm squares.
Together with GenericGlobalBorelProjection this gives the full projection
algebra and strong countable additivity, without assuming a PVM.
-/

namespace ImbalancedChen.Part3.GenericGlobalBorelCountableAdditivity20261025a

noncomputable section
open Filter MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericCyclicBorelProjection20261025a
open ImbalancedChen.Part3.GenericCyclicBorelCountableAdditivity20261025a
open ImbalancedChen.Part3.GenericGlobalBorelProjection20261025a
open ImbalancedChen.Part3.GenericSpectralSumDominatedConvergence20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem diagonalBorel_finset_sum {ι : Type*}
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ j, MeasurableSet (B j))
    (hdisj : Pairwise (fun j k => Disjoint (B j) (B k)))
    (s : Finset ι) (ξ : SpectralSum R hSA) :
    (∑ j ∈ s, diagonalBorel R hSA (B j) (hB j) ξ) =
      diagonalBorel R hSA (finiteUnion R B s) (measurableSet_finiteUnion R B hB s) ξ := by
  classical
  ext i
  simpa only [lp.coeFn_sum, Finset.sum_apply, diagonalBorel_apply] using
    borelMultiplier_finset_sum R hSA (i : H) B hB hdisj s (ξ i)

theorem globalBorelProjection_finset_sum {ι : Type*}
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ j, MeasurableSet (B j))
    (hdisj : Pairwise (fun j k => Disjoint (B j) (B k)))
    (s : Finset ι) (u : H) :
    (∑ j ∈ s, globalBorelProjection R hSA (B j) (hB j) u) =
      globalBorelProjection R hSA (finiteUnion R B s) (measurableSet_finiteUnion R B hB s) u := by
  classical
  simpa only [globalBorelProjection_apply, map_sum] using
    congrArg (spectralUnitary R hSA)
      (diagonalBorel_finset_sum R hSA B hB hdisj s ((spectralUnitary R hSA).symm u))

theorem globalBorelProjection_finset_sum_norm_le {ι : Type*}
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ j, MeasurableSet (B j))
    (hdisj : Pairwise (fun j k => Disjoint (B j) (B k)))
    (s : Finset ι) (u : H) :
    ‖∑ j ∈ s, globalBorelProjection R hSA (B j) (hB j) u‖ ≤ ‖u‖ := by
  rw [globalBorelProjection_finset_sum R hSA B hB hdisj s u]
  exact globalBorelProjection_norm_le R hSA _ _ u

/-- Strong additivity first on the entire spectral direct sum, not only
on finitely supported vectors. -/
theorem diagonalBorel_hasSum {ι : Type*} [Countable ι]
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ j, MeasurableSet (B j))
    (hdisj : Pairwise (fun j k => Disjoint (B j) (B k))) (ξ : SpectralSum R hSA) :
    HasSum (fun j => diagonalBorel R hSA (B j) (hB j) ξ)
      (diagonalBorel R hSA (⋃ j, B j) (MeasurableSet.iUnion hB) ξ) := by
  classical
  let η := diagonalBorel R hSA (⋃ j, B j) (MeasurableSet.iUnion hB) ξ
  let F : Finset ι → SpectralSum R hSA := fun s => ∑ j ∈ s, diagonalBorel R hSA (B j) (hB j) ξ
  change Tendsto F atTop (𝓝 η)
  apply spectralSum_tendsto_of_dominated R hSA F η (fun i => 4 * ‖ξ i‖ ^ 2)
    ((spectralSum_summable_norm_sq R hSA ξ).mul_left 4)
  · intro i
    have hi := borelMultiplier_hasSum R hSA (i : H) B hB hdisj (ξ i)
    simpa only [HasSum, F, η, lp.coeFn_sum, Finset.sum_apply, diagonalBorel_apply] using hi
  · apply Filter.Eventually.of_forall
    intro s i
    have hfinite := borelMultiplier_finset_sum_norm_le R hSA (i : H) B hB hdisj s (ξ i)
    have hunion := borelMultiplier_norm_le R hSA (i : H)
      (⋃ j, B j) (MeasurableSet.iUnion hB) (ξ i)
    change ‖(∑ j ∈ s, diagonalBorel R hSA (B j) (hB j) ξ) i -
      diagonalBorel R hSA (⋃ j, B j) (MeasurableSet.iUnion hB) ξ i‖ ^ 2 ≤ _
    simp only [lp.coeFn_sum, Finset.sum_apply, diagonalBorel_apply]
    calc
      _ ≤ (‖∑ j ∈ s, borelMultiplier R hSA (i : H) (B j) (hB j) (ξ i)‖ +
          ‖borelMultiplier R hSA (i : H) (⋃ j, B j) (MeasurableSet.iUnion hB) (ξ i)‖) ^ 2 := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ (‖ξ i‖ + ‖ξ i‖) ^ 2 := by gcongr
      _ = 4 * ‖ξ i‖ ^ 2 := by ring

/-- The full global strong countable-additivity identity. The only
assumptions on sets are measurability and pairwise disjointness. -/
theorem globalBorelProjection_hasSum {ι : Type*} [Countable ι]
    (B : ι → Set (ResolventSpectrum R)) (hB : ∀ j, MeasurableSet (B j))
    (hdisj : Pairwise (fun j k => Disjoint (B j) (B k))) (u : H) :
    HasSum (fun j => globalBorelProjection R hSA (B j) (hB j) u)
      (globalBorelProjection R hSA (⋃ j, B j) (MeasurableSet.iUnion hB) u) := by
  have h := (spectralUnitary R hSA).toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (diagonalBorel_hasSum R hSA B hB hdisj ((spectralUnitary R hSA).symm u))
  simpa only [globalBorelProjection_apply] using h

end
end ImbalancedChen.Part3.GenericGlobalBorelCountableAdditivity20261025a
