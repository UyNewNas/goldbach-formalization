import ImbalancedChen.Part3GenericResolventCyclicIntertwining
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Injective generic self-adjoint operators have no scalar zero atom

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

On the genuine scalar-measure L2 quotient the coordinate multiplier
intertwines the actual bounded self-adjoint operator through the proved
cyclic isometry. Injectivity of the operator therefore forces injectivity
of the coordinate multiplier. The actual L2 indicator of the zero fiber
is killed by that multiplier, hence is zero, so the zero fiber is null.

The absence of an atom, the indicator norm, any weighted-measure identity,
positivity, contraction, and spectral projection operators are not input
premises. H and R are arbitrary; no whole-plane or actual Gamma0 alias is
used. This is a bounded scalar-measure primitive for downstream bindings.
-/

namespace ImbalancedChen.Part3.GenericResolventScalarZeroAtom20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

/-- Injectivity transports through the ACTUAL cyclic isometry and its
proved coordinate intertwining, with no spectral-kernel premise. -/
theorem coordinateMultiplier_injective (hRinj : Function.Injective R) (f : H) :
    Function.Injective (coordinateMultiplier R hSA f) := by
  intro ξ η hξη
  apply (cyclicIsometry R hSA f).injective
  change cyclicExtension R hSA f ξ = cyclicExtension R hSA f η
  apply hRinj
  exact ((cyclicExtension_intertwine R hSA f ξ).symm.trans
    (congrArg (cyclicExtension R hSA f) hξη)).trans
      (cyclicExtension_intertwine R hSA f η)

/-- The genuine scalar RMK measure has no zero-coordinate atom for any
vector whenever the actual bounded self-adjoint operator is injective. -/
theorem scalarMeasure_zeroFiber (hRinj : Function.Injective R) (f : H) :
    scalarMeasure R hSA f {t : ResolventSpectrum R | (t : ℝ) = 0} = 0 := by
  classical
  let μ := scalarMeasure R hSA f
  let B : Set (ResolventSpectrum R) := {t | (t : ℝ) = 0}
  have hB : MeasurableSet B := by
    dsimp only [B]
    fun_prop
  have hμB : μ B ≠ ∞ := measure_ne_top μ B
  let ξ : ScalarL2 R hSA f := indicatorConstLp 2 hB hμB (1 : ℂ)
  have hξae : ξ =ᵐ[μ] B.indicator (fun _ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have hMξ : coordinateMultiplier R hSA f ξ = 0 := by
    apply Lp.ext
    filter_upwards [coordinateMultiplier_coe_ae R hSA f ξ, hξae,
      Lp.coeFn_zero ℂ 2 μ] with t hM hξ h0
    rw [hM,hξ,h0]
    by_cases ht : t ∈ B
    · have ht0 : (t : ℝ) = 0 := ht
      rw [Set.indicator_of_mem ht]
      simp only [ht0,Complex.ofReal_zero,zero_mul]
    · rw [Set.indicator_of_notMem ht,mul_zero]
  have hξzero : ξ = 0 := (coordinateMultiplier_injective R hSA hRinj f)
    (hMξ.trans (map_zero (coordinateMultiplier R hSA f)).symm)
  have hindicator : B.indicator (fun _ => (1 : ℂ)) =ᵐ[μ] (fun _ => 0) := by
    have hzero : ξ =ᵐ[μ] (fun _ => 0) := by
      rw [hξzero]
      exact Lp.coeFn_zero ℂ 2 μ
    exact hξae.symm.trans hzero
  have hnot : ∀ᵐ t ∂μ, t ∉ B := by
    filter_upwards [hindicator] with t ht
    intro hmem
    have hone : (1 : ℂ) = 0 := by
      simpa only [Set.indicator_of_mem hmem] using ht
    exact one_ne_zero hone
  have hnull : μ B = 0 := by
    simpa only [not_not] using (ae_iff.mp hnot)
  exact hnull

theorem scalarMeasure_ae_coordinate_ne_zero (hRinj : Function.Injective R) (f : H) :
    ∀ᵐ t ∂scalarMeasure R hSA f, (t : ℝ) ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not] using scalarMeasure_zeroFiber R hSA hRinj f

end
end ImbalancedChen.Part3.GenericResolventScalarZeroAtom20261025a
