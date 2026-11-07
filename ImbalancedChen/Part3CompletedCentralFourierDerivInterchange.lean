import ImbalancedChen.Part3CompletedCentralParameterDomination
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Genuine central parameter differentiation under the ORIGINAL physical
Fourier integral, with its actual fourierPhase and every integer mode.
The positive height is arbitrary and integral horizontal dilation may have
either sign or be zero. Actual K normal convergence proves measurable
continuous traces, and the independently proved actual parameter bound
provides the integrable derivative majorant. The pinned dominated derivative
theorem is applied with every hypothesis proved. The full-level derivative
vanishes by its actual local reflection symmetry, not by assuming a Fourier
coefficient. This supplies finite oldform callers without an interchange
assumption.
-/

noncomputable section
open Set Complex Filter Metric MeasureTheory Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3.PrimeCentralFourierFunctional20261026b
open ImbalancedChen.Part3.PrimeCentralChannelDerivative20261026b
open ImbalancedChen.Part3.CompletedCentralParameterDomination20261026b

namespace ImbalancedChen.Part3.CompletedCentralFourierDerivInterchange20261026b

theorem completedFourier_hasDerivAt_center_zero (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun s : ℂ => completedEisensteinFourier s y x) 0 (1 / 2 : ℂ) := by
  simpa [completedActualEisenstein, horizontalPoint] using
    completedActual_hasDerivAt_center_zero (horizontalPoint y hy x)

/-- The original Fourier functional genuinely admits the derivative integral.
The local majorant is proved uniformly in the actual horizontal variable. -/
theorem completedFourier_integral_hasDerivAt_center (n k : ℤ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1,
      fourierPhase n x * completedEisensteinFourier s y ((k : ℝ) * x))
      (∫ x in (0 : ℝ)..1, fourierPhase n x *
        deriv (fun s : ℂ => completedEisensteinFourier s y ((k : ℝ) * x)) (1 / 2)) (1 / 2 : ℂ) := by
  obtain ⟨D, hDpos, hD⟩ := exists_completedFourier_center_derivative_bound y hy
  let F : ℂ → ℝ → ℂ := fun s x => fourierPhase n x * completedEisensteinFourier s y ((k : ℝ) * x)
  let F' : ℂ → ℝ → ℂ := fun s x => fourierPhase n x *
    deriv (fun w : ℂ => completedEisensteinFourier w y ((k : ℝ) * x)) s
  have hcont (s : ℂ) : Continuous (F s) :=
    (fourierPhase_continuous n).mul (completedFourier_scaled_continuous s hy k)
  have hzero (x : ℝ) : F' (1 / 2) x = 0 := by
    dsimp [F']
    rw [(completedFourier_hasDerivAt_center_zero y hy ((k : ℝ) * x)).deriv, mul_zero]
  have hmeas : ∀ᶠ s : ℂ in 𝓝 (1 / 2 : ℂ),
      AEStronglyMeasurable (F s) (volume.restrict (Ι (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall (fun s => (hcont s).aestronglyMeasurable)
  have hint : IntervalIntegrable (F (1 / 2)) volume 0 1 := (hcont _).intervalIntegrable 0 1
  have hderivmeas : AEStronglyMeasurable (F' (1 / 2)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    have he : F' (1 / 2) = fun _ : ℝ => (0 : ℂ) := funext hzero
    rw [he]
    exact aestronglyMeasurable_const
  have hbound : ∀ᵐ x : ℝ ∂volume, x ∈ Ι (0 : ℝ) 1 →
      ∀ s ∈ ball (1 / 2 : ℂ) (1 / 8 : ℝ), ‖F' s x‖ ≤ D := by
    apply Filter.Eventually.of_forall
    intro x hx s hs
    dsimp [F']
    rw [norm_mul, norm_fourierPhase, one_mul]
    exact hD s hs ((k : ℝ) * x)
  have hDint : IntervalIntegrable (fun _ : ℝ => D) volume 0 1 := intervalIntegrable_const
  have hdiff : ∀ᵐ x : ℝ ∂volume, x ∈ Ι (0 : ℝ) 1 →
      ∀ s ∈ ball (1 / 2 : ℂ) (1 / 8 : ℝ), HasDerivAt (fun w : ℂ => F w x) (F' s x) s := by
    apply Filter.Eventually.of_forall
    intro x hx s hs
    have hquarter : s ∈ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ) :=
      mem_closedBall.mpr (le_trans (mem_ball.mp hs).le (by norm_num))
    have hpole := quarter_disk_avoids_poles hquarter
    exact ((completedEisensteinFourier_analyticAt hy ((k : ℝ) * x) hpole.1 hpole.2)
      .differentiableAt.hasDerivAt).const_mul (fourierPhase n x)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ => D) (μ := volume) (a := 0) (b := 1)
    (ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8))
    hmeas hint hderivmeas hbound hDint hdiff
  simpa only [F, F'] using h.2

/-- Literal derivative/integral equality, rather than an integral merely
labelled as a derivative coefficient. -/
theorem completedFourier_deriv_integral_center (n k : ℤ) (y : ℝ) (hy : 0 < y) :
    deriv (fun s : ℂ => ∫ x in (0 : ℝ)..1,
      fourierPhase n x * completedEisensteinFourier s y ((k : ℝ) * x)) (1 / 2) =
      ∫ x in (0 : ℝ)..1, fourierPhase n x *
        deriv (fun s : ℂ => completedEisensteinFourier s y ((k : ℝ) * x)) (1 / 2) :=
  (completedFourier_integral_hasDerivAt_center n k y hy).deriv

theorem completedFourier_integral_hasDerivAt_center_zero (n k : ℤ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1,
      fourierPhase n x * completedEisensteinFourier s y ((k : ℝ) * x)) 0 (1 / 2 : ℂ) := by
  have h := completedFourier_integral_hasDerivAt_center n k y hy
  have hz (x : ℝ) : deriv (fun s : ℂ => completedEisensteinFourier s y ((k : ℝ) * x)) (1 / 2) = 0 :=
    (completedFourier_hasDerivAt_center_zero y hy ((k : ℝ) * x)).deriv
  simp only [hz, mul_zero, intervalIntegral.integral_zero] at h
  exact h

end ImbalancedChen.Part3.CompletedCentralFourierDerivInterchange20261026b
