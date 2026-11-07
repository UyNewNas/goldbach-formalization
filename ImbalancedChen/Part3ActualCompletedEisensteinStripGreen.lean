import ImbalancedChen.Part3PeriodicCuspStripStokes
import ImbalancedChen.Part3ActualCompletedGreenCurrentRegularity
import ImbalancedChen.Part3ActualEisensteinHorocycleGreenFlux
import Mathlib.Tactic

/-!
# Exact actual completed Eisenstein Green identity on a finite cusp strip

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
All derivatives, C1 regularity, periodicity and eigen-equations are proved
suppliers for the ACTUAL continued completed Eisenstein family. Native
finite-strip Stokes gives the exact top-minus-bottom horocycle flux.
The hyperbolic pairing keeps its literal 1/y^2 density. No spectral gap,
Green identity, boundary cancellation or completeness is assumed.
The actual high-cusp estimate then replaces only the upper flux by its
exact completed-constant flux, with an explicit exponentially small error.
-/
namespace ImbalancedChen.Part3.ActualCompletedEisensteinStripGreen20261026b
noncomputable section
open Set MeasureTheory
open scoped Topology Interval
open PeriodicCuspStripStokes20261026b
open CompletedEisensteinReflection20261025a ContinuedFourierSpatialContDiffTwo
open ActualEisensteinHorocycleGreenFlux20261026b
open ActualCompletedEisensteinGreenInterior20261026b ActualCompletedGreenCurrentRegularity20261026b
open CompletedEisensteinCuspTail20261025a ActualEisensteinHeightDerivativeTail20261026b

def stripHyperbolicPairing (s u : ℂ) (Y T : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, ∫ y in Y..T,
    star (completedEisensteinFourier s y x) * completedEisensteinFourier u y x / (y : ℂ) ^ 2

def greenSpectralDifference (s u : ℂ) : ℂ := star (s * (1 - s)) - u * (1 - u)

/-- True finite-strip Green identity for the actual family, with exact
physical dy dx / y^2 interior density and the actual two horocycle fluxes. -/
theorem actual_completed_eisenstein_strip_green (s u : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    {Y T : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) :
    greenSpectralDifference s u * stripHyperbolicPairing s u Y T =
      (∫ x in (0 : ℝ)..1, actualGreenCurrent s u T x) -
        ∫ x in (0 : ℝ)..1, actualGreenCurrent s u Y x := by
  have hx : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => actualGreenCurrentX s u p.2 p.1) positiveStripChart :=
    actualGreenCurrentX_contDiffOn_one s u
  have hy : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => actualGreenCurrent s u p.2 p.1) positiveStripChart :=
    actualGreenCurrent_contDiffOn_one s u
  have hp : ∀ y : ℝ, 0 < y → Function.Periodic
      (fun x : ℝ => actualGreenCurrentX s u y x) 1 :=
    fun y hy => actualGreenCurrentX_periodic s u hs0 hs1 hu0 hu1 y hy
  have hstokes := periodic_positive_strip_stokes
    (fun p : ℝ × ℝ => actualGreenCurrentX s u p.2 p.1)
    (fun p : ℝ × ℝ => actualGreenCurrent s u p.2 p.1) hx hy hp hY hYT
  have hmass :
      (∫ x in (0 : ℝ)..1, ∫ y in Y..T,
        stripDivergence (fun p : ℝ × ℝ => actualGreenCurrentX s u p.2 p.1)
          (fun p : ℝ × ℝ => actualGreenCurrent s u p.2 p.1) (x,y)) =
        greenSpectralDifference s u * stripHyperbolicPairing s u Y T := by
    calc
      _ = ∫ x in (0 : ℝ)..1, ∫ y in Y..T,
          greenSpectralDifference s u *
            (star (completedEisensteinFourier s y x) * completedEisensteinFourier u y x / (y : ℂ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x _
        apply intervalIntegral.integral_congr
        intro y hyR
        have hy0 : 0 < y := hY.trans_le (by simpa only [min_eq_left hYT] using hyR.1)
        unfold stripDivergence greenSpectralDifference
        rw [actualGreen_fderiv_divergence_eq s u hs0 hs1 hu0 hu1 x y hy0]
        ring
      _ = _ := by
        simp_rw [intervalIntegral.integral_const_mul]
        rfl
  rw [hmass] at hstokes
  exact hstokes

/-- Both upper and lower completed constants remain exact. Replacing
ONLY the upper actual flux costs the proved exponentially small remainder;
the lower actual boundary is retained without an asymptotic assumption. -/
theorem actual_completed_strip_upper_boundary_error (M : ℕ) {s u : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hu : |u.re| ≤ (M : ℝ))
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    {Y T : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) (hT : 1 ≤ T) :
    ‖greenSpectralDifference s u * stripHyperbolicPairing s u Y T -
      constantGreenCurrent s u T + (∫ x in (0 : ℝ)..1, actualGreenCurrent s u Y x)‖ ≤
      2 * (cuspTailConstant M * derivativeTailConstant M) *
        (Real.exp (-(Real.pi / 2) * T)) ^ 2 := by
  rw [actual_completed_eisenstein_strip_green s u hs0 hs1 hu0 hu1 hY hYT]
  have heq :
      ((∫ x in (0 : ℝ)..1, actualGreenCurrent s u T x) -
        (∫ x in (0 : ℝ)..1, actualGreenCurrent s u Y x)) - constantGreenCurrent s u T +
        (∫ x in (0 : ℝ)..1, actualGreenCurrent s u Y x) =
      (∫ x in (0 : ℝ)..1, actualGreenCurrent s u T x) - constantGreenCurrent s u T := by ring
  rw [heq]
  exact actualGreenCurrent_constant_error_bound M hs hu hs0 hs1 hu0 hu1 hT

end
end ImbalancedChen.Part3.ActualCompletedEisensteinStripGreen20261026b
