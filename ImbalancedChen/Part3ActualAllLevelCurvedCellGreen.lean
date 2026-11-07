import ImbalancedChen.Part3StandardModularCellCurvedStokes
import ImbalancedChen.Part3ActualAllLevelGreenInterior
import Mathlib.Tactic

/-!
# Actual all-level completed Eisenstein Green identity on the curved cell

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The literal all-level native chart, its true C1 current, and its proved
Maass eigen-equation instantiate the genuine curved modular-cell Stokes
formula. The result keeps the original physical 1/y^2 pairing and all four
boundary pieces. No actual eigen-equation, Stokes identity, periodicity,
coset trace cancellation or final spectral normalization is an assumption.
-/
namespace ImbalancedChen.Part3.ActualAllLevelCurvedCellGreen20261026b
noncomputable section
open Set MeasureTheory
open scoped Topology Interval
open StandardModularCellGraph20261026b StandardModularCellCurvedStokes20261026b
open PeriodicCuspStripStokes20261026b
open AllLevelContinuedMaass20261026a LevelOldformScattering20261026a
open ActualAllLevelGreenInterior20261026b

def actualLevelCellPairing (N : ℕ) (s u : ℂ) (T : ℝ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T,
    star (completedLevelChart N s (x,y)) * completedLevelChart N u (x,y) / (y : ℂ) ^ 2

/-- The true all-level continued native family on the ACTUAL curved
standard cell, with every boundary trace retained for the separately
proved coset-trace S/T cancellation. -/
theorem actual_alllevel_standard_cell_green (N : ℕ) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    {T : ℝ} (hT : 1 ≤ T) :
    (star (s * (1 - s)) - u * (1 - u)) * actualLevelCellPairing N s u T =
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), actualLevelGreenCurrentY N s u T x) +
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), lowerGraphFlux
        (fun p : ℝ × ℝ => actualLevelGreenCurrentX N s u p.2 p.1)
        (fun p : ℝ × ℝ => actualLevelGreenCurrentY N s u p.2 p.1) x) +
      (∫ y in modularBottom (1 / 2)..T, actualLevelGreenCurrentX N s u y (1 / 2)) -
      (∫ y in modularBottom (-(1 / 2))..T, actualLevelGreenCurrentX N s u y (-(1 / 2))) := by
  have hX : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => actualLevelGreenCurrentX N s u p.2 p.1) positiveStripChart :=
    actualLevelGreenCurrentX_contDiffOn_one N s u
  have hY : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => actualLevelGreenCurrentY N s u p.2 p.1) positiveStripChart :=
    actualLevelGreenCurrentY_contDiffOn_one N s u
  have hstokes := standard_modular_cell_curved_stokes
    (fun p : ℝ × ℝ => actualLevelGreenCurrentX N s u p.2 p.1)
    (fun p : ℝ × ℝ => actualLevelGreenCurrentY N s u p.2 p.1) hX hY hT
  have hmass :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T,
        stripDivergence (fun p : ℝ × ℝ => actualLevelGreenCurrentX N s u p.2 p.1)
          (fun p : ℝ × ℝ => actualLevelGreenCurrentY N s u p.2 p.1) (x,y)) =
      (star (s * (1 - s)) - u * (1 - u)) * actualLevelCellPairing N s u T := by
    calc
      _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T,
          (star (s * (1 - s)) - u * (1 - u)) *
            (star (completedLevelChart N s (x,y)) * completedLevelChart N u (x,y) / (y : ℂ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hxR
        apply intervalIntegral.integral_congr
        intro y hyR
        have hxCell : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
          simpa only [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] using hxR
        have hxOpen := modular_cell_interval_subset hxCell
        have hbottomT : modularBottom x ≤ T := (modularBottom_le_one x).trans hT
        have hy0 : 0 < y := (modularBottom_pos hxOpen).trans_le
          (by simpa only [min_eq_left hbottomT] using hyR.1)
        unfold stripDivergence
        rw [actualLevelGreen_fderiv_divergence_eq N s u hs hu x y hy0]
        ring
      _ = _ := by
        simp_rw [intervalIntegral.integral_const_mul]
        rfl
  rw [hmass] at hstokes
  exact hstokes

end
end ImbalancedChen.Part3.ActualAllLevelCurvedCellGreen20261026b
