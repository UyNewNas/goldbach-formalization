import ImbalancedChen.Part3StandardModularCellCurvedStokes
import ImbalancedChen.Part3ActualFiniteCosetGreenDivergence
import Mathlib.Tactic

/-!
# Actual finite-coset trace Green identity on the curved standard cell

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The exact original finite-coset trace has proved C1 components and proved
signed spectral divergence. Genuine curved-cell Stokes therefore yields
its full four-boundary identity. All sides are retained: the held
side-cancellation API is neither imported nor assumed.
-/
namespace ImbalancedChen.Part3.ActualFiniteCosetCurvedCellGreen20261026b
noncomputable section
open Set MeasureTheory
open scoped Topology Interval
open StandardModularCellGraph20261026b StandardModularCellCurvedStokes20261026b
open PeriodicCuspStripStokes20261026b
open ActualFiniteCosetGreenDivergence20261026b LevelOldformScattering20261026a

def actualTraceCellPairing (N : ℕ) [NeZero N] (s u : ℂ) (T : ℝ) : ℂ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T,
    actualCosetTraceProduct N s u (x,y) / (y : ℂ) ^ 2

/-- Original actual trace top, curved bottom, right and left currents.
This definition preserves every side without a side-cancellation premise. -/
def actualTraceCellBoundary (N : ℕ) [NeZero N] (s u : ℂ) (T : ℝ) : ℂ :=
  (∫ x in (-(1 / 2 : ℝ))..(1 / 2), actualCosetTraceY N s u (x,T)) +
  (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
    lowerGraphFlux (actualCosetTraceX N s u) (actualCosetTraceY N s u) x) +
  (∫ y in modularBottom (1 / 2)..T, actualCosetTraceX N s u (1 / 2,y)) -
  (∫ y in modularBottom (-(1 / 2))..T, actualCosetTraceX N s u (-(1 / 2),y))

/-- True spectral-density/actual-boundary identity for the full original
finite-coset trace on the ACTUAL curved truncated modular cell. -/
theorem actual_finite_coset_curved_cell_green (N : ℕ) [NeZero N] (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    {T : ℝ} (hT : 1 ≤ T) :
    (star (s * (1 - s)) - u * (1 - u)) * actualTraceCellPairing N s u T =
      actualTraceCellBoundary N s u T := by
  have hstokes := standard_modular_cell_curved_stokes (actualCosetTraceX N s u)
    (actualCosetTraceY N s u) (actualCosetTraceX_contDiffOn_one N s u)
      (actualCosetTraceY_contDiffOn_one N s u) hT
  have hmass :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T,
        stripDivergence (actualCosetTraceX N s u) (actualCosetTraceY N s u) (x,y)) =
      (star (s * (1 - s)) - u * (1 - u)) * actualTraceCellPairing N s u T := by
    calc
      _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ∫ y in modularBottom x..T,
          (star (s * (1 - s)) - u * (1 - u)) * (actualCosetTraceProduct N s u (x,y) / (y : ℂ) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hxR
        apply intervalIntegral.integral_congr
        intro y hyR
        have hxCell : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
          simpa only [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] using hxR
        have hbottomT : modularBottom x ≤ T := (modularBottom_le_one x).trans hT
        have hy0 : 0 < y := (modularBottom_pos (modular_cell_interval_subset hxCell)).trans_le
          (by simpa only [min_eq_left hbottomT] using hyR.1)
        unfold stripDivergence
        rw [actualCosetTrace_divergence_eq N s u hs hu x y hy0]
        ring
      _ = _ := by
        simp_rw [intervalIntegral.integral_const_mul]
        rfl
  rw [hmass] at hstokes
  exact hstokes

end
end ImbalancedChen.Part3.ActualFiniteCosetCurvedCellGreen20261026b
