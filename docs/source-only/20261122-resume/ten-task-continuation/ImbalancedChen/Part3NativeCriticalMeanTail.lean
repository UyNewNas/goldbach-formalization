import ImbalancedChen.Part3CriticalConstantPairTail
import ImbalancedChen.Part3ActualCriticalScatteringEntry

/-! Apply the critical-pair tail criterion to the physical constant term
of the continued parabolic series in two arbitrary normalized cusp frames. -/

namespace ImbalancedChen.Part3.NativeCriticalMeanTail

noncomputable section
open MeasureTheory Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Classical
open ActualCharacterCuspExpansion20261110 ActualParabolicScatteringRows20261110
open ActualCriticalScatteringEntry20261110 ActualCriticalCuspEvaluation20261110
open CriticalEisensteinScattering20261025a CuspConstantModeTailL2SourceOnly
open CriticalConstantPairTail

/-- The existing mean in the observation frame at every positive height. -/
def nativeMean (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (t y : ℝ) : ℂ :=
  if hy : 0 < y then horocycleMean N hN g h y hy (criticalPoint t) else 0

/-- Away from the center the observed row is in tail L² exactly when both
its unit incoming channel and its outgoing scattering entry vanish. At
the center it is the sum of the two coefficients that must vanish. -/
theorem nativeMean_tailL2_iff (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    TailL2 (nativeMean N hN g h t) Y ↔
      if t = 0 then
        incoming N g h (criticalPoint t) 1 + continuedEntry N hN g h (criticalPoint t) = 0
      else
        nativeFrameOrbit N h ≠ nativeFrameOrbit N g ∧
          continuedEntry N hN g h (criticalPoint t) = 0 := by
  let A : ℂ := if nativeFrameOrbit N h = nativeFrameOrbit N g then 1 else 0
  let B := continuedEntry N hN g h (criticalPoint t)
  have hs : criticalPoint t = criticalParameter t := by
    unfold criticalPoint criticalParameter
    ring
  have hmean (y : ℝ) (hy : 0 < y) : nativeMean N hN g h t y = criticalPair t A B y := by
    rw [nativeMean, dif_pos hy]
    calc
      _ = incoming N g h (criticalPoint t) y +
          continuedEntry N hN g h (criticalPoint t) * (y : ℂ) ^ (1 - criticalPoint t) :=
        critical_native_constant_term N hN g h t y hy
      _ = _ := by
        by_cases e : nativeFrameOrbit N h = nativeFrameOrbit N g <;>
          simp [criticalPair, incoming, A, B, e, hs]
  have heq : TailL2 (nativeMean N hN g h t) Y ↔ TailL2 (criticalPair t A B) Y := by
    apply integrableOn_congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [hyperbolicEnergyDensity, hmean y (hY.trans hy)]
  rw [heq]
  by_cases ht : t = 0
  · subst t
    rw [if_pos rfl, criticalPair_zero_tailL2_iff hY]
    simp [A, B, incoming]
  · rw [if_neg ht, criticalPair_tailL2_iff ht hY]
    by_cases e : nativeFrameOrbit N h = nativeFrameOrbit N g <;> simp [A, B, e]

end
end ImbalancedChen.Part3.NativeCriticalMeanTail
