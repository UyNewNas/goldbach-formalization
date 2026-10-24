import ImbalancedChen.Part5UpperTableLookup
import ImbalancedChen.P5ZU11MeasurableEnvelope

/-!
Actual H248 table measurability at the original U11 ordinary-kernel interface.
SOURCE ONLY. H430 is deliberately absent from this adapter's statements.
No ordinary candidate is proved to estimate the actual U11 source here.
-/

namespace ImbalancedChen.P5Z.U11Integral

noncomputable section

open MeasureTheory

theorem measurable_original_H248_ordinaryKernel
    (L : ℕ → LogFour → ℝ) (j : ℕ) (hL : Measurable (L j)) :
    Measurable (ordinaryKernel Part5UpperTables.H248 L j) :=
  measurable_ordinaryKernel Part5UpperTables.H248 L j
    Part5UpperTables.measurable_H248 hL

/-- Exact connection to the finite-atom dictionary, retaining the max-two query. -/
theorem original_H248_ordinaryKernel_eq_base_sub
    (L : ℕ → LogFour → ℝ) (j : ℕ) (v : LogFour) :
    ordinaryKernel Part5UpperTables.H248 L j v =
      4 / L j v -
        Part5UpperTables.upperRoot Part5UpperTables.H248Numerators (L j v / v 3) *
          (4 / L j v) := by
  dsimp [ordinaryKernel, Part5UpperTables.H248, Part5UpperTables.upperRoot]
  ring

end
end ImbalancedChen.P5Z.U11Integral
