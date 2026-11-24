import ImbalancedChen.P2Winner9OriginalTerminal
import ImbalancedChen.P4AOriginalFull87SourcePrimeTests

/-!
SOURCE ONLY / NOT COMPILED.

The literal Winner9 terminal is the original Full87 cell `.remaining (.nine 11)`.
For P1, import the existing original Full87 owner instead of the isolated
extracted definition cores. The original full cell alphabet, all literal rows,
and `P4AOriginalFull87SourcePrimeTests.cellIntegral` retain their original
owners. The already verified bridge proof bodies below are unchanged.
This import adaptation still needs its combined P1 Lean check.

The density retains the factor 4 in `eq:current-eighth-saving` of the 20261106
manuscript, without a Chen quarter or an ordering factorial.
-/

namespace ImbalancedChen.P2Winner9OriginalFull87Bridge

noncomputable section

open scoped BigOperators
open Set MeasureTheory
open P2Winner9OriginalTerminal
open P4AOriginalFull87SourceDictionary (Point)

set_option maxRecDepth 20000

/-- All 97 tagged rows, including every coefficient, are the original cell's
literal rows in the original order. -/
theorem terminal41_rows_eq_original :
    terminal41Rows = P4AOriginalSeed7Unequal15Literal.nineRows 11 := by
  rfl

/-- Equality of the actual open source sets, not merely inclusion of the
finite archive vertices or equality up to a numerical sample. -/
theorem terminal41_source_eq_original :
    terminal41Source =
      P4AOriginalFull87StrictActionTrim.sourceSet (.remaining (.nine 11)) := by
  change {t : Point | ∀ j : Fin 97,
      0 < ((terminal41Rows j).2 0 : ℝ) +
        ∑ k : Fin 8, ((terminal41Rows j).2 k.succ : ℝ) * t k} =
    {t : Point | ∀ j : Fin 97,
      0 < ((P4AOriginalSeed7Unequal15Literal.nineRows 11 j).2 0 : ℝ) +
        ∑ k : Fin 8,
          ((P4AOriginalSeed7Unequal15Literal.nineRows 11 j).2 k.succ : ℝ) * t k}
  rw [terminal41_rows_eq_original]

theorem terminal41_comparison_eq_original (t : Point) :
    terminal41Comparison t =
      P4AOriginalFull87SourceDictionary.comparison (.remaining (.nine 11)) t := by
  rfl

private theorem original_selected_sum (t : Point) :
    P4AOriginalRemainingEighthSources.selectedSum (.nine 11) t =
      t 1 + t 3 + t 7 := by
  change (∑ i ∈ ({1, 3, 7} : Finset (Fin 8)), t i) = t 1 + t 3 + t 7
  rw [Finset.sum_insert (by decide : (1 : Fin 8) ∉ ({3, 7} : Finset (Fin 8))),
    Finset.sum_insert (by decide : (3 : Fin 8) ∉ ({7} : Finset (Fin 8))),
    Finset.sum_singleton]
  exact (add_assoc _ _ _).symm

theorem terminal41_newCap_eq_original (t : Point) :
    terminal41NewCap t =
      P4AOriginalFull87SourceDictionary.newCap (.remaining (.nine 11)) t := by
  change terminal41NewCap t =
    VariableEnvelope.A (P4AOriginalRemainingEighthSources.selectedSum (.nine 11) t) -
      P4AOriginalRemainingEighthSources.eta
  rw [original_selected_sum]
  rfl

/-- Equality of the full real density, including both residual denominators
and the eight coordinate factors, on every ambient point. -/
theorem terminal41_kernel_eq_original (t : Point) :
    terminal41Kernel t =
      P4AOriginalFull87EighthKernelControl.kernel (.remaining (.nine 11)) t := by
  simp only [P4AOriginalFull87EighthKernelControl.kernel,
    P4AOriginalFull87EighthKernelControl.residual,
    P4AOriginalFull87EighthKernelControl.total,
    P4AOriginalFull87EighthKernelControl.product,
    ← terminal41_comparison_eq_original, ← terminal41_newCap_eq_original,
    terminal41Kernel]

/-- The target uses the original fully qualified integral declaration. -/
theorem terminal41_integral_eq_original :
    P2Winner9OriginalTerminal.terminal41Integral =
      P4AOriginalFull87SourcePrimeTests.cellIntegral (.remaining (.nine 11)) := by
  simp only [P2Winner9OriginalTerminal.terminal41Integral,
    P4AOriginalFull87SourcePrimeTests.cellIntegral,
    terminal41_source_eq_original, terminal41_kernel_eq_original]

end
end ImbalancedChen.P2Winner9OriginalFull87Bridge
