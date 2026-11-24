import ImbalancedChen.P4AOriginalFull87SourceDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! SOURCE ONLY / NOT COMPILED. Mechanical extraction of existing declarations.
See ../docs/source-only/20261124-p2-winner9-original-full87/DEFINITION_RECEIPT.json.
Names, types and bodies are retained. Original modules must import this core
and remove these declarations using the accompanying refactor patch. -/

namespace ImbalancedChen.P4AOriginalFull87EighthKernelControl
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

def total (t : Point) : ℝ := ∑ i, t i

def product (t : Point) : ℝ := ∏ i, t i

def residual (S J P M : ℝ) : ℝ := 4 * (M - P) / ((P - S) * (M - S) * J)

def kernel (c : Cell) (t : Point) : ℝ :=
  residual (total t) (product t) (comparison c t) (newCap c t)

end
end ImbalancedChen.P4AOriginalFull87EighthKernelControl

namespace ImbalancedChen.P4AOriginalFull87SourcePrimeTests
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim P4AOriginalFull87EighthKernelControl

def cellIntegral (c : Cell) : ℝ := ∫ t in sourceSet c, kernel c t

end
end ImbalancedChen.P4AOriginalFull87SourcePrimeTests
