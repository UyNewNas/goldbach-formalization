import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Source-only exact declaration extraction for the actual U5 count consumer.
No elaboration or kernel acceptance is claimed. -/
namespace ImbalancedChen.P1OriginalSharpFiniteReceiver
noncomputable section
open Classical Filter
open scoped BigOperators

abbrev cut (N : ℕ) := Nat.floor ((N:ℝ)^(9/20:ℝ))


end
end ImbalancedChen.P1OriginalSharpFiniteReceiver

namespace ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
noncomputable section
open Classical
open scoped BigOperators

def primeMass (N : ℕ) : ℝ := ((chenPrimePrefix N).card : ℝ)


def densityTest (d : ℕ) : ℝ := 1 / (Nat.totient d : ℝ)


end
end ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger

namespace ImbalancedChen.P4AOriginalFull87SignedSharpReceiver
noncomputable section
open Classical
open P4AOriginalFull87EighthPrimeMeanLedger
open scoped BigOperators

def sharpPrimeError (N d : ℕ) : ℝ :=
  chenPrimeAPCount N N d - primeMass N * densityTest d

end
end ImbalancedChen.P4AOriginalFull87SignedSharpReceiver

