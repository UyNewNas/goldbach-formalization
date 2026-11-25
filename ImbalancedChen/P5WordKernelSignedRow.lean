import ImbalancedChen.P5IndependentPrimeSourceWordDictionary
import ImbalancedChen.P5ProperPowerSignedMeanHBTransport

/-! Source-only exact declaration extraction for the actual U5 count consumer.
No elaboration or kernel acceptance is claimed. -/
namespace ImbalancedChen.P4BActualUpperTrimPayment
noncomputable section
open Classical Filter
open P5Z.IndependentPrimeSourceWordDictionary
open P5Z.ProperPowerSignedMeanHBTransport
open scoped BigOperators

theorem wordKernel_eq_signedRow (Q : Finset ℕ) (rho : ℕ → ℂ)
    (N : ℕ) (ps : List ℕ) :
    wordKernel Q rho N ps = signedRow Q rho N ps.prod := by
  unfold wordKernel signedRow
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  rw [residueKernel_real]
  by_cases hc : Nat.ModEq q ps.prod N <;>
    by_cases hg : ps.prod.Coprime q <;> simp [signedKernel, hc, hg]

end
end ImbalancedChen.P4BActualUpperTrimPayment

