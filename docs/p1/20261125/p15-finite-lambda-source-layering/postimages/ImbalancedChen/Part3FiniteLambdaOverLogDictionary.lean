import ImbalancedChen.Part3FiniteLambdaOverLogCore
import ImbalancedChen.P5SortedPlainPPExactPrimeCharts
import ImbalancedChen.Part3ActualOriginalProperPowerChartBridge
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready=false.
-- Pinned mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 supplies
-- vonMangoldt_apply_pow, vonMangoldt_apply_prime, vonMangoldt_eq_zero_iff,
-- and isPrimePow_nat_iff. No new foundational Lambda theorem is assumed.

namespace ImbalancedChen.Part3.FiniteLambdaOverLogDictionary

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.SortedPlainPPExactPrimeCharts
open OriginalProperPowerActualChart

-- Defining n<=1 as zero avoids the totalized 0/0 at n=1. All genuine
-- prime and proper-power entries are >=2, so this changes no source term.







-- This finite identity includes n=1 (coefficient zero), prime n
-- (coefficient one), composite prime powers, and all other zero terms.
-- It counts each natural n once, so no permutation or representation
-- multiplicity is silently discarded.

-- Every term in the second finite sum carries the exact 1/e coefficient.
-- The pinned isPrimePow_nat_iff gives p and e; e=1 is excluded by ¬Prime.

-- Apply the exact one-natural-coordinate dictionary to a word in the
-- actual sorted independent-u prime carrier. `u.set` retains occurrence
-- positions and the original chartTerm eta/psi/W, with no rho or physical
-- mark t introduced. This is algebraic: the composite W support and
-- pointwise amplitude needed to pay its absolute sum are Phase7 guards.
theorem sorted_prime_chart_one_slot_lambda_split
    (N : ℕ) (tau : ℝ) (input : List ℕ)
    (u : List ℕ) (hu : u ∈ sortedWord N tau input)
    (chi eta : ℝ → ℝ) (W F : List ℕ → ℂ)
    (T kappa0 : ℝ) (js : List ℕ)
    (hjs : js ∈ chartBank (carrierCap (sortedWord N tau input)) input.length)
    (i : Fin input.length) :
    u.length = input.length ∧
    js.length = input.length ∧
    let cap := carrierCap (sortedWord N tau input)
    let G : ℕ → ℂ := fun n =>
      chartTerm chi eta W T kappa0 js (u.set i.val n) *
        F (u.set i.val n)
    (∑ n ∈ Finset.Icc 1 cap, (lambdaOverLog n : ℂ) * G n) =
      (∑ p ∈ (Finset.Icc 1 cap).filter Nat.Prime, G p) +
      (∑ n ∈ (Finset.Icc 1 cap).filter
        (fun n => IsPrimePow n ∧ ¬n.Prime),
        (lambdaOverLog n : ℂ) * G n) := by
  have hlen := (sortedWord_prime_data N tau input hu).1
  have hjlen := (words_spec
    (Finset.range (cutoffIndex (carrierCap (sortedWord N tau input))+1))
    input.length js hjs).1
  refine ⟨hlen,hjlen,?_⟩
  exact finite_lambdaOverLog_split
    (carrierCap (sortedWord N tau input))
    (fun n => chartTerm chi eta W T kappa0 js (u.set i.val n) *
      F (u.set i.val n))

end
end ImbalancedChen.Part3.FiniteLambdaOverLogDictionary
