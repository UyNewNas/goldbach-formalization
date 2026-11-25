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
def lambdaOverLog (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else
    ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)

theorem lambdaOverLog_zero : lambdaOverLog 0 = 0 := by
  simp [lambdaOverLog]

theorem lambdaOverLog_one : lambdaOverLog 1 = 0 := by
  simp [lambdaOverLog]

theorem lambdaOverLog_prime {p : ℕ} (hp : p.Prime) :
    lambdaOverLog p = 1 := by
  have hnot : ¬p ≤ 1 := by omega
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  simp only [lambdaOverLog, if_neg hnot,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact div_self hlog

theorem lambdaOverLog_prime_pow {p e : ℕ} (hp : p.Prime)
    (he : 2 ≤ e) : lambdaOverLog (p ^ e) = 1 / (e : ℝ) := by
  have hepos : 0 < e := by omega
  have hpow : 1 < p ^ e := hp.one_lt.trans_le (Nat.le_pow hepos)
  have hnot : ¬p ^ e ≤ 1 := by omega
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have heReal : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hepos)
  calc
    lambdaOverLog (p ^ e) =
        Real.log (p : ℝ) / ((e : ℝ) * Real.log (p : ℝ)) := by
          simp only [lambdaOverLog, if_neg hnot,
            ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hepos),
            ArithmeticFunction.vonMangoldt_apply_prime hp,
            Nat.cast_pow, Real.log_pow]
    _ = 1 / (e : ℝ) := by field_simp [hlog, heReal] <;> ring

theorem lambdaOverLog_off_prime_powers {n : ℕ} (hn : ¬IsPrimePow n) :
    lambdaOverLog n = 0 := by
  by_cases hsmall : n ≤ 1
  · simp [lambdaOverLog, hsmall]
  · simp only [lambdaOverLog, if_neg hsmall,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]

theorem lambdaOverLog_pointwise_split (n : ℕ) :
    lambdaOverLog n = (if n.Prime then 1 else 0) +
      (if IsPrimePow n ∧ ¬n.Prime then lambdaOverLog n else 0) := by
  by_cases hp : n.Prime
  · simp [hp, lambdaOverLog_prime hp]
  · by_cases hpp : IsPrimePow n
    · simp [hp, hpp]
    · simp [hp, hpp, lambdaOverLog_off_prime_powers hpp]

-- This finite identity includes n=1 (coefficient zero), prime n
-- (coefficient one), composite prime powers, and all other zero terms.
-- It counts each natural n once, so no permutation or representation
-- multiplicity is silently discarded.
theorem finite_lambdaOverLog_split (cap : ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 cap, (lambdaOverLog n : ℂ) * F n) =
      (∑ p ∈ (Finset.Icc 1 cap).filter Nat.Prime, F p) +
      (∑ n ∈ (Finset.Icc 1 cap).filter
        (fun n => IsPrimePow n ∧ ¬n.Prime),
        (lambdaOverLog n : ℂ) * F n) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [hp, lambdaOverLog_prime hp]
  · by_cases hpp : IsPrimePow n
    · simp [hp, hpp]
    · simp [hp, hpp, lambdaOverLog_off_prime_powers hpp]

-- Every term in the second finite sum carries the exact 1/e coefficient.
-- The pinned isPrimePow_nat_iff gives p and e; e=1 is excluded by ¬Prime.
theorem proper_term_has_prime_exponent {n : ℕ}
    (hproper : IsPrimePow n ∧ ¬n.Prime) :
    ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e ∧
      lambdaOverLog n = 1 / (e : ℝ) := by
  obtain ⟨p,e,hp,he,hpow⟩ := (isPrimePow_nat_iff n).mp hproper.1
  have he2 : 2 ≤ e := by
    by_contra hne
    have he1 : e = 1 := by omega
    have hnprime : n.Prime := by
      rw [← hpow, he1, pow_one]
      exact hp
    exact hproper.2 hnprime
  refine ⟨p,e,hp,he2,hpow,?_⟩
  rw [← hpow]
  exact lambdaOverLog_prime_pow hp he2

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
