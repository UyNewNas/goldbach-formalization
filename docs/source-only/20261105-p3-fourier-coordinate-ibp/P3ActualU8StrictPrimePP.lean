import ImbalancedChen.P3ActualU8DirectUnitPayment
import ImbalancedChen.P3ActualU8SharpKOffshift
import Mathlib.Tactic

/-!
P3.6: remove the actual terminal p₂=q diagonal from the U8
ANALYTIC prime-product obligation, rather than deleting its labels.

The genuine positive counting inequality is applied ONLY to the
strict p₂<q labelled triple source. All repeated-terminal labels,
the original small Goldbach-prime exception (strict cutoff P<z),
and quotient-one pair labels are paid directly by existing actual
source cardinality budgets. Neither the signed physical coefficient
nor the primitive-coprime mean is changed within the strict source.

This is SOURCE_ONLY until the pinned Lean dependency chain elaborates.
It does NOT prove PP for the hard strict source, nor identify final rho_T.
-/

namespace ImbalancedChen.P3ActualU8StrictPrimePP

noncomputable section
open scoped BigOperators
open Filter Topology
open ImbalancedChen.P5U8SharpKSource
open ImbalancedChen.P3ActualU8SharpKOffshift

/-- Exact finite prime-count partition BEFORE applying any sieve:
the inclusive q=p₂ part is not discarded, merely kept as a separate
directly bounded summand with its original multiplicity. -/
theorem actual_u8_prime_mass_strict_diagonal (N : ℕ) :
    p5z_labelledPrimeMass (arithmeticTriples N) product
        (fun _ => (1 : ℝ)) N =
      p5z_labelledPrimeMass (strictTriples N) product
        (fun _ => (1 : ℝ)) N +
      p5z_labelledPrimeMass (diagonalTriples N) product
        (fun _ => (1 : ℝ)) N := by
  unfold p5z_labelledPrimeMass
  exact actual_u8_sum_partition N
    (fun t => if product t < N ∧ Nat.Prime (N - product t)
      then (1 : ℝ) else 0)

/-- The ACTUAL eighth count needs signed prime-product discrepancy
only for the strict sorted p₁<p₂<q source. The inclusive terminal
q=p₂ triples and quotient-one pairs remain in the counting bound,
both with genuine labels. The strict source uses one physical Q/rho in
its density, exact coprime correction, and signed discrepancy.

The hypothesis hmajor is the genuine pointwise sieve-majorant, NOT
a PP error hypothesis. This does not assert that the hard strict
indicator is automatically a smooth admissible W_N. -/
theorem actual_u8_upper_via_strict_prime_PP
    (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hz : (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    currentChenUpsilon8 N ≤
      p5z_labelledMass (strictTriples N) (fun _ => (1 : ℝ)) *
        physicalDensitySum Q rho +
      p5z_labelledCoprimeCorrection (strictTriples N) product
        (fun _ => (1 : ℝ)) Q rho +
      p5z_labelledDistributionError (strictTriples N) product
        (fun _ => (1 : ℝ)) N Q rho +
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
      ((diagonalTriples N).card : ℝ) +
      ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  classical
  have hcount : currentChenUpsilon8 N =
      p5z_labelledPrimeMass (arithmeticTriples N) product
        (fun _ => (1 : ℝ)) N +
      ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
    have hproduct : p5z_labelledPrimeMass (Finset.range N) id
        (productWeight N) N =
        p5z_labelledPrimeMass (arithmeticTriples N) product
          (fun _ => (1 : ℝ)) N := by
      simpa only [p5z_labelledPrimeMass, id_eq, mul_ite,
        mul_one, mul_zero] using
        (productWeight_sum N (fun m =>
          if m < N ∧ Nat.Prime (N - m) then (1 : ℝ) else 0))
    rw [currentChenUpsilon8_eq_primeMass_add_units, hproduct]
  have hdiag : p5z_labelledPrimeMass (diagonalTriples N) product
      (fun _ => (1 : ℝ)) N ≤
      ((diagonalTriples N).card : ℝ) := by
    unfold p5z_labelledPrimeMass
    calc
      (∑ t ∈ diagonalTriples N,
        if product t < N ∧ Nat.Prime (N - product t)
        then (1 : ℝ) else 0) ≤
          ∑ _t ∈ diagonalTriples N, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            split_ifs <;> norm_num
      _ = _ := by simp
  have hsmallPart :
      p5z_labelledSmallPrimeMass (arithmeticTriples N) product
          (fun _ => (1 : ℝ)) N z =
        p5z_labelledSmallPrimeMass (strictTriples N) product
          (fun _ => (1 : ℝ)) N z +
        p5z_labelledSmallPrimeMass (diagonalTriples N) product
          (fun _ => (1 : ℝ)) N z := by
    unfold p5z_labelledSmallPrimeMass
    exact actual_u8_sum_partition N
      (fun t => if product t < N ∧ Nat.Prime (N - product t) ∧
          N - product t < z then (1 : ℝ) else 0)
  have hsmallDiag : 0 ≤
      p5z_labelledSmallPrimeMass (diagonalTriples N) product
        (fun _ => (1 : ℝ)) N z := by
    unfold p5z_labelledSmallPrimeMass
    apply Finset.sum_nonneg
    intro t ht
    split_ifs <;> norm_num
  have hsmallFull :
      p5z_labelledSmallPrimeMass (arithmeticTriples N) product
        (fun _ => (1 : ℝ)) N z ≤
        ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) := by
    have hproduct : p5z_labelledSmallPrimeMass (Finset.range N)
        id (productWeight N) N z =
        p5z_labelledSmallPrimeMass (arithmeticTriples N) product
          (fun _ => (1 : ℝ)) N z := by
      simpa only [p5z_labelledSmallPrimeMass, id_eq, mul_ite,
        mul_one, mul_zero] using
        (productWeight_sum N (fun m =>
          if m < N ∧ Nat.Prime (N - m) ∧ N - m < z
          then (1 : ℝ) else 0))
    rw [← hproduct]
    exact P3ActualU8DirectUnitPayment.actual_u8_small_prime_PP_loss_le_source_count
      N z hz
  have hsmallStrict :
      p5z_labelledSmallPrimeMass (strictTriples N) product
        (fun _ => (1 : ℝ)) N z ≤
        ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) := by
    linarith only [hsmallPart, hsmallDiag, hsmallFull]
  have hstrict := p5z_labelledPrimeMass_le_main_add_errors
    (strictTriples N) product (fun _ => (1 : ℝ))
    N z Q rho
    (by intro t ht; norm_num)
    (by
      intro t ht
      exact (arithmetic_product_lt (Finset.mem_filter.mp ht).1).le)
    hmajor
  rw [hcount, actual_u8_prime_mass_strict_diagonal N]
  linarith only [hstrict, hdiag, hsmallStrict]

/-- All direct losses (small Goldbach primes, repeated terminal
p₂=q, and quotient-one pairs) are o(H_N), with a threshold chosen
before z, Q or rho. Only the actual STRICT labelled triple signed PP
still needs arithmetic cancellation. This does not supply that bound. -/
theorem eventually_actual_u8_upper_via_strict_prime_PP
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ),
        (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) →
        (∀ n : ℕ,
          (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
            physicalDivisorSum Q rho n) →
        currentChenUpsilon8 N ≤
          p5z_labelledMass (strictTriples N) (fun _ => (1 : ℝ)) *
            physicalDensitySum Q rho +
          p5z_labelledCoprimeCorrection (strictTriples N) product
            (fun _ => (1 : ℝ)) Q rho +
          p5z_labelledDistributionError (strictTriples N) product
            (fun _ => (1 : ℝ)) N Q rho +
          ε * singularNormalization N := by
  have hsource :=
    eventually_currentChenUpsilon8_sourceErrors_le_singularNormalization
      (ε / 2) (half_pos hε)
  have hdiag :=
    eventually_powerLog_le_singularNormalization
      1 (2 / 3) 0 (by norm_num) (ε / 2) (half_pos hε)
  filter_upwards [hsource, hdiag,
    Filter.eventually_ge_atTop (1 : ℕ)] with N hs hd hN z Q rho hz hmajor
  have hdiagPower := diagonal_card_le_power hN
  have hdiagBudget :
      ((diagonalTriples N).card : ℝ) ≤
        (ε / 2) * singularNormalization N :=
    hdiagPower.trans (by simpa only [one_mul, pow_zero, mul_one] using hd)
  have hfinite := actual_u8_upper_via_strict_prime_PP N z Q rho hz hmajor
  linarith only [hs, hdiagBudget, hfinite]

end
end ImbalancedChen.P3ActualU8StrictPrimePP
