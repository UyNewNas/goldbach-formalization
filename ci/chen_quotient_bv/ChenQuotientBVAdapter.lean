/-
SPDX-License-Identifier: Apache-2.0

HELD, UNCOMPILED CONSUMER CANDIDATE. No Lean/Lake execution, kernel replay,
axiom audit, publication, or owned-core integration has been performed for
this candidate. The new finite dependency must also be verified first.

The sole foreign root is reused through ChenInitialBVAdapter, whose frozen
source SHA-256 is 4347879db98115050861b9afd3313573524710610464c8b6c688a43eb9c530e5:
  MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional
at subfish-zhou/goldbach-lean commit 09b97db5764ade1246bfb77206baa1b124760958.
That approved ordinary-BV closure has 270 production modules and nine
Architect support modules. This file adds no foreign module to that closure.
The adjacent LICENSE is the unchanged upstream Apache-2.0 license.

Lean leanprover/lean4:v4.33.0-rc1;
Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1;
LeanArchitect 78dd66840d3efe8c824c699fc03381cec817c271.
-/
import ImbalancedChen.ChenQuotientBVFinite
import ImbalancedChen.ChenInitialBVAdapter

/-!
# Actual ordinary-BV consumer for all four selected quotient remainder sums

The bound is on the original third through sixth selected quotient-sieve
remainders. Each inner row can vary independently, but every full product
modulus b*d must lie below the single literal logarithmic square-root cap.

The secondary base error is preserved and paid by active-row pooling,
not discarded. The finite four-term cost is
  4 * [1 + 4 * (1 + log(max(1,Q)))] * E_Q + full centre cost.
At log N >= 1 and Q <= N its AP coefficient is at most 36 log N.
The genuine approved maximal ordinary-BV theorem is invoked at K+2:
one extra logarithm pays active-row pooling and one absorbs its fixed
constant. The nonnegative level exponent B is chosen before epsilon.

There is no analytic estimate premise. This is a distribution conclusion
only, not a lower-sieve mean estimate, the coefficient 1.8271, or a Chen theorem.
-/

namespace ImbalancedChen.ChenQuotientBVAdapter

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory.BombieriVinogradov
open scoped BigOperators
open Classical

/-- The actual centre residue is reduced to its canonical class without
changing the inclusive AP count, including the unique class modulo one. -/
theorem abs_chenQuotientPrimeAPError_le_supplier (N k : ℕ)
    (hk : 0 < k) (hcop : Nat.Coprime k N) :
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k| ≤
      standardPrimeAPPrefixMaxError N k := by
  have hcount : chenPrimeAPCount N N k = chenPrimeAPCount N (N % k) k := by
    unfold chenPrimeAPCount
    apply congrArg (fun S : Finset ℕ => (S.card : ℝ))
    ext P
    constructor
    · intro hP
      obtain ⟨hPc, hmod⟩ := Finset.mem_filter.mp hP
      exact Finset.mem_filter.mpr ⟨hPc, by
        simpa only [Nat.ModEq, Nat.mod_mod] using hmod⟩
    · intro hP
      obtain ⟨hPc, hmod⟩ := Finset.mem_filter.mp hP
      exact Finset.mem_filter.mpr ⟨hPc, by
        simpa only [Nat.ModEq, Nat.mod_mod] using hmod⟩
  have hres := (mem_finiteReducedResidues (N % k) k).mp
    ((mod_mem_finiteReducedResidues_iff N k hk).mpr hcop.symm)
  rw [chenQuotientPrimeAPError, hcount]
  exact ChenInitialBVAdapter.abs_chenPrimeAPCount_sub_supplier_main_le_prefixMax
    N k (N % k) hres.1 hres.2

/-- The actual primitive AP pool is controlled by the supplier's genuine
prefix-and-residue maximum; no endpoint maximum is silently substituted. -/
theorem sum_chenQuotientPrimeAPError_le_supplier (N Q R : ℕ) (hQ : Q ≤ R) :
    (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
      |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
      ∑ k ∈ Finset.Icc 1 R, standardPrimeAPPrefixMaxError N k := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        standardPrimeAPPrefixMaxError N k := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkQ, hcop⟩ := Finset.mem_filter.mp hk
      exact abs_chenQuotientPrimeAPError_le_supplier N k
        (Finset.mem_Icc.mp hkQ).1 hcop
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨hk1, hkQ⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
        exact Finset.mem_Icc.mpr ⟨hk1, hkQ.trans hQ⟩
      · intro k _ _
        exact standardPrimeAPPrefixMaxError_nonneg N k

/-- One logarithm pays the four secondary active-row pools. Q=0 is
covered by the literal max; the requested asymptotic is only at large N. -/
theorem four_pool_logCoefficient_le (N Q : ℕ) (hN1 : 1 ≤ (N : ℝ))
    (hQ : (Q : ℝ) ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ)) :
    4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) ≤
      36 * Real.log (N : ℝ) := by
  have hpos : (0 : ℝ) < max 1 (Q : ℝ) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlogQ := Real.log_le_log hpos (max_le hN1 hQ)
  linarith

/-- Actual all-four selected quotient BV, with the level chosen before
epsilon and every eventual row choice. No analytic premise is required. -/
theorem exists_logLevel_chenUpsilon36_remainder_logAccuracy (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in atTop, ∀ hN : Even N, ∀ Q : ℕ,
          ∀ S₃ S₄ : ℕ → Finset ℕ, ∀ S₅ S₆ : (ℕ × ℕ) → Finset ℕ,
          Q ≤ Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) →
          ChenUpsilon36Rows N Q S₃ S₄ S₅ S₆ →
          chenUpsilon36RemainderSum N hN S₃ S₄ S₅ S₆ ≤
            epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
      ((K + 2 : ℕ) : ℝ) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  filter_upwards
    [hBV,
      ChenInitialBVAdapter.eventually_two_mul_supplier_bound_le_half_accuracy
        (18 * C) K epsilon hepsilon,
      eventually_chenUpsilon36CentreCost_le_of_rows K
        (epsilon / 2) (half_pos hepsilon),
      eventually_one_le_nat_log, eventually_ge_atTop (2 : ℕ)]
    with N hBVN hconstant hcost hlog hN2
  intro hN Q S₃ S₄ S₅ S₆ hQ hrows
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hQproducer : Q ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
    rwa [ChenInitialBVAdapter.supplier_cutoff_eq_sqrt_level]
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hQcast : (Q : ℝ) ≤
        (Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) : ℝ) := by
      exact_mod_cast hQ
    exact hQcast.trans (ChenInitialBVAdapter.sqrt_log_level_cast_le_sqrt N B hlog hB)
  have hQN : (Q : ℝ) ≤ (N : ℝ) := hQsqrt.trans
    (Real.sqrt_le_self_iff.mpr (Or.inr hN1))
  have hBVnatural :
      (∑ k ∈ Finset.Icc 1 (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
        standardPrimeAPPrefixMaxError N k) ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 2) := by
    simpa only [Real.rpow_natCast] using hBVN hN2
  have hpool := (sum_chenQuotientPrimeAPError_le_supplier N Q _ hQproducer).trans
    hBVnatural
  have hcoeff0 : 0 ≤ 4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) := by
    have h : 0 ≤ Real.log (max 1 (Q : ℝ)) := Real.log_nonneg (le_max_left _ _)
    positivity
  have hpay :
      (4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        (C * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 2))) ≤
          (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
    calc
      _ ≤ (36 * Real.log (N : ℝ)) *
          (C * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 2)) :=
        mul_le_mul_of_nonneg_right (four_pool_logCoefficient_le N Q hN1 hQN hlog)
          (div_nonneg (mul_nonneg hC.le (Nat.cast_nonneg N))
            (pow_nonneg hlogpos.le (K + 2)))
      _ = 2 * ((18 * C) * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 1)) := by
        rw [show K + 2 = (K + 1) + 1 by omega, pow_succ]
        field_simp [hlogpos.ne']
        ring
      _ ≤ _ := hconstant
  calc
    _ ≤ (4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ))))) *
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) +
            chenUpsilon36CentreCost N S₃ S₄ S₅ S₆ :=
      chenUpsilon36RemainderSum_le_primitive_log_add_cost N Q hN
        (trueLogarithmicIntegral N) S₃ S₄ S₅ S₆ hrows
    _ ≤ (4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ))))) *
        (C * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 2)) +
          (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K :=
      add_le_add (mul_le_mul_of_nonneg_left hpool hcoeff0)
        (hcost hN Q S₃ S₄ S₅ S₆ hQsqrt hrows)
    _ ≤ (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K +
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K :=
      add_le_add hpay le_rfl
    _ = epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by ring

end

end ImbalancedChen.ChenQuotientBVAdapter
