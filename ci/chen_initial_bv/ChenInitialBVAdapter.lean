/-
SPDX-License-Identifier: Apache-2.0

STATIC CONSUMER CANDIDATE. Held outside the owned project source tree.
At preparation, this file had not been elaborated, axiom-audited,
kernel-replayed, published, or integrated into the owned core.
Independent review was required before runtime.

The sole external root is the already approved production supplier at
subfish-zhou/goldbach-lean revision
09b97db5764ade1246bfb77206baa1b124760958:
MathlibNt/AnalyticNumberTheory/BombieriVinogradov/
  Bombieri1965Richert418Unconditional.lean.
Its 270 production-source modules and nine Architect support modules were
source-cold checked and kernel-replayed in run 37778759271. That validation
does not validate this new consumer. No held extension modules are imported.

Supplier interfaces and the elementary cutoff estimate are adapted from
that Apache-2.0 project. Original contributors retain their copyright; the
full upstream license is preserved in the adjacent LICENSE file. Source:
https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/LICENSE

Lean: leanprover/lean4:v4.33.0-rc1.
Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
LeanArchitect: 78dd66840d3efe8c824c699fc03381cec817c271.
Owned ChenInitialCorrectionBudget.lean frozen source SHA-256:
983e6ae56fcfecd1eeea5144c5c02c43b6535e25e51b657b2e830954eba4b264.
-/
import ImbalancedChen.ChenInitialCorrectionBudget
import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional

/-!
# Actual ordinary-BV supplier for the genuine initial Chen sieve

For every fixed natural accuracy A, a single real logarithmic level B >= 0
is chosen BEFORE epsilon. Eventually in N the actual absolute remainder
sum is at most epsilon * N / (log N)^A, uniformly in the real sieve cutoff,
the evenness proof, every smaller level D, and every primitive modulus
subset of [1,D]. The sum includes all positive primitive moduli, with no
squarefree restriction; modulus one is retained.

The supplier counts the literal inclusive prime prefix P <= N. An exact
finite-set bridge identifies that count with the owned chenPrimeAPCount.
The owned correction theorem retains both centre-prime corrections and
the NEGATIVE modulus-prime atom in its signed identity. Its proved positive
majorant is paid here; no correction or endpoint is silently discarded.

The actual unconditional standardBombieriVinogradov theorem is invoked at
A + 1. Its fixed constant is absorbed by the extra logarithm after N grows,
without changing B after epsilon is chosen. The result has no BV, PNT,
prime-distribution, or desired-conclusion hypothesis. This supplies only
initial-sieve distribution, not a lower-sieve estimate or a Chen theorem.
-/

namespace ImbalancedChen.ChenInitialBVAdapter

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory.BombieriVinogradov
open scoped BigOperators

/-- Exact inclusive AP-count bridge. There is no endpoint correction,
no coprimality mask on the prime source, and no large-N hypothesis. -/
theorem chenPrimeAPCount_eq_supplier (N a d : ℕ) :
    chenPrimeAPCount N a d = (primesInAP N d a : ℝ) := by
  classical
  unfold chenPrimeAPCount chenPrimePrefix primesInAP
  apply congrArg (fun S : Finset ℕ => (S.card : ℝ))
  ext p
  simp only [Finset.mem_filter]
  tauto

/-- The literal square-root level equals the supplier's rpow notation;
the logarithmic loss exponent remains real. -/
theorem supplier_cutoff_eq_sqrt_level (N : ℕ) (B : ℝ) :
    MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B =
      Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) := by
  unfold MathlibNt.SieveTheory.LiuWeight.panModulusCutoff
  rw [Real.sqrt_eq_rpow]

/-- The approved residue maximum controls every canonical primitive class,
including the unique class zero modulo one. -/
theorem abs_chenPrimeAPCount_sub_supplier_main_le_prefixMax
    (N d a : ℕ) (ha : a < d) (hacop : Nat.Coprime a d) :
    |chenPrimeAPCount N a d - trueLogarithmicIntegral N / (Nat.totient d : ℝ)| ≤
      standardPrimeAPPrefixMaxError N d := by
  rw [chenPrimeAPCount_eq_supplier]
  change |standardPrimeAPError N d a| ≤ standardPrimeAPPrefixMaxError N d
  have hunit : a ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hacop⟩
  exact (abs_standardPrimeAPError_le_max hunit).trans
    (standardPrimeAPMaxError_le_prefixMaxError N d)

/-- Finite triangle transfer to the actual supplier, preserving the owned
correction cost. Only a nonnegative extension of the modulus sum is used. -/
theorem sum_abs_chenInitial_rem_le_supplier_add_cost
    (N : ℕ) (z : ℝ) (hN : Even N) (D Q : ℕ) (S : Finset ℕ)
    (hD : D ≤ Q) (hS : S ⊆ chenInitialPrimitiveModuli N D) :
    (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d|) ≤
      2 * (∑ d ∈ Finset.Icc 1 Q, standardPrimeAPPrefixMaxError N d) +
        chenInitialCorrectionCost N S := by
  classical
  have hfinite := sum_abs_chenInitial_rem_le_ordinary_primeAP_budget
    N z hN D S hS
    (fun d => trueLogarithmicIntegral N / (Nat.totient d : ℝ))
    (standardPrimeAPPrefixMaxError N)
    (fun d _ a ha hacop =>
      abs_chenPrimeAPCount_sub_supplier_main_le_prefixMax N d a ha hacop)
  have hsubset : S ⊆ Finset.Icc 1 Q := by
    intro d hd
    obtain ⟨hd1, hdD, _⟩ := mem_chenInitialPrimitiveModuli.mp (hS hd)
    exact Finset.mem_Icc.mpr ⟨hd1, hdD.trans hD⟩
  have hsum : (∑ d ∈ S, standardPrimeAPPrefixMaxError N d) ≤
      ∑ d ∈ Finset.Icc 1 Q, standardPrimeAPPrefixMaxError N d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro d _ _
    exact standardPrimeAPPrefixMaxError_nonneg N d
  exact hfinite.trans (add_le_add
    (mul_le_mul_of_nonneg_left hsum (by norm_num)) le_rfl)

/-- Nonnegative real B puts the literal logarithmic level below sqrt N
once log N >= 1. This is the range of the proved correction estimate. -/
theorem sqrt_log_level_cast_le_sqrt (N : ℕ) (B : ℝ)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    (Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) : ℝ) ≤
      Real.sqrt (N : ℝ) := by
  have hden : 1 ≤ (Real.log (N : ℝ)) ^ B := Real.one_le_rpow hlog hB
  calc
    (Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) : ℝ) ≤
        Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B :=
      Nat.floor_le (div_nonneg (Real.sqrt_nonneg _) (by linarith))
    _ ≤ Real.sqrt (N : ℝ) := div_le_self (Real.sqrt_nonneg _) hden

/-- One extra fixed logarithm absorbs the supplier's constant after N
grows. The requested accuracy A is natural; the supplier uses real rpow. -/
theorem eventually_two_mul_supplier_bound_le_half_accuracy (C : ℝ) (A : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      2 * (C * (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 1)) ≤
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  have hlarge : ∀ᶠ N : ℕ in atTop,
      4 * C / epsilon ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 * C / epsilon))
  filter_upwards [hlarge, eventually_one_le_nat_log] with N hlargeN hlogN
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hscalar : 2 * C / Real.log (N : ℝ) ≤ epsilon / 2 := by
    apply (div_le_iff₀ hlogpos).mpr
    have hpaid := (div_le_iff₀ hepsilon).mp hlargeN
    nlinarith
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
    div_nonneg (Nat.cast_nonneg N) (pow_nonneg hlogpos.le A)
  calc
    2 * (C * (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 1)) =
        (2 * C / Real.log (N : ℝ)) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := by
      rw [pow_succ]
      field_simp [hlogpos.ne'] <;> ring
    _ ≤ (epsilon / 2) * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) :=
      mul_le_mul_of_nonneg_right hscalar hbase
    _ = (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring

/-- Genuine initial-Chen BV at every fixed natural logarithmic accuracy.
B is fixed before epsilon and before all eventual or finite choices.
There is no analytic hypothesis: the pinned unconditional supplier is
applied in this proof, and the actual correction is paid by the owned core. -/
theorem exists_logLevel_chenInitial_rem_logAccuracy (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N, ∀ D : ℕ, ∀ S : Finset ℕ,
          D ≤ Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) →
          S ⊆ chenInitialPrimitiveModuli N D →
          (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d|) ≤
            epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  obtain ⟨B, hB, C, _hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
      ((A + 1 : ℕ) : ℝ) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  filter_upwards
    [hBV,
      eventually_two_mul_supplier_bound_le_half_accuracy C A epsilon hepsilon,
      eventually_chenInitialCorrectionCost_le_logAccuracy A
        (epsilon / 2) (half_pos hepsilon),
      eventually_one_le_nat_log, eventually_ge_atTop (2 : ℕ)]
    with N hBVN hconstant hcost hlog hN2
  intro z hN D S hD hS
  have hDproducer : D ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
    rwa [supplier_cutoff_eq_sqrt_level]
  have hDsqrt : (D : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hDcast : (D : ℝ) ≤
        (Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) : ℝ) := by
      exact_mod_cast hD
    exact hDcast.trans (sqrt_log_level_cast_le_sqrt N B hlog hB)
  have hBVnatural :
      (∑ d ∈ Finset.Icc 1 (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
        standardPrimeAPPrefixMaxError N d) ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 1) := by
    simpa only [Real.rpow_natCast] using hBVN hN2
  calc
    (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d|) ≤
        2 * (∑ d ∈ Finset.Icc 1
          (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
          standardPrimeAPPrefixMaxError N d) + chenInitialCorrectionCost N S :=
      sum_abs_chenInitial_rem_le_supplier_add_cost N z hN D _ S hDproducer hS
    _ ≤ 2 * (C * (N : ℝ) / (Real.log (N : ℝ)) ^ (A + 1)) +
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
      add_le_add (mul_le_mul_of_nonneg_left hBVnatural (by norm_num))
        (hcost D S hDsqrt hS)
    _ ≤ (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A +
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
      add_le_add hconstant le_rfl
    _ = epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring

/-- The same theorem with its primitive-support condition written out:
every selected positive modulus at most D must be coprime to N. -/
theorem exists_logLevel_chenInitial_rem_logAccuracy_of_primitive_subset (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N, ∀ D : ℕ, ∀ S : Finset ℕ,
          D ≤ Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) →
          S ⊆ Finset.Icc 1 D → (∀ d ∈ S, Nat.Coprime d N) →
          (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d|) ≤
            epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  obtain ⟨B, hB, hbound⟩ := exists_logLevel_chenInitial_rem_logAccuracy A
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  filter_upwards [hbound epsilon hepsilon] with N hNbound
  intro z hN D S hD hS hcop
  apply hNbound z hN D S hD
  intro d hd
  obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp (hS hd)
  exact mem_chenInitialPrimitiveModuli.mpr ⟨hd1, hdD, hcop d hd⟩

/-- In particular, the literal allowed sieve-divisor remainder sum is
small at the same fixed level, uniformly in every real cutoff. -/
theorem exists_logLevel_chenInitial_sieve_rem_logAccuracy (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N, ∀ D : ℕ,
          D ≤ Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) →
          (∑ d ∈ Finset.Icc 1 D with d ∣ sieveProduct N (Nat.ceil z),
            |(chenInitialBoundingSieve N z hN).rem d|) ≤
              epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  obtain ⟨B, hB, hbound⟩ := exists_logLevel_chenInitial_rem_logAccuracy A
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  filter_upwards [hbound epsilon hepsilon] with N hNbound
  intro z hN D hD
  exact hNbound z hN D _ hD (chenInitial_sieve_moduli_subset N D z)

end

end ImbalancedChen.ChenInitialBVAdapter
