import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget
import ImbalancedChen.P5zPositiveFamilyBudget
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The genuine U8 q=1 quotient fibre is already a literal finite count
with a power-saving source cardinality. The actual U8 counting insertion
therefore needs physical signed PP only for its original arithmetic
prime-quotient triples. It must NOT manufacture a separate modulus-
weighted PP obligation for q=1 quotient pairs merely to bound U8.

Preserves U8's inclusive repeated terminal prime, exact original
product weights and labels, a single signed physical rho, the exact
coprime correction, and a strict small-Goldbach-prime cutoff.
The majorant hypothesis is a pointwise finite sieve inequality, NOT
an assumed PP discrepancy or the desired U8 count inequality.
No particular integer physical rho_T is identified here.
-/

namespace ImbalancedChen.P3ActualU8DirectUnitPayment

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

/-- The genuine original small-prime cutoff mass is bounded by the
already existing actual small-Goldbach-prime triple count. This
retains inclusive equality at the power cutoff, the actual triple
labels (including q=p2), and the strict sieve cutoff P<z. -/
theorem actual_u8_small_prime_PP_loss_le_source_count (N z : ℕ)
    (hz : (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ)) :
    p5z_labelledSmallPrimeMass (Finset.range N) id
        (P5U8SharpKSource.productWeight N) N z ≤
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) := by
  classical
  let B : Finset P5U8SharpKSource.Triple :=
    (P5U8SharpKSource.arithmeticTriples N).filter fun t =>
      P5U8SharpKSource.product t < N ∧
        Nat.Prime (N - P5U8SharpKSource.product t) ∧
          N - P5U8SharpKSource.product t < z
  have hsubset : B ⊆ currentChenUpsilon8SmallGoldbachPrimeTriples N := by
    intro t ht
    obtain ⟨htA, _, hprime, hcut⟩ := Finset.mem_filter.mp ht
    have hactual : t ∈ currentChenUpsilon8PrimeTriples N := by
      rw [← P5U8SharpKSource.arithmetic_filter_prime_eq N]
      exact Finset.mem_filter.mpr ⟨htA, hprime⟩
    have hcutR : (((N - P5U8SharpKSource.product t) : ℕ) : ℝ) <
        (z : ℝ) := by
      exact_mod_cast hcut
    have hpower : (((N - P5U8SharpKSource.product t) : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 5 : ℝ) :=
      (hcutR.trans_le hz).le
    exact Finset.mem_filter.mpr
      ⟨hactual, by simpa only [P5U8SharpKSource.product] using hpower⟩
  have hF := P5U8SharpKSource.productWeight_sum N
    (fun m => if m < N ∧ Nat.Prime (N - m) ∧ N - m < z
      then (1 : ℝ) else 0)
  have hmass :
      p5z_labelledSmallPrimeMass (Finset.range N) id
          (P5U8SharpKSource.productWeight N) N z =
        ∑ t ∈ P5U8SharpKSource.arithmeticTriples N,
          if P5U8SharpKSource.product t < N ∧
              Nat.Prime (N - P5U8SharpKSource.product t) ∧
              N - P5U8SharpKSource.product t < z
          then (1 : ℝ) else 0 := by
    simpa only [p5z_labelledSmallPrimeMass, id_eq, mul_ite,
      mul_one, mul_zero] using hF
  have hcard :
      (∑ t ∈ P5U8SharpKSource.arithmeticTriples N,
        if P5U8SharpKSource.product t < N ∧
            Nat.Prime (N - P5U8SharpKSource.product t) ∧
            N - P5U8SharpKSource.product t < z
        then (1 : ℝ) else 0) = (B.card : ℝ) := by
    simp [B, Finset.sum_filter, Finset.card_eq_sum_ones]
  calc
    _ = (B.card : ℝ) := hmass.trans hcard
    _ ≤ ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset

/-- An exact U8 counting insertion, NOT a claimed analytic PP bound.
The q=1 *quotient* remains a directly paid source-count correction;
the physical sieve Q and its single signed rho occur only in the
genuine rank-three prime-quotient source. The majorant is independent
of the target distribution assertion and applies to all integers. -/
theorem actual_u8_upper_via_prime_PP_no_unit_PP
    (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hz : (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    currentChenUpsilon8 N ≤
      p5z_labelledMass (Finset.range N) (P5U8SharpKSource.productWeight N) *
        physicalDensitySum Q rho +
      p5z_labelledCoprimeCorrection (Finset.range N) id
        (P5U8SharpKSource.productWeight N) Q rho +
      Part3.primeProductSignedError 3 N N Q rho
        (P5U8SharpKSource.physicalWeight N) +
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
      ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  have hbase := p5z_labelledPrimeMass_le_main_add_errors
    (Finset.range N) id (P5U8SharpKSource.productWeight N)
    N z Q rho
    (fun m _ => P5U8SharpKSource.productWeight_nonneg N m)
    (fun m hm => (Finset.mem_range.mp hm).le) hmajor
  rw [P5U8SharpKSource.productWeight_distribution_eq_physicalPP] at hbase
  have hsmall := actual_u8_small_prime_PP_loss_le_source_count N z hz
  calc
    currentChenUpsilon8 N =
        p5z_labelledPrimeMass (Finset.range N) id
            (P5U8SharpKSource.productWeight N) N +
          ((currentChenUpsilon8UnitFibres N).card : ℝ) :=
      P5U8SharpKSource.currentChenUpsilon8_eq_primeMass_add_units N
    _ ≤ _ := by linarith only [hbase, hsmall]

/-- The source-error threshold is chosen BEFORE z, Q and rho. Thus
the existing power-saving unit and small-prime bounds are spent
uniformly without an L1 norm premise on any future physical rho_T.
Only the actual prime-triple signed PP remains to be estimated. -/
theorem eventually_actual_u8_upper_via_prime_PP_no_unit_PP
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ),
        (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) →
        (∀ n : ℕ,
          (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
            physicalDivisorSum Q rho n) →
        currentChenUpsilon8 N ≤
          p5z_labelledMass (Finset.range N) (P5U8SharpKSource.productWeight N) *
            physicalDensitySum Q rho +
          p5z_labelledCoprimeCorrection (Finset.range N) id
            (P5U8SharpKSource.productWeight N) Q rho +
          Part3.primeProductSignedError 3 N N Q rho
            (P5U8SharpKSource.physicalWeight N) +
          ε * singularNormalization N := by
  filter_upwards [
    eventually_currentChenUpsilon8_sourceErrors_le_singularNormalization ε hε
  ] with N hsource z Q rho hz hmajor
  have hbound := actual_u8_upper_via_prime_PP_no_unit_PP N z Q rho hz hmajor
  linarith only [hsource, hbound]

end

end ImbalancedChen.P3ActualU8DirectUnitPayment
