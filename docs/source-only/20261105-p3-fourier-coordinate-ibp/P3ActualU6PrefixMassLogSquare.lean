import ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
import ImbalancedChen.P3ActualRawActiveLevelTotientCap
import ImbalancedChen.P3ActualPhysicalTotientConvolution
import Mathlib.Tactic

/-!
P3.6 manuscript-internal successor: the literal sixth-selector pair prefix
mass, previously exposed but UNPAID in the all-U6 primitive ledger.

The source is the actual `sixthSupport N` at the original prime bands
N^(417/5000), N^(19/125), N^(59/250), with its pair labels, not a
substituted quotient rho. Every selected component is an original
additive-prime-carrier member, hence in [1,N]. The reciprocal totient
product inequality requires only positive factors; it is therefore safe
without asserting a new coprimality or density hypothesis. The all-row
integer LOWER coefficient, full physical modulus b*q, signs, and
discrepancy term are preserved via the preceding exact ledger.

This pays only the PHYSICAL PREFIX reciprocal-totient mass. It does not
supply the common Rosser level A(N), the signed offshift discrepancy,
the final global rho_N, or the PP estimate.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6PrefixMassLogSquare
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5SelectedMaskTransport
open ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualSignedPairTotientCap
open ImbalancedChen.P3ActualPhysicalTotientConvolution

/-- The genuine U6 selector is a SUBSET of the square of the original
positive integer prime carrier, with no artificial product cut. -/
theorem original_U6_selector_subset_positive_prefix (N : ℕ) :
    sixthSupport N ⊆ (Finset.Icc 1 N).product (Finset.Icc 1 N) := by
  classical
  intro t ht
  have hraw : t ∈ chenY6PrimeSelector N
      ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)) := ht
  unfold chenY6PrimeSelector at hraw
  obtain ⟨hp, hq⟩ :=
    Finset.mem_product.mp (Finset.mem_filter.mp hraw).1
  obtain ⟨hpN, hpprime, _⟩ :=
    mem_chenAdditivePrimeCarrier_iff_le.mp hp
  obtain ⟨hqN, hqprime, _⟩ :=
    mem_chenAdditivePrimeCarrier_iff_le.mp hq
  have hpPos : 1 ≤ t.1 := by
    have h := hpprime.two_le
    omega
  have hqPos : 1 ≤ t.2 := by
    have h := hqprime.two_le
    omega
  have hpBound : t.1 ≤ N := by omega
  have hqBound : t.2 ≤ N := by omega
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpPos, hpBound⟩,
     Finset.mem_Icc.mpr ⟨hqPos, hqBound⟩⟩

/-- The previously unpaid actual U6 physical prefix mass costs at
most TWO finite logarithmic reciprocal-totient envelopes. No prime
distribution statement is used. The sum retains each original pair
label and is not over distinct products. -/
theorem original_U6_prefix_mass_le_log_square (N : ℕ) :
    originalU6PrefixMass N ≤ (logTotientCap N) ^ 2 := by
  classical
  let K := Finset.Icc 1 N
  let S : ℝ := ∑ a ∈ K, (Nat.totient a : ℝ)⁻¹
  have hsub : sixthSupport N ⊆ K.product K :=
    original_U6_selector_subset_positive_prefix N
  have hcap : S ≤ logTotientCap N :=
    sum_reciprocal_totient_le_log N
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a ha => by positivity)
  calc
    originalU6PrefixMass N =
        ∑ t ∈ sixthSupport N,
          (Nat.totient (t.1 * t.2) : ℝ)⁻¹ := rfl
    _ ≤ ∑ t ∈ sixthSupport N,
          (Nat.totient t.1 : ℝ)⁻¹ *
            (Nat.totient t.2 : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro t ht
          obtain ⟨hp, hq⟩ := Finset.mem_product.mp (hsub ht)
          exact reciprocal_totient_product_le t.1 t.2
            (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hq).1
    _ ≤ ∑ t ∈ K.product K,
          (Nat.totient t.1 : ℝ)⁻¹ *
            (Nat.totient t.2 : ℝ)⁻¹ := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun t ht hnot => by positivity)
    _ = S * S := by
          simp only [K, S, Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ logTotientCap N * logTotientCap N := by
          calc
            S * S ≤ logTotientCap N * S :=
              mul_le_mul_of_nonneg_right hcap hS
            _ ≤ logTotientCap N * logTotientCap N :=
              mul_le_mul_of_nonneg_left hcap (logTotientCap_nonneg N)
    _ = (logTotientCap N) ^ 2 := by ring

/-- Actual ALL labelled even-first-exit LOWER rows: the prefix-mass
factor is now paid by a fixed two-log envelope. The common A(N) and
actual signed nonzero-shift discrepancy remain separate INTERNAL jobs.
The Mertens constant is unchanged and chosen before N, A, policy, w,L. -/
theorem exists_all_original_U6_quotient_correction_with_paid_prefix :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (hN : 2 ≤ N)
        (policy : (ℕ × ℕ) → List ℕ → Bool)
        (w L : (ℕ × ℕ) → ℝ),
        (∀ t ∈ sixthSupport N,
          w t ≤ P5CausalRhoQuotientBridge.cutoff N) →
        (∀ t ∈ sixthSupport N, L t ≤ (A : ℝ)) →
        |∑ t ∈ sixthSupport N,
          rowQuotientPrimeCorrection N policy w L t| ≤
          (logTotientCap N) ^ 2 *
            (logTotientCap A * (C * (1 + Real.log (N : ℝ))) *
              ((Nat.log 2 A : ℝ) + C * (1 + Real.log (N : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_all_original_U6_quotient_prime_correction_bound
  refine ⟨C, hC, ?_⟩
  intro N A hN policy w L hwz hLA
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    have h := hN
    exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hU : 0 ≤ C * (1 + Real.log (N : ℝ)) :=
    mul_nonneg (le_of_lt hC) (by linarith)
  have hF :
      0 ≤ logTotientCap A * (C * (1 + Real.log (N : ℝ))) *
          ((Nat.log 2 A : ℝ) + C * (1 + Real.log (N : ℝ))) :=
    mul_nonneg
      (mul_nonneg (logTotientCap_nonneg A) hU)
      (add_nonneg (by positivity) hU)
  exact (hbound N A hN policy w L hwz hLA).trans
    (mul_le_mul_of_nonneg_right
      (original_U6_prefix_mass_le_log_square N) hF)

end
end ImbalancedChen.P3ActualU6PrefixMassLogSquare
