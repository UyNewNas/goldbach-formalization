import ImbalancedChen.Part3ElementaryCRTSpacing

/-!
# Arbitrary-residue divisor payment with the exact lcm denominator

SOURCE PROPOSAL ONLY -- UNCOMPILED -- HOLD -- 2026-10-22.
The future CRTSpacing import is the uncompiled source proposal SHA256
3efe260ca0e39d4316ebffece2598b95ff3dba3c70e352dd927600959a8fd5b0.
Its RealEndpoint parent is accepted at source SHA256
5c386ee17594c075b81b15d56143284fd0f77364f87129d0a96632f17064f8ad.
No future import resolution, elaboration or kernel acceptance is asserted.
Every integer residue r is allowed, independently of any signed shift.
This pays the actual d_K sum by a finite weighted lcm sum. A subsequent
harmonic lcm/divisor splitting bound is still needed for the closed
d_K(q) logarithmic main term. General-q analytic M2 remains open.
-/

namespace ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A reusable weighted CRT payment on the original real-supported set. -/
theorem sum_real_supported_progression_divisor_weights_le_lcm
    (S : Finset ℕ) {a b : ℝ} {D q : ℕ} {r : ℤ} (w : ℕ → ℝ)
    (hab : a ≤ b) (hq : 0 < q)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b)
    (hmod : ∀ n ∈ S, Int.ModEq (q : ℤ) (n : ℤ) r)
    (hw : ∀ d ∈ Icc 1 D, 0 ≤ w d) :
    (∑ n ∈ S, ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), w d) ≤
      ∑ d ∈ Icc 1 D, w d * ((b - a) / (Nat.lcm d q : ℝ) + 1) := by
  rw [sum_real_supported_divisor_weights_swap]
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (hw d hd)
  apply card_real_supported_modEq_dvd_le_lcm (S.filter (fun n => d ∣ n))
    hab hq (by have := (Finset.mem_Icc.mp hd).1; omega)
  · intro n hn
    exact hS n (Finset.mem_filter.mp hn).1
  · intro n hn
    exact hmod n (Finset.mem_filter.mp hn).1
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- Sharp strict-floor truncation followed by the genuine progression payment. -/
theorem sum_fouvryTau_real_progression_floor_lcm_payment
    (S : Finset ℕ) {K q : ℕ} {r : ℤ} (hK : 2 ≤ K) (hq : 0 < q)
    {a b Z : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hZ : 2 ≤ Z) (hbZ : b ≤ Z)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b)
    (hmod : ∀ n ∈ S, Int.ModEq (q : ℤ) (n : ℤ) r) :
    (∑ n ∈ S, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * ∑ d ∈ Icc 1 ⌊realDeletionRadius K Z⌋₊,
        (fouvryTau (K - 1) d : ℝ) * ((b - a) / (Nat.lcm d q : ℝ) + 1) := by
  let D : ℕ := ⌊realDeletionRadius K Z⌋₊
  have hpoint : ∀ n ∈ S, (fouvryTau K n : ℝ) ≤
      (K : ℝ) * ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n),
        (fouvryTau (K - 1) d : ℝ) := by
    intro n hn
    have hnR : (0 : ℝ) < n :=
      lt_of_lt_of_le (by linarith : 0 < a) (hS n hn).1
    have hnpos : 0 < n := by exact_mod_cast hnR
    have hcut : n ^ (K - 1) < (D + 1) ^ K :=
      floor_radius_strict_cutoff hK (by linarith : 1 ≤ Z) ((hS n hn).2.trans hbZ)
    have hnat := fouvryTau_le_truncated_divisor_sum_strict hK
      (by omega : 1 ≤ n) hcut
    rw [truncated_divisor_carrier_eq hnpos] at hnat
    exact_mod_cast hnat
  calc
    (∑ n ∈ S, (fouvryTau K n : ℝ)) ≤
        ∑ n ∈ S, (K : ℝ) *
          ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (K : ℝ) * (∑ n ∈ S,
        ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * ∑ d ∈ Icc 1 D,
        (fouvryTau (K - 1) d : ℝ) * ((b - a) / (Nat.lcm d q : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left
        (sum_real_supported_progression_divisor_weights_le_lcm S
          (fun d => (fouvryTau (K - 1) d : ℝ)) hab hq hS hmod
          (fun d _hd => Nat.cast_nonneg (fouvryTau (K - 1) d)))
        (Nat.cast_nonneg K)

end
end ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
