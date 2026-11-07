import ImbalancedChen.Part3DistributionTargets
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWFamily
import Mathlib.NumberTheory.AbelSummation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal independently sieved prime coefficient with a frozen real
smooth weight. The estimate is derived from the pinned prime-interval SW
supplier by Abel summation. Its multiplier is the actual endpoint norm
plus the integral of the absolute derivative. The residue and both full
integer moduli are unchanged. No SW hypothesis for the weighted coefficient
is assumed. This is not the high-physical-modulus prime-product estimate.
-/

namespace ImbalancedChen.Part3.WeightedPrimeIntervalSW20261026b

noncomputable section
open Classical Finset MeasureTheory
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The original prime indicator times the actual frozen smooth weight. -/
def weightedPrimeCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  f n * primeSWBeta n

private def primeKernel (d h b n : ℕ) : ℝ :=
  (if n.Coprime h ∧ Nat.ModEq d n b then primeSWBeta n else 0) -
    (if n.Coprime (d*h) then primeSWBeta n else 0) / (d.totient : ℝ)

private theorem sum_primeKernel (S : Finset ℕ) (d h b : ℕ) :
    (∑ n ∈ S, primeKernel d h b n) =
      betaCoprimeAPDiscrepancy S primeSWBeta d h b := by
  simp only [primeKernel, Finset.sum_sub_distrib, ← Finset.sum_div,
    betaCoprimeAPDiscrepancy, coprimeMass]

/-- The weighted expression has the literal coprime mean; no total-prime
mass is substituted for the primitive mean. -/
theorem weighted_discrepancy_eq_sum (S : Finset ℕ) (f : ℝ → ℝ) (d h b : ℕ) :
    betaCoprimeAPDiscrepancy S (weightedPrimeCoefficient f) d h b =
      ∑ n ∈ S, f n * primeKernel d h b n := by
  unfold betaCoprimeAPDiscrepancy coprimeMass
  simp only [primeKernel, mul_sub, mul_div_assoc,
    Finset.sum_sub_distrib, Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hn' : n.Coprime h ∧ Nat.ModEq d n b <;>
      simp only [weightedPrimeCoefficient, hn', if_true, if_false, mul_zero]
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hn' : n.Coprime (d*h) <;>
      simp only [weightedPrimeCoefficient, hn', if_true, if_false, mul_zero,
        mul_div_assoc]

/-- A genuine derivative-weighted prime SW estimate. The constant is
chosen before the real interval, smooth weight, complete modulus, auxiliary
integer and moving primitive residue. The exact interval is (u,v]. -/
theorem weighted_prime_interval_SW (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T u v : ℝ,
      1 ≤ T → T ≤ u → u ≤ v → v ≤ 2*T →
      ∀ (f : ℝ → ℝ),
      (∀ t ∈ Set.Icc u v, DifferentiableAt ℝ f t) →
      IntegrableOn (deriv f) (Set.Icc u v) →
      ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy (primeSWInterval u v)
        (weightedPrimeCoefficient f) d h b| ≤
        (C*T*(fouvryTau 2 h : ℝ) / Real.log (2*T)^B) *
          (|f v| + ∫ t in Set.Ioc u v, |deriv f t|) := by
  obtain ⟨C,hC,hSW⟩ := primeSW_uniform_real B
  refine ⟨C,hC,?_⟩
  intro T u v hT hTu huv hv f hfd hfi d h hd hh b hb
  let c : ℕ → ℝ := fun n =>
    if Nat.floor u < n then primeKernel d h b n else 0
  let E : ℝ := C*T*(fouvryTau 2 h : ℝ) / Real.log (2*T)^B
  have hu0 : 0 ≤ u := by linarith
  have hprefix (t : ℝ) :
      (∑ n ∈ Finset.Icc 0 (Nat.floor t), c n) =
        betaCoprimeAPDiscrepancy (primeSWInterval u t) primeSWBeta d h b := by
    have hset : (Finset.Icc 0 (Nat.floor t)).filter
        (fun n => Nat.floor u < n) = Finset.Ioc (Nat.floor u) (Nat.floor t) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    change (∑ n ∈ Finset.Icc 0 (Nat.floor t),
      if Nat.floor u < n then primeKernel d h b n else 0) = _
    rw [← Finset.sum_filter, hset, sum_primeKernel]
    rfl
  have hprefix_zero : (∑ n ∈ Finset.Icc 0 (Nat.floor u), c n) = 0 := by
    rw [hprefix]
    simp [primeSWInterval, betaCoprimeAPDiscrepancy, coprimeMass]
  have hprefix_bound (t : ℝ) (ht : t ∈ Set.Icc u v) :
      |∑ n ∈ Finset.Icc 0 (Nat.floor t), c n| ≤ E := by
    rw [hprefix]
    exact hSW T u t hT hTu ht.1 (ht.2.trans hv) d h hd hh b hb
  have hsum : betaCoprimeAPDiscrepancy (primeSWInterval u v)
      (weightedPrimeCoefficient f) d h b =
      f v * (∑ n ∈ Finset.Icc 0 (Nat.floor v), c n) -
        ∫ t in Set.Ioc u v, deriv f t * ∑ n ∈ Finset.Icc 0 (Nat.floor t), c n := by
    rw [weighted_discrepancy_eq_sum]
    have heq : (∑ n ∈ primeSWInterval u v, f n * primeKernel d h b n) =
        ∑ n ∈ Finset.Ioc (Nat.floor u) (Nat.floor v), f n * c n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [c, if_pos (Finset.mem_Ioc.mp hn).1]
    rw [heq, sum_mul_eq_sub_sub_integral_mul c hu0 huv hfd hfi,
      hprefix_zero, mul_zero, sub_zero]
  have hmajor : IntegrableOn (fun t => |deriv f t| * E) (Set.Ioc u v) := by
    simpa only [Real.norm_eq_abs] using
      ((hfi.mono_set Set.Ioc_subset_Icc_self).norm.mul_const E)
  have hIntegral :
      |∫ t in Set.Ioc u v, deriv f t * ∑ n ∈ Finset.Icc 0 (Nat.floor t), c n| ≤
        (∫ t in Set.Ioc u v, |deriv f t|) * E := by
    have hi := norm_integral_le_of_norm_le hmajor (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hprefix_bound t ⟨ht.1.le,ht.2⟩) (abs_nonneg _))
    simpa only [Real.norm_eq_abs, integral_mul_const] using hi
  rw [hsum]
  calc
    _ ≤ |f v * (∑ n ∈ Finset.Icc 0 (Nat.floor v), c n)| +
        |∫ t in Set.Ioc u v, deriv f t * ∑ n ∈ Finset.Icc 0 (Nat.floor t), c n| :=
      abs_sub _ _
    _ ≤ |f v| * E + (∫ t in Set.Ioc u v, |deriv f t|) * E :=
      add_le_add (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hprefix_bound v ⟨huv,le_rfl⟩)
          (abs_nonneg _)) hIntegral
    _ = _ := by dsimp only [E]; ring

end
end ImbalancedChen.Part3.WeightedPrimeIntervalSW20261026b
