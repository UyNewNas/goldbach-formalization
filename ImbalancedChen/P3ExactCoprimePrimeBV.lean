import ImbalancedChen.Part3PrimeAPDistribution
import ImbalancedChen.BoundaryLogMesh

/-! Classical prime BV for the literal finite-coprime discrepancy of the
inclusive prime prefix. The physical coefficients may vary after the
modulus cutoff, and their signs are kept in the finite sum. -/

namespace ImbalancedChen.P3ExactCoprimePrimeBV

noncomputable section

open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- The log-integral discrepancy, the unit-modulus prime-prefix discrepancy
and the primes dividing the full modulus have their literal signs. -/
theorem exact_prime_discrepancy_eq (N a q : ℕ) :
    finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) a q =
      part3PrimeAPError N a q - part3PrimeAPError N 1 1 / (q.totient : ℝ) +
        chenPrimeDivisorCount N q / (q.totient : ℝ) := by
  have hmass : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) a q =
      chenPrimeAPCount N a q := by simp [finiteCongruenceMass, chenPrimeAPCount]
  have hunit : part3PrimeAPError N 1 1 =
      ((chenPrimePrefix N).card : ℝ) - trueLogarithmicIntegral N := by
    simp [part3PrimeAPError, chenPrimeAPCount, Nat.ModEq]
    simp only [Nat.mod_one, Finset.filter_true]
  rw [finitePrimitiveDiscrepancy, chenPrimePrefix_coprime_mass, hmass, hunit, part3PrimeAPError]
  ring

/-- Every primitive class at a modulus lies within the same BV envelope
of the common log-integral centre. Their actual average is the exact
coprime mass divided by the totient, hence the factor two. -/
theorem abs_exact_prime_discrepancy_le {N a q : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    |finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) a q| ≤
      2 * standardPrimeAPPrefixMaxError N q := by
  apply abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_primitive (chenPrimePrefix N)
    (fun _ => 1) (trueLogarithmicIntegral N / (q.totient : ℝ)) _ a q hq ha
  intro b _ hb
  have hm : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) b q =
      chenPrimeAPCount N b q := by simp [finiteCongruenceMass, chenPrimeAPCount]
  rw [hm]
  exact part3_abs_primeAPError_le_prefix le_rfl hq hb

/-- The cutoff and the analytic bound are chosen before every finite
physical subfamily, its residue selector and its real signed coefficient. -/
theorem exists_signed_classical_payment (A : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 (panModulusCutoff N B) →
        ∀ a : ℕ → ℕ, (∀ q ∈ S, (a q).Coprime q) →
          ∀ w : ℕ → ℝ, (∀ q ∈ S, |w q| ≤ 1) →
            |∑ q ∈ S, w q * finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) (a q) q| ≤
              C * (N : ℝ) / Real.log (N : ℝ)^A := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
      ((A + 1 : ℕ) : ℝ) (by positivity)
  refine ⟨B, hB, 2 * C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards [hBV, eventually_one_le_nat_log, eventually_ge_atTop (2 : ℕ)] with N hBVN hlog hN
  intro S hS a ha w hw
  have hpool := hBVN hN
  simp only [Real.rpow_natCast] at hpool
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have he : Real.log (N : ℝ)^A ≤ Real.log (N : ℝ)^(A+1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hlogpos.le _) hlog
  calc
    _ ≤ ∑ q ∈ S, |w q * finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) (a q) q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ S, 2 * standardPrimeAPPrefixMaxError N q := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hw q hq)).trans
        (abs_exact_prime_discrepancy_le (Finset.mem_Icc.mp (hS hq)).1 (ha q hq))
    _ = 2 * ∑ q ∈ S, standardPrimeAPPrefixMaxError N q := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ∑ q ∈ Finset.Icc 1 (panModulusCutoff N B), standardPrimeAPPrefixMaxError N q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun q _ _ => standardPrimeAPPrefixMaxError_nonneg N q)) (by norm_num)
    _ ≤ 2 * (C * (N : ℝ) / Real.log (N : ℝ)^(A+1)) :=
      mul_le_mul_of_nonneg_left hpool (by norm_num)
    _ ≤ 2 * (C * (N : ℝ) / Real.log (N : ℝ)^A) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
        (mul_nonneg hC.le (Nat.cast_nonneg _)) (pow_pos hlogpos _) he) (by norm_num)
    _ = _ := by ring

end
end ImbalancedChen.P3ExactCoprimePrimeBV
