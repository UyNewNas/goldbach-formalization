import ImbalancedChen.Part5OriginalH430FrozenClassicalRootModuli
import ImbalancedChen.ChenInitialCorrectionBudget

/-! Complete AP payment for the ordinary upper polynomial of the original
classical U3 root boxes. Pooling sees each full modulus once. The true-li
shift and the deleted centre primes are included before applying BV. -/
namespace ImbalancedChen.Part5OriginalH430FrozenClassicalRootAP
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open MathlibNt.SieveTheory.BombieriVinogradov MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P2SameQSeedCoprimeMean (finiteAPDiscrepancy finiteMeanShift)
open P5OriginalU5FrozenSource (receiver finiteAPDiscrepancy_eq_actualSource
  finiteMeanShift_eq_actualSource)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand original_band_prime)
open Part5OriginalH430RootRosserSurplus (signedAP)
open Part5OriginalH430ClassicalTailBV (receiver_atom_eq_trueLi)
open Part5OriginalH430FrozenClassicalRootModuli

private def primeError (N k : ℕ) : ℝ :=
  finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N k +
    (((chenAdditivePrimeCarrier N).card : ℝ) - logarithmicIntegral N -
      chenPrimeDivisorCount N k) / (Nat.totient k : ℝ)

private theorem primeError_bound {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hcop : k.Coprime N) (hlog : 1 ≤ Real.log (N:ℝ)) :
    |primeError N k| ≤ |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k| +
      (3 / Real.log 2) * Real.log (N : ℝ) := by
  have heq : primeError N k = chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k +
        (2/Real.log 2)/(Nat.totient k : ℝ) - chenCentrePrimeAPCount N N k := by
    calc
      _ = finiteAPDiscrepancy N (receiver N) k + finiteMeanShift N (receiver N) k := by
        rw [finiteAPDiscrepancy_eq_actualSource, finiteMeanShift_eq_actualSource hcop]
        rfl
      _ = _ := receiver_atom_eq_trueLi N k
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnum : 0 ≤ (2:ℝ)/Real.log 2 := by positivity
  have hφ : (1:ℝ) ≤ Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk
  have ha := div_le_self hnum hφ
  have hc := (chenCentrePrimeAPCount_le_divisorCount N N k).trans
    (chenPrimeDivisorCount_le_log N hN)
  have hli := le_mul_of_one_le_right hnum hlog
  rw [heq]
  calc
    _ ≤ (|chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k| +
      |(2/Real.log 2)/(Nat.totient k : ℝ)|) + |chenCentrePrimeAPCount N N k| :=
        (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ _ := by
      rw [abs_of_nonneg (div_nonneg hnum (Nat.cast_nonneg _)),
        abs_of_nonneg (chenCentrePrimeAPCount_nonneg _ _ _)]
      have hsum : (2/Real.log 2)*Real.log (N:ℝ) + Real.log (N:ℝ)/Real.log 2 =
          (3/Real.log 2)*Real.log (N:ℝ) := by ring
      linarith only [ha, hc, hli, hsum]

private theorem abs_row_le_active (N n m p : ℕ) (τ : ℝ) :
    |signedAP N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ)| ≤
      ∑ r ∈ activeDivisors N n m p τ, |primeError N (p*r)| := by
  let z := cutoffAt N n m p τ
  let D := P2ActualMarkedCountState.rootLevel (rootQ N n .U3 τ p) p
  let w := ordinaryRosserWeight true N p D z
  have ht : signedAP N p (rootQ N n .U3 τ p) z =
      ∑ r ∈ activeDivisors N n m p τ, w r * primeError N (p*r) := by
    unfold signedAP activeDivisors
    rw [sum_filter]
    apply sum_congr rfl
    intro r _
    by_cases h : w r = 0
    · change w r * primeError N (p*r) = if w r ≠ 0 then _ else _
      simp [h]
    · change w r * primeError N (p*r) = if w r ≠ 0 then _ else _
      simp [h]
  rw [ht]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (ordinaryRosserWeight_abs_le_one true N p D r z)
    (abs_nonneg _)).trans_eq (one_mul _)

/-- All the original frozen classical root queries together. The bound
controls the sum of the absolute signed rows, with no factor for the
number of p, the number of cells, or the number of surviving quotients. -/
theorem classical_tail_AP_log_saving {τ : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1/12)
    (K : ℕ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n m : ℕ,
      1/((n:ℝ)+1) ≤ 11/384 →
      (∑ p ∈ classicalBand N, |signedAP N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ)|) ≤
        C * (N:ℝ) / Real.log (N:ℝ)^K := by
  obtain ⟨B, hB, C, hC, hBV⟩ := part3_chenQuotientPrimeAPError_pool_log_saving
    (K:ℝ) (by exact_mod_cast hK)
  have hcap : ∀ᶠ N : ℕ in atTop,
      ⌊(N:ℝ)^(1/2-τ)⌋₊ ≤ panModulusCutoff N B := by
    simpa only [liuSourceDEpsilon] using
      eventually_liuSourceDEpsilon_le_panModulusCutoff τ B hτ hB
  refine ⟨C+1, by linarith, ?_⟩
  filter_upwards [hBV, hcap, eventually_one_le_nat_log, eventually_ge_atTop (2:ℕ),
    eventually_powerLog_le_logAccuracy (3/Real.log 2) (1/2) 1 K
      (by norm_num) 1 zero_lt_one] with N hBV hcap hlog hN hpower
  intro n m hn
  let D := ⌊(N:ℝ)^(1/2-τ)⌋₊
  let S := fun p => activeDivisors N n m p τ
  let M := chenPooledQuotientModuli (classicalBand N) id S
  let P := sieveProduct N (Nat.ceil ((N:ℝ)^a))
  let b := (3/Real.log 2) * Real.log (N:ℝ)
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hb : 0 ≤ b := mul_nonneg (by positivity) (by linarith)
  have hsup := pooled_support (m := m) hN hτ.le hτ' hn
  have hprim (p : ℕ) (hp : p ∈ classicalBand N) := original_band_prime (Finset.mem_filter.mp hp).1
  have hrough (p : ℕ) (hp : p ∈ classicalBand N) : p.Coprime P :=
    (chenSinglePrimeSelector_sieve_data (Finset.mem_filter.mp hp).1).2.2
  have hsub : M ⊆ (Finset.Icc 1 D).filter (fun k => k.Coprime N) :=
    chenPooledQuotientModuli_subset_primitive (classicalBand N) id S N
      ((N:ℝ)^a) D (fun p hp => (hprim p hp).1.pos)
      (fun p hp => (hprim p hp).2) hsup.1 hsup.2
  have hcard : (M.card : ℝ) ≤ (N:ℝ)^(1/2:ℝ) := by
    have hc : M.card ≤ D := by
      simpa using card_le_card (hsub.trans (Finset.filter_subset _ _))
    have hNr : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hD : 0 ≤ (N:ℝ)^(1/2-τ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    exact (show (M.card : ℝ) ≤ D by exact_mod_cast hc).trans
      ((Nat.floor_le hD).trans (rpow_le_rpow_of_exponent_le hNr (by linarith)))
  have hcent : (M.card : ℝ) * b ≤ (N:ℝ) / Real.log (N:ℝ)^K := by
    calc
      _ ≤ (N:ℝ)^(1/2:ℝ) * b := mul_le_mul_of_nonneg_right hcard hb
      _ = (3/Real.log 2) * (N:ℝ)^(1/2:ℝ) * Real.log (N:ℝ) := by dsimp [b]; ring
      _ ≤ _ := by simpa only [pow_one, one_mul] using hpower
  have hpool :
      (∑ k ∈ M, |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
        C*(N:ℝ)/Real.log (N:ℝ)^K := by
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _)).trans
      (by simpa only [Real.rpow_natCast] using hBV D hcap)
  calc
    _ ≤ ∑ p ∈ classicalBand N, ∑ r ∈ S p, |primeError N (p*r)| :=
      sum_le_sum (fun p _ => abs_row_le_active N n m p τ)
    _ = ∑ k ∈ M, |primeError N k| := sum_chenPooledQuotientModuli (classicalBand N) id
      S P hrough (fun _ _ _ _ h => h) hsup.1 (fun k => |primeError N k|)
    _ ≤ ∑ k ∈ M, (|chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k| + b) := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hI, hcop⟩ := Finset.mem_filter.mp (hsub hk)
      exact primeError_bound (by omega) (Finset.mem_Icc.mp hI).1 hcop hlog
    _ ≤ _ := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      calc
        _ ≤ C*(N:ℝ)/Real.log (N:ℝ)^K + (N:ℝ)/Real.log (N:ℝ)^K := add_le_add hpool hcent
        _ = _ := by ring

end
end ImbalancedChen.Part5OriginalH430FrozenClassicalRootAP
