import ImbalancedChen.Part5OriginalU34PrimeCorrectionPayment
import ImbalancedChen.ChenPooledQuotientAP
import ImbalancedChen.Part3PrimeAPDistribution
import ImbalancedChen.P2MarkedThetaLiNormalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual U3 classical-tail ordinary Rosser rows, with the existing K row
weights, strict source selector, original receiver, physical Q and signs.
Their full moduli are pooled using the existing gcd recovery theorem.
The classical BV bound is obtained without a root p^2<=Q hypothesis.

This pays the true-li prime AP component of the actual initial rows.
It does not assert the positive four-round seed, W1/W2 analytic actions,
all-descendant source coverage, or H430. The literal-li constant and
centre-prime term are recorded exactly rather than silently dropped.
-/

namespace ImbalancedChen.Part5OriginalH430ClassicalTailBV

noncomputable section
open Set Finset Filter Wu2008DoubleSieve
open scoped Classical BigOperators
open Part5UpperTables.OriginalU34 Part5UpperTables.OriginalU34.CountEntrance
open Part5OriginalUpsilon5CausalDictionary (a)
open P2ActualMarkedCountState (rootLevel)
open P2FrozenReceiverCountActions P2SameQSeedCoprimeMean
open P2SameQPhysicalRosserSeed (seedError)
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

def originalU3Primes (N : ℕ) : Finset ℕ :=
  chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(1/3 : ℝ))

def tailActive (side : Bool) (N : ℕ) (tau : ℝ) (p : ℕ) : Finset ℕ :=
  if tailCutoff ≤ primeCoordinate N p then rowActive side N p (U3Residual tau) else ∅

theorem mem_tailActive {side : Bool} {N p q : ℕ} {tau : ℝ} :
    q ∈ tailActive side N tau p ↔
      tailCutoff ≤ primeCoordinate N p ∧ q ∈ rowActive side N p (U3Residual tau) := by
  by_cases h : tailCutoff ≤ primeCoordinate N p <;> simp [tailActive, h]

/-- The original t=e boundary belongs to this complete below-half route. -/
theorem tail_row_Q {N p : ℕ} {tau : ℝ}
    (htail : tailCutoff ≤ primeCoordinate N p) :
    rowTotalLevel N p (U3Residual tau) = (N : ℝ)^(1/2-tau) := by
  unfold rowTotalLevel
  congr 1
  simp only [U3Residual, if_neg (not_lt.mpr htail), tailResidual]
  ring

/-- This is the genuine full-modulus support theorem, specialized to the
original source. The selected prime is not required to satisfy p^2<=Q. -/
theorem tail_complete_modulus {side : Bool} {N p q : ℕ} {tau : ℝ}
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hp : p ∈ originalU3Primes N) (hq : q ∈ tailActive side N tau p) :
    0 < p*q ∧ ((p*q : ℕ) : ℝ) ≤ (N : ℝ)^(1/2-tau) ∧ (p*q).Coprime N := by
  obtain ⟨htail, hqa⟩ := mem_tailActive.mp hq
  obtain ⟨hqd, hqw⟩ := mem_filter.mp hqa
  have hps := chenSinglePrimeSelector_sieve_data hp
  have hpc := primeCoordinate_mem hN hp
  have hr := U3Residual_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hs := P2ActualMarkedCountState.root_coefficient_full_Q
    (by omega : 0 < p)
    (row_residual_gt_one hN (by omega : 0 < p)
      (lt_of_lt_of_le (by norm_num) hr.1)) hqw
  refine ⟨Nat.mul_pos (by omega) (Nat.pos_of_mem_divisors hqd), ?_, ?_⟩
  · simpa only [tail_row_Q htail] using hs.1
  · exact hps.2.1.mul_left (hs.2.of_dvd_right (dvd_mul_left N p))

/-- The strict sieve product is embedded in a common original cutoff
product. This is a divisor identity, not an auxiliary density level. -/
theorem ordinaryProduct_dvd_common (N p : ℕ) {z A : ℝ} (hz : z ≤ A) :
    ordinarySievePrimeProduct (p*N) z ∣ sieveProduct N (Nat.ceil A) := by
  unfold ordinarySievePrimeProduct sieveProduct
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  have hw := mem_primeWindow.mp hq
  have hqP : q ∣ ordinarySievePrimeProduct (p*N) z := by
    unfold ordinarySievePrimeProduct
    exact Finset.dvd_prod_of_mem _ hq
  have hcop := ((ordinarySievePrimeProduct_coprime (p*N) z).of_dvd_left hqP).of_dvd_right
    (dvd_mul_left N p)
  exact mem_sievePrimes_chen_real_cap.mpr
    ⟨hw.2.2.2.trans_le hz, hw.1, hw.1.coprime_iff_not_dvd.mp hcop⟩

theorem tailActive_common_divisors {side : Bool} {N : ℕ} {tau : ℝ}
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (p : ℕ) (hp : p ∈ originalU3Primes N) :
    tailActive side N tau p ⊆ (sieveProduct N (Nat.ceil ((N : ℝ)^a))).divisors := by
  intro q hq
  obtain ⟨_, hqa⟩ := mem_tailActive.mp hq
  have hqd := (mem_filter.mp hqa).1
  have hpc := primeCoordinate_mem hN hp
  have hpp := (chenSinglePrimeSelector_sieve_data hp).1
  have hr := U3Residual_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hz : rowCutoff N p (U3Residual tau) ≤ (N : ℝ)^a := by
    rw [rowCutoff_eq_physical hN (by omega : 0 < p)
      (lt_of_lt_of_le (by norm_num) hr.1)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (min_le_left _ _)
  have hP : sieveProduct N (Nat.ceil ((N : ℝ)^a)) ≠ 0 := by
    unfold sieveProduct
    exact Finset.prod_ne_zero_iff.mpr (fun ell hell =>
      (mem_sievePrimes_chen_real_cap.mp hell).2.1.pos.ne')
  exact Nat.mem_divisors.mpr
    ⟨(Nat.mem_divisors.mp hqd).1.trans (ordinaryProduct_dvd_common N p hz), hP⟩

def tailSignedPrimeAP (side : Bool) (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ p ∈ originalU3Primes N, ∑ q ∈ tailActive side N tau p,
    rowWeight side N p (U3Residual tau) q *
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p*q)

/-- Exact old pooling is used; no number-of-primes or tuple-cardinality
factor is incurred. Every signed coefficient remains the K rowWeight. -/
theorem tailSignedPrimeAP_le_pool {N : ℕ} {tau : ℝ}
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (side : Bool) :
    |tailSignedPrimeAP side N tau| ≤
      ∑ m ∈ Finset.Icc 1 ⌊(N : ℝ)^(1/2-tau)⌋₊ with m.Coprime N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) m| := by
  have hpool := chenSinglePrimeSelector_pooled_AP_bound N ((N : ℝ)^a)
    ((N : ℝ)^(1/3 : ℝ)) (trueLogarithmicIntegral N) ⌊(N : ℝ)^(1/2-tau)⌋₊
    (tailActive side N tau)
    (tailActive_common_divisors hN htau htauhi)
    (fun p hp q hq => Nat.le_floor (tail_complete_modulus hN htau htauhi hp hq).2.1)
  refine le_trans ?_ hpool
  unfold tailSignedPrimeAP
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right
    (ordinaryRosserWeight_abs_le_one side N p
      (rootLevel (rowTotalLevel N p (U3Residual tau)) p) q
      (rowCutoff N p (U3Residual tau))) (abs_nonneg _)).trans_eq (one_mul _)

/-- A fixed positive tau is chosen BEFORE N. Classical BV pays the
actual initial tail AP component; no square/RootLicense is an input. -/
theorem eventually_tailSignedPrimeAP_log_saving {tau : ℝ}
    (htau : 0 < tau) (htauhi : tau ≤ 1/12) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ side : Bool,
      |tailSignedPrimeAP side N tau| ≤ C*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨B, hB, C, hC, hBV⟩ := part3_chenQuotientPrimeAPError_pool_log_saving A hA
  have hcap : ∀ᶠ N : ℕ in atTop,
      ⌊(N : ℝ)^(1/2-tau)⌋₊ ≤ panModulusCutoff N B := by
    simpa only [liuSourceDEpsilon] using
      eventually_liuSourceDEpsilon_le_panModulusCutoff tau B htau hB
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBV, hcap, eventually_ge_atTop (2 : ℕ)] with N hBVN hcapN hN
  intro side
  exact (tailSignedPrimeAP_le_pool hN htau.le htauhi side).trans (hBVN _ hcapN)

/-- Exact recentering to the true-li BV atom. The extra literal-li
constant and centre deletion retain their signs and complete modulus. -/
theorem receiver_atom_eq_trueLi (N m : ℕ) :
    finiteAPDiscrepancy N (P5OriginalU5FrozenSource.receiver N) m +
      finiteMeanShift N (P5OriginalU5FrozenSource.receiver N) m =
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) m +
        (2/Real.log 2)/(Nat.totient m : ℝ) - chenCentrePrimeAPCount N N m := by
  rw [P5OriginalU5FrozenSource.receiver_error_eq_sharp_prime_error]
  have hAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N m =
      chenPrimeAPCount N N m := by
    simp only [finiteCongruenceMass, chenPrimeAPCount, sum_const, nsmul_eq_mul, mul_one]
  unfold finitePrimitiveDiscrepancy
  rw [hAP, chenPrimePrefix_coprime_mass, P2MarkedThetaLiNormalization.trueLi_eq_literalLi_add]
  unfold chenQuotientPrimeAPError
  ring

/-- The AP term is genuinely a component of the original rowError. No
source identity or error decomposition is assumed by the caller. -/
theorem rowError_eq_trueLi_components (side : Bool) (N p : ℕ) (r : ℝ → ℝ) :
    rowError side N p r =
      ∑ q ∈ rowDivisors N p r, rowWeight side N p r q *
        (chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (p*q) +
          (2/Real.log 2)/(Nat.totient (p*q) : ℝ) - chenCentrePrimeAPCount N N (p*q)) := by
  unfold rowError seedError
  unfold signedAPDiscrepancy signedMeanShift
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [← mul_add, receiver_atom_eq_trueLi]

end
end ImbalancedChen.Part5OriginalH430ClassicalTailBV
