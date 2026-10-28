import ImbalancedChen.P2EnhancedTwentyOneSourceComparison
import ImbalancedChen.ActualSmallRosser

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Actual negative children of the same-Q 21-term mother. The lower Rosser
coefficient uses the OLD mask d*N and physical level Q/(d*p). Original
prime labels (including p dividing d), cutoff endpoints, and zero/unit
receiver surfaces are preserved. No H248 density identity is proposed. -/

namespace ImbalancedChen.P2EnhancedNegativeChildRosser

noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve P2EnhancedTwentyOneSameQWeighted
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

def rawPrimeAPCarrier (N m : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun ell => ell.Prime ∧ m ∣ N - ell)

def rawPrimeAPCount (N m : ℕ) : ℝ := (rawPrimeAPCarrier N m).card

def childLevel (Q : ℝ) (d p : ℕ) : ℝ := Q / ((d * p : ℕ) : ℝ)

def childSupport (N : ℕ) (Q : ℝ) (d : ℕ) : Finset ℕ :=
  actualSmallRosserSupport (d * N) (Nat.ceil (cutoff Q d (227 / 50))) (cutoff Q d (227 / 50))

def childCoefficient (N : ℕ) (Q : ℝ) (d p k : ℕ) : ℝ :=
  actualSmallRosserMinus (d * N) (Nat.ceil (cutoff Q d (227 / 50)))
    (cutoff Q d (227 / 50)) (childLevel Q d p) k

def childEstimator (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k * rawPrimeAPCount N (d * p * k)

/-- A selected p above the strict cutoff creates no unscaled-to-quotient
defect at the unchanged old mask. No p-coprime-d hypothesis is added. -/
theorem negative_source_eq_quotient (N d p : ℕ) (a : ℝ)
    (hp : p.Prime) (hpa : a ≤ (p : ℝ)) :
    sourceSieveCarrier N (d * p) (d * N) a = sieveCarrier N (d * p) (d * N) a := by
  have hd : Sifted (d * N) d a := by
    intro q hq hqM hqa
    exact siftedLE_of_dvd_modulus (dvd_mul_right d N) a q hq hqM hqa.le
  have hs : Sifted (d * N) (d * p) a :=
    (sifted_mul_iff _ _ _ _).mpr ⟨hd, sifted_prime_of_le hp hpa⟩
  rw [sourceSieveCarrier_eq_ite, if_pos hs]

theorem small_product_coprime_iff_sifted (M cap n : ℕ) (a : ℝ)
    (hcap : a ≤ (cap : ℝ)) :
    (actualSmallPrimeProduct M cap a).Coprime n ↔ Sifted M n a := by
  rw [actualSmallPrimeProduct, Nat.coprime_prod_left_iff]
  constructor
  · intro h q hq hqM hqa
    have hqS := (mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hcap).mpr
      ⟨hq, hq.coprime_iff_not_dvd.mp hqM, hqa⟩
    exact hq.coprime_iff_not_dvd.mp (h q hqS)
  · intro h q hq
    have hqS := (mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hcap).mp hq
    exact hqS.1.coprime_iff_not_dvd.mpr
      (h q hqS.1 (hqS.1.coprime_iff_not_dvd.mpr hqS.2.1) hqS.2.2)

/-- Divisibility fibres keep actual original prime receivers. In
particular no centre-prime or endpoint is silently deleted. -/
theorem rawPrimeAPCarrier_divisor_fibre (N m k : ℕ) :
    (rawPrimeAPCarrier N m).filter (fun ell => k ∣ (N - ell) / m) =
      rawPrimeAPCarrier N (m * k) := by
  ext ell
  simp only [rawPrimeAPCarrier, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hr, hp, hm⟩, hk⟩
    exact ⟨hr, hp, (Nat.dvd_div_iff_mul_dvd hm).mp hk⟩
  · rintro ⟨hr, hp, hmk⟩
    have hm := (dvd_mul_right m k).trans hmk
    exact ⟨⟨hr, hp, hm⟩, (Nat.dvd_div_iff_mul_dvd hm).mpr hmk⟩

theorem childEstimator_eq_receiver_divisor_sum (N : ℕ) (Q : ℝ) (d p : ℕ) :
    childEstimator N Q d p =
      ∑ ell ∈ rawPrimeAPCarrier N (d * p),
        supportedDivisorSum (childSupport N Q d) (childCoefficient N Q d p)
          ((N - ell) / (d * p)) := by
  unfold childEstimator supportedDivisorSum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_filter, rawPrimeAPCarrier_divisor_fibre]
  simp only [Finset.sum_const, nsmul_eq_mul, rawPrimeAPCount]
  ring

/-- The exact child lower estimator is proved below the real negative
source count. It is not an enhanced mean or a hypothesized gain. -/
theorem childEstimator_le_negative_source (N : ℕ) (Q : ℝ) (d p : ℕ)
    (hp : p.Prime) (hpa : cutoff Q d (227 / 50) ≤ (p : ℝ))
    (hL : 1 < childLevel Q d p) (haL : cutoff Q d (227 / 50) ≤ childLevel Q d p) :
    childEstimator N Q d p ≤
      (sourceSieveCount N (d * p) (d * N) (cutoff Q d (227 / 50)) : ℝ) := by
  rw [childEstimator_eq_receiver_divisor_sum]
  have hpoint (ell : ℕ) :
      supportedDivisorSum (childSupport N Q d) (childCoefficient N Q d p)
        ((N - ell) / (d * p)) ≤
        if Sifted (d * N) ((N - ell) / (d * p)) (cutoff Q d (227 / 50))
          then (1 : ℝ) else 0 := by
    have h := (actualSmallRosser_sandwich_nat (d * N)
      (Nat.ceil (cutoff Q d (227 / 50))) (cutoff Q d (227 / 50))
      (childLevel Q d p) hL haL ((N - ell) / (d * p))).1
    simpa only [childSupport, childCoefficient,
      small_product_coprime_iff_sifted _ _ _ _ (Nat.le_ceil _)] using h
  calc
    _ ≤ ∑ ell ∈ rawPrimeAPCarrier N (d * p),
        if Sifted (d * N) ((N - ell) / (d * p)) (cutoff Q d (227 / 50))
          then (1 : ℝ) else 0 := Finset.sum_le_sum (fun ell _ => hpoint ell)
    _ = (sourceSieveCount N (d * p) (d * N) (cutoff Q d (227 / 50)) : ℝ) := by
      rw [← Finset.sum_filter]
      have hc : (rawPrimeAPCarrier N (d * p)).filter
          (fun ell => Sifted (d * N) ((N - ell) / (d * p)) (cutoff Q d (227 / 50))) =
          sieveCarrier N (d * p) (d * N) (cutoff Q d (227 / 50)) := by
        ext ell
        simp [rawPrimeAPCarrier, sieveCarrier, and_assoc]
      rw [hc, ← negative_source_eq_quotient N d p _ hp hpa]
      simp [sourceSieveCount]

/-- Literal original cutoffs alone give legal ordinary residual levels
for every one of the three negative windows. -/
theorem negative_child_level_gates {Q : ℝ} {N d p : ℕ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ))
    (hp : p ∈ primeWindow N (cutoff Q d (227 / 50)) (cutoff Q d (11 / 5))) :
    1 < childLevel Q d p ∧ cutoff Q d (227 / 50) < childLevel Q d p := by
  have hD : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (mem_primeWindow.mp hp).1.pos
  have hR0 : 0 < Q / (d : ℝ) := zero_lt_one.trans hR
  have hFpos : 0 < cutoff Q d (11 / 5) := Real.rpow_pos_of_pos hR0 _
  have hApos : 0 < cutoff Q d (227 / 50) := Real.rpow_pos_of_pos hR0 _
  have hAF : cutoff Q d (227 / 50) ≤ cutoff Q d (11 / 5) :=
    Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num)
  have hFle : cutoff Q d (11 / 5) ≤ Q / (d : ℝ) := by
    simpa only [cutoff, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num : 1 / (11 / 5 : ℝ) ≤ 1)
  have hF2 : cutoff Q d (11 / 5) * cutoff Q d (11 / 5) ≤ Q / (d : ℝ) := by
    change (Q / (d : ℝ)) ^ (1 / (11 / 5 : ℝ)) *
      (Q / (d : ℝ)) ^ (1 / (11 / 5 : ℝ)) ≤ Q / (d : ℝ)
    rw [← Real.rpow_add hR0]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR.le
      (by norm_num : 1 / (11 / 5 : ℝ) + 1 / (11 / 5 : ℝ) ≤ 1)
  have hpF := (mem_primeWindow.mp hp).2.2.2
  have hL : childLevel Q d p = (Q / (d : ℝ)) / (p : ℝ) := by
    simp only [childLevel, Nat.cast_mul, div_div]
  rw [hL]
  constructor
  · exact (lt_div_iff₀ hp0).mpr (by simpa only [one_mul] using hpF.trans_le hFle)
  · apply (lt_div_iff₀ hp0).mpr
    exact ((mul_lt_mul_of_pos_left hpF hApos).trans_le
      (mul_le_mul_of_nonneg_right hAF hFpos.le)).trans_le hF2

def windowEstimator (N : ℕ) (Q : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N (cutoff Q d (227 / 50)) u, childEstimator N Q d p

theorem windowEstimator_le_single {N d : ℕ} {Q u : ℝ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ)) (hu : u ≤ cutoff Q d (11 / 5)) :
    windowEstimator N Q d u ≤ fourthRowMotherSingle N d N (cutoff Q d (227 / 50)) u := by
  unfold windowEstimator fourthRowMotherSingle
  apply Finset.sum_le_sum
  intro p hp
  have hpf := mem_primeWindow.mpr ⟨(mem_primeWindow.mp hp).1, (mem_primeWindow.mp hp).2.1,
    (mem_primeWindow.mp hp).2.2.1, (mem_primeWindow.mp hp).2.2.2.trans_le hu⟩
  have hgate := negative_child_level_gates hd hR hpf
  exact childEstimator_le_negative_source N Q d p (mem_primeWindow.mp hp).1
    (mem_primeWindow.mp hp).2.2.1 hgate.1 hgate.2.le

/-- The AP model has the actual full modulus and the true coprime-class
gate. The discrepancy below includes all exceptional prime receivers. -/
def childAPMean (N : ℕ) (m : ℕ) : ℝ :=
  if m.Coprime N then logarithmicIntegral N / (Nat.totient m : ℝ) else 0

def childMean (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k * childAPMean N (d * p * k)

def childSignedRemainder (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k *
    (rawPrimeAPCount N (d * p * k) - childAPMean N (d * p * k))

theorem childEstimator_eq_mean_add_signed_remainder (N : ℕ) (Q : ℝ) (d p : ℕ) :
    childEstimator N Q d p = childMean N Q d p + childSignedRemainder N Q d p := by
  unfold childEstimator childMean childSignedRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

def childResidualDensity (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k / (Nat.totient k : ℝ)

/-- The very same support is coprime to the physical prefix d*p. This
uses p>=a and the OLD mask d*N; it does not exclude p dividing d. -/
theorem childSupport_coprime_prefix {N d p k : ℕ} {Q : ℝ}
    (hp : p.Prime) (hpa : cutoff Q d (227 / 50) ≤ (p : ℝ))
    (hk : k ∈ childSupport N Q d) : k.Coprime (d * p) ∧ k.Coprime N := by
  have hkM := actualSmallRosserSupport_coprime_target (d * N)
    (Nat.ceil (cutoff Q d (227 / 50))) (cutoff Q d (227 / 50)) hk
  have hkd : k.Coprime d := hkM.of_dvd_right (dvd_mul_right d N)
  have hkN : k.Coprime N := hkM.of_dvd_right (dvd_mul_left N d)
  have hprod : (actualSmallPrimeProduct (d * N)
      (Nat.ceil (cutoff Q d (227 / 50))) (cutoff Q d (227 / 50))).Coprime p :=
    (small_product_coprime_iff_sifted _ _ _ _ (Nat.le_ceil _)).mpr
      (sifted_prime_of_le hp hpa)
  have hkp : k.Coprime p := hprod.of_dvd_left (Nat.mem_divisors.mp hk).1
  exact ⟨hkd.mul_right hkp, hkN⟩

/-- An active coefficient is a true physical modulus below the original
Q, with its coprimality and small-prime support derived from that very
coefficient. No independently supplied residual-wellness predicate. -/
theorem childCoefficient_active_fullQ {N d p k : ℕ} {Q : ℝ}
    (hd : 0 < d) (hp : p.Prime) (hpa : cutoff Q d (227 / 50) ≤ (p : ℝ))
    (hk : childCoefficient N Q d p k ≠ 0) :
    ((d * p * k : ℕ) : ℝ) < Q ∧ k.Coprime (d * p) ∧ k.Coprime N ∧
      SmallPrimeSupportedAt (cutoff Q d (227 / 50)) k := by
  have hact := actualSmallRosserMinus_active hk
  have hdp : (0 : ℝ) < ((d * p : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos hd hp.pos)
  have hbound := (lt_div_iff₀ hdp).mp hact.2.1
  have hcop := childSupport_coprime_prefix hp hpa hact.1
  refine ⟨?_, hcop.1, hcop.2, hact.2.2⟩
  simpa only [Nat.cast_mul, mul_comm] using hbound

/-- Exact factorization of the ordinary AP MODEL mean of precisely the
signed coefficients in the count inequality. This li(N) model is distinct
from the finite coprime-population mean defined below. No H248 occurs. -/
theorem childMean_eq_guarded_residual_density {N d p : ℕ} {Q : ℝ}
    (hp : p.Prime) (hpa : cutoff Q d (227 / 50) ≤ (p : ℝ)) :
    childMean N Q d p =
      if (d * p).Coprime N then
        (logarithmicIntegral N / (Nat.totient (d * p) : ℝ)) * childResidualDensity N Q d p
      else 0 := by
  unfold childMean childResidualDensity
  by_cases hbase : (d * p).Coprime N
  · rw [if_pos hbase, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hcop := childSupport_coprime_prefix hp hpa hk
    rw [childAPMean, if_pos (hbase.mul_left hcop.2),
      Nat.totient_mul hcop.1.symm, Nat.cast_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [if_neg hbase]
    apply Finset.sum_eq_zero
    intro k hk
    have hnot : ¬ (d * p * k).Coprime N := fun h =>
      hbase (h.of_dvd_left (dvd_mul_right (d * p) k))
    simp only [childAPMean, if_neg hnot, mul_zero]

def windowMean (N : ℕ) (Q : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N (cutoff Q d (227 / 50)) u, childMean N Q d p

def windowSignedRemainder (N : ℕ) (Q : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N (cutoff Q d (227 / 50)) u, childSignedRemainder N Q d p

theorem windowEstimator_eq_mean_add_signed_remainder (N : ℕ) (Q : ℝ) (d : ℕ) (u : ℝ) :
    windowEstimator N Q d u = windowMean N Q d u + windowSignedRemainder N Q d u := by
  simp only [windowEstimator, windowMean, windowSignedRemainder,
    childEstimator_eq_mean_add_signed_remainder, Finset.sum_add_distrib]

/-- A genuine negative-child count inequality with the original signed
AP discrepancy retained. There is no small-error premise. -/
theorem windowMean_add_remainder_le_single {N d : ℕ} {Q u : ℝ}
    (hd : 0 < d) (hR : 1 < Q / (d : ℝ)) (hu : u ≤ cutoff Q d (11 / 5)) :
    windowMean N Q d u + windowSignedRemainder N Q d u ≤
      fourthRowMotherSingle N d N (cutoff Q d (227 / 50)) u := by
  rw [← windowEstimator_eq_mean_add_signed_remainder]
  exact windowEstimator_le_single hd hR hu

/-- The independently defined original finite prime population at the
physical modulus m. Its zero/centre/endpoints follow rawPrimeAPCarrier. -/
def coprimePrimePopulation (N m : ℕ) : ℝ :=
  (((rawPrimeAPCarrier N 1).filter (fun ell => ell.Coprime m)).card : ℝ)

/-- Exact-coprime population mean per reduced residue class, with the
actual class N mod m required to be reduced. No li approximation. -/
def finiteCoprimeAPMean (N m : ℕ) : ℝ :=
  if m.Coprime N then coprimePrimePopulation N m / (Nat.totient m : ℝ) else 0

def childFiniteCoprimeMean (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k *
    finiteCoprimeAPMean N (d * p * k)

def childFiniteSignedRemainder (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k *
    (rawPrimeAPCount N (d * p * k) - finiteCoprimeAPMean N (d * p * k))

/-- The exact same estimator admits the finite-coprime-population split.
Primes dividing the physical modulus are not silently replaced by li(N). -/
theorem childEstimator_eq_finite_mean_add_remainder (N : ℕ) (Q : ℝ) (d p : ℕ) :
    childEstimator N Q d p =
      childFiniteCoprimeMean N Q d p + childFiniteSignedRemainder N Q d p := by
  unfold childEstimator childFiniteCoprimeMean childFiniteSignedRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact signed difference between the finite coprime mean and its AP
li-model. This is not asserted to be small in this source step. -/
def childFiniteMeanShift (N : ℕ) (Q : ℝ) (d p : ℕ) : ℝ :=
  ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k *
    (finiteCoprimeAPMean N (d * p * k) - childAPMean N (d * p * k))

theorem childFiniteMean_eq_model_add_shift (N : ℕ) (Q : ℝ) (d p : ℕ) :
    childFiniteCoprimeMean N Q d p = childMean N Q d p + childFiniteMeanShift N Q d p := by
  unfold childFiniteCoprimeMean childMean childFiniteMeanShift
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem childFiniteRemainder_eq_model_sub_shift (N : ℕ) (Q : ℝ) (d p : ℕ) :
    childFiniteSignedRemainder N Q d p =
      childSignedRemainder N Q d p - childFiniteMeanShift N Q d p := by
  unfold childFiniteSignedRemainder childSignedRemainder childFiniteMeanShift
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

def windowFiniteCoprimeMean (N : ℕ) (Q : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N (cutoff Q d (227 / 50)) u, childFiniteCoprimeMean N Q d p

def windowFiniteSignedRemainder (N : ℕ) (Q : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N (cutoff Q d (227 / 50)) u, childFiniteSignedRemainder N Q d p

theorem windowEstimator_eq_finite_mean_add_remainder (N : ℕ) (Q : ℝ) (d : ℕ) (u : ℝ) :
    windowEstimator N Q d u =
      windowFiniteCoprimeMean N Q d u + windowFiniteSignedRemainder N Q d u := by
  simp only [windowEstimator, windowFiniteCoprimeMean, windowFiniteSignedRemainder,
    childEstimator_eq_finite_mean_add_remainder, Finset.sum_add_distrib]

end
end ImbalancedChen.P2EnhancedNegativeChildRosser
