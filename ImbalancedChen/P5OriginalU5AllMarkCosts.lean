import ImbalancedChen.P5OriginalU5PlateauPrimeBV
import ImbalancedChen.P4BPrimorialDivisorEnvelope
import ImbalancedChen.ChenQuotientCentreBudget
import ImbalancedChen.P5OriginalSingletonLowerTrimPaid

/-! The two outer prime corrections of the original U5 causal finite sum.
The positive count over displayed quotients includes zero-coefficient
rows. Unique recovery of the two marks permits counting each q once. -/
namespace ImbalancedChen.P5OriginalU5AllMarkCosts

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV
  (Policy markedProduct fullModulus moduli integerRho primorial quotient_mem_primorial
   integerRho_at_original remainingPrimitive)
open P3ActualU6PhysicalRhoPushforward (taggedPhysicalModuli)
open P3ActualEvenLowerIntegerRho (actualEvenLowerIntegerRho_cast)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry (fouvryTau_two)

/-- Including every rank of the original smaller-prime quotient, the
largest possible prime factor is still below the original larger mark's
upper endpoint. This places the complete labelled q in one primorial
without imposing an upper bound on its product. -/
theorem full_modulus_data {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (P : Policy)
    (hw : smallCutoff N e ≤ cutoff N) {q : ℕ} (hq : q ∈ moduli N e P) :
    q ∈ (sieveProduct N N).divisors ∧ |(integerRho N e P q : ℝ)| ≤ 1 ∧
      ∀ p ∈ q.primeFactors, (p : ℝ) < (N : ℝ)^(19/125 : ℝ) := by
  obtain ⟨t, ht, hm⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
  have hmark := chenY5PrimeSelector_sieve_data ht
  have hprime := chenY5PrimeSelector_ordered_prime_data ht
  have hband := (Finset.mem_filter.mp ht).2.2.2
  have hd := Nat.dvd_of_mem_divisors (quotient_mem_primorial (P t) hw hk)
  have hcop := chenQuotient_allowed_coprime hmark.2.2 hd
  have hsf : Squarefree (fullModulus t k) := (Nat.squarefree_mul hcop).mpr
    ⟨chenY5PrimeSelector_multiplier_squarefree ht,
      (sieveProduct_squarefree N (Nat.ceil (cutoff N))).squarefree_of_dvd hd⟩
  have hqN := chenQuotient_allowed_primitive hmark.2.1 hd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpmax (p : ℕ) (hp : p ∈ (fullModulus t k).primeFactors) :
      (p : ℝ) < (N : ℝ)^(19/125 : ℝ) := by
    have pp := Nat.prime_of_mem_primeFactors hp
    have pd : p ∣ (t.1*t.2)*k := Nat.dvd_of_mem_primeFactors hp
    rcases pp.dvd_mul.mp pd with hm | hm
    · rcases pp.dvd_mul.mp hm with h1 | h2
      · rw [(Nat.prime_dvd_prime_iff_eq pp hprime.1).mp h1]
        exact (Nat.cast_lt.mpr hprime.2.2).trans hband
      · rwa [(Nat.prime_dvd_prime_iff_eq pp hprime.2.1).mp h2]
    · have hs := mem_sievePrimes.mp (prime_mem_sievePrimes_of_dvd pp (hm.trans hd))
      exact (Nat.lt_ceil.mp hs.1).trans_le (Real.rpow_le_rpow_of_exponent_le hN1
        (show (417/5000 : ℝ) ≤ 19/125 by norm_num))
  have hsub : (fullModulus t k).primeFactors ⊆ sievePrimes N N := by
    intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    have hle : (N : ℝ)^(19/125 : ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
        (show (19/125 : ℝ) ≤ 1 by norm_num)
    exact mem_sievePrimes.mpr ⟨by exact_mod_cast (hpmax p hp).trans_le hle, pp,
      pp.coprime_iff_not_dvd.mp (hqN.symm.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))⟩
  have hdiv : fullModulus t k ∣ sieveProduct N N := by
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  refine ⟨Nat.mem_divisors.mpr ⟨hdiv, (sieveProduct_squarefree N N).ne_zero⟩, ?_, hpmax⟩
  rw [integerRho_at_original P hw ht hk]
  change |(P3ActualEvenLowerIntegerRho.actualEvenLowerIntegerRho _ _ _ _ _ _ _ : ℝ)| ≤ 1
  rw [actualEvenLowerIntegerRho_cast]
  exact actualLowerSmallRoughRho_abs_le_one _ _ _ _ _ _ _

theorem unweighted_pool {N : ℕ} {e : ℝ} (P : Policy)
    (hw : smallCutoff N e ≤ cutoff N) (F : ℕ → ℝ) :
    (∑ t ∈ pairSupport N, ∑ k ∈ support N e (P t), F (fullModulus t k)) =
      ∑ q ∈ moduli N e P, F q := by
  let T := pairSupport N
  let S := fun t => support N e (P t)
  have heq : chenPooledQuotientModuli T markedProduct S = moduli N e P := by
    ext q
    constructor
    · intro hq
      obtain ⟨⟨t, k⟩, hk, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ht, hk⟩ := Finset.mem_sigma.mp hk
      exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩
    · intro hq
      obtain ⟨t, ht, hm⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_image.mpr ⟨⟨t,k⟩, Finset.mem_sigma.mpr ⟨ht,hk⟩, rfl⟩
  rw [← heq]
  exact sum_chenPooledQuotientModuli T markedProduct S (primorial N)
    (fun _ ht => (chenY5PrimeSelector_sieve_data ht).2.2)
    (chenY5PrimeSelector_multiplier_injOn N _ _)
    (fun t _ _ hk => quotient_mem_primorial (P t) hw hk) F

theorem exists_moduli_reciprocal_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → Even N → ∀ (e : ℝ) (P : Policy),
      smallCutoff N e ≤ cutoff N →
      (∑ q ∈ moduli N e P, 1/(Nat.totient q : ℝ)) ≤ C*Real.log (N : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := P4BPrimorialDivisorEnvelope.exists_sievePrimorial_divisor_mass_le_log
  exact ⟨C, hC, fun N hN he e P hw =>
    (Finset.sum_le_sum_of_subset_of_nonneg (fun _ hq => (full_modulus_data hN P hw hq).1)
      (fun _ _ _ => by positivity)).trans (hmass N N he (by exact_mod_cast hN))⟩

/-- The two original positive costs have arbitrary logarithmic accuracy,
uniformly over the entire U5 triangle and all pair-dependent policies. -/
theorem eventually_all_outer_costs (p : ℕ) (tol : ℝ) (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
      primeCostSum N e P + centreCostSum N e P ≤ tol*(N : ℝ)/(Real.log (N : ℝ))^p := by
  obtain ⟨C, hC, hmass⟩ := exists_moduli_reciprocal_mass
  obtain ⟨D, hD, hTau⟩ := Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show (0 : ℝ) < 1/2 by norm_num)
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    eventually_powerLog_le_logAccuracy (2*C) (19/125) 1 p (by norm_num) (tol/2) (by positivity),
    eventually_powerLog_le_logAccuracy (D/Real.log 2) (1/2) 1 p (by norm_num) (tol/2)
      (by positivity)] with N hN hpayP hpayC
  intro hev e he he8 P
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hw := (attachment_gates hN2 he he8).2.2
  let Q := moduli N e P
  let H := (N : ℝ)^(19/125 : ℝ)
  have hH : 1 ≤ H := Real.one_le_rpow hN1 (by norm_num)
  have hfac (q : ℕ) (hq : q ∈ Q) : chenPrimeDivisorCount N q ≤ 2*H := by
    have hs := full_modulus_data hN2 P hw hq
    have hsub : q.primeFactors ⊆ Finset.range (Nat.ceil H) := by
      intro l hl
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (hs.2.2 l hl))
    have hc : (q.primeFactors.card : ℝ) ≤ (Nat.ceil H : ℝ) := by
      exact_mod_cast (show q.primeFactors.card ≤ Nat.ceil H by
        simpa only [Finset.card_range] using Finset.card_le_card hsub)
    have hu := (Nat.ceil_lt_add_one (zero_le_one.trans hH)).le
    exact (chenPrimeDivisorCount_le_primeFactors_card N (Nat.pos_of_mem_divisors hs.1)).trans
      (hc.trans (by linarith))
  have hP : primeCostSum N e P ≤ (2*C)*H*Real.log (N : ℝ) := by
    unfold primeCostSum rowPrimeCost
    rw [unweighted_pool P hw (fun q => chenPrimeDivisorCount N q/(Nat.totient q : ℝ))]
    calc
      _ ≤ ∑ q ∈ Q, (2*H)*(1/(Nat.totient q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [mul_one_div] using div_le_div_of_nonneg_right (hfac q hq) (Nat.cast_nonneg _)
      _ = (2*H)*(∑ q ∈ Q, 1/(Nat.totient q : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ (2*H)*(C*Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmass N hN2 hev e P hw) (by linarith)
      _ = _ := by ring
  have hcentre (l : ℕ) (hl : l ∈ chenCentrePrimeCarrier N) :
      ((Q.filter (fun q => id q ∣ N-l)).card : ℝ) ≤ D*(N : ℝ)^(1/2 : ℝ) := by
    have hp := chenCentrePrimeCarrier_sub_pos (chen_not_prime_of_even_four_le hev hN) hl
    have hsub : (Q.filter (fun q => id q ∣ N-l)) ⊆ (N-l).divisors :=
      fun _ hq => Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hq).2, hp.ne'⟩
    have ht := hTau (N-l) hp
    rw [fouvryTau_two] at ht
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (ht.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.sub_le N l) (by norm_num : (0 : ℝ) ≤ 1/2)) hD.le))
  have hC' : centreCostSum N e P ≤ (D/Real.log 2)*(N : ℝ)^(1/2 : ℝ)*Real.log (N : ℝ) := by
    unfold centreCostSum rowCentreCost
    rw [unweighted_pool P hw (chenCentrePrimeAPCount N N)]
    change chenSelectedCentreMass N Q id ≤ _
    calc
      _ ≤ chenPrimeDivisorCount N N*(D*(N : ℝ)^(1/2 : ℝ)) :=
        chenSelectedCentreMass_le_of_incidence_bound N Q id _ hcentre
      _ ≤ (Real.log (N : ℝ)/Real.log 2)*(D*(N : ℝ)^(1/2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (chenPrimeDivisorCount_le_log N (by omega)) (by positivity)
      _ = _ := by ring
  simp only [pow_one] at hpayP hpayC
  change (2*C)*H*Real.log (N : ℝ) ≤ _ at hpayP
  linarith only [hP, hC', hpayP, hpayC]

/-- Production lower-count entry after both outer costs and the previous
short rectangle have been paid. The long/complementary primitive rows
appear with their original sign. -/
theorem exists_original_count_paid (p : ℕ) {eta eMax : ℝ} (heta : 0 < eta) (hMax : 0 < eMax) :
    ∃ D : ℝ, 0 < D ∧ ∃ e : ℝ, 0 < e ∧ e < 1/8 ∧ e < eMax ∧
      ∃ M : ℕ, 2 ≤ M ∧ ∀ N : ℕ, M ≤ N → Even N → ∀ P : Policy,
      fullProjectedMainSum N P - projectionReserve N eta + remainingPrimitive N e P -
        D*(N : ℝ)/(Real.log (N : ℝ))^p ≤ currentChenUpsilon5 N := by
  obtain ⟨C, hC, e, he, he8, heMax, M, hM, hold⟩ :=
    P5OriginalU5PlateauPrimeBV.exists_projected_count_lower p heta hMax
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (eventually_all_outer_costs p 1 zero_lt_one)
  refine ⟨C+1, by linarith, e, he, he8, heMax, max J M, hM.trans (le_max_right _ _), ?_⟩
  intro N hN hev P
  have hf := hold N ((le_max_right _ _).trans hN) hev P
  have hc := hJ N ((le_max_left _ _).trans hN) hev e he he8 P
  linarith only [hf, hc]

end
end ImbalancedChen.P5OriginalU5AllMarkCosts
