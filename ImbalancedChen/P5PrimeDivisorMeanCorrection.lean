import ImbalancedChen.SingletonPrimeProductTransportP5
import ImbalancedChen.TotientReciprocalBudget
import ImbalancedChen.PowerErrorBudget
import Mathlib.Data.Nat.Squarefree

/-!
# The full modulus-prime correction in the original singleton mean

This is not an endpoint-delta mean bound. It pays all primes dividing the
physical modulus when exact-coprime prime mass is replaced by total pi(N).
Squarefreeness is used at the genuine factorization q=p*(q/p), before the
totient factor is separated. The same rho remains in the exact PP target.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5PrimeDivisorMean

noncomputable section
open scoped BigOperators
open Classical Filter Topology

def modulusPrimeMass (N : ℕ) (omega : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ p ∈ chenPrimePrefix N with p ∣ q, omega p

def correction (N : ℕ) (S : Finset ℕ) (rho omega : ℕ → ℝ) : ℝ :=
  ∑ q ∈ S, rho q * (modulusPrimeMass N omega q / (Nat.totient q : ℝ))

/-- Exact squarefree factor separation at one actual modulus-prime pair. -/
theorem squarefree_totient_split {q p : ℕ} (hq : Squarefree q)
    (hp : Nat.Prime p) (hpq : p ∣ q) :
    Nat.Coprime p (q/p) ∧ Nat.totient q = (p-1)*Nat.totient (q/p) := by
  have hsq : Squarefree (p*(q/p)) := by
    rw [Nat.mul_div_cancel' hpq]
    exact hq
  have hcop := Nat.coprime_of_squarefree_mul hsq
  refine ⟨hcop,?_⟩
  calc
    Nat.totient q = Nat.totient (p*(q/p)) :=
      congrArg Nat.totient (Nat.mul_div_cancel' hpq).symm
    _ = _ := by rw [Nat.totient_mul hcop,Nat.totient_prime hp]

/-- Actual squarefree moduli divisible by p inject into their quotients.
The quotient carrier is enlarged only after the exact totient split. -/
theorem sum_reciprocal_totient_prime_fiber_le
    (S : Finset ℕ) (Q p : ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q) (hp : Nat.Prime p) :
    (∑ q ∈ S with p ∣ q, 1 / (Nat.totient q : ℝ)) ≤
      (1 / ((p-1 : ℕ) : ℝ)) * ∑ e ∈ Finset.Icc 1 Q, 1 / (Nat.totient e : ℝ) := by
  let U := S.filter (fun q => p ∣ q)
  let E := U.image (fun q => q/p)
  have hE : E ⊆ Finset.Icc 1 Q := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
    have hqS := (Finset.mem_filter.mp hq).1
    have hdiv := (Finset.mem_filter.mp hq).2
    have hqpos : 0 < q := (Finset.mem_Icc.mp (hS hqS)).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdiv) hp.pos,
      (Nat.div_le_self q p).trans (Finset.mem_Icc.mp (hS hqS)).2⟩
  have hinj : Set.InjOn (fun q => q/p) (U : Set ℕ) := by
    intro q hq r hr heq
    have hdq := (Finset.mem_filter.mp hq).2
    have hdr := (Finset.mem_filter.mp hr).2
    calc
      q = p*(q/p) := (Nat.mul_div_cancel' hdq).symm
      _ = p*(r/p) := congrArg (fun e => p*e) heq
      _ = r := Nat.mul_div_cancel' hdr
  calc
    _ = ∑ q ∈ U, (1 / ((p-1 : ℕ) : ℝ)) * (1 / (Nat.totient (q/p) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hs := squarefree_totient_split (hsq q (Finset.mem_filter.mp hq).1)
        hp (Finset.mem_filter.mp hq).2
      rw [hs.2,Nat.cast_mul]
      simp only [one_div,mul_inv_rev]
      ring
    _ = ∑ e ∈ E, (1 / ((p-1 : ℕ) : ℝ)) * (1 / (Nat.totient e : ℝ)) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ e ∈ Finset.Icc 1 Q,
        (1 / ((p-1 : ℕ) : ℝ)) * (1 / (Nat.totient e : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ => by positivity)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The genuine prime predecessor sum is dominated by the harmonic sum.
No estimate for the number or distribution of primes is used. -/
theorem prime_predecessor_sum_le_harmonic (Q : ℕ) :
    (∑ p ∈ chenPrimePrefix Q, 1 / ((p-1 : ℕ) : ℝ)) ≤ (harmonic (Q-1) : ℝ) := by
  let E := (chenPrimePrefix Q).image (fun p => p-1)
  have hE : E ⊆ Finset.Icc 1 (Q-1) := by
    intro e he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    have hdata := mem_chenPrimePrefix.mp hp
    have hp2 := hdata.2.two_le
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hinj : Set.InjOn (fun p => p-1) (chenPrimePrefix Q : Set ℕ) := by
    intro p hp r hr heq
    have hp2 := (mem_chenPrimePrefix.mp hp).2.two_le
    have hr2 := (mem_chenPrimePrefix.mp hr).2.two_le
    omega
  have hH : (harmonic (Q-1) : ℝ) =
      ∑ e ∈ Finset.Icc 1 (Q-1), 1/(e : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [hH]
  calc
    _ = ∑ e ∈ E, 1/(e : ℝ) := by rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ => by positivity)

/-- Two finite Fubini steps expose the true double-logarithmic correction. -/
theorem sum_prime_divisor_count_div_totient_le_harmonic
    (N Q : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q) :
    (∑ q ∈ S, chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) ≤
      (4*(1+Real.log (max 1 (Q : ℝ)))) * (harmonic (Q-1) : ℝ) := by
  have hpoint (q : ℕ) (hq : q ∈ S) :
      chenPrimeDivisorCount N q / (Nat.totient q : ℝ) ≤
        ∑ p ∈ chenPrimePrefix Q with p ∣ q, 1/(Nat.totient q : ℝ) := by
    have hsub : (chenPrimePrefix N).filter (fun p => p ∣ q) ⊆
        (chenPrimePrefix Q).filter (fun p => p ∣ q) := by
      intro p hp
      obtain ⟨hpN,hpq⟩ := Finset.mem_filter.mp hp
      have hprime := (mem_chenPrimePrefix.mp hpN).2
      have hqpos : 0 < q := (Finset.mem_Icc.mp (hS hq)).1
      exact Finset.mem_filter.mpr ⟨mem_chenPrimePrefix.mpr
        ⟨(Nat.le_of_dvd hqpos hpq).trans (Finset.mem_Icc.mp (hS hq)).2,hprime⟩,hpq⟩
    calc
      _ = ∑ p ∈ chenPrimePrefix N with p ∣ q, 1/(Nat.totient q : ℝ) := by
        simp only [chenPrimeDivisorCount,Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  calc
    _ ≤ ∑ q ∈ S, ∑ p ∈ chenPrimePrefix Q with p ∣ q, 1/(Nat.totient q : ℝ) :=
      Finset.sum_le_sum (fun q hq => hpoint q hq)
    _ = ∑ p ∈ chenPrimePrefix Q, ∑ q ∈ S with p ∣ q, 1/(Nat.totient q : ℝ) := by
      simp only [Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ p ∈ chenPrimePrefix Q,
        (1/((p-1 : ℕ) : ℝ)) * ∑ e ∈ Finset.Icc 1 Q, 1/(Nat.totient e : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_reciprocal_totient_prime_fiber_le S Q p hS hsq (mem_chenPrimePrefix.mp hp).2
    _ = (∑ p ∈ chenPrimePrefix Q, 1/((p-1 : ℕ) : ℝ)) *
        ∑ e ∈ Finset.Icc 1 Q, 1/(Nat.totient e : ℝ) := by rw [Finset.sum_mul]
    _ ≤ (harmonic (Q-1) : ℝ) * (4*(1+Real.log (max 1 (Q : ℝ)))) :=
      mul_le_mul (prime_predecessor_sum_le_harmonic Q) (sum_reciprocal_totient_le_log Q)
        (Finset.sum_nonneg (fun _ _ => by positivity))
        ((Finset.sum_nonneg (fun _ _ => by positivity)).trans
          (prime_predecessor_sum_le_harmonic Q))
    _ = _ := mul_comm _ _

/-- Explicit bound C=4 for every cap Q, including Q=0 and Q=1. -/
theorem sum_prime_divisor_count_div_totient_le_log_square
    (N Q : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q) :
    (∑ q ∈ S, chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) ≤
      4*(1+Real.log (max 1 (Q : ℝ)))^2 := by
  have hlog : Real.log ((Q-1 : ℕ) : ℝ) ≤ Real.log (max 1 (Q : ℝ)) := by
    by_cases hzero : Q-1 = 0
    · simpa only [hzero,Nat.cast_zero,Real.log_zero] using
        Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hzero)
        ((show ((Q-1 : ℕ) : ℝ) ≤ (Q : ℝ) by exact_mod_cast Nat.sub_le Q 1).trans
          (le_max_right _ _))
  have hH : (harmonic (Q-1) : ℝ) ≤ 1+Real.log (max 1 (Q : ℝ)) :=
    (harmonic_le_one_add_log (Q-1)).trans (add_le_add_left hlog 1)
  have hL : 0 ≤ 4*(1+Real.log (max 1 (Q : ℝ))) := by
    have hh := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    positivity
  calc
    _ ≤ (4*(1+Real.log (max 1 (Q : ℝ)))) * (harmonic (Q-1) : ℝ) :=
      sum_prime_divisor_count_div_totient_le_harmonic N Q S hS hsq
    _ ≤ (4*(1+Real.log (max 1 (Q : ℝ)))) * (1+Real.log (max 1 (Q : ℝ))) :=
      mul_le_mul_of_nonneg_left hH hL
    _ = _ := by ring

theorem abs_modulusPrimeMass_le_count (N : ℕ) (omega : ℕ → ℝ)
    (homega : ∀ p ∈ chenPrimePrefix N, |omega p| ≤ 1) (q : ℕ) :
    |modulusPrimeMass N omega q| ≤ chenPrimeDivisorCount N q := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ p ∈ chenPrimePrefix N with p ∣ q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact homega p (Finset.mem_filter.mp hp).1
    _ = _ := by simp [chenPrimeDivisorCount]

/-- The complete signed correction, for arbitrary bounded prime weights.
The absolute value is after the original same-rho modulus sum. -/
theorem abs_correction_le_log_square
    (N Q : ℕ) (S : Finset ℕ) (rho omega : ℕ → ℝ)
    (hS : S ⊆ Finset.Icc 1 Q) (hsq : ∀ q ∈ S, Squarefree q)
    (hrho : ∀ q ∈ S, |rho q| ≤ 1)
    (homega : ∀ p ∈ chenPrimePrefix N, |omega p| ≤ 1) :
    |correction N S rho omega| ≤ 4*(1+Real.log (max 1 (Q : ℝ)))^2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (sum_prime_divisor_count_div_totient_le_log_square N Q S hS hsq)
  apply Finset.sum_le_sum
  intro q hq
  rw [abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg (Nat.totient q))]
  calc
    _ ≤ 1 * (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) :=
      mul_le_mul (hrho q hq)
        (div_le_div_of_nonneg_right (abs_modulusPrimeMass_le_count N omega homega q)
          (Nat.cast_nonneg _))
        (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) zero_le_one
    _ = _ := one_mul _

/-- Weighted prime-prefix coprime mass loses precisely the prime divisors
of q; this is the full prefix, with no endpoint delta restriction. -/
theorem primePrefix_coprime_mass_eq_total_sub_modulusPrimeMass
    (N q : ℕ) (omega : ℕ → ℝ) :
    finiteCoprimeMass (chenPrimePrefix N) omega q =
      finiteSourceMass (chenPrimePrefix N) omega - modulusPrimeMass N omega q := by
  have hfilter : (chenPrimePrefix N).filter (fun p => Nat.Coprime p q) =
      (chenPrimePrefix N).filter (fun p => ¬p ∣ q) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp,hcop⟩
      exact ⟨hp,(mem_chenPrimePrefix.mp hp).2.coprime_iff_not_dvd.mp hcop⟩
    · rintro ⟨hp,hnot⟩
      exact ⟨hp,(mem_chenPrimePrefix.mp hp).2.coprime_iff_not_dvd.mpr hnot⟩
  unfold finiteCoprimeMass
  rw [hfilter]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := chenPrimePrefix N)
    (p := fun p => p ∣ q) (f := omega)
  unfold finiteSourceMass modulusPrimeMass
  linarith

/-- Exact original rank-one dictionary at the SAME physical rho.
Replacing the exact-coprime mean by total prime mass adds precisely the
modulus-prime correction paid above. No distribution estimate is assumed. -/
theorem singleton_PP_eq_total_prime_mean_add_correction
    (N : ℕ) (S : Finset ℕ) (rho omega : ℕ → ℝ) :
    Part3.primeProductSignedError 1 N N S rho (P5S1SingletonPP.singletonWeight N omega) =
      (∑ q ∈ S, rho q * (finiteCongruenceMass (chenPrimePrefix N) omega N q -
        finiteSourceMass (chenPrimePrefix N) omega / (Nat.totient q : ℝ))) +
      correction N S rho omega := by
  rw [P5S1SingletonPP.primeProductSignedError_singleton_eq]
  unfold correction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [finitePrimitiveDiscrepancy,primePrefix_coprime_mass_eq_total_sub_modulusPrimeMass]
  ring

theorem abs_singleton_PP_sub_total_prime_mean_le
    (N Q : ℕ) (S : Finset ℕ) (rho omega : ℕ → ℝ)
    (hS : S ⊆ Finset.Icc 1 Q) (hsq : ∀ q ∈ S, Squarefree q)
    (hrho : ∀ q ∈ S, |rho q| ≤ 1)
    (homega : ∀ p ∈ chenPrimePrefix N, |omega p| ≤ 1) :
    |Part3.primeProductSignedError 1 N N S rho (P5S1SingletonPP.singletonWeight N omega) -
      ∑ q ∈ S, rho q * (finiteCongruenceMass (chenPrimePrefix N) omega N q -
        finiteSourceMass (chenPrimePrefix N) omega / (Nat.totient q : ℝ))| ≤
      4*(1+Real.log (max 1 (Q : ℝ)))^2 := by
  rw [singleton_PP_eq_total_prime_mean_add_correction,add_sub_cancel_left]
  exact abs_correction_le_log_square N Q S rho omega hS hsq hrho homega

/-- Unit prime weights give exactly pi(N;q,N)-pi(N)/phi(q). -/
theorem abs_singleton_PP_sub_total_pi_error_le
    (N Q : ℕ) (S : Finset ℕ) (rho : ℕ → ℝ)
    (hS : S ⊆ Finset.Icc 1 Q) (hsq : ∀ q ∈ S, Squarefree q)
    (hrho : ∀ q ∈ S, |rho q| ≤ 1) :
    |Part3.primeProductSignedError 1 N N S rho (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
      ∑ q ∈ S, rho q * (chenPrimeAPCount N N q -
        ((chenPrimePrefix N).card : ℝ) / (Nat.totient q : ℝ))| ≤
      4*(1+Real.log (max 1 (Q : ℝ)))^2 := by
  simpa only [finiteCongruenceMass,chenPrimeAPCount,finiteSourceMass,
    Finset.sum_const,nsmul_eq_mul,mul_one] using
    abs_singleton_PP_sub_total_prime_mean_le N Q S rho (fun _ => 1) hS hsq hrho
      (fun _ _ => by norm_num)

/-- The actual first-exit causal coefficient supplies squarefree support
and |rho|<=1 itself. Only its genuine finite physical cap is required. -/
theorem actual_causal_singleton_PP_sub_total_pi_error_le
    (retainEven : List ℕ → Bool) (N cap Q : ℕ) (w z L : ℝ)
    (hQ : ∀ q ∈ P5S1OriginalLower.active retainEven N cap w z L, q ≤ Q) :
    |Part3.primeProductSignedError 1 N N (P5S1OriginalLower.active retainEven N cap w z L)
        (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
      ∑ q ∈ P5S1OriginalLower.active retainEven N cap w z L,
        actualLowerSmallRoughRho retainEven N cap w z L q * (chenPrimeAPCount N N q -
          ((chenPrimePrefix N).card : ℝ) / (Nat.totient q : ℝ))| ≤
      4*(1+Real.log (max 1 (Q : ℝ)))^2 := by
  apply abs_singleton_PP_sub_total_pi_error_le
  · intro q hq
    have hdata := P5S1SingletonPP.active_physical_data retainEven N cap w z L hq
    exact Finset.mem_Icc.mpr ⟨hdata.1,hQ q hq⟩
  · intro q hq
    exact (P5S1SingletonPP.active_physical_data retainEven N cap w z L hq).2.1
  · intro q hq
    exact actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q

/-- The genuine full modulus-prime correction is negligible uniformly at
all physical caps Q<=N. This follows from the proved power-log payment,
without any PNT or distribution assumption. -/
theorem eventually_log_square_cap_le_normalization (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ N →
      4*(1+Real.log (max 1 (Q : ℝ)))^2 ≤ epsilon*singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization 16 0 2 (by norm_num)
    epsilon hepsilon,eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)]
    with N hpaid hlog hN
  intro Q hQN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hNr (by exact_mod_cast hQN))
  have hL0 : 0 ≤ 1+Real.log (max 1 (Q : ℝ)) := by
    have hh := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    linarith
  have hL : 1+Real.log (max 1 (Q : ℝ)) ≤ 2*Real.log (N : ℝ) := by linarith
  have hs := (sq_le_sq₀ hL0 (by positivity : 0 ≤ 2*Real.log (N : ℝ))).mpr hL
  have hbound : 4*(1+Real.log (max 1 (Q : ℝ)))^2 ≤ 16*Real.log (N : ℝ)^2 := by
    nlinarith
  exact hbound.trans (by simpa only [Real.rpow_zero,mul_one] using hpaid)

/-- Actual same-rho rank-one PP and total-pi AP error have arbitrarily
small difference in the unchanged root normalization. The missing
analytic smooth PP and lower trim estimates remain separate obligations. -/
theorem eventually_actual_causal_singleton_PP_sub_total_pi_error_normalized
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap Q : ℕ) (w z L : ℝ),
      Q ≤ N → (∀ q ∈ P5S1OriginalLower.active retainEven N cap w z L, q ≤ Q) →
      |Part3.primeProductSignedError 1 N N (P5S1OriginalLower.active retainEven N cap w z L)
          (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
        ∑ q ∈ P5S1OriginalLower.active retainEven N cap w z L,
          actualLowerSmallRoughRho retainEven N cap w z L q * (chenPrimeAPCount N N q -
            ((chenPrimePrefix N).card : ℝ)/(Nat.totient q : ℝ))| ≤
          epsilon*singularNormalization N := by
  filter_upwards [eventually_log_square_cap_le_normalization epsilon hepsilon] with N hpaid
  intro retainEven cap Q w z L hQN hQ
  exact (actual_causal_singleton_PP_sub_total_pi_error_le retainEven N cap Q w z L hQ).trans
    (hpaid Q hQN)

end
end ImbalancedChen.P5PrimeDivisorMean
