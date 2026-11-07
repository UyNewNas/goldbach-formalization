import ImbalancedChen.P5ActualRoughMobiusConvolution
import ImbalancedChen.DivisorMomentBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite supported-prime Rankin bounds.  The support contains ALL prime
powers, not only squarefree divisors.  Neither an Euler-product bound nor
a supported-tail estimate is an input.  The only divisor moment used is
the fourth convolution power of the reciprocal function, proved below.
-/
namespace ImbalancedChen.P5Z.ActualRoughMobiusRankin
noncomputable section
open Classical Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta
open ActualRoughMobiusConvolution

def supportedCarrier (E H : ℕ) : Finset ℕ :=
  (Icc 1 H).filter (PrimeSupported E)

theorem primeSupported_coprime {E w q : ℕ}
    (hE : E.Coprime q) (hw : PrimeSupported E w) : w.Coprime q := by
  by_contra h
  obtain ⟨p,hp,hpw,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (hp.not_dvd_one) (by
    rw [← hE]
    exact Nat.dvd_gcd (hw p hp hpw) hpq)

theorem primeSupported_dvd_pow {E w H : ℕ} (hE : E ≠ 0)
    (hw : 0 < w) (hwH : w ≤ H) (hs : PrimeSupported E w) : w ∣ E^H := by
  have hsub : w.primeFactors ⊆ E.primeFactors := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      (hs p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)) hE
  exact ((Nat.dvd_pow_self_iff hw.ne' hE).mpr hsub).trans
    (pow_dvd_pow E hwH)

/-- A genuine arithmetic function at zero; the negative exponent is
nonzero, so the real-power convention gives value zero there. -/
def reciprocalHalf : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)^(-(1/2 : ℝ)), by norm_num⟩

theorem reciprocalHalf_apply (n : ℕ) :
    reciprocalHalf n = (n : ℝ)^(-(1/2 : ℝ)) := rfl

theorem reciprocalHalf_nonneg (n : ℕ) : 0 ≤ reciprocalHalf n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem reciprocalHalf_multiplicative : reciprocalHalf.IsMultiplicative := by
  refine ⟨by simp [reciprocalHalf],?_⟩
  intro a b hab
  simp only [reciprocalHalf,ArithmeticFunction.coe_mk,Nat.cast_mul]
  exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

theorem reciprocalHalf_prime_le_three_quarters {p : ℕ} (hp : p.Prime) :
    reciprocalHalf p ≤ 3/4 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs : (reciprocalHalf p)^2 = (p : ℝ)⁻¹ := by
    rw [reciprocalHalf_apply,← Real.rpow_natCast,
      ← Real.rpow_mul hpR.le]
    norm_num
  have hi : (p : ℝ)⁻¹ ≤ (1/2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hp2
  have hnonneg := reciprocalHalf_nonneg p
  nlinarith

theorem geometric_sum_le_four {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 3/4)
    (K : ℕ) : (∑ j ∈ range K, r^j) ≤ 4 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ']
      simp only [pow_zero,pow_succ,← Finset.sum_mul]
      have h := mul_le_mul_of_nonneg_right ih hr0
      nlinarith

theorem reciprocalHalf_prime_power_sum_le {p : ℕ} (hp : p.Prime) (K : ℕ) :
    (∑ j ∈ range K, reciprocalHalf (p^j)) ≤ 4 := by
  have heq (j : ℕ) : reciprocalHalf (p^j) = (reciprocalHalf p)^j := by
    simp only [reciprocalHalf_apply,Nat.cast_pow]
    calc
      ((p : ℝ)^j)^(-(1/2 : ℝ)) = (p : ℝ)^((j : ℝ)*(-(1/2 : ℝ))) :=
        (Real.rpow_natCast_mul (Nat.cast_nonneg p) j _).symm
      _ = (p : ℝ)^((-(1/2 : ℝ))*(j : ℝ)) := by rw [mul_comm]
      _ = _ := Real.rpow_mul_natCast (Nat.cast_nonneg p) _ j
  simp_rw [heq]
  exact geometric_sum_le_four (reciprocalHalf_nonneg p)
    (reciprocalHalf_prime_le_three_quarters hp) K

theorem reciprocalHalf_divisor_sum_eq {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, reciprocalHalf d) =
      ∏ p ∈ n.primeFactors,
        ∑ j ∈ range (n.factorization p+1), reciprocalHalf (p^j) := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    (reciprocalHalf_multiplicative.mul isMultiplicative_zeta.natCast).
      multiplicative_factorization _ hn]
  apply Finset.prod_congr n.support_factorization
  intro p hp
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

theorem reciprocalHalf_divisor_sum_le {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, reciprocalHalf d) ≤ (4 : ℝ)^n.primeFactors.card := by
  rw [reciprocalHalf_divisor_sum_eq hn,← Finset.prod_const]
  exact Finset.prod_le_prod
    (fun p _ => Finset.sum_nonneg (fun j _ => reciprocalHalf_nonneg _))
    (fun p hp => reciprocalHalf_prime_power_sum_le
      (Nat.prime_of_mem_primeFactors hp) _)

theorem four_pow_primeFactors_le_divisor_square {E : ℕ} (hE : E ≠ 0) :
    (4 : ℝ)^E.primeFactors.card ≤ (E.divisors.card : ℝ)^2 := by
  have htwo : (2 : ℝ)^E.primeFactors.card ≤ (E.divisors.card : ℝ) := by
    rw [Nat.card_divisors hE,Nat.cast_prod,← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by norm_num)
    intro p hp
    have hf := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
      hE (Nat.dvd_of_mem_primeFactors hp)
    have : 2 ≤ E.factorization p+1 := by omega
    exact_mod_cast this
  calc
    (4 : ℝ)^E.primeFactors.card = ((2 : ℝ)^E.primeFactors.card)^2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    _ ≤ _ := pow_le_pow_left₀ (by positivity) htwo 2

/-- All supported powers up to the actual finite cap are retained. -/
theorem supported_reciprocalHalf_sum_le (E H : ℕ) (hE : E ≠ 0) :
    (∑ w ∈ supportedCarrier E H, (w : ℝ)^(-(1/2 : ℝ))) ≤
      (E.divisors.card : ℝ)^2 := by
  by_cases hH : H = 0
  · simpa [supportedCarrier,hH] using sq_nonneg (E.divisors.card : ℝ)
  have hsub : supportedCarrier E H ⊆ (E^H).divisors := by
    intro w hw
    obtain ⟨hwI,hws⟩ := Finset.mem_filter.mp hw
    obtain ⟨hw1,hwH⟩ := Finset.mem_Icc.mp hwI
    exact Nat.mem_divisors.mpr
      ⟨primeSupported_dvd_pow hE hw1 hwH hws,pow_ne_zero _ hE⟩
  calc
    _ = ∑ w ∈ supportedCarrier E H, reciprocalHalf w := rfl
    _ ≤ ∑ w ∈ (E^H).divisors, reciprocalHalf w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun w _ _ => reciprocalHalf_nonneg w)
    _ ≤ (4 : ℝ)^(E^H).primeFactors.card :=
      reciprocalHalf_divisor_sum_le (pow_ne_zero _ hE)
    _ = (4 : ℝ)^E.primeFactors.card := by rw [Nat.primeFactors_pow E hH]
    _ ≤ _ := four_pow_primeFactors_le_divisor_square hE

theorem supported_reciprocal_sum_le (E H : ℕ) (hE : E ≠ 0) :
    (∑ w ∈ supportedCarrier E H, 1/(w : ℝ)) ≤ (E.divisors.card : ℝ)^2 := by
  refine (Finset.sum_le_sum (fun w hw => ?_)).trans
    (supported_reciprocalHalf_sum_le E H hE)
  have hw1 : (1 : ℝ) ≤ w := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hw).1).1
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hw1 (by norm_num)

theorem rankin_point {V : ℝ} (hV : 0 < V) {w : ℕ}
    (hw : V^(1/4 : ℝ) < (w : ℝ)) :
    1/(w : ℝ) ≤ V^(-(1/8 : ℝ)) * (w : ℝ)^(-(1/2 : ℝ)) := by
  have hw0 : (0 : ℝ) < w := (Real.rpow_pos_of_pos hV _).trans hw
  have hhalf := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hV (1/4 : ℝ)) hw.le (by norm_num : -(1/2 : ℝ) ≤ 0)
  rw [← Real.rpow_mul hV.le] at hhalf
  norm_num at hhalf
  calc
    1/(w : ℝ) = (w : ℝ)^(-(1/2 : ℝ)) * (w : ℝ)^(-(1/2 : ℝ)) := by
      rw [← Real.rpow_add hw0]
      norm_num [one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hw0.le _)

/-- The manuscript's Rankin exponent and fixed divisor square. -/
theorem supported_large_tail_le (E H : ℕ) (hE : E ≠ 0)
    {V : ℝ} (hV : 0 < V) :
    (∑ w ∈ (supportedCarrier E H).filter (fun w => V^(1/4 : ℝ)<(w:ℝ)),
      2*V/(w : ℝ)) ≤ 2*V^(7/8 : ℝ)*(E.divisors.card : ℝ)^2 := by
  let T := (supportedCarrier E H).filter (fun w => V^(1/4 : ℝ)<(w:ℝ))
  have htail : (∑ w ∈ T, 1/(w : ℝ)) ≤
      V^(-(1/8 : ℝ))*(E.divisors.card : ℝ)^2 := by
    calc
      _ ≤ ∑ w ∈ T, V^(-(1/8 : ℝ))*(w : ℝ)^(-(1/2 : ℝ)) :=
        Finset.sum_le_sum (fun w hw => rankin_point hV (Finset.mem_filter.mp hw).2)
      _ = V^(-(1/8 : ℝ))*(∑ w ∈ T, (w : ℝ)^(-(1/2 : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ V^(-(1/8 : ℝ))*(∑ w ∈ supportedCarrier E H,
          (w : ℝ)^(-(1/2 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hV.le _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun w _ _ => Real.rpow_nonneg (Nat.cast_nonneg w) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (supported_reciprocalHalf_sum_le E H hE)
        (Real.rpow_nonneg hV.le _)
  calc
    _ = (2*V)*(∑ w ∈ T, 1/(w : ℝ)) := by simp only [Finset.mul_sum]; ring
    _ ≤ (2*V)*(V^(-(1/8 : ℝ))*(E.divisors.card : ℝ)^2) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by
      have hp : V*V^(-(1/8 : ℝ)) = V^(7/8 : ℝ) := by
        nth_rw 1 [← Real.rpow_one V]
        rw [← Real.rpow_add hV]
        norm_num
      calc
        (2*V)*(V^(-(1/8 : ℝ))*(E.divisors.card : ℝ)^2) =
            2*(V*V^(-(1/8 : ℝ)))*(E.divisors.card : ℝ)^2 := by ring
        _ = _ := by rw [hp]

def reciprocal : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩

theorem reciprocal_nonneg (n : ℕ) : 0 ≤ reciprocal n := by
  simp only [reciprocal,ArithmeticFunction.coe_mk]
  positivity

theorem reciprocal_multiplicative : reciprocal.IsMultiplicative := by
  refine ⟨by simp [reciprocal],?_⟩
  intro a b hab
  simp [reciprocal,Nat.cast_mul,mul_inv_rev,mul_comm]

theorem reciprocal_pow_prime (j : ℕ) {p : ℕ} (hp : p.Prime) :
    (reciprocal^j) p = (j : ℝ)*reciprocal p := by
  induction j with
  | zero => simp [ArithmeticFunction.one_apply,hp.ne_one]
  | succ j ih =>
      have hunit : (reciprocal^j) 1 = 1 := reciprocal_multiplicative.pow.map_one
      have hnot : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
        simpa only [Finset.mem_singleton] using hp.ne_one.symm
      rw [pow_succ,ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (fun a b => (reciprocal^j) a*reciprocal b),hp.divisors]
      simp only [Finset.sum_insert hnot,Finset.sum_singleton,Nat.div_one,
        Nat.div_self hp.pos,hunit,show reciprocal 1 = 1 by simp [reciprocal],
        one_mul,mul_one,ih,Nat.cast_succ]
      ring

/-- Squarefreeness of the actual Brun support makes order FOUR exact. -/
theorem reciprocal_fourth_squarefree {n : ℕ} (hn : Squarefree n) :
    (reciprocal^4) n = (n.divisors.card : ℝ)^2/(n : ℝ) := by
  have hpow : (n.divisors.card : ℝ)^2 = ∏ p ∈ n.primeFactors, (4 : ℝ) := by
    rw [ImbalancedChen.squarefree_divisors_card_eq_prod_two hn,← Finset.prod_pow]
    norm_num
  rw [← reciprocal_multiplicative.pow.prod_primeFactors hn]
  calc
    _ = ∏ p ∈ n.primeFactors, (4 : ℝ)*reciprocal p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact reciprocal_pow_prime 4 (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, (4 : ℝ))*reciprocal n := by
      rw [Finset.prod_mul_distrib,reciprocal_multiplicative.prod_primeFactors hn]
    _ = _ := by rw [← hpow]; rfl

theorem squarefree_divisor_square_harmonic_le (S : Finset ℕ) (D : ℕ)
    (hS : S ⊆ Icc 1 D) (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (d.divisors.card : ℝ)^2/(d : ℝ)) ≤
      (1+Real.log (max 1 (D : ℝ)))^4 := by
  have hsum : (∑ d ∈ Icc 1 D, reciprocal d) ≤
      1+Real.log (max 1 (D : ℝ)) := by
    have hh : (∑ d ∈ Icc 1 D, reciprocal d) = (harmonic D : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
        reciprocal,ArithmeticFunction.coe_mk]
    rw [hh]
    by_cases hD : D = 0
    · simp [hD]
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hD
    rw [max_eq_right hD1]
    exact harmonic_le_one_add_log D
  calc
    _ = ∑ d ∈ S, (reciprocal^4) d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (reciprocal_fourth_squarefree (hsq d hd)).symm
    _ ≤ ∑ d ∈ Icc 1 D, (reciprocal^4) d :=
      Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun d _ _ => ImbalancedChen.arithmeticFunction_pow_nonneg
          reciprocal reciprocal_nonneg 4 d)
    _ ≤ (∑ d ∈ Icc 1 D, reciprocal d)^4 := by
      simpa using ImbalancedChen.sum_arithmeticFunction_pow_succ_le
        reciprocal reciprocal_nonneg 3 D
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ => reciprocal_nonneg d)) hsum 4

/-- Summing the Rankin envelope over any actual squarefree Brun carrier
uses a fixed log-four loss, independent of the requested accuracy. -/
theorem brun_rankin_sum_le (S : Finset ℕ) {U : ℝ} (hU : 1 ≤ U)
    (hS : S ⊆ Icc 1 (Nat.floor (U^(1/4 : ℝ))))
    (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, 2*(U/(d : ℝ))^(7/8 : ℝ)*(d.divisors.card : ℝ)^2) ≤
      2*U^(29/32 : ℝ)*(1+Real.log U)^4 := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hD0 : 0 ≤ U^(1/4 : ℝ) := Real.rpow_nonneg hU0.le _
  have hpower : U^(1/4 : ℝ) ≤ U := by
    nth_rw 2 [← Real.rpow_one U]
    exact Real.rpow_le_rpow_of_exponent_le hU (by norm_num)
  have hmass := squarefree_divisor_square_harmonic_le S _ hS hsq
  have hlog : (1+Real.log (max 1 (Nat.floor (U^(1/4 : ℝ)) : ℝ)))^4 ≤
      (1+Real.log U)^4 := by
    have hmax : max 1 (Nat.floor (U^(1/4 : ℝ)) : ℝ) ≤ U :=
      max_le hU ((Nat.floor_le hD0).trans hpower)
    apply pow_le_pow_left₀
      (by have := Real.log_nonneg (le_max_left 1 (Nat.floor (U^(1/4 : ℝ)) : ℝ)); linarith)
      (add_le_add_left (Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax) 1) 4
  calc
    _ ≤ ∑ d ∈ S, (2*U^(29/32 : ℝ))*((d.divisors.card : ℝ)^2/(d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp (hS hd)).1
      have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
      have hdU : (d : ℝ) ≤ U^(1/4 : ℝ) :=
        (Nat.le_floor_iff hD0).mp (Finset.mem_Icc.mp (hS hd)).2
      have heighth := Real.rpow_le_rpow hd0.le hdU (by norm_num : (0:ℝ)≤1/8)
      rw [← Real.rpow_mul hU0.le] at heighth
      norm_num at heighth
      have hid : (U/(d : ℝ))^(7/8 : ℝ) =
          U^(7/8 : ℝ)*(d : ℝ)^(1/8 : ℝ)/(d : ℝ) := by
        rw [Real.div_rpow hU0.le hd0.le]
        have hsplit : (d : ℝ)^(7/8 : ℝ)*(d : ℝ)^(1/8 : ℝ) = d := by
          rw [← Real.rpow_add hd0]; norm_num
        field_simp [(Real.rpow_pos_of_pos hd0 (7/8 : ℝ)).ne',hd0.ne']
        calc
          U^(7/8 : ℝ)*(d : ℝ) =
              U^(7/8 : ℝ)*((d : ℝ)^(7/8 : ℝ)*(d : ℝ)^(1/8 : ℝ)) := by rw [hsplit]
          _ = _ := by ring
      rw [hid]
      have hp : U^(7/8 : ℝ)*U^(1/32 : ℝ) = U^(29/32 : ℝ) := by
        rw [← Real.rpow_add hU0]; norm_num
      have h := mul_le_mul_of_nonneg_left heighth (Real.rpow_nonneg hU0.le (7/8 : ℝ))
      rw [hp] at h
      have hh := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right h hd0.le) (sq_nonneg (d.divisors.card : ℝ))
      nlinarith
    _ = (2*U^(29/32 : ℝ))*(∑ d ∈ S,(d.divisors.card : ℝ)^2/(d : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2*U^(29/32 : ℝ))*(1+Real.log U)^4 :=
      mul_le_mul_of_nonneg_left (hmass.trans hlog) (by positivity)

end
end ImbalancedChen.P5Z.ActualRoughMobiusRankin
