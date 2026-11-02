import ImbalancedChen.P5ActualRoughHeathBrownWords
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact internal Mobius identity in the original prime-product completion,
section 5.  The support is ALL powers of primes dividing E, not squarefree
divisors of E.  This is a finite convolution identity, not a distribution
estimate or a replacement of the chart-rough slot by a prime coefficient.
-/
namespace ImbalancedChen.P5Z.ActualRoughMobiusConvolution
noncomputable section
open Classical Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open ImbalancedChen.Part3
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b
open ActualRoughHeathBrownWords

def PrimeSupported (E n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∣ E

def supportedOne (E : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else if PrimeSupported E n then 1 else 0, by simp⟩

def coprimeMu (E : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n.Coprime E then μ n else 0, by simp⟩

theorem primeSupported_one (E : ℕ) : PrimeSupported E 1 := by
  intro p hp h
  exact False.elim (hp.not_dvd_one h)

theorem primeSupported_mul (E a b : ℕ) :
    PrimeSupported E (a*b) ↔ PrimeSupported E a ∧ PrimeSupported E b := by
  constructor
  · intro h
    exact ⟨fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa b),
      fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb a)⟩
  · rintro ⟨ha,hb⟩ p hp h
    rcases hp.dvd_mul.mp h with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

theorem primeSupported_prime_pow (E : ℕ) {p j : ℕ}
    (hp : p.Prime) (hj : 0 < j) :
    PrimeSupported E (p^j) ↔ p ∣ E := by
  constructor
  · intro h
    exact h p hp (dvd_pow_self p hj.ne')
  · intro h r hr hrp
    have hrp' : r = p := Nat.prime_eq_prime_of_dvd_pow hr hp hrp
    simpa only [hrp'] using h

theorem supportedOne_multiplicative (E : ℕ) : (supportedOne E).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [supportedOne,primeSupported_one],?_⟩
  intro a b ha hb hab
  simp only [supportedOne,ArithmeticFunction.coe_mk,if_neg ha,if_neg hb,
    if_neg (mul_ne_zero ha hb),primeSupported_mul]
  by_cases hsa : PrimeSupported E a <;> by_cases hsb : PrimeSupported E b <;>
    simp [hsa,hsb]

theorem coprimeMu_multiplicative (E : ℕ) : (coprimeMu E).IsMultiplicative := by
  refine ⟨by simp [coprimeMu],?_⟩
  intro a b hab
  simp only [coprimeMu,ArithmeticFunction.coe_mk,Nat.coprime_mul_iff_left,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab]
  by_cases ha : a.Coprime E <;> by_cases hb : b.Coprime E <;> simp [ha,hb]

/-- The divisor sum of the coprime Mobius function detects exactly the
integers supported on primes of E.  E is allowed to be zero or nonsquarefree. -/
theorem coprimeMu_mul_zeta (E : ℕ) :
    coprimeMu E * (ζ : ArithmeticFunction ℤ) = supportedOne E := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    (coprimeMu E * (ζ : ArithmeticFunction ℤ))
    ((coprimeMu_multiplicative E).mul isMultiplicative_zeta.natCast)
    (supportedOne E) (supportedOne_multiplicative E)).mpr
  intro p j hp
  by_cases hj : j = 0
  · subst j
    simp [coprimeMu,supportedOne,primeSupported_one]
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj
  have hpj0 : p^j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpj1 : p^j ≠ 1 := (Nat.one_lt_pow hj hp.one_lt).ne'
  rw [show supportedOne E (p^j) = (if p ∣ E then (1 : ℤ) else 0) by
    simp only [supportedOne,ArithmeticFunction.coe_mk,if_neg hpj0,
      primeSupported_prime_pow E hp hjpos]]
  by_cases hE : p ∣ E
  · rw [if_pos hE,coe_mul_zeta_apply,Nat.sum_divisors_prime_pow hp,
      Finset.sum_range_succ']
    have hzero (i : ℕ) : coprimeMu E (p^(i+1)) = 0 := by
      simp [coprimeMu,Nat.coprime_pow_left_iff (Nat.succ_pos i),
        hp.coprime_iff_not_dvd,hE]
    simp [hzero,coprimeMu]
  · rw [if_neg hE]
    have hco : p.Coprime E := hp.coprime_iff_not_dvd.mpr hE
    have heq : (coprimeMu E * (ζ : ArithmeticFunction ℤ)) (p^j) =
        (μ * (ζ : ArithmeticFunction ℤ)) (p^j) := by
      rw [coe_mul_zeta_apply,coe_mul_zeta_apply,
        Nat.sum_divisors_prime_pow hp,Nat.sum_divisors_prime_pow hp]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [coprimeMu,ArithmeticFunction.coe_mk,if_pos (hco.pow_left i)]
    rw [heq,ArithmeticFunction.moebius_mul_coe_zeta]
    simp [ArithmeticFunction.one_apply,hpj1]

/-- Convolution with the unrestricted Mobius function removes the zeta
factor.  This is proved internally, not supplied as a convolution licence. -/
theorem supportedOne_mul_moebius (E : ℕ) :
    supportedOne E * μ = coprimeMu E := by
  rw [← coprimeMu_mul_zeta E,mul_assoc,ArithmeticFunction.coe_zeta_mul_moebius,mul_one]

/-- Literal finite identity from the manuscript, with every prime power w
allowed.  A sum merely over w dividing E would be a different, false identity. -/
theorem coprime_moebius_eq_supported_divisor_sum (E : ℕ) {n : ℕ} (hn : 0 < n) :
    (if n.Coprime E then μ n else 0) =
      ∑ w ∈ n.divisors with PrimeSupported E w, μ (n/w) := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) (supportedOne_mul_moebius E)
  change (supportedOne E * μ) n = (if n.Coprime E then μ n else 0) at h
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal] at h
  rw [← h,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  have hw0 : w ≠ 0 := (Nat.pos_of_mem_divisors hw).ne'
  by_cases hs : PrimeSupported E w <;> simp [supportedOne,hw0,hs]

theorem moebius_mul_exact (a b : ℕ) :
    μ (a*b) = if a.Coprime b then μ a*μ b else 0 := by
  by_cases h : a.Coprime b
  · rw [if_pos h,ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  · rw [if_neg h]
    exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (fun hs => h (Nat.coprime_of_squarefree_mul hs))

/-- The genuine strict chart-rough Mobius slot is the same finite
convolution for E = product of the primes p <= z, including a prime at z. -/
theorem roughMoebius_eq_supported_divisor_sum {z : ℝ} (hz : 0 ≤ z)
    {n : ℕ} (hn : 0 < n) :
    roughMoebiusSlot z n =
      ∑ w ∈ n.divisors with PrimeSupported (smallProduct z) w,
        ((μ (n/w) : ℤ) : ℂ) := by
  have h := congrArg (fun a : ℤ => (a : ℂ))
    (coprime_moebius_eq_supported_divisor_sum (smallProduct z) hn)
  simp only [Int.cast_sum] at h
  rw [roughMoebiusSlot,roughOneSlot_eq_coprime_indicator hz]
  by_cases hc : n.Coprime (smallProduct z)
  · simpa only [hc,if_true,mul_one] using h
  · simpa only [hc,if_false,mul_zero,Int.cast_zero] using h

/-- The ORIGINAL real cutoff is retained exactly.  No floor, strict-cutoff
change, or prime singleton replacement occurs in this coefficient identity. -/
theorem roughMuTrunc_eq_supported_divisor_sum {z : ℝ} (hz : 0 ≤ z)
    (y : ℝ) {n : ℕ} (hn : 0 < n) :
    actual z y .mobius n =
      if (n : ℝ) ≤ y then
        ∑ w ∈ n.divisors with PrimeSupported (smallProduct z) w,
          ((μ (n/w) : ℤ) : ℂ)
      else 0 := by
  simp only [actual,roughMuTrunc,roughMoebius_eq_supported_divisor_sum hz hn]

end
end ImbalancedChen.P5Z.ActualRoughMobiusConvolution
