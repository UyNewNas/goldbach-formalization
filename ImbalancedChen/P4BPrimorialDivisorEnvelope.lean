import ImbalancedChen.RoughAbsoluteDensity
import ImbalancedChen.P4BPrimitiveModulusEndpoints

/-!
# Prime-divisible absolute rho mass without a modulus-size premise

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The injection d -> d/ell stays among divisors of the same sieve primorial.
Its full reciprocal-totient mass is an exact finite Euler product. The proved
Goldbach inverse-interval estimate bounds this product by C log z uniformly
in every even target. This replaces a log(max q) cost by log z without any
polynomial support assertion for the retained policy.

The actual attached coefficient supplies both its unit amplitude and its
primorial divisibility. No full22 history, P3 saving, or currentK density is
assumed or produced here. The missing original full22 range remains relevant
to P3 geometric licensing, although this arithmetic estimate does not need it.
-/

namespace ImbalancedChen.P4BPrimorialDivisorEnvelope

noncomputable section
open scoped Classical BigOperators
open P4BPrimitiveModulusEndpoints

/-- Dividing a prime-divisible positive divisor by that prime is injective
and remains in the same divisor lattice. Totient supermultiplicativity
retains the estimate even when the prime occurs more than once. -/
theorem prime_divisible_reciprocalTotient_le_divisor_mass
    (M : ℕ) (hM : M ≠ 0) (D : Finset ℕ) (hD : D ⊆ M.divisors)
    (ell : ℕ) (hell : Nat.Prime ell) :
    (∑ d ∈ D, if ell ∣ d then 1 / (Nat.totient d : ℝ) else 0) ≤
      (1 / ((ell : ℝ) - 1)) * ∑ m ∈ M.divisors, 1 / (Nat.totient m : ℝ) := by
  let T := D.filter (fun d => ell ∣ d)
  have hT : ∀ d ∈ T, 0 < d ∧ ell ∣ d := by
    intro d hd
    obtain ⟨hdD, hdell⟩ := Finset.mem_filter.mp hd
    have hdM := (Nat.mem_divisors.mp (hD hdD)).1
    have hd0 : d ≠ 0 := by
      intro hz
      rw [hz, zero_dvd_iff] at hdM
      exact hM hdM
    exact ⟨Nat.pos_of_ne_zero hd0, hdell⟩
  have hquotpos : ∀ d ∈ T, 0 < d / ell := by
    intro d hd
    apply Nat.pos_of_ne_zero
    intro hz
    have heq := Nat.mul_div_cancel' (hT d hd).2
    rw [hz, mul_zero] at heq
    exact (hT d hd).1.ne' heq.symm
  have hinj : Set.InjOn (fun d : ℕ => d / ell) (T : Set ℕ) := by
    intro d hd e he hde
    calc
      d = ell * (d / ell) := (Nat.mul_div_cancel' (hT d hd).2).symm
      _ = ell * (e / ell) := congrArg (fun a : ℕ => ell * a) hde
      _ = e := Nat.mul_div_cancel' (hT e he).2
  have hquot : T.image (fun d => d / ell) ⊆ M.divisors := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    have hdM := (Nat.mem_divisors.mp (hD (Finset.mem_filter.mp hd).1)).1
    have hdiv : d / ell ∣ d :=
      ⟨ell, (Nat.div_mul_cancel (hT d hd).2).symm⟩
    exact Nat.mem_divisors.mpr ⟨hdiv.trans hdM, hM⟩
  have hellPhi : (0 : ℝ) < Nat.totient ell := by
    exact_mod_cast Nat.totient_pos.mpr hell.pos
  have hterm : ∀ d ∈ T, 1 / (Nat.totient d : ℝ) ≤
      (1 / (Nat.totient ell : ℝ)) * (1 / (Nat.totient (d / ell) : ℝ)) := by
    intro d hd
    have hmPhi : (0 : ℝ) < Nat.totient (d / ell) := by
      exact_mod_cast Nat.totient_pos.mpr (hquotpos d hd)
    have hsuper : (Nat.totient ell : ℝ) * (Nat.totient (d / ell) : ℝ) ≤
        (Nat.totient d : ℝ) := by
      have h := Nat.totient_super_multiplicative ell (d / ell)
      rw [Nat.mul_div_cancel' (hT d hd).2] at h
      exact_mod_cast h
    calc
      _ ≤ 1 / ((Nat.totient ell : ℝ) * (Nat.totient (d / ell) : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos hellPhi hmPhi) hsuper
      _ = _ := by simp only [one_div, mul_inv_rev]; ring
  have hellCast : (Nat.totient ell : ℝ) = (ell : ℝ) - 1 := by
    rw [Nat.totient_prime hell, Nat.cast_sub hell.one_le, Nat.cast_one]
  calc
    _ = ∑ d ∈ T, 1 / (Nat.totient d : ℝ) := by simp only [T, Finset.sum_filter]
    _ ≤ ∑ d ∈ T,
        (1 / (Nat.totient ell : ℝ)) * (1 / (Nat.totient (d / ell) : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (1 / (Nat.totient ell : ℝ)) *
        ∑ m ∈ T.image (fun d => d / ell), 1 / (Nat.totient m : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ (1 / (Nat.totient ell : ℝ)) * ∑ m ∈ M.divisors, 1 / (Nat.totient m : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hquot (fun _ _ _ => by positivity))
        (one_div_nonneg.mpr hellPhi.le)
    _ = _ := by rw [hellCast]

/-- The whole sieve primorial has logarithmic reciprocal-totient mass,
uniformly over all even targets. Its largest divisor can be much larger
than any fixed power of N; no bound for that divisor is used. -/
theorem exists_sievePrimorial_divisor_mass_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ N z : ℕ, Even N → (2 : ℝ) ≤ z →
      (∑ d ∈ (sieveProduct N z).divisors, 1 / (Nat.totient d : ℝ)) ≤
        C * Real.log (z : ℝ) := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hKpos : 0 < K := zero_lt_one.trans hK
  let C : ℝ := (1 + K / Real.log 2) / Real.log 2
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N z hEven hz
  let P := sievePrimes N z
  have hprime : ∀ p ∈ P, Nat.Prime p := fun p hp => (mem_sievePrimes.mp hp).2.1
  have hcop : ∀ p ∈ P, Nat.Coprime p N := by
    intro p hp
    exact (hprime p hp).coprime_iff_not_dvd.mpr (mem_sievePrimes.mp hp).2.2
  have hodd : ∀ p ∈ P, Nat.Prime p ∧ 2 < p := by
    intro p hp
    have hp2 := (hprime p hp).two_le
    have hne : p ≠ 2 := by
      intro heq
      exact (mem_sievePrimes.mp hp).2.2 (by simpa only [heq] using hEven.two_dvd)
    exact ⟨hprime p hp, by omega⟩
  have hprod : (∏ p ∈ P, 1 + 1 / ((p : ℝ) - 1)) ≤
      ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (hodd p hp).2
      have hp1 : 0 < (p : ℝ) - 1 := by linarith only [hp2]
      exact add_nonneg zero_le_one (div_nonneg zero_le_one hp1.le)
    · intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (hodd p hp).2
      have hx : (1 : ℝ) / ((p : ℝ) - 1) < 1 :=
        (div_lt_one (by linarith only [hp2])).mpr (by linarith only [hp2])
      rw [← one_div]
      apply (le_div_iff₀ (sub_pos.mpr hx)).mpr
      nlinarith only [sq_nonneg (1 / ((p : ℝ) - 1))]
  have hbound := hinterval P hodd 2 (z : ℝ) (by norm_num) hz (by
    intro p hp
    exact ⟨by exact_mod_cast (hprime p hp).two_le,
      by exact_mod_cast (mem_sievePrimes.mp hp).1⟩)
  calc
    _ = ∏ p ∈ P, 1 + 1 / ((p : ℝ) - 1) :=
      reciprocalTotient_sum_divisors_primeProduct N P hprime hcop
    _ ≤ ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1))⁻¹ := hprod
    _ ≤ Real.log (z : ℝ) / Real.log 2 * (1 + K / Real.log 2) := hbound
    _ = C * Real.log (z : ℝ) := by dsimp only [C]; ring

/-- The actual same-rho prime-divisible mass has a logarithmic sieve-cap
envelope even for arbitrary retention and arbitrarily large active moduli. -/
theorem exists_actual_upper_prime_divisor_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ nu r epsilon : ℝ, 0 < nu → 0 < r → epsilon ^ 2 ≤ r →
      ∀ (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ), Even N → 2 ≤ N →
      ∀ ell : ℕ, Nat.Prime ell →
        (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
          if ell ∣ d then |attachedUpperCoefficient nu r epsilon retain cap N d| /
            (Nat.totient d : ℝ) else 0) ≤
          (C * (nu * r + 1) * Real.log (N : ℝ)) / ((ell : ℝ) - 1) := by
  obtain ⟨C, hC, hmass⟩ := exists_sievePrimorial_divisor_mass_le_log
  refine ⟨C, hC, ?_⟩
  intro nu r epsilon hnu hr hepsilon retain cap N hEven hN ell hell
  let Z : ℕ := Nat.ceil ((N : ℝ) ^ (nu * r))
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hpowOne : 1 < (N : ℝ) ^ (nu * r) := Real.one_lt_rpow hN1 (mul_pos hnu hr)
  have hZ : 2 ≤ Z := Nat.add_one_le_ceil_iff.mpr hpowOne
  have hZreal : (2 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hdiv : attachedUpperModuli nu r epsilon retain cap N ⊆
      (sieveProduct N Z).divisors := by
    intro d hd
    apply Nat.mem_divisors.mpr
    exact ⟨actualSmallRoughModuli_dvd_sieveProduct_ceil (retain N) N (cap N) _ _
      (Real.rpow_le_rpow_of_exponent_le hN1.le
        (mul_le_mul_of_nonneg_left hepsilon hnu.le)) hd,
      (sieveProduct_squarefree N Z).ne_zero⟩
  have hprimeBound := prime_divisible_reciprocalTotient_le_divisor_mass
    (sieveProduct N Z) (sieveProduct_squarefree N Z).ne_zero
    (attachedUpperModuli nu r epsilon retain cap N) hdiv ell hell
  have hell2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell.two_le
  have hell1 : 0 < (ell : ℝ) - 1 := by linarith only [hell2]
  have hZupper : (Z : ℝ) ≤ 2 * (N : ℝ) ^ (nu * r) := by
    have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hNpos.le (nu * r))).le
    change (Z : ℝ) ≤ (N : ℝ) ^ (nu * r) + 1 at hceil
    linarith only [hceil, hpowOne]
  have hlogZ : Real.log (Z : ℝ) ≤ (nu * r + 1) * Real.log (N : ℝ) := by
    have hlog := Real.log_le_log (by exact_mod_cast (show 0 < Z by omega)) hZupper
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hNpos _).ne', Real.log_rpow hNpos] at hlog
    have hlog2 : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    nlinarith only [hlog, hlog2]
  calc
    _ ≤ ∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        if ell ∣ d then 1 / (Nat.totient d : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · exact div_le_div_of_nonneg_right
          (actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d) (Nat.cast_nonneg _)
      · exact le_rfl
    _ ≤ (1 / ((ell : ℝ) - 1)) *
        ∑ m ∈ (sieveProduct N Z).divisors, 1 / (Nat.totient m : ℝ) := hprimeBound
    _ ≤ (1 / ((ell : ℝ) - 1)) * (C * Real.log (Z : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass N Z hEven hZreal) (one_div_nonneg.mpr hell1.le)
    _ ≤ (1 / ((ell : ℝ) - 1)) * (C * ((nu * r + 1) * Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogZ hC.le)
        (one_div_nonneg.mpr hell1.le)
    _ = _ := by ring

end
end ImbalancedChen.P4BPrimorialDivisorEnvelope
