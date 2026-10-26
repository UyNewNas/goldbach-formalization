import ImbalancedChen.Part3CentralHeightLogEuler

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The reflected central constant is computed from the genuine finite height
logarithms. A zero in every distinct local Euler factor leaves precisely a
single-prime logarithmic contribution. With two distinct primes the whole
central reflected constant vanishes. These are conclusions about the
actual completed mean and the actual ordinary central derivative, without
substitution into a totalized Lambda quotient at its pole.
-/

noncomputable section
open Set Complex
open scoped BigOperators UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinCentralHeight
open ImbalancedChen.Part3.OrdinaryCentralFourierMeans20261026b
open ImbalancedChen.Part3.CentralHeightLogEuler20261026b
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.CentralReflectedLogEuler20261026b

/-- The exact vanishing local Euler product at the antidiagonal exponent. -/
def zeroEulerProduct (S : Finset PrimeIndex) : ℂ := ∏ p ∈ S, (0 : ℂ)

/-- Its explicit first logarithmic coefficient; empty complementary products
are one. This definition involves no choice of a prime divisor. -/
def zeroEulerLog (S : Finset PrimeIndex) : ℂ :=
  ∑ p ∈ S, primeLog p * zeroEulerProduct (S.erase p)

theorem zeroEulerProduct_eq_zero {S : Finset PrimeIndex} {p : PrimeIndex} (hp : p ∈ S) :
    zeroEulerProduct S = 0 := by
  unfold zeroEulerProduct
  exact Finset.prod_eq_zero hp rfl

theorem zeroEulerLog_insert (S : Finset PrimeIndex) (p : PrimeIndex) (hp : p ∉ S) :
    zeroEulerLog (insert p S) = primeLog p * zeroEulerProduct S := by
  classical
  unfold zeroEulerLog
  rw [Finset.sum_insert hp]
  have he : (insert p S).erase p = S := Finset.erase_insert hp
  rw [he]
  have hz : (∑ q ∈ S, primeLog q * zeroEulerProduct ((insert p S).erase q)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hpq : p ≠ q := by intro h; subst q; exact hp hq
    rw [zeroEulerProduct_eq_zero (Finset.mem_erase.mpr ⟨hpq, by simp⟩), mul_zero]
  rw [hz, add_zero]

theorem termMoment_center_antidiagonal (L : List PrimeIndex) :
    termMoment (oldformTerms L (1 / 2)) (-(1 / 2)) =
      (primeProduct L : ℂ) ^ (-(1 / 2 : ℂ)) * zeroEulerProduct L.toFinset := by
  rw [termMoment_oldforms]
  simp only [show -(1 / 2 : ℂ) - -(1 / 2 : ℂ) = 0 by ring,
    Complex.cpow_zero, sub_self, zeroEulerProduct]

/-- The actual logarithmic oldform moment at the central antidiagonal. -/
theorem termLogMoment_center_antidiagonal (L : List PrimeIndex) :
    termLogMoment (oldformTerms L (1 / 2)) (-(1 / 2)) =
      (primeProduct L : ℂ) ^ (-(1 / 2 : ℂ)) * zeroEulerLog L.toFinset := by
  classical
  induction L with
  | nil => simp [oldformTerms, termLogMoment, primeProduct, zeroEulerLog]
  | cons p L ih =>
      rw [termLogMoment_oldform_cons, ih, termMoment_center_antidiagonal,
        show primeProduct (p :: L) = p.1 * primeProduct L from rfl,
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow, List.toFinset_cons]
      by_cases h : p ∈ L
      · have hd := (prime_dvd_product_iff p L).mpr h
        rw [if_pos hd, Finset.insert_eq_of_mem (List.mem_toFinset.mpr h),
          zeroEulerProduct_eq_zero (List.mem_toFinset.mpr h)]
        ring
      · have hd : ¬ p.1 ∣ primeProduct L := by simpa only [prime_dvd_product_iff] using h
        rw [if_neg hd, sub_self, zero_mul, zero_add,
          zeroEulerLog_insert L.toFinset p (by simpa using h)]
        ring

/-- Exact finite reflected height-log sum, proved before specializing the
oldform coefficients. The positive heights justify the real logarithms. -/
theorem reflected_log_sum (N : ℕ) (hN : 0 < N) (T : List (ℕ+ × ℂ)) :
    (T.map (fun t => t.2 * (((N : ℝ) / (t.1 : ℝ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      (Real.log ((N : ℝ) / (t.1 : ℝ)) : ℂ))).sum =
      (N : ℂ) ^ (1 / 2 : ℂ) *
        ((Real.log (N : ℝ) : ℂ) * termMoment T (-(1 / 2)) -
          termLogMoment T (-(1 / 2))) := by
  induction T with
  | nil => simp [termMoment, termLogMoment]
  | cons t T ih =>
      have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have htr : (t.1 : ℝ) ≠ 0 := by exact_mod_cast t.1.ne_zero
      simp only [List.map_cons, List.sum_cons, termMoment, termLogMoment] at ih ⊢
      rw [ih, Complex.ofReal_div,
        Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg N)
          (by positivity : (0 : ℝ) ≤ t.1) (1 / 2 : ℂ),
        Real.log_div hNr htr, Complex.ofReal_sub]
      simp only [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
      ring

theorem canonical_support_nonempty (N : ℕ) (hN : 1 < N) :
    (canonicalPrimeList N).toFinset.Nonempty := by
  classical
  have hL : canonicalPrimeList N ≠ [] := by
    intro he
    have hprod := canonicalPrimeList_product (lt_trans Nat.zero_lt_one hN)
    rw [he] at hprod
    simp only [primeProduct, List.map_nil, List.prod_nil] at hprod
    omega
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil hL
  exact ⟨p, List.mem_toFinset.mpr hp⟩

/-- The reflected finite central mean has no height logarithm at N>1.
Its remaining coefficient is the explicit logarithmic local Euler sum. -/
theorem completedReflectedConstant_half_logEuler (N : ℕ) (hN : 1 < N)
    (y : ℝ) (hy : 0 < y) :
    completedReflectedConstant N (1 / 2) y =
      -(y : ℂ) ^ (1 / 2 : ℂ) * zeroEulerLog (canonicalPrimeList N).toFinset /
        oldformNormalization (canonicalPrimeList N) (1 / 2) := by
  have hNpos : 0 < N := lt_trans Nat.zero_lt_one hN
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have hD := oldformNormalization_ne_zero_of_re_pos (canonicalPrimeList N) (1 / 2) (by norm_num)
  obtain ⟨p, hp⟩ := canonical_support_nonempty N hN
  have hP : zeroEulerProduct (canonicalPrimeList N).toFinset = 0 :=
    zeroEulerProduct_eq_zero hp
  have hM : termMoment (oldformTerms (canonicalPrimeList N) (1 / 2)) (-(1 / 2)) = 0 := by
    rw [termMoment_center_antidiagonal, hP, mul_zero]
  have hV : ((oldformTerms (canonicalPrimeList N) (1 / 2)).map
      (fun t => t.2 * (((N : ℝ) / (t.1 : ℝ) : ℝ) : ℂ) ^ (1 / 2 : ℂ))).sum = 0 := by
    have hm := reflectedHeightMoment_eq_finite_sum N (1 / 2 : ℂ) (1 / 2 : ℂ)
    rw [reflected_incoming_moment_zero N hN] at hm
    exact (div_eq_zero_iff.mp hm.symm).resolve_right hD
  unfold completedReflectedConstant
  rw [scaledCentral_list _ (fun n => (N : ℝ) / (n : ℝ))
    (fun n => div_pos (by exact_mod_cast hNpos) (by exact_mod_cast n.pos)) y hy,
    hV, mul_zero, zero_add, reflected_log_sum N hNpos,
    hM, mul_zero, zero_sub, termLogMoment_center_antidiagonal,
    canonicalPrimeList_product hNpos]
  have hpow : (N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ hNC]
    norm_num
  calc
    _ = -(y : ℂ) ^ (1 / 2 : ℂ) *
        ((N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (-(1 / 2 : ℂ))) *
          zeroEulerLog (canonicalPrimeList N).toFinset /
            oldformNormalization (canonicalPrimeList N) (1 / 2) := by ring
    _ = _ := by rw [hpow]; ring

theorem zeroEulerLog_singleton (p : PrimeIndex) : zeroEulerLog {p} = primeLog p := by
  classical
  simp [zeroEulerLog, zeroEulerProduct]

/-- Two distinct prime divisors force every complementary Euler product to
contain a genuine zero. No asymptotic or numerical calculation is used. -/
theorem zeroEulerLog_eq_zero_of_two {S : Finset PrimeIndex}
    (p q : PrimeIndex) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    zeroEulerLog S = 0 := by
  classical
  unfold zeroEulerLog
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hpr : p = r
  · subst r
    rw [zeroEulerProduct_eq_zero (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩), mul_zero]
  · rw [zeroEulerProduct_eq_zero (Finset.mem_erase.mpr ⟨hpr, hp⟩), mul_zero]

theorem ordinary_central_derivative_zeroCusp_mean_logEuler (N : ℕ) (hN : 1 < N)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, deriv (fun s : ℂ =>
      centralOrdinaryLevel N s (frickeSL N (lt_trans Nat.zero_lt_one hN) • horizontalPoint y hy x))
        (1 / 2)) =
      -2 * (y : ℂ) ^ (1 / 2 : ℂ) * zeroEulerLog (canonicalPrimeList N).toFinset /
        oldformNormalization (canonicalPrimeList N) (1 / 2) := by
  rw [ordinary_central_derivative_zeroCusp_mean N (lt_trans Nat.zero_lt_one hN) y hy,
    completedReflectedConstant_half_logEuler N hN y hy]
  ring

/-- Explicit nonzero-prime-support case; the Euler denominator retains all
prime-power multiplicity through N^(1/2). No nonvanishing claim is assumed. -/
theorem completedReflectedConstant_half_singlePrime (N : ℕ) (hN : 1 < N)
    (p : PrimeIndex) (hS : (canonicalPrimeList N).toFinset = {p})
    (y : ℝ) (hy : 0 < y) :
    completedReflectedConstant N (1 / 2) y =
      -(y : ℂ) ^ (1 / 2 : ℂ) * primeLog p /
        ((N : ℂ) ^ (1 / 2 : ℂ) * (1 - (p.1 : ℂ)⁻¹)) := by
  rw [completedReflectedConstant_half_logEuler N hN y hy,
    normalization_eq_product, canonicalPrimeList_product (lt_trans Nat.zero_lt_one hN),
    hS, zeroEulerLog_singleton]
  norm_num [primeEulerFactor]

theorem completedReflectedConstant_half_twoPrimes (N : ℕ) (hN : 1 < N)
    (p q : PrimeIndex) (hp : p ∈ (canonicalPrimeList N).toFinset)
    (hq : q ∈ (canonicalPrimeList N).toFinset) (hpq : p ≠ q)
    (y : ℝ) (hy : 0 < y) : completedReflectedConstant N (1 / 2) y = 0 := by
  rw [completedReflectedConstant_half_logEuler N hN y hy,
    zeroEulerLog_eq_zero_of_two p q hp hq hpq, mul_zero, zero_div]

theorem ordinary_central_derivative_zeroCusp_mean_twoPrimes (N : ℕ) (hN : 1 < N)
    (p q : PrimeIndex) (hp : p ∈ (canonicalPrimeList N).toFinset)
    (hq : q ∈ (canonicalPrimeList N).toFinset) (hpq : p ≠ q)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, deriv (fun s : ℂ =>
      centralOrdinaryLevel N s (frickeSL N (lt_trans Nat.zero_lt_one hN) • horizontalPoint y hy x))
        (1 / 2)) = 0 := by
  rw [ordinary_central_derivative_zeroCusp_mean N (lt_trans Nat.zero_lt_one hN) y hy,
    completedReflectedConstant_half_twoPrimes N hN p q hp hq hpq y hy, mul_zero]

end ImbalancedChen.Part3.CentralReflectedLogEuler20261026b
