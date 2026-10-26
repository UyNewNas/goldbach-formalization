import ImbalancedChen.Part3OrdinaryCentralFourierMeans
import ImbalancedChen.Part3CompletedEisensteinCentralHeight

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual central dslope constant is propagated through the finite oldform
list. Its logarithmic moment is computed, including repeated prime powers.
At infinity the exact correction is log N + sum_{p|N} log p/(p-1).
The physical ordinary central derivative mean is consequently an explicit
height logarithm with this finite Euler correction. No central coefficient
or logarithmic moment identity is assumed.
-/

noncomputable section
open Set Complex
open scoped BigOperators UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinCentralHeight
open ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
open ImbalancedChen.Part3.OrdinaryCentralFourierMeans20261026b
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.CentralHeightLogEuler20261026b

def primeLog (p : PrimeIndex) : ℂ := (Real.log (p.1 : ℝ) : ℂ)

def termLogMoment (T : List (ℕ+ × ℂ)) (u : ℂ) : ℂ :=
  (T.map (fun t => t.2 * ((t.1 : ℕ) : ℂ) ^ u * (Real.log (t.1 : ℝ) : ℂ))).sum

theorem termLogMoment_raise (p : PrimeIndex) (T : List (ℕ+ × ℂ)) (u : ℂ) :
    termLogMoment (T.map (fun t => (primePNat p * t.1, t.2))) u =
      (p.1 : ℂ) ^ u * (primeLog p * termMoment T u + termLogMoment T u) := by
  induction T with
  | nil => simp [termLogMoment, termMoment]
  | cons t T ih =>
      have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
      have ht : (t.1 : ℝ) ≠ 0 := by exact_mod_cast t.1.ne_zero
      simp only [termLogMoment, termMoment, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp only [primePNat, PNat.coe_mul, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, Real.log_mul hp ht, Complex.ofReal_add, primeLog]
      ring

theorem termLogMoment_scale (a : ℂ) (T : List (ℕ+ × ℂ)) (u : ℂ) :
    termLogMoment (T.map (fun t => (t.1, a * t.2))) u = a * termLogMoment T u := by
  induction T with
  | nil => simp [termLogMoment]
  | cons t T ih =>
      simp only [termLogMoment, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem termLogMoment_oldform_cons (p : PrimeIndex) (L : List PrimeIndex) (s u : ℂ) :
    termLogMoment (oldformTerms (p :: L) s) u =
      (if p.1 ∣ primeProduct L then (p.1 : ℂ) ^ u
       else (p.1 : ℂ) ^ u - (p.1 : ℂ) ^ (-s)) * termLogMoment (oldformTerms L s) u +
        primeLog p * (p.1 : ℂ) ^ u * termMoment (oldformTerms L s) u := by
  unfold oldformTerms
  split_ifs
  · rw [termLogMoment_raise]
    ring
  · rw [show termLogMoment
        ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2)) ++
          (oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) u =
        termLogMoment ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2))) u +
          termLogMoment ((oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) u by
        simp only [termLogMoment, List.map_append, List.sum_append]]
    rw [termLogMoment_raise, termLogMoment_scale]
    ring

/-- Multiplicity is retained by the first sum; the second uses distinct primes. -/
def centralEulerCorrection (L : List PrimeIndex) : ℂ :=
  (L.map primeLog).sum + ∑ p ∈ L.toFinset, primeLog p / ((p.1 : ℂ) - 1)

theorem centralEulerCorrection_cons (p : PrimeIndex) (L : List PrimeIndex) :
    centralEulerCorrection (p :: L) =
      (if p ∈ L then primeLog p else primeLog p + primeLog p / ((p.1 : ℂ) - 1)) +
        centralEulerCorrection L := by
  classical
  unfold centralEulerCorrection
  simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
  by_cases h : p ∈ L
  · rw [if_pos h, Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]
    ring
  · rw [if_neg h, Finset.sum_insert (by simpa using h)]
    ring

private theorem central_local_log_identity (p : PrimeIndex) :
    ((p.1 : ℂ) ^ (1 / 2 : ℂ) - (p.1 : ℂ) ^ (-(1 / 2 : ℂ))) *
      (primeLog p + primeLog p / ((p.1 : ℂ) - 1)) =
        primeLog p * (p.1 : ℂ) ^ (1 / 2 : ℂ) := by
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  have hp1 : (p.1 : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast p.2.ne_one)
  have he : (p.1 : ℂ) ^ (1 / 2 : ℂ) - (p.1 : ℂ) ^ (-(1 / 2 : ℂ)) =
      (p.1 : ℂ) ^ (1 / 2 : ℂ) * (1 - (p.1 : ℂ)⁻¹) := by
    convert prime_difference_factor p (1 / 2 : ℂ) using 1 <;> norm_num [primeEulerFactor]
  rw [he]
  field_simp [hp0, hp1]
  <;> ring

/-- Exact logarithmic moment of the literal finite oldform coefficients. -/
theorem termLogMoment_center_diagonal (L : List PrimeIndex) :
    termLogMoment (oldformTerms L (1 / 2)) (1 / 2) =
      oldformNormalization L (1 / 2) * centralEulerCorrection L := by
  classical
  induction L with
  | nil => simp [oldformTerms, termLogMoment, oldformNormalization, centralEulerCorrection]
  | cons p L ih =>
      rw [termLogMoment_oldform_cons, ih, termMoment_diagonal, centralEulerCorrection_cons]
      by_cases h : p ∈ L
      · have hd := (prime_dvd_product_iff p L).mpr h
        simp only [oldformNormalization, if_pos hd, if_pos h]
        ring
      · have hd : ¬ p.1 ∣ primeProduct L := by simpa only [prime_dvd_product_iff] using h
        simp only [oldformNormalization, if_neg hd, if_neg h]
        have he := central_local_log_identity p
        linear_combination -oldformNormalization L (1 / 2) * he

private theorem primeProduct_pos (L : List PrimeIndex) : 0 < primeProduct L := by
  induction L with
  | nil => simp [primeProduct]
  | cons p L ih => exact Nat.mul_pos p.2.pos ih

theorem primeLog_sum (L : List PrimeIndex) :
    (L.map primeLog).sum = (Real.log (primeProduct L : ℝ) : ℂ) := by
  induction L with
  | nil => simp [primeProduct]
  | cons p L ih =>
      have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
      have hL : (primeProduct L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (primeProduct_pos L).ne'
      rw [show primeProduct (p :: L) = p.1 * primeProduct L from rfl,
        Nat.cast_mul, Real.log_mul hp hL]
      simp only [List.map_cons, List.sum_cons, ih, primeLog, Complex.ofReal_add]

theorem canonical_centralEulerCorrection (N : ℕ) (hN : 0 < N) :
    centralEulerCorrection (canonicalPrimeList N) = (Real.log (N : ℝ) : ℂ) +
      ∑ p ∈ (canonicalPrimeList N).toFinset, primeLog p / ((p.1 : ℂ) - 1) := by
  rw [centralEulerCorrection, primeLog_sum, canonicalPrimeList_product hN]

/-- True central height-log term at every positive dilation. -/
theorem completedConstant_scaled_half (a : ℝ) (ha : 0 < a) (y : ℝ) (hy : 0 < y) :
    completedConstant (a * y) (1 / 2 : ℂ) =
      (y : ℂ) ^ (1 / 2 : ℂ) * (a : ℂ) ^ (1 / 2 : ℂ) *
        (centralScalar + (Real.log y : ℂ) + (Real.log a : ℂ)) := by
  rw [completedConstant_half (a * y) (mul_pos ha hy)]
  unfold centralHeight
  rw [← complex_half_power_eq_root0 (a * y) (mul_pos ha hy), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le hy.le (1 / 2 : ℂ),
    Real.log_mul ha.ne' hy.ne', Complex.ofReal_add]
  ring

theorem scaledCentral_list (T : List (ℕ+ × ℂ)) (height : ℕ+ → ℝ)
    (hh : ∀ n, 0 < height n) (y : ℝ) (hy : 0 < y) :
    (T.map (fun t => t.2 * completedConstant (height t.1 * y) (1 / 2 : ℂ))).sum =
      (y : ℂ) ^ (1 / 2 : ℂ) *
        ((centralScalar + (Real.log y : ℂ)) *
          (T.map (fun t => t.2 * (height t.1 : ℂ) ^ (1 / 2 : ℂ))).sum +
          (T.map (fun t => t.2 * (height t.1 : ℂ) ^ (1 / 2 : ℂ) *
            (Real.log (height t.1) : ℂ))).sum) := by
  induction T with
  | nil => simp
  | cons t T ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [completedConstant_scaled_half _ (hh t.1) y hy, ih]
      ring

/-- Closed central constant with explicit finite logarithmic Euler correction. -/
theorem completedInfinityConstant_half_log (N : ℕ) (y : ℝ) (hy : 0 < y) :
    completedInfinityConstant N (1 / 2) y =
      (y : ℂ) ^ (1 / 2 : ℂ) *
        (centralScalar + (Real.log y : ℂ) + centralEulerCorrection (canonicalPrimeList N)) := by
  have hD := oldformNormalization_ne_zero_of_re_pos (canonicalPrimeList N) (1 / 2) (by norm_num)
  unfold completedInfinityConstant
  rw [scaledCentral_list _ (fun n => (n : ℝ)) (fun n => by exact_mod_cast n.pos) y hy]
  simp only [Complex.ofReal_natCast]
  change (y : ℂ) ^ (1 / 2 : ℂ) *
    ((centralScalar + (Real.log y : ℂ)) * termMoment (oldformTerms _ _) (1 / 2) +
      termLogMoment (oldformTerms _ _) (1 / 2)) / _ = _
  rw [termMoment_diagonal, termLogMoment_center_diagonal]
  field_simp [hD]
  <;> ring

/-- Physical Fourier mean of the actual ordinary derivative, with full
height logarithm and the exact finite prime-divisor correction. -/
theorem ordinary_central_derivative_infinity_mean_log (N : ℕ) (hN : 0 < N)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      deriv (fun s : ℂ => centralOrdinaryLevel N s (horizontalPoint y hy x)) (1 / 2)) =
      2 * (y : ℂ) ^ (1 / 2 : ℂ) *
        (centralScalar + (Real.log y : ℂ) + (Real.log (N : ℝ) : ℂ) +
          ∑ p ∈ (canonicalPrimeList N).toFinset, primeLog p / ((p.1 : ℂ) - 1)) := by
  rw [ordinary_central_derivative_infinity_mean N y hy, completedInfinityConstant_half_log N y hy,
    canonical_centralEulerCorrection N hN]
  ring

end ImbalancedChen.Part3.CentralHeightLogEuler20261026b
