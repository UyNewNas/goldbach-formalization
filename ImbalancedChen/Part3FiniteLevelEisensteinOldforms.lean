import ImbalancedChen.Part3PrimeLevelEisensteinDegeneracy
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.PNat.Basic

/-!
Finite oldforms for every positive level. This is the equivalent undivided
prime-factor-list formula: the RHS is an explicitly constructed FINITE list
of scalar multiples of E_1 at positive integral dilations. No E_M for M>1
occurs in that list. Each new prime creates the two terms of (T_p-p^(-s));
a repeated prime creates only T_p. The normalization is proved to be
N^s times the product of (1-p^(-2s)) over the distinct prime factors.
All factors are genuinely nonzero on Re(s)>1, so division is justified.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open Complex
open scoped BigOperators UpperHalfPlane
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a

namespace ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a

abbrev PrimeIndex := {p : ℕ // p.Prime}

def primePNat (p : PrimeIndex) : ℕ+ := ⟨p.1, p.2.pos⟩
def primeProduct (L : List PrimeIndex) : ℕ := (L.map Subtype.val).prod

def pnatDilate (n : ℕ+) (z : UpperHalfPlane) : UpperHalfPlane :=
  dilate (n : ℝ) (by exact_mod_cast n.pos) z

theorem pnatDilate_one (z : UpperHalfPlane) : pnatDilate 1 z = z := by
  ext <;> simp [pnatDilate, dilate]

theorem pnatDilate_mul (m n : ℕ+) (z : UpperHalfPlane) :
    pnatDilate (m * n) z = pnatDilate n (pnatDilate m z) := by
  ext <;> simp [pnatDilate, dilate] <;> push_cast <;> ring

theorem pnatDilate_prime (p : PrimeIndex) (z : UpperHalfPlane) :
    pnatDilate (primePNat p) z = dilate p.1 (prime_real_pos p.2) z := rfl

/-- A finite list of dilation indices and explicit scalar coefficients. -/
def oldformTerms : List PrimeIndex → ℂ → List (ℕ+ × ℂ)
  | [], _ => [(1, 1)]
  | p :: L, s =>
      let T := oldformTerms L s
      let raised := T.map (fun t => (primePNat p * t.1, t.2))
      if p.1 ∣ primeProduct L then raised
      else raised ++ T.map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))

def evaluateTerms (s : ℂ) (z : UpperHalfPlane) (T : List (ℕ+ × ℂ)) : ℂ :=
  (T.map (fun t => t.2 * levelPrimitiveComplexEisenstein 1 s (pnatDilate t.1 z))).sum

def oldformNumerator (L : List PrimeIndex) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  evaluateTerms s z (oldformTerms L s)

def oldformNormalization : List PrimeIndex → ℂ → ℂ
  | [], _ => 1
  | p :: L, s =>
      (if p.1 ∣ primeProduct L then (p.1 : ℂ) ^ s
       else (p.1 : ℂ) ^ s - (p.1 : ℂ) ^ (-s)) * oldformNormalization L s

theorem evaluateTerms_raise (p : PrimeIndex) (T : List (ℕ+ × ℂ))
    (s : ℂ) (z : UpperHalfPlane) :
    evaluateTerms s z (T.map (fun t => (primePNat p * t.1, t.2))) =
      evaluateTerms s (pnatDilate (primePNat p) z) T := by
  induction T with
  | nil => simp [evaluateTerms]
  | cons t T ih => simpa only [evaluateTerms, List.map_cons, List.sum_cons,
      pnatDilate_mul] using congrArg (fun w => t.2 *
        levelPrimitiveComplexEisenstein 1 s (pnatDilate t.1 (pnatDilate (primePNat p) z)) + w) ih

theorem evaluateTerms_scale (a : ℂ) (T : List (ℕ+ × ℂ)) (s : ℂ) (z : UpperHalfPlane) :
    evaluateTerms s z (T.map (fun t => (t.1, a * t.2))) = a * evaluateTerms s z T := by
  induction T with
  | nil => simp [evaluateTerms]
  | cons t T ih => simp only [evaluateTerms, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; ring

theorem numerator_nil (s : ℂ) (z : UpperHalfPlane) :
    oldformNumerator [] s z = levelPrimitiveComplexEisenstein 1 s z := by
  simp [oldformNumerator, oldformTerms, evaluateTerms, pnatDilate_one]

theorem numerator_cons (p : PrimeIndex) (L : List PrimeIndex) (s : ℂ) (z : UpperHalfPlane) :
    oldformNumerator (p :: L) s z =
      if p.1 ∣ primeProduct L then oldformNumerator L s (pnatDilate (primePNat p) z)
      else oldformNumerator L s (pnatDilate (primePNat p) z) -
        (p.1 : ℂ) ^ (-s) * oldformNumerator L s z := by
  classical
  unfold oldformNumerator oldformTerms
  split_ifs with h
  · exact evaluateTerms_raise p _ s z
  · rw [show evaluateTerms s z
        ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2)) ++
          (oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) =
          evaluateTerms s z ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2))) +
          evaluateTerms s z ((oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) by
        simp only [evaluateTerms, List.map_append, List.sum_append]]
    rw [evaluateTerms_raise, evaluateTerms_scale]
    ring

/-- The finite RHS contains only genuine E_1 terms; the induction uses
the two proved actual prime-level recurrences at each step. -/
theorem finite_oldform_undivided (L : List PrimeIndex) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) :
    oldformNormalization L s * levelPrimitiveComplexEisenstein (primeProduct L) s z =
      oldformNumerator L s z := by
  induction L generalizing z with
  | nil => simp [oldformNormalization, primeProduct, numerator_nil]
  | cons p L ih =>
      have hprod : primeProduct (p :: L) = p.1 * primeProduct L := rfl
      rw [hprod, oldformNormalization, numerator_cons]
      split_ifs with h
      · rw [← ih, pnatDilate_prime,
          prime_degeneracy_of_dvd p.2 (primeProduct L) h z s hs]
        ring
      · rw [← ih, ← ih, pnatDilate_prime,
          prime_degeneracy_of_not_dvd p.2 (primeProduct L) h z s hs]
        ring

theorem prime_dvd_product_iff (p : PrimeIndex) (L : List PrimeIndex) :
    p.1 ∣ primeProduct L ↔ p ∈ L := by
  induction L with
  | nil => simp [primeProduct, p.2.not_dvd_one]
  | cons q L ih =>
      have hpq : p.1 ∣ q.1 ↔ p = q := by
        rw [Nat.dvd_prime q.2, or_iff_right p.2.ne_one]
        exact Subtype.ext_iff.symm
      change p.1 ∣ q.1 * primeProduct L ↔ p ∈ q :: L
      rw [p.2.dvd_mul, hpq, ih, List.mem_cons]

def primeEulerFactor (p : PrimeIndex) (s : ℂ) : ℂ := 1 - (p.1 : ℂ) ^ (-2 * s)

theorem prime_difference_factor (p : PrimeIndex) (s : ℂ) :
    (p.1 : ℂ) ^ s - (p.1 : ℂ) ^ (-s) = (p.1 : ℂ) ^ s * primeEulerFactor p s := by
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  have hpow : (p.1 : ℂ) ^ s * (p.1 : ℂ) ^ (-2 * s) = (p.1 : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  unfold primeEulerFactor
  rw [mul_sub, mul_one, hpow]

/-- The exact normalizing product, with each distinct prime counted once. -/
theorem normalization_eq_product (L : List PrimeIndex) (s : ℂ) :
    oldformNormalization L s = (primeProduct L : ℂ) ^ s *
      ∏ p ∈ L.toFinset, primeEulerFactor p s := by
  classical
  induction L with
  | nil => simp [oldformNormalization, primeProduct]
  | cons p L ih =>
      have hprod : primeProduct (p :: L) = p.1 * primeProduct L := rfl
      rw [oldformNormalization, hprod, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
        List.toFinset_cons]
      by_cases h : p ∈ L
      · have hd := (prime_dvd_product_iff p L).mpr h
        rw [if_pos hd, ih, Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]
        ring
      · have hd : ¬ p.1 ∣ primeProduct L := by simpa only [prime_dvd_product_iff] using h
        rw [if_neg hd, ih, prime_difference_factor,
          Finset.prod_insert (by simpa using h)]
        ring

theorem primeEulerFactor_ne_zero (p : PrimeIndex) (s : ℂ) (hs : 1 < s.re) :
    primeEulerFactor p s ≠ 0 := by
  have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hn : ‖(p.1 : ℂ) ^ (-2 * s)‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hpR)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hpR
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofNat_re, Complex.ofNat_im,
      neg_zero, zero_mul, sub_zero]
    linarith
  intro h
  have heq : (p.1 : ℂ) ^ (-2 * s) = 1 := (sub_eq_zero.mp h).symm
  rw [heq, norm_one] at hn
  exact lt_irrefl _ hn

theorem normalization_ne_zero (L : List PrimeIndex) (s : ℂ) (hs : 1 < s.re) :
    oldformNormalization L s ≠ 0 := by
  induction L with
  | nil => simp [oldformNormalization]
  | cons p L ih =>
      have hp0 : (p.1 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero)
      rw [oldformNormalization]
      split_ifs
      · exact mul_ne_zero hp0 ih
      · rw [prime_difference_factor]
        exact mul_ne_zero (mul_ne_zero hp0 (primeEulerFactor_ne_zero p s hs)) ih

/-- Canonical finite prime list; repetitions encode prime powers exactly. -/
def canonicalPrimeList (N : ℕ) : List PrimeIndex :=
  N.primeFactorsList.attach.map (fun p => ⟨p.1, Nat.prime_of_mem_primeFactorsList p.2⟩)

theorem canonicalPrimeList_product {N : ℕ} (hN : 0 < N) :
    primeProduct (canonicalPrimeList N) = N := by
  simpa [primeProduct, canonicalPrimeList, List.map_map, Function.comp_def] using
    (Nat.prod_primeFactorsList hN.ne')

theorem canonicalPrimeList_mem {N : ℕ} (hN : 0 < N) (p : PrimeIndex) :
    p ∈ canonicalPrimeList N ↔ p.1 ∣ N := by
  calc
    _ ↔ p.1 ∣ primeProduct (canonicalPrimeList N) :=
      (prime_dvd_product_iff p (canonicalPrimeList N)).symm
    _ ↔ p.1 ∣ N := by rw [canonicalPrimeList_product hN]

/-- Every positive actual level, in an explicit finite undivided oldform formula. -/
theorem actual_level_finite_oldforms_undivided (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    ((N : ℂ) ^ s * ∏ p ∈ (canonicalPrimeList N).toFinset, primeEulerFactor p s) *
      levelPrimitiveComplexEisenstein N s z =
      evaluateTerms s z (oldformTerms (canonicalPrimeList N) s) := by
  have h := finite_oldform_undivided (canonicalPrimeList N) s hs z
  simpa only [normalization_eq_product, canonicalPrimeList_product hN, oldformNumerator] using h

/-- Division is a conclusion of genuine nonvanishing, never a premise. -/
theorem actual_level_finite_oldforms (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    levelPrimitiveComplexEisenstein N s z =
      evaluateTerms s z (oldformTerms (canonicalPrimeList N) s) /
        ((N : ℂ) ^ s * ∏ p ∈ (canonicalPrimeList N).toFinset, primeEulerFactor p s) := by
  have hn := normalization_ne_zero (canonicalPrimeList N) s hs
  rw [normalization_eq_product, canonicalPrimeList_product hN] at hn
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using actual_level_finite_oldforms_undivided N hN s hs z

end ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
