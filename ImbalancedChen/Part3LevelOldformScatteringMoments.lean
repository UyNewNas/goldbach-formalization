import ImbalancedChen.Part3FiniteLevelEisensteinOldforms
import ImbalancedChen.Part3CompletedActualEisensteinIdentity
import ImbalancedChen.Part3LevelEisensteinScatteringFactors

/-!
The shared literal all-level completed oldform expression, identified with
the actual primitive level series on Re(s)>1. Exact finite height moments
are computed from the already constructed oldformTerms, not from assumed
Eisenstein coefficients. The reflected moments give the precise finite
Euler correction for the Fricke-transformed heights N/n.

This file does not identify the Fricke Fourier integral, prove a scalar
functional equation at arbitrary level, or prove scattering-matrix unitarity.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.
-/

noncomputable section
open Complex
open scoped BigOperators UpperHalfPlane
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.LevelEisensteinScatteringFactors20261025a
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a

namespace ImbalancedChen.Part3.LevelOldformScattering20261026a

/-- The actual finite numerator, using the completed full-level Fourier
family at the exact positive integral dilations of the proven oldform formula. -/
def completedOldformNumerator (N : ℕ) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  ((oldformTerms (canonicalPrimeList N) s).map
    (fun t => t.2 * completedActualEisenstein s (pnatDilate t.1 z))).sum

/-- Shared literal definition for subsequent parameter and spatial continuation. -/
def completedLevelOldform (N : ℕ) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  completedOldformNumerator N s z / oldformNormalization (canonicalPrimeList N) s

private theorem completed_list_initial (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs : 1 < s.re) (z : UpperHalfPlane) :
    (T.map (fun t => t.2 * completedActualEisenstein s (pnatDilate t.1 z))).sum =
      completionFactor s * evaluateTerms s z T := by
  induction T with
  | nil => simp [evaluateTerms]
  | cons t T ih =>
      simp only [List.map_cons, List.sum_cons, completedActualEisenstein_eq_initial s hs,
        evaluateTerms, levelPrimitiveComplexEisenstein_one] at ih ⊢
      rw [ih]
      ring

theorem completedOldformNumerator_eq_initial (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    completedOldformNumerator N s z = completionFactor s *
      (oldformNormalization (canonicalPrimeList N) s * levelPrimitiveComplexEisenstein N s z) := by
  rw [completedOldformNumerator, completed_list_initial _ s hs z]
  have h := finite_oldform_undivided (canonicalPrimeList N) s hs z
  rw [canonicalPrimeList_product hN] at h
  exact congrArg (completionFactor s * ·) h.symm

/-- Actual initial identification; no continuation or reconstruction supplier is assumed. -/
theorem completedLevelOldform_eq_initial (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    completedLevelOldform N s z = completionFactor s * levelPrimitiveComplexEisenstein N s z := by
  rw [completedLevelOldform, completedOldformNumerator_eq_initial N hN s hs z]
  have hn := normalization_ne_zero (canonicalPrimeList N) s hs
  field_simp [hn]
  <;> ring

/-- Moment of the literal finite list of dilation indices and coefficients. -/
def termMoment (T : List (ℕ+ × ℂ)) (u : ℂ) : ℂ :=
  (T.map (fun t => t.2 * ((t.1 : ℕ) : ℂ) ^ u)).sum

theorem termMoment_raise (p : PrimeIndex) (T : List (ℕ+ × ℂ)) (u : ℂ) :
    termMoment (T.map (fun t => (primePNat p * t.1, t.2))) u =
      (p.1 : ℂ) ^ u * termMoment T u := by
  induction T with
  | nil => simp [termMoment]
  | cons t T ih =>
      simp only [termMoment, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp only [primePNat, PNat.coe_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      ring

theorem termMoment_scale (a : ℂ) (T : List (ℕ+ × ℂ)) (u : ℂ) :
    termMoment (T.map (fun t => (t.1, a * t.2))) u = a * termMoment T u := by
  induction T with
  | nil => simp [termMoment]
  | cons t T ih =>
      simp only [termMoment, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem termMoment_oldform_cons (p : PrimeIndex) (L : List PrimeIndex) (s u : ℂ) :
    termMoment (oldformTerms (p :: L) s) u =
      (if p.1 ∣ primeProduct L then (p.1 : ℂ) ^ u
       else (p.1 : ℂ) ^ u - (p.1 : ℂ) ^ (-s)) * termMoment (oldformTerms L s) u := by
  unfold oldformTerms
  split_ifs
  · exact termMoment_raise p _ u
  · rw [show termMoment
        ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2)) ++
          (oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) u =
        termMoment ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2))) u +
          termMoment ((oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) u by
        simp only [termMoment, List.map_append, List.sum_append]]
    rw [termMoment_raise, termMoment_scale]
    ring

private theorem cpow_difference_factor (p : PrimeIndex) (s u : ℂ) :
    (p.1 : ℂ) ^ u - (p.1 : ℂ) ^ (-s) =
      (p.1 : ℂ) ^ u * (1 - (p.1 : ℂ) ^ (-s - u)) := by
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  have h : (p.1 : ℂ) ^ u * (p.1 : ℂ) ^ (-s - u) = (p.1 : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [mul_sub, mul_one, h]

/-- Exact finite Euler product for EVERY height exponent, before normalization. -/
theorem termMoment_oldforms (L : List PrimeIndex) (s u : ℂ) :
    termMoment (oldformTerms L s) u = (primeProduct L : ℂ) ^ u *
      ∏ p ∈ L.toFinset, (1 - (p.1 : ℂ) ^ (-s - u)) := by
  classical
  induction L with
  | nil => simp [oldformTerms, termMoment, primeProduct]
  | cons p L ih =>
      have hprod : primeProduct (p :: L) = p.1 * primeProduct L := rfl
      rw [termMoment_oldform_cons, hprod, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
        List.toFinset_cons]
      by_cases h : p ∈ L
      · rw [if_pos ((prime_dvd_product_iff p L).mpr h), ih,
          Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]
        ring
      · have hd : ¬ p.1 ∣ primeProduct L := by simpa only [prime_dvd_product_iff] using h
        rw [if_neg hd, ih, cpow_difference_factor, Finset.prod_insert (by simpa using h)]
        ring

/-- The incoming-height moment is exactly the oldform normalizing factor. -/
theorem termMoment_diagonal (L : List PrimeIndex) (s : ℂ) :
    termMoment (oldformTerms L s) s = oldformNormalization L s := by
  rw [termMoment_oldforms, normalization_eq_product]
  simp only [primeEulerFactor, show -s - s = -2 * s by ring]

/-- Denominator nonvanishing extends from the initial halfplane to Re(s)>0. -/
theorem oldformNormalization_ne_zero_of_re_pos (L : List PrimeIndex)
    (s : ℂ) (hs : 0 < s.re) : oldformNormalization L s ≠ 0 := by
  induction L with
  | nil => simp [oldformNormalization]
  | cons p L ih =>
      have hp0 : (p.1 : ℂ) ^ s ≠ 0 :=
        Complex.cpow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero)
      rw [oldformNormalization]
      split_ifs
      · exact mul_ne_zero hp0 ih
      · rw [prime_difference_factor]
        exact mul_ne_zero (mul_ne_zero hp0
          (localScatteringFactor_denominator_ne_zero p.2 hs)) ih

theorem oldformNormalization_critical_ne_zero (N : ℕ) (t : ℝ) :
    oldformNormalization (canonicalPrimeList N) (criticalParameter t) ≠ 0 :=
  oldformNormalization_ne_zero_of_re_pos _ _ (by rw [criticalParameter_re]; norm_num)

def normalizedHeightMoment (N : ℕ) (s u : ℂ) : ℂ :=
  termMoment (oldformTerms (canonicalPrimeList N) s) u /
    oldformNormalization (canonicalPrimeList N) s

/-- Exact normalized height moment of the ACTUAL oldform list. The formula
is an algebraic identity; regular continuation requires the stated nonzero
denominator theorem above, rather than interpreting totalized pole values. -/
theorem normalizedHeightMoment_eq_product (N : ℕ) (hN : 0 < N) (s u : ℂ) :
    normalizedHeightMoment N s u = (N : ℂ) ^ (u - s) *
      ∏ p ∈ (canonicalPrimeList N).toFinset,
        ((1 - (p.1 : ℂ) ^ (-s - u)) / (1 - (p.1 : ℂ) ^ (-2 * s))) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [normalizedHeightMoment, termMoment_oldforms, normalization_eq_product,
    canonicalPrimeList_product hN, Complex.cpow_sub _ _ hN0, Finset.prod_div_distrib]
  simp only [primeEulerFactor, div_eq_mul_inv, mul_inv_rev]
  ring

theorem normalizedHeightMoment_diagonal (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    normalizedHeightMoment N s s = 1 := by
  rw [normalizedHeightMoment, termMoment_diagonal,
    div_self (oldformNormalization_ne_zero_of_re_pos _ _ hs)]

theorem infinity_outgoing_moment (N : ℕ) (hN : 0 < N) (s : ℂ) :
    normalizedHeightMoment N s (1 - s) = (N : ℂ) ^ (1 - 2 * s) *
      ∏ p ∈ (canonicalPrimeList N).toFinset,
        ((1 - (p.1 : ℂ) ^ (-1 : ℂ)) / (1 - (p.1 : ℂ) ^ (-2 * s))) := by
  rw [normalizedHeightMoment_eq_product N hN]
  simp only [show (1 - s) - s = 1 - 2 * s by ring,
    show -s - (1 - s) = (-1 : ℂ) by ring]

/-- Reflected height moment: the literal Fricke height replacement n ↦ N/n. -/
def reflectedHeightMoment (N : ℕ) (s u : ℂ) : ℂ :=
  (N : ℂ) ^ u * normalizedHeightMoment N s (-u)

theorem reflectedHeightMoment_eq_product (N : ℕ) (hN : 0 < N) (s u : ℂ) :
    reflectedHeightMoment N s u = (N : ℂ) ^ (-s) *
      ∏ p ∈ (canonicalPrimeList N).toFinset,
        ((1 - (p.1 : ℂ) ^ (u - s)) / (1 - (p.1 : ℂ) ^ (-2 * s))) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [reflectedHeightMoment, normalizedHeightMoment_eq_product N hN]
  rw [← mul_assoc, ← Complex.cpow_add _ _ hN0]
  simp only [show u + (-u - s) = -s by ring,
    show -s - -u = u - s by ring]

/-- Exact finite off-diagonal Euler correction, with no scattering
coefficient or functional equation supplied as a hypothesis. -/
theorem reflected_outgoing_moment (N : ℕ) (hN : 0 < N) (s : ℂ) :
    reflectedHeightMoment N s (1 - s) = (N : ℂ) ^ (-s) *
      ∏ p ∈ (canonicalPrimeList N).toFinset,
        ((1 - (p.1 : ℂ) ^ (1 - 2 * s)) / (1 - (p.1 : ℂ) ^ (-2 * s))) := by
  rw [reflectedHeightMoment_eq_product N hN]
  simp only [show (1 - s) - s = 1 - 2 * s by ring]

private theorem reflected_term_sum (N : ℕ) (T : List (ℕ+ × ℂ)) (u : ℂ) :
    (T.map (fun t => t.2 * (((N : ℝ) / (t.1 : ℝ) : ℝ) : ℂ) ^ u)).sum =
      (N : ℂ) ^ u * termMoment T (-u) := by
  induction T with
  | nil => simp [termMoment]
  | cons t T ih =>
      have hn : 0 ≤ (t.1 : ℝ) := by positivity
      simp only [List.map_cons, List.sum_cons, termMoment] at ih ⊢
      rw [ih, Complex.ofReal_div,
        Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg N) hn]
      simp only [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
      ring

/-- Literal N/n-height interpretation of the reflected moment. -/
theorem reflectedHeightMoment_eq_finite_sum (N : ℕ) (s u : ℂ) :
    reflectedHeightMoment N s u =
      ((oldformTerms (canonicalPrimeList N) s).map
        (fun t => t.2 * (((N : ℝ) / (t.1 : ℝ) : ℝ) : ℂ) ^ u)).sum /
          oldformNormalization (canonicalPrimeList N) s := by
  rw [reflected_term_sum]
  unfold reflectedHeightMoment normalizedHeightMoment
  ring

/-- The incoming Fricke height piece vanishes at every nontrivial level. -/
theorem reflected_incoming_moment_zero (N : ℕ) (hN : 1 < N) (s : ℂ) :
    reflectedHeightMoment N s s = 0 := by
  classical
  have hpos : 0 < N := lt_trans Nat.zero_lt_one hN
  have hne : canonicalPrimeList N ≠ [] := by
    intro he
    have hprod := canonicalPrimeList_product hpos
    rw [he] at hprod
    simp only [primeProduct, List.map_nil, List.prod_nil] at hprod
    omega
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil hne
  rw [reflectedHeightMoment_eq_product N hpos]
  have hz : (∏ q ∈ (canonicalPrimeList N).toFinset,
      ((1 - (q.1 : ℂ) ^ (s - s)) / (1 - (q.1 : ℂ) ^ (-2 * s)))) = 0 := by
    apply Finset.prod_eq_zero (List.mem_toFinset.mpr hp)
    simp
  rw [hz, mul_zero]

private theorem scaled_constant_sum (T : List (ℕ+ × ℂ)) (height : ℕ+ → ℝ)
    (hh : ∀ n, 0 ≤ height n) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : s ≠ 1 / 2) :
    (T.map (fun t => t.2 * completedConstant (height t.1 * y) s)).sum =
      completedRiemannZeta (2 * s) * (y : ℂ) ^ s *
        (T.map (fun t => t.2 * (height t.1 : ℂ) ^ s)).sum +
      completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) *
        (T.map (fun t => t.2 * (height t.1 : ℂ) ^ (1 - s))).sum := by
  induction T with
  | nil => simp
  | cons t T ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, completedConstant_eq_raw _ s hs, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hh t.1) hy.le s,
        Complex.mul_cpow_ofReal_nonneg (hh t.1) hy.le (1 - s)]
      ring

/-- The completed constant PIECES of the literal finite oldform expansion.
Identification with an integrated continued zero mode is a separate theorem. -/
def completedInfinityConstant (N : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  ((oldformTerms (canonicalPrimeList N) s).map
    (fun t => t.2 * completedConstant ((t.1 : ℝ) * y) s)).sum /
      oldformNormalization (canonicalPrimeList N) s

def completedReflectedConstant (N : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  ((oldformTerms (canonicalPrimeList N) s).map
    (fun t => t.2 * completedConstant (((N : ℝ) / (t.1 : ℝ)) * y) s)).sum /
      oldformNormalization (canonicalPrimeList N) s

/-- Exact completed infinity constant expression on the right halfplane,
with the central removable value kept out of the raw two-Lambda formula. -/
theorem completedInfinityConstant_eq (N : ℕ) (s : ℂ) (hs : 0 < s.re)
    (hhalf : s ≠ 1 / 2) (y : ℝ) (hy : 0 < y) :
    completedInfinityConstant N s y = completedRiemannZeta (2 * s) * (y : ℂ) ^ s +
      completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) *
        normalizedHeightMoment N s (1 - s) := by
  have hn := oldformNormalization_ne_zero_of_re_pos (canonicalPrimeList N) s hs
  unfold completedInfinityConstant
  rw [scaled_constant_sum _ (fun n => (n : ℝ)) (fun n => by positivity) y hy s hhalf]
  simp only [Complex.ofReal_natCast]
  change (_ * termMoment (oldformTerms (canonicalPrimeList N) s) s +
    _ * termMoment (oldformTerms (canonicalPrimeList N) s) (1 - s)) /
      oldformNormalization (canonicalPrimeList N) s = _
  rw [termMoment_diagonal]
  unfold normalizedHeightMoment
  field_simp [hn]
  <;> ring

theorem completedReflectedConstant_eq_moments (N : ℕ) (s : ℂ)
    (hhalf : s ≠ 1 / 2) (y : ℝ) (hy : 0 < y) :
    completedReflectedConstant N s y =
      completedRiemannZeta (2 * s) * (y : ℂ) ^ s * reflectedHeightMoment N s s +
      completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) *
        reflectedHeightMoment N s (1 - s) := by
  unfold completedReflectedConstant
  rw [scaled_constant_sum _ (fun n => (N : ℝ) / (n : ℝ))
    (fun n => div_nonneg (Nat.cast_nonneg N) (by positivity)) y hy s hhalf]
  rw [reflected_term_sum, reflected_term_sum]
  unfold reflectedHeightMoment normalizedHeightMoment
  simp only [div_eq_mul_inv]
  ring

/-- The exact Fricke-height outgoing constant, obtained from actual
finite oldform coefficients. This is not a full scattering-matrix theorem. -/
theorem completedReflectedConstant_eq_euler (N : ℕ) (hN : 1 < N)
    (s : ℂ) (hhalf : s ≠ 1 / 2) (y : ℝ) (hy : 0 < y) :
    completedReflectedConstant N s y =
      completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) *
        ((N : ℂ) ^ (-s) * ∏ p ∈ (canonicalPrimeList N).toFinset,
          ((1 - (p.1 : ℂ) ^ (1 - 2 * s)) / (1 - (p.1 : ℂ) ^ (-2 * s)))) := by
  rw [completedReflectedConstant_eq_moments N s hhalf y hy,
    reflected_incoming_moment_zero N hN s, mul_zero, zero_add,
    reflected_outgoing_moment N (lt_trans Nat.zero_lt_one hN) s]

end ImbalancedChen.Part3.LevelOldformScattering20261026a
