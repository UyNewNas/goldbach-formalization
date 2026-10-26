import ImbalancedChen.Part3LevelOldformScatteringMoments
import ImbalancedChen.Part3FrickeNormalizer

/-!
Actual native Fricke transport of the finite completed oldform expression.
The matrix W_N is the literal normalized real determinant-one matrix.
Its action is computed, and integer S-invariance of the genuine completed
level-one family changes n W_N z to (N/n)z. Every index n in the actual
oldform list is proved to divide N, so N/n is a positive integral dilation.
No Fricke action, scalar mixing coefficient, or Fourier identity is assumed.
The identity includes s=1/2 and never divides by the completion factor.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.
-/

noncomputable section
open Complex Matrix
open scoped UpperHalfPlane MatrixGroups ModularGroup
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.LevelOldformFricke20261026a

/-- Divisibility of every actual finite oldform index, including repeated primes. -/
theorem oldformTerms_index_dvd (L : List PrimeIndex) (s : ℂ)
    (t : ℕ+ × ℂ) (ht : t ∈ oldformTerms L s) : (t.1 : ℕ) ∣ primeProduct L := by
  induction L generalizing t with
  | nil =>
      simp only [oldformTerms, List.mem_singleton] at ht
      subst t
      exact one_dvd _
  | cons p L ih =>
      change (t.1 : ℕ) ∣ p.1 * primeProduct L
      unfold oldformTerms at ht
      split_ifs at ht with h
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
        simpa only [primePNat, PNat.coe_mul] using Nat.mul_dvd_mul_left p.1 (ih w hw)
      · rcases List.mem_append.mp ht with ht | ht
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
          simpa only [primePNat, PNat.coe_mul] using Nat.mul_dvd_mul_left p.1 (ih w hw)
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
          exact dvd_mul_of_dvd_right (ih w hw) p.1

theorem canonical_oldform_index_dvd (N : ℕ) (hN : 0 < N) (s : ℂ)
    (t : ℕ+ × ℂ) (ht : t ∈ oldformTerms (canonicalPrimeList N) s) : (t.1 : ℕ) ∣ N := by
  simpa only [canonicalPrimeList_product hN] using
    oldformTerms_index_dvd (canonicalPrimeList N) s t ht

def complementaryIndex (N : ℕ) (hN : 0 < N) (n : ℕ+) (hn : (n : ℕ) ∣ N) : ℕ+ :=
  ⟨N / (n : ℕ), Nat.div_pos (Nat.le_of_dvd hN hn) n.pos⟩

theorem complementaryIndex_real (N : ℕ) (hN : 0 < N) (n : ℕ+) (hn : (n : ℕ) ∣ N) :
    (complementaryIndex N hN n hn : ℝ) = (N : ℝ) / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
  apply (eq_div_iff hnR).mpr
  have hm : (n : ℕ) * (N / (n : ℕ)) = N := Nat.mul_div_cancel' hn
  have hmR : (n : ℝ) * ((N / (n : ℕ) : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hm
  simpa only [complementaryIndex, mul_comm] using hmR

/-- The literal positive real complementary dilation; the preceding
support theorem identifies it with an integer on every actual oldform term. -/
def reflectedDilation (N : ℕ) (hN : 0 < N) (n : ℕ+) (z : UpperHalfPlane) : UpperHalfPlane :=
  dilate ((N : ℝ) / (n : ℝ))
    (div_pos (by exact_mod_cast hN) (by exact_mod_cast n.pos)) z

theorem reflectedDilation_eq_integer (N : ℕ) (hN : 0 < N) (n : ℕ+)
    (hn : (n : ℕ) ∣ N) (z : UpperHalfPlane) :
    reflectedDilation N hN n z = pnatDilate (complementaryIndex N hN n hn) z := by
  apply UpperHalfPlane.ext
  simp only [reflectedDilation, pnatDilate, dilate_coe, complementaryIndex_real]

/-- Direct action of the original normalized Fricke matrix. -/
theorem fricke_action_coe (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    ((frickeSL N hN • z : UpperHalfPlane) : ℂ) = -1 / ((N : ℂ) * (z : ℂ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hr : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hNr).ne'
  have hr2 : (Real.sqrt (N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    exact_mod_cast Real.sq_sqrt hNr.le
  calc
    _ = -1 / ((Real.sqrt (N : ℝ) : ℂ) ^ 2 * (z : ℂ)) := by
      simp [UpperHalfPlane.coe_specialLinearGroup_apply, frickeSL, frickeMatrix]
      <;> field_simp [hr, z.ne_zero]
      <;> ring
    _ = _ := by rw [hr2]

/-- Actual geometric identity n W_N z = S ((N/n)z). It holds for every
positive n; integrality of N/n is supplied separately on the finite support. -/
theorem dilation_fricke_eq_inversion (N : ℕ) (hN : 0 < N) (n : ℕ+)
    (z : UpperHalfPlane) :
    pnatDilate n (frickeSL N hN • z) = ModularGroup.S • reflectedDilation N hN n z := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  change ((n : ℝ) : ℂ) * ((frickeSL N hN • z : UpperHalfPlane) : ℂ) =
    (-((((N : ℝ) / (n : ℝ)) : ℂ) * (z : ℂ)))⁻¹
  rw [fricke_action_coe]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, inv_neg]
  field_simp [hNC, hnC, z.ne_zero]
  <;> ring

/-- Genuine completed level-one identity, including the central parameter. -/
theorem completed_levelOne_fricke_dilation (N : ℕ) (hN : 0 < N) (n : ℕ+)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    completedActualEisenstein s (pnatDilate n (frickeSL N hN • z)) =
      completedActualEisenstein s (reflectedDilation N hN n z) := by
  rw [dilation_fricke_eq_inversion,
    completedActualEisenstein_SL2_invariant s hs0 hs1 ModularGroup.S]

theorem completed_levelOne_fricke_integer (N : ℕ) (hN : 0 < N) (n : ℕ+)
    (hn : (n : ℕ) ∣ N) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    completedActualEisenstein s (pnatDilate n (frickeSL N hN • z)) =
      completedActualEisenstein s (pnatDilate (complementaryIndex N hN n hn) z) := by
  rw [completed_levelOne_fricke_dilation N hN n s hs0 hs1,
    reflectedDilation_eq_integer N hN n hn]

def reflectedCompletedNumerator (N : ℕ) (hN : 0 < N) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  ((oldformTerms (canonicalPrimeList N) s).map
    (fun t => t.2 * completedActualEisenstein s (reflectedDilation N hN t.1 z))).sum

def reflectedCompletedLevel (N : ℕ) (hN : 0 < N) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  reflectedCompletedNumerator N hN s z / oldformNormalization (canonicalPrimeList N) s

theorem completedOldformNumerator_fricke (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    completedOldformNumerator N s (frickeSL N hN • z) = reflectedCompletedNumerator N hN s z := by
  unfold completedOldformNumerator reflectedCompletedNumerator
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [completed_levelOne_fricke_dilation N hN t.1 s hs0 hs1 z]

/-- Full finite reflected oldform identity, with no scalar Fricke-eigenfunction assertion. -/
theorem completedLevelOldform_fricke (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    completedLevelOldform N s (frickeSL N hN • z) = reflectedCompletedLevel N hN s z := by
  unfold completedLevelOldform reflectedCompletedLevel
  rw [completedOldformNumerator_fricke N hN s hs0 hs1 z]

/-- No totalized division by Gamma or zeta is used at s=1/2. -/
theorem completedLevelOldform_fricke_half (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    completedLevelOldform N (1 / 2) (frickeSL N hN • z) =
      reflectedCompletedLevel N hN (1 / 2) z :=
  completedLevelOldform_fricke N hN _ (by norm_num) (by norm_num) z

/-- The reflected finite expression is identified with the ACTUAL initial
primitive level series at the literal Fricke point. -/
theorem reflectedCompletedLevel_eq_initial (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    reflectedCompletedLevel N hN s z =
      completionFactor s * levelPrimitiveComplexEisenstein N s (frickeSL N hN • z) := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  rw [← completedLevelOldform_fricke N hN s hs0 hs1 z,
    completedLevelOldform_eq_initial N hN s hs]

/-- The same identity retains the genuine GammaInfinity\Gamma0 cusp sum. -/
theorem reflectedCompletedLevel_eq_actualParabolic (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    reflectedCompletedLevel N hN s z =
      completionFactor s * actualComplexParabolicEisenstein N s (frickeSL N hN • z) := by
  rw [actualComplexParabolicEisenstein_eq_half_pair_sum N s hs,
    reflectedCompletedLevel_eq_initial N hN s hs]

/-- Exact height of the reflected horizontal full-level term. -/
theorem reflectedDilation_horizontal_im (N : ℕ) (hN : 0 < N) (n : ℕ+)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (reflectedDilation N hN n (horizontalPoint y hy x)).im = (N : ℝ) / (n : ℝ) * y := by
  simp only [reflectedDilation, dilate_im, horizontalPoint]

end ImbalancedChen.Part3.LevelOldformFricke20261026a
