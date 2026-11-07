import ImbalancedChen.Part3InfinityZeroArithmetic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual infinity-to-zero generalized finite sum is reduced to the
literal physical Kloosterman definition by the proved finite permutation
u -> N*u. The exact formula is S_d(-n*inverseResidue(d,N), -m).
Both signs and argument order are explicit. Noncoprime denominators give
an empty actual determinant gate. The proof includes d=1 and N=1 and does
not assume an inversion permutation or desired sum identity.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.InfinityZeroPhysicalKloosterman20261025a

open scoped BigOperators
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

/-- The actual finite generalized zero-cusp sum becomes the literal
physical Kloosterman sum under the genuine denominator coprimality.
The change of residue is proved bijective from the actual unit N. -/
theorem zeroGeneralized_eq_physical (N d : ℕ) [NeZero d]
    (hNd : N.Coprime d) (m n : ℤ) :
    zeroGeneralizedKloosterman N d m n =
      kloosterman d (-n * inverseResidue d (N : ℤ)) (-m) := by
  have hN : IsUnit (N : ZMod d) := (ZMod.isUnit_iff_coprime N d).mpr hNd
  have hbij : Function.Bijective (fun u : ZMod d => (N : ZMod d) * u) :=
    (IsUnit.isUnit_iff_mulLeft_bijective (a := (N : ZMod d))).mp hN
  have hinv : (inverseResidue d (N : ℤ) : ZMod d) = (N : ZMod d)⁻¹ := by
    simp only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [zeroGeneralizedKloosterman, Physical.kloosterman_eq_zmod]
  apply Fintype.sum_bijective (fun u : ZMod d => (N : ZMod d) * u) hbij
  intro u
  by_cases hu : IsUnit ((N : ZMod d) * u)
  · simp only [if_pos hu]
    congr 1
    simp only [Int.cast_mul, Int.cast_neg, hinv]
    have hcancel : (N : ZMod d)⁻¹ * ((N : ZMod d) * u) = u := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit (N : ZMod d) hN, one_mul]
    linear_combination (n : ZMod d) * hcancel
  · simp only [if_neg hu]

/-- An inadmissible denominator has no actual zero-cusp determinant gate. -/
theorem zeroGeneralized_eq_zero_of_not_coprime (N d : ℕ) [NeZero d]
    (hNd : ¬ N.Coprime d) (m n : ℤ) :
    zeroGeneralizedKloosterman N d m n = 0 := by
  unfold zeroGeneralizedKloosterman
  apply Finset.sum_eq_zero
  intro u hu
  apply if_neg
  intro hunit
  exact hNd ((ZMod.isUnit_iff_coprime N d).mp (isUnit_of_mul_isUnit_left hunit))

/-- Complete arithmetic formula, retaining the exact actual denominator
gate rather than silently replacing a forbidden denominator by a physical sum. -/
theorem zeroGeneralized_eq_physical_or_zero (N d : ℕ) [NeZero d] (m n : ℤ) :
    zeroGeneralizedKloosterman N d m n =
      if N.Coprime d then kloosterman d (-n * inverseResidue d (N : ℤ)) (-m) else 0 := by
  by_cases hNd : N.Coprime d
  · rw [if_pos hNd]
    exact zeroGeneralized_eq_physical N d hNd m n
  · rw [if_neg hNd]
    exact zeroGeneralized_eq_zero_of_not_coprime N d hNd m n

/-- The finite sum of the ACTUAL normalized gamma*sigma0 phases now has
the literal physical arithmetic factor, including the true gate. -/
theorem sum_zeroNormalizedPhase_eq_physical (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (m n : ℤ) :
    (∑ r : ZeroResidue N d, zeroNormalizedPhase N hN d m n r) =
      if N.Coprime d then kloosterman d (-n * inverseResidue d (N : ℤ)) (-m) else 0 := by
  rw [sum_zeroNormalizedPhase_eq_generalized, zeroGeneralized_eq_physical_or_zero]

/-- For a denominator exhibited by an actual Gamma0 matrix, its needed
coprimality is DERIVED from the determinant and is not an extra licence. -/
theorem sum_zeroNormalizedPhase_eq_physical_of_actual_matrix
    (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (hd : g 1 1 = (d : ℤ)) (m n : ℤ) :
    (∑ r : ZeroResidue N d, zeroNormalizedPhase N hN d m n r) =
      kloosterman d (-n * inverseResidue d (N : ℤ)) (-m) := by
  rw [sum_zeroNormalizedPhase_eq_generalized]
  exact zeroGeneralized_eq_physical N d (zero_actual_denominator_coprime N d g hg hd) m n

/-- The level-one boundary needs no integer representative equality for
inverseResidue: its actual ZMod phase directly gives S_d(-n,-m), even d=1. -/
theorem zeroGeneralized_level_one (d : ℕ) [NeZero d] (m n : ℤ) :
    zeroGeneralizedKloosterman 1 d m n = kloosterman d (-n) (-m) := by
  rw [zeroGeneralizedKloosterman, Physical.kloosterman_eq_zmod]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Nat.cast_one, one_mul, Int.cast_neg]
  by_cases hunit : IsUnit u
  · simp only [if_pos hunit]
    congr 1
    ring
  · simp only [if_neg hunit]

/-- The denominator-one boundary is genuinely retained: its one actual
residue and normalized character contribute one at every level and mode. -/
theorem zeroGeneralized_denominator_one (N : ℕ) (m n : ℤ) :
    zeroGeneralizedKloosterman N 1 m n = 1 := by
  have hunit (u : ZMod 1) : IsUnit ((N : ZMod 1) * u) := by
    have h : (N : ZMod 1) * u = 1 := Subsingleton.elim _ _
    rw [h]
    exact isUnit_one
  have hphase (u : ZMod 1) :
      ZMod.stdAddChar (-(m : ZMod 1) * (((N : ZMod 1) * u)⁻¹) - (n : ZMod 1) * u) = 1 := by
    have hz : -(m : ZMod 1) * (((N : ZMod 1) * u)⁻¹) - (n : ZMod 1) * u = 0 :=
      Subsingleton.elim _ _
    rw [hz]
    exact AddChar.map_zero_eq_one _
  simp [zeroGeneralizedKloosterman, hunit, hphase]

end ImbalancedChen.Part3.InfinityZeroPhysicalKloosterman20261025a
