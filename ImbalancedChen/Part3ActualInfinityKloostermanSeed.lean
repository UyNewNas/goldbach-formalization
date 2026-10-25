import ImbalancedChen.Part3Gamma0ParabolicBottomRow
import ImbalancedChen.Part3CoprimeKloostermanCRT
import ImbalancedChen.Part3CuspTranslationFourierPhase
import Mathlib.Analysis.Fourier.AddCircle

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

This module concerns infinity-to-infinity double cosets only. Its modulus
is the actual lower-left integer c, with N|c at level N. It does not use
or change the infinity-to-cusp-1 modulus t=c+d or its sqrt(N) scaling.

Actual unit residues construct actual determinant-one Gamma0 matrices.
Every actual matrix of lower-left entry c is a two-sided integral
translation of a canonical matrix. The actual normalized matrix phases
sum to the literal physical Kloosterman sum (with the stated frequency
order). Bruhat factorization also splits a genuine Fourier-radial cusp
seed under the actual upper-half-plane action. No full parabolic integral unfolding,
Bessel transform, spectral decomposition or cancellation estimate is
claimed.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

/-- The integer representative of the lower-right unit residue. -/
def lowerRepresentative (c : ℕ) (u : UnitResidue c) : ℤ := (u.1.val : ℤ)

/-- The actual inverse representative, which will be the upper-left entry. -/
def upperRepresentative (c : ℕ) (u : UnitResidue c) : ℤ := ((u.1⁻¹).val : ℤ)

theorem lowerRepresentative_cast (c : ℕ) [NeZero c] (u : UnitResidue c) :
    (lowerRepresentative c u : ZMod c) = u.1 := by
  simp only [lowerRepresentative, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem upperRepresentative_cast (c : ℕ) [NeZero c] (u : UnitResidue c) :
    (upperRepresentative c u : ZMod c) = u.1⁻¹ := by
  simp only [upperRepresentative, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The determinant-one completion is obtained from the actual unit
inverse equation by divisibility, rather than postulated. -/
theorem upperRight_exists (c : ℕ) [NeZero c] (u : UnitResidue c) :
    ∃ b : ℤ, upperRepresentative c u * lowerRepresentative c u - b * (c : ℤ) = 1 := by
  have hzero :
      ((upperRepresentative c u * lowerRepresentative c u - 1 : ℤ) : ZMod c) = 0 := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one,
      upperRepresentative_cast, lowerRepresentative_cast,
      ZMod.inv_mul_of_unit u.1 u.2, sub_self]
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).mp hzero
  refine ⟨b, ?_⟩
  linear_combination hb

def upperRight (c : ℕ) [NeZero c] (u : UnitResidue c) : ℤ :=
  Classical.choose (upperRight_exists c u)

theorem upperRight_spec (c : ℕ) [NeZero c] (u : UnitResidue c) :
    upperRepresentative c u * lowerRepresentative c u - upperRight c u * (c : ℤ) = 1 :=
  Classical.choose_spec (upperRight_exists c u)

/-- An actual integral determinant-one matrix for the infinity-to-infinity
unit residue, with its literal lower-left modulus c. -/
def canonicalMatrix (c : ℕ) [NeZero c] (u : UnitResidue c) : SL(2, ℤ) :=
  ⟨!![upperRepresentative c u, upperRight c u; (c : ℤ), lowerRepresentative c u], by
    rw [Matrix.det_fin_two_of]
    exact upperRight_spec c u⟩

theorem canonicalMatrix_entries (c : ℕ) [NeZero c] (u : UnitResidue c) :
    canonicalMatrix c u 0 0 = upperRepresentative c u ∧
    canonicalMatrix c u 1 0 = (c : ℤ) ∧
    canonicalMatrix c u 1 1 = lowerRepresentative c u := by
  simp [canonicalMatrix]

/-- The level gate for the actual infinity-to-infinity matrix is N|c. -/
theorem canonicalMatrix_mem_gamma0 (N c : ℕ) [NeZero c]
    (hNc : N ∣ c) (u : UnitResidue c) :
    canonicalMatrix c u ∈ CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_iff_level_dvd_c]
  change (N : ℤ) ∣ (c : ℤ)
  exact_mod_cast hNc

/-- The determinant of every actual matrix with lower-left entry c
forces its lower-right residue to be a unit modulo c. -/
theorem actual_lowerRight_isUnit (c : ℕ) [NeZero c]
    (g : SL(2, ℤ)) (hc : g 1 0 = (c : ℤ)) : IsUnit (g 1 1 : ZMod c) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hcast := congrArg (fun a : ℤ => (a : ZMod c)) hdet
  rw [hc] at hcast
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one,
    ZMod.natCast_self, mul_zero, sub_zero] at hcast
  apply isUnit_iff_exists_inv.mpr
  exact ⟨(g 0 0 : ZMod c), by simpa only [mul_comm] using hcast⟩

/-- Every actual matrix at fixed nonzero lower-left modulus lies in the
two-sided infinity parabolic orbit of the constructed unit representative.
The right translation is derived from the lower-right congruence; the
left translation is supplied by the actual equal-bottom-row theorem. -/
theorem canonicalMatrix_surjective_on_double_cosets (c : ℕ) [NeZero c]
    (g : SL(2, ℤ)) (hc : g 1 0 = (c : ℤ)) :
    ∃ u : UnitResidue c, ∃ l k : ℤ,
      canonicalMatrix c u = ModularGroup.T ^ l * g * ModularGroup.T ^ k := by
  let u : UnitResidue c := ⟨(g 1 1 : ZMod c), actual_lowerRight_isUnit c g hc⟩
  have hdiv : (c : ℤ) ∣ lowerRepresentative c u - g 1 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ c).mp
    simp only [Int.cast_sub, lowerRepresentative_cast, u, sub_self]
  obtain ⟨k, hk⟩ := hdiv
  have hrows : bottomRow (canonicalMatrix c u) = bottomRow (g * ModularGroup.T ^ k) := by
    funext j
    fin_cases j
    · simp [bottomRow, canonicalMatrix, coe_mul, ModularGroup.coe_T_zpow,
        Matrix.mul_fin_two, hc]
    · simp [bottomRow, canonicalMatrix, coe_mul, ModularGroup.coe_T_zpow,
        Matrix.mul_fin_two, hc]
      linear_combination hk
  obtain ⟨l, hl⟩ := (bottomRow_eq_iff_left_translation
    (g * ModularGroup.T ^ k) (canonicalMatrix c u)).mp hrows
  exact ⟨u, l, k, by simpa only [mul_assoc] using hl⟩

/-- Distinct unit residues give distinct two-sided infinity parabolic
orbits at fixed lower-left modulus. -/
theorem canonicalMatrix_double_coset_injective (c : ℕ) [NeZero c]
    (u v : UnitResidue c)
    (horbit : ∃ l k : ℤ,
      canonicalMatrix c v = ModularGroup.T ^ l * canonicalMatrix c u * ModularGroup.T ^ k) :
    u = v := by
  obtain ⟨l, k, hmatrix⟩ := horbit
  have hbottom := congrArg (fun g : SL(2, ℤ) => g 1 1) hmatrix
  have hd : lowerRepresentative c v =
      (c : ℤ) * k + lowerRepresentative c u := by
    simpa [canonicalMatrix, coe_mul, ModularGroup.coe_T_zpow,
      Matrix.mul_fin_two] using hbottom
  have hcast := congrArg (fun a : ℤ => (a : ZMod c)) hd
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, zero_add, lowerRepresentative_cast] at hcast
  exact Subtype.ext hcast.symm

/-- Real upper unipotent translation, in the actual SL2 action. -/
def realTranslation (x : ℝ) : SL(2, ℝ) :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The actual Weyl matrix of lower-left entry c. -/
def scaledWeyl (c : ℝ) (hc : c ≠ 0) : SL(2, ℝ) :=
  ⟨!![0, -(1 / c); c, 0], by simp [Matrix.det_fin_two_of, hc]⟩

theorem realTranslation_smul (x : ℝ) (z : UpperHalfPlane) :
    realTranslation x • z = x +ᵥ z := by
  apply UpperHalfPlane.ext
  simp [realTranslation, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_vadd, add_comm]

/-- Genuine Bruhat factorization of every actual integral matrix with
nonzero lower-left entry. The determinant supplies the upper-right entry. -/
theorem actual_bruhat (g : SL(2, ℤ)) (hc : (g 1 0 : ℝ) ≠ 0) :
    SpecialLinearGroup.map (algebraMap ℤ ℝ) g =
      realTranslation ((g 0 0 : ℝ) / (g 1 0 : ℝ)) *
        scaledWeyl (g 1 0 : ℝ) hc *
        realTranslation ((g 1 1 : ℝ) / (g 1 0 : ℝ)) := by
  have hdet : (g 0 0 : ℝ) * (g 1 1 : ℝ) -
      (g 0 1 : ℝ) * (g 1 0 : ℝ) = 1 := by
    exact_mod_cast (show g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 by
      simpa only [Matrix.det_fin_two] using g.det_coe)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realTranslation, scaledWeyl, SpecialLinearGroup.map, coe_mul,
      Matrix.mul_fin_two, hc] <;>
    field_simp [hc] <;> nlinarith [hdet]

/-- Bruhat factorization acts on the genuine upper half-plane: both
translations and the Weyl action retain their actual meanings. -/
theorem actual_bruhat_smul (g : SL(2, ℤ)) (hc : (g 1 0 : ℝ) ≠ 0)
    (z : UpperHalfPlane) :
    g • z = ((g 0 0 : ℝ) / (g 1 0 : ℝ)) +ᵥ
      (scaledWeyl (g 1 0 : ℝ) hc •
        (((g 1 1 : ℝ) / (g 1 0 : ℝ)) +ᵥ z)) := by
  change SpecialLinearGroup.map (algebraMap ℤ ℝ) g • z = _
  rw [actual_bruhat g hc, mul_smul, mul_smul,
    realTranslation_smul, realTranslation_smul]

/-- A genuine Fourier-radial cusp seed on H, with arbitrary radial profile. -/
def fourierRadialSeed (m : ℤ) (h : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  AddCircle.fourier m (z.re : UnitAddCircle) * h z.im

/-- Horizontal translation of this actual seed produces its actual
additive Fourier phase; no automorphic coefficient is a premise. -/
theorem fourierRadialSeed_translate (m : ℤ) (h : ℝ → ℂ)
    (x : ℝ) (z : UpperHalfPlane) :
    fourierRadialSeed m h (x +ᵥ z) =
      AddCircle.fourier m (x : UnitAddCircle) * fourierRadialSeed m h z := by
  simp only [fourierRadialSeed, UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im,
    AddCircle.coe_add, AddCircle.fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]
  ring

/-- The actual transformed seed has the upper-left/c phase and the
lower-right/c translation required before continuous Fourier folding. -/
theorem fourierRadialSeed_actual_bruhat (m : ℤ) (h : ℝ → ℂ)
    (g : SL(2, ℤ)) (hc : (g 1 0 : ℝ) ≠ 0) (z : UpperHalfPlane) :
    fourierRadialSeed m h (g • z) =
      AddCircle.fourier m (((g 0 0 : ℝ) / (g 1 0 : ℝ)) : UnitAddCircle) *
        fourierRadialSeed m h (scaledWeyl (g 1 0 : ℝ) hc •
          ((((g 1 1 : ℝ) / (g 1 0 : ℝ))) +ᵥ z)) := by
  rw [actual_bruhat_smul, fourierRadialSeed_translate]

private theorem fourier_int_ratio (c : ℕ) [NeZero c] (m a : ℤ) :
    AddCircle.fourier m (((a : ℝ) / (c : ℝ)) : UnitAddCircle) =
      ZMod.stdAddChar ((m : ZMod c) * (a : ZMod c)) := by
  rw [← Int.cast_mul, ZMod.stdAddChar_coe, AddCircle.fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- Literal normalized matrix phase on the actual canonical double coset.
The first frequency multiplies a/c; the second multiplies d/c. -/
def canonicalMatrixPhase (c : ℕ) [NeZero c] (m n : ℤ) (u : UnitResidue c) : ℂ :=
  AddCircle.fourier m
      (((canonicalMatrix c u 0 0 : ℤ) : ℝ) / (c : ℝ) : UnitAddCircle) *
    AddCircle.fourier n
      (((canonicalMatrix c u 1 1 : ℤ) : ℝ) / (c : ℝ) : UnitAddCircle)

/-- The determinant-forced inverse and the actual lower-right unit
identify this genuine matrix phase with the physical residue phase. -/
theorem canonicalMatrixPhase_eq_stdAddChar (c : ℕ) [NeZero c]
    (m n : ℤ) (u : UnitResidue c) :
    canonicalMatrixPhase c m n u =
      ZMod.stdAddChar ((n : ZMod c) * u.1 + (m : ZMod c) * u.1⁻¹) := by
  have hentries := canonicalMatrix_entries c u
  simp only [canonicalMatrixPhase, hentries.1, hentries.2.2,
    fourier_int_ratio, upperRepresentative_cast, lowerRepresentative_cast]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The complete finite double-coset phase sum is the LITERAL physical
Kloosterman sum. Frequency order is explicit because physical `kloosterman`
uses the linear unit frequency first and inverse frequency second. -/
theorem sum_canonicalMatrixPhase_eq_kloosterman (c : ℕ) [NeZero c] (m n : ℤ) :
    (∑ u : UnitResidue c, canonicalMatrixPhase c m n u) = kloosterman c n m := by
  rw [kloosterman_eq_unitResidueSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact canonicalMatrixPhase_eq_stdAddChar c m n u

/-- The exact finite canonical-translation section. Its coefficients are
actual normalized circle integrals; obtaining its kernel F by periodizing
an actual transformed radial seed is a separate analytic caller. -/
def canonicalFiniteSection (c : ℕ) [NeZero c] (m : ℤ)
    (F : UnitAddCircle → ℂ) : UnitAddCircle → ℂ :=
  ∑ u : UnitResidue c, fun x =>
    AddCircle.fourier m
        (((canonicalMatrix c u 0 0 : ℤ) : ℝ) / (c : ℝ) : UnitAddCircle) *
      P3CuspTranslationFourierPhaseSourceOnly.translated F
        ((((canonicalMatrix c u 1 1 : ℤ) : ℝ) / (c : ℝ)) : UnitAddCircle) x

/-- Finite-modulus Fourier folding with all canonical matrix phases
identified. The input is only integrability of the common circle kernel;
no coefficient identity, spectral supplier, or arithmetic bound is assumed.
The genuine integral normalization is the period-one Haar normalization. -/
theorem canonicalFiniteSection_fourierCoeff (c : ℕ) [NeZero c]
    (m n : ℤ) (F : UnitAddCircle → ℂ)
    (hF : MeasureTheory.Integrable F AddCircle.haarAddCircle) :
    AddCircle.fourierCoeff (canonicalFiniteSection c m F) n =
      kloosterman c n m * AddCircle.fourierCoeff F n := by
  let sections : UnitResidue c → UnitAddCircle → ℂ := fun u x =>
    AddCircle.fourier m
        (((canonicalMatrix c u 0 0 : ℤ) : ℝ) / (c : ℝ) : UnitAddCircle) *
      P3CuspTranslationFourierPhaseSourceOnly.translated F
        ((((canonicalMatrix c u 1 1 : ℤ) : ℝ) / (c : ℝ)) : UnitAddCircle) x
  have hsections (u : UnitResidue c) :
      MeasureTheory.Integrable (sections u) AddCircle.haarAddCircle := by
    exact (P3CuspTranslationFourierPhaseSourceOnly.integrable_translated F hF _).const_mul _
  have hsum : AddCircle.fourierCoeff (canonicalFiniteSection c m F) n =
      ∑ u : UnitResidue c, AddCircle.fourierCoeff (sections u) n := by
    simpa only [Finset.sum_apply] using congrFun (AddCircle.fourierCoeff.sum
      (Finset.univ : Finset (UnitResidue c)) sections (fun u hu => hsections u)) n
  rw [hsum]
  calc
    _ = ∑ u : UnitResidue c,
        canonicalMatrixPhase c m n u * AddCircle.fourierCoeff F n := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [sections, AddCircle.fourierCoeff.const_mul,
        P3CuspTranslationFourierPhaseSourceOnly.fourierCoeff_translated,
        canonicalMatrixPhase]
      ring
    _ = (∑ u : UnitResidue c, canonicalMatrixPhase c m n u) *
        AddCircle.fourierCoeff F n := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [sum_canonicalMatrixPhase_eq_kloosterman]
end ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a



