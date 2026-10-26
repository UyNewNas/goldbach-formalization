import ImbalancedChen.Part3PrimeScatteringLocalIdentities
import ImbalancedChen.Part3OrdinaryCentralFourierMeans

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual completed prime-level functions at the literal infinity and
Fricke cusps satisfy a two-channel functional equation. Its entries are
the existing finite A,B Euler factors, now applied to genuine physical
functions rather than prescribed coefficients. The proof starts with the
actual finite oldform list, the literal Fricke dilation identity and the
actual full-level completed Fourier reflection. No global scattering
matrix supplier is assumed. The central matrix is not replaced by a
false scalar relation between the independent completed cusp functions.
-/

noncomputable section
open Set Complex
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.LevelOldformFricke20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.PrimeCompletedChannelReflection20261026b

theorem completedActual_reflection (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (z : UpperHalfPlane) : completedActualEisenstein (1 - s) z = completedActualEisenstein s z :=
  completedEisensteinFourier_reflection s z.im z.im_pos z.re hs0 hs1

/-- Literal expansion of the actual canonical prime oldform list. -/
theorem completed_prime_explicit {p : ℕ} (hp : p.Prime) (s : ℂ) (z : UpperHalfPlane) :
    completedLevelOldform p s z =
      (completedActualEisenstein s (pnatDilate ⟨p, hp.pos⟩ z) -
        primeRatio p s * completedActualEisenstein s z) /
          ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := by
  simp [completedLevelOldform, completedOldformNumerator, canonicalPrimeList_prime hp,
    oldformTerms, oldformNormalization, primeProduct, hp.not_dvd_one,
    pnatDilate_one, primePNat, primeRatio, sub_eq_add_neg]

private theorem reflected_prime_eq_self {p : ℕ} (hp : p.Prime) (z : UpperHalfPlane) :
    reflectedDilation p hp.pos ⟨p, hp.pos⟩ z = z := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  apply UpperHalfPlane.ext
  simp [reflectedDilation, dilate, hpR]

private theorem reflected_one_eq_prime {p : ℕ} (hp : p.Prime) (z : UpperHalfPlane) :
    reflectedDilation p hp.pos 1 z = pnatDilate ⟨p, hp.pos⟩ z := by
  apply UpperHalfPlane.ext
  simp [reflectedDilation, pnatDilate, dilate]

/-- Literal second physical column, with no eigenfunction assertion. -/
theorem completed_prime_fricke_explicit {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    completedLevelOldform p s (frickeSL p hp.pos • z) =
      (completedActualEisenstein s z - primeRatio p s *
        completedActualEisenstein s (pnatDilate ⟨p, hp.pos⟩ z)) /
          ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) := by
  rw [completedLevelOldform_fricke p hp.pos s hs0 hs1 z]
  simp [reflectedCompletedLevel, reflectedCompletedNumerator, canonicalPrimeList_prime hp,
    oldformTerms, oldformNormalization, primeProduct, hp.not_dvd_one,
    reflected_prime_eq_self hp, reflected_one_eq_prime hp,
    primePNat, primeRatio, sub_eq_add_neg]

theorem primeRatio_ne_zero {p : ℕ} (hp : p.Prime) (s : ℂ) : primeRatio p s ≠ 0 :=
  Complex.cpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)

theorem primeRatio_reflection {p : ℕ} (hp : p.Prime) (s : ℂ) :
    primeRatio p (1 - s) = ((p : ℂ) * primeRatio p s)⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold primeRatio
  rw [show -(1 - s) = s + (-1 : ℂ) by ring, Complex.cpow_add _ _ hp0,
    Complex.cpow_neg_one, Complex.cpow_neg]
  simp only [mul_inv_rev, inv_inv]

private theorem denominator_rewrite {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (p : ℂ) ^ s - (p : ℂ) ^ (-s) =
      (1 - primeRatio p s ^ 2) / primeRatio p s := by
  have hq := primeRatio_ne_zero hp s
  have hinv : (p : ℂ) ^ s = (primeRatio p s)⁻¹ := by simp [primeRatio, Complex.cpow_neg]
  rw [hinv]
  change (primeRatio p s)⁻¹ - primeRatio p s = _
  field_simp [hq]
  <;> ring

theorem completed_prime_q_explicit {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs : 0 < s.re) (z : UpperHalfPlane) :
    completedLevelOldform p s z = primeRatio p s *
      (completedActualEisenstein s (pnatDilate ⟨p, hp.pos⟩ z) -
        primeRatio p s * completedActualEisenstein s z) / (1 - primeRatio p s ^ 2) := by
  rw [completed_prime_explicit hp, denominator_rewrite hp]
  field_simp [primeRatio_ne_zero hp s, prime_local_denominator_ne_zero hp hs]
  <;> ring

theorem completed_prime_fricke_q_explicit {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) (z : UpperHalfPlane) :
    completedLevelOldform p s (frickeSL p hp.pos • z) = primeRatio p s *
      (completedActualEisenstein s z - primeRatio p s *
        completedActualEisenstein s (pnatDilate ⟨p, hp.pos⟩ z)) /
          (1 - primeRatio p s ^ 2) := by
  have hs0 : s ≠ 0 := by intro h; subst s; simpa using hs
  rw [completed_prime_fricke_explicit hp s hs0 hs1, denominator_rewrite hp]
  field_simp [primeRatio_ne_zero hp s, prime_local_denominator_ne_zero hp hs]
  <;> ring

private theorem finite_channel_algebra (P q X Y : ℂ) (hP : P ≠ 0) (hq : q ≠ 0)
    (hd : 1 - q ^ 2 ≠ 0) (hr : 1 - ((P * q)⁻¹) ^ 2 ≠ 0) :
    q * (Y - q * X) / (1 - q ^ 2) =
      ((P - 1) * q ^ 2 / (1 - q ^ 2)) *
        ((P * q)⁻¹ * (Y - (P * q)⁻¹ * X) / (1 - ((P * q)⁻¹) ^ 2)) +
      (q * (1 - P * q ^ 2) / (1 - q ^ 2)) *
        ((P * q)⁻¹ * (X - (P * q)⁻¹ * Y) / (1 - ((P * q)⁻¹) ^ 2)) := by
  field_simp [hd, hr, hP, hq]
  <;> ring

/-- Actual pointwise two-channel completed functional equation on the
open strip. Its center is included; no totalized completion factor appears. -/
theorem completed_prime_channel_reflection {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1) (z : UpperHalfPlane) :
    completedLevelOldform p s z =
      primeDiagonal p s * completedLevelOldform p (1 - s) z +
        primeOffDiagonal p s * completedLevelOldform p (1 - s) (frickeSL p hp.pos • z) := by
  have hs0 : s ≠ 0 := by intro h; subst s; simpa using hs.1
  have hs1 : s ≠ 1 := by intro h; subst s; simpa using hs.2
  have ht : 0 < (1 - s).re := by simp; linarith
  have ht1 : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  rw [completed_prime_q_explicit hp s hs.1,
    completed_prime_q_explicit hp (1 - s) ht,
    completed_prime_fricke_q_explicit hp (1 - s) ht ht1]
  simp_rw [completedActual_reflection s hs0 hs1]
  have hd := prime_local_denominator_ne_zero hp hs.1
  have hr := prime_local_denominator_ne_zero hp ht
  simp_rw [primeRatio_reflection hp s] at hr ⊢
  exact finite_channel_algebra (p : ℂ) (primeRatio p s) _ _
    (Nat.cast_ne_zero.mpr hp.ne_zero) (primeRatio_ne_zero hp s) hd hr

end ImbalancedChen.Part3.PrimeCompletedChannelReflection20261026b
