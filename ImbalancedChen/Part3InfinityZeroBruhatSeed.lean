import ImbalancedChen.Part3InfinityZeroPhysicalKloosterman
import ImbalancedChen.Part3ActualCompactBruhatKernel

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Actual gamma*sigma0 Bruhat action and Fourier-radial seed factorization.
For gamma10=N*k and gamma11=d != 0, the common actual Weyl modulus is
C=sqrt(N)*d, the left shift is b/d, and the right shift is -k/d.
The exact real/imaginary action and actual kernel equality are proved.
No integrability, Fourier integral, Bessel identity or spectral statement
is supplied as a premise or claimed here. N=1 and d=1 are retained.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.InfinityZeroBruhatSeed20261025a

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.CuspKloostermanMatrixSourceOnly (gammaReal)
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a

/-- The actual real determinant-one product gamma*sigma0. -/
def zeroScaledSL (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ)) : SL(2, ℝ) :=
  SpecialLinearGroup.map (Int.castRingHom ℝ) g * zeroSL N hN

theorem zeroScaledSL_matrix (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ)) :
    (zeroScaledSL N hN g : Matrix (Fin 2) (Fin 2) ℝ) = zeroCuspProduct N g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroScaledSL, zeroSL, zeroCuspProduct, gammaReal,
      SpecialLinearGroup.map, coe_mul, Matrix.mul_fin_two]

theorem zeroScaledSL_smul (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    zeroScaledSL N hN g • z = g • (zeroSL N hN • z) := by
  rw [zeroScaledSL, mul_smul]
  rfl

/-- Bruhat decomposition for an ACTUAL real SL2 matrix; this is needed
because gamma*sigma0 is a real rather than integral matrix. -/
theorem realSL_bruhat (G : SL(2, ℝ)) (hC : G 1 0 ≠ 0) :
    G = realTranslation (G 0 0 / G 1 0) * scaledWeyl (G 1 0) hC *
      realTranslation (G 1 1 / G 1 0) := by
  have hdet : G 0 0 * G 1 1 - G 0 1 * G 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using G.det_coe
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realTranslation, scaledWeyl, coe_mul, Matrix.mul_fin_two, hC] <;>
    field_simp [hC] <;> nlinarith [hdet]

theorem realSL_bruhat_smul (G : SL(2, ℝ)) (hC : G 1 0 ≠ 0) (z : UpperHalfPlane) :
    G • z = (G 0 0 / G 1 0) +ᵥ
      (scaledWeyl (G 1 0) hC • ((G 1 1 / G 1 0) +ᵥ z)) := by
  rw [realSL_bruhat G hC, mul_smul, mul_smul, realTranslation_smul, realTranslation_smul]

/-- Actual zero-cusp common Weyl modulus is nonzero whenever the genuine
lower-right integral denominator is nonzero. -/
theorem zeroWeylModulus_ne_zero (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ))
    (hd : g 1 1 ≠ 0) : Real.sqrt (N : ℝ) * (g 1 1 : ℝ) ≠ 0 := by
  exact mul_ne_zero (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
    (by exact_mod_cast hd)

/-- Complete actual action identity for gamma*sigma0. The two shifts
come from the true matrix ratios and retain their signs. -/
theorem gamma_zeroScaling_bruhat (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ))
    (k : ℤ) (hc : g 1 0 = (N : ℤ) * k) (hd : g 1 1 ≠ 0) (z : UpperHalfPlane) :
    g • (zeroSL N hN • z) = ((g 0 1 : ℝ) / (g 1 1 : ℝ)) +ᵥ
      (scaledWeyl (Real.sqrt (N : ℝ) * (g 1 1 : ℝ))
        (zeroWeylModulus_ne_zero N hN g hd) •
          ((-((k : ℝ) / (g 1 1 : ℝ))) +ᵥ z)) := by
  let G := zeroScaledSL N hN g
  have hmatrix := zeroScaledSL_matrix N hN g
  have hCeq : G 1 0 = Real.sqrt (N : ℝ) * (g 1 1 : ℝ) := by
    change (zeroScaledSL N hN g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = _
    rw [hmatrix]
    exact (zeroCuspProduct_entries N g).2.1
  have hC : G 1 0 ≠ 0 := by rw [hCeq]; exact zeroWeylModulus_ne_zero N hN g hd
  have hcoords := zero_normalized_coordinates N hN g k hc hd
  have hA : G 0 0 / G 1 0 = (g 0 1 : ℝ) / (g 1 1 : ℝ) := by
    change (zeroScaledSL N hN g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 /
      (zeroScaledSL N hN g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = _
    simpa only [hmatrix] using hcoords.1
  have hD : G 1 1 / G 1 0 = -((k : ℝ) / (g 1 1 : ℝ)) := by
    change (zeroScaledSL N hN g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 /
      (zeroScaledSL N hN g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = _
    simpa only [hmatrix, neg_div] using hcoords.2
  rw [← zeroScaledSL_smul]
  change G • z = _
  rw [realSL_bruhat_smul G hC z, hA, hD, hCeq]

/-- Gamma0 membership supplies the k parameter for the actual action
identity; there is no external congruence or kernel licence. -/
theorem gamma0_zeroScaling_bruhat (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (hd : g 1 1 ≠ 0) (z : UpperHalfPlane) :
    ∃ k : ℤ, g 1 0 = (N : ℤ) * k ∧
      g • (zeroSL N hN • z) = ((g 0 1 : ℝ) / (g 1 1 : ℝ)) +ᵥ
        (scaledWeyl (Real.sqrt (N : ℝ) * (g 1 1 : ℝ))
          (zeroWeylModulus_ne_zero N hN g hd) •
            ((-((k : ℝ) / (g 1 1 : ℝ))) +ᵥ z)) := by
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c N g).mp hg
  exact ⟨k, hk, gamma_zeroScaling_bruhat N hN g k hk hd z⟩

/-- Explicit real and imaginary parts of the ACTUAL gamma*sigma0 action,
with the common sqrt(N)*d Weyl modulus fully retained. -/
theorem gamma_zeroScaling_horizontal_coordinates (N : ℕ) (hN : 0 < N)
    (g : SL(2, ℤ)) (k : ℤ) (hc : g 1 0 = (N : ℤ) * k) (hd : g 1 1 ≠ 0)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (g • (zeroSL N hN • horizontalPoint y hy x)).re =
      (g 0 1 : ℝ) / (g 1 1 : ℝ) -
        (x - (k : ℝ) / (g 1 1 : ℝ)) /
          ((Real.sqrt (N : ℝ) * (g 1 1 : ℝ)) ^ 2 *
            ((x - (k : ℝ) / (g 1 1 : ℝ)) ^ 2 + y ^ 2)) ∧
    (g • (zeroSL N hN • horizontalPoint y hy x)).im =
      y / ((Real.sqrt (N : ℝ) * (g 1 1 : ℝ)) ^ 2 *
        ((x - (k : ℝ) / (g 1 1 : ℝ)) ^ 2 + y ^ 2)) := by
  have hpoint : (-((k : ℝ) / (g 1 1 : ℝ))) +ᵥ horizontalPoint y hy x =
      horizontalPoint y hy (x - (k : ℝ) / (g 1 1 : ℝ)) := by
    apply UpperHalfPlane.ext
    ext <;> simp [horizontalPoint, UpperHalfPlane.coe_vadd] <;> ring
  simp only [gamma_zeroScaling_bruhat N hN g k hc hd, hpoint]
  constructor
  · rw [UpperHalfPlane.vadd_re, scaledWeyl_horizontal_re]
    ring
  · rw [UpperHalfPlane.vadd_im, scaledWeyl_horizontal_im]

/-- The same actual height formula with sqrt(N)^2 simplified to N;
there is no missing level factor in the kernel denominator. -/
theorem gamma_zeroScaling_horizontal_height (N : ℕ) (hN : 0 < N)
    (g : SL(2, ℤ)) (k : ℤ) (hc : g 1 0 = (N : ℤ) * k) (hd : g 1 1 ≠ 0)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    (g • (zeroSL N hN • horizontalPoint y hy x)).im =
      y / ((N : ℝ) * (g 1 1 : ℝ) ^ 2 *
        ((x - (k : ℝ) / (g 1 1 : ℝ)) ^ 2 + y ^ 2)) := by
  have hh := (gamma_zeroScaling_horizontal_coordinates N hN g k hc hd y hy x).2
  have hs : (Real.sqrt (N : ℝ) * (g 1 1 : ℝ)) ^ 2 =
      (N : ℝ) * (g 1 1 : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hN.le)]
  rwa [hs] at hh

/-- Exact Fourier-radial seed factor for the ACTUAL gamma*sigma0 action.
The upper phase is e(m*b/d), the kernel is shifted by -k/d, and the
kernel modulus is the actual C=sqrt(N)*d. -/
theorem gamma_zeroScaling_fourierRadialSeed (N : ℕ) (hN : 0 < N)
    (g : SL(2, ℤ)) (k : ℤ) (hc : g 1 0 = (N : ℤ) * k) (hd : g 1 1 ≠ 0)
    (y : ℝ) (hy : 0 < y) (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ) :
    fourierRadialSeed m ψ (g • (zeroSL N hN • horizontalPoint y hy x)) =
      AddCircle.fourier m (((g 0 1 : ℝ) / (g 1 1 : ℝ)) : UnitAddCircle) *
        actualKernel (Real.sqrt (N : ℝ) * (g 1 1 : ℝ))
          (zeroWeylModulus_ne_zero N hN g hd) y hy m ψ
            (x - (k : ℝ) / (g 1 1 : ℝ)) := by
  have hpoint : (-((k : ℝ) / (g 1 1 : ℝ))) +ᵥ horizontalPoint y hy x =
      horizontalPoint y hy (x - (k : ℝ) / (g 1 1 : ℝ)) := by
    apply UpperHalfPlane.ext
    ext <;> simp [horizontalPoint, UpperHalfPlane.coe_vadd] <;> ring
  rw [gamma_zeroScaling_bruhat N hN g k hc hd, fourierRadialSeed_translate, hpoint]
  rfl

/-- In particular the actual finite canonical zero-cusp representatives
all use the SAME Weyl modulus sqrt(N)*d and the exact derived residue shift. -/
theorem zeroCanonical_fourierRadialSeed (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (r : ZeroResidue N d) (y : ℝ) (hy : 0 < y)
    (m : ℤ) (ψ : ℝ → ℂ) (x : ℝ) :
    fourierRadialSeed m ψ
      (zeroCanonicalMatrix N d r • (zeroSL N hN • horizontalPoint y hy x)) =
      AddCircle.fourier m (((canonicalB N d r.1 : ℤ) : ℝ) / (d : ℝ) : UnitAddCircle) *
        actualKernel (Real.sqrt (N : ℝ) * (d : ℝ))
          (mul_ne_zero (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
            (by exact_mod_cast NeZero.ne d)) y hy m ψ
          (x - ((r.1.val : ℕ) : ℝ) / (d : ℝ)) := by
  have hd : zeroCanonicalMatrix N d r 1 1 ≠ 0 := by
    change (d : ℤ) ≠ 0
    exact_mod_cast NeZero.ne d
  simpa only [zeroCanonicalMatrix, Int.cast_natCast] using
    gamma_zeroScaling_fourierRadialSeed N hN (zeroCanonicalMatrix N d r)
      (r.1.val : ℤ) rfl hd y hy m ψ x

end ImbalancedChen.Part3.InfinityZeroBruhatSeed20261025a

