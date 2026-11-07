import ImbalancedChen.Part3Gamma0ActualCusps
import ImbalancedChen.Part3ActualCuspScalingSourceOnly
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The literal infinity-to-cusp-1 matrices for Gamma0(N) are computed here.
For gamma = [[a,b],[c,d]], write c = N*k, t = c+d and alpha = a+b.
The new chart has entries A = sqrt(N)*alpha, C = sqrt(N)*t,
D = -c/sqrt(N). The old chart has the same A,C and D = d/sqrt(N).
The determinant says a*t - N*k*alpha = 1, so the new phase has
alpha/t and -k/t, with N*(-k)*alpha congruent to 1 modulo t.
The old D/C exceeds the new D/C by 1/N, matching the established
old/new Fourier phase e(n/N). No Kuznetsov or spectral assertion occurs.
-/

namespace ImbalancedChen.Part3.CuspKloostermanMatrixSourceOnly
noncomputable section

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open P3ActualCuspScalingSourceOnly

/-- The real matrix of the actual integral modular element. -/
def gammaReal (gamma : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(gamma 0 0 : ℝ), (gamma 0 1 : ℝ);
     (gamma 1 0 : ℝ), (gamma 1 1 : ℝ)]

/-- At infinity the scaling matrix is the identity, so these products are
literally sigma_infinity^(-1) gamma sigma_one in the two cusp-1 charts. -/
def newCuspProduct (N : ℕ) (gamma : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  gammaReal gamma * newScaling (N : ℝ)

def oldCuspProduct (N : ℕ) (gamma : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  gammaReal gamma * oldScaling (N : ℝ)

theorem newCuspProduct_entries (N : ℕ) (gamma : SL(2, ℤ)) :
    newCuspProduct N gamma 0 0 =
        Real.sqrt (N : ℝ) * ((gamma 0 0 : ℝ) + (gamma 0 1 : ℝ)) ∧
    newCuspProduct N gamma 1 0 =
        Real.sqrt (N : ℝ) * ((gamma 1 0 : ℝ) + (gamma 1 1 : ℝ)) ∧
    newCuspProduct N gamma 1 1 = -(gamma 1 0 : ℝ) / Real.sqrt (N : ℝ) := by
  simp [newCuspProduct, gammaReal, newScaling, Matrix.mul_fin_two]
  <;> ring

theorem oldCuspProduct_entries (N : ℕ) (gamma : SL(2, ℤ)) :
    oldCuspProduct N gamma 0 0 =
        Real.sqrt (N : ℝ) * ((gamma 0 0 : ℝ) + (gamma 0 1 : ℝ)) ∧
    oldCuspProduct N gamma 1 0 =
        Real.sqrt (N : ℝ) * ((gamma 1 0 : ℝ) + (gamma 1 1 : ℝ)) ∧
    oldCuspProduct N gamma 1 1 = (gamma 1 1 : ℝ) / Real.sqrt (N : ℝ) := by
  simp [oldCuspProduct, gammaReal, oldScaling, Matrix.mul_fin_two]
  <;> ring

/-- Exact integral parameter relation. This is the coprimality certificate
behind the residue in the explicit infinity-to-1 Kloosterman sum. -/
theorem cusp_parameters_bezout (N : ℕ) (gamma : SL(2, ℤ))
    (hgamma : gamma ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ k : ℤ, gamma 1 0 = (N : ℤ) * k ∧
      gamma 0 0 * (gamma 1 0 + gamma 1 1) -
        (N : ℤ) * k * (gamma 0 0 + gamma 0 1) = 1 := by
  obtain ⟨k, hk⟩ := (gamma0_mem_iff_level_dvd_c N gamma).mp hgamma
  have hdet : gamma 0 0 * gamma 1 1 - gamma 0 1 * gamma 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using gamma.property
  refine ⟨k, hk, ?_⟩
  rw [hk] at hdet ⊢
  nlinarith [hdet]

/-- Any common divisor of the normalized integer modulus t=c+d and the
level N divides 1. This is the exact coprimality condition in Lemma B's
infinity-to-1 specialization (r=N, s=1). -/
theorem cusp_modulus_coprime_certificate (N : ℕ) (gamma : SL(2, ℤ))
    (hgamma : gamma ∈ CongruenceSubgroup.Gamma0 N) (z : ℤ)
    (hzN : z ∣ (N : ℤ)) (hzt : z ∣ gamma 1 0 + gamma 1 1) :
    z ∣ (1 : ℤ) := by
  obtain ⟨k, _, hbez⟩ := cusp_parameters_bezout N gamma hgamma
  obtain ⟨u, hu⟩ := hzN
  obtain ⟨v, hv⟩ := hzt
  refine ⟨gamma 0 0 * v - u * k * (gamma 0 0 + gamma 0 1), ?_⟩
  rw [hu, hv] at hbez
  nlinarith [hbez]

/-- Conversely each Bezout solution builds an actual Gamma0(N) matrix.
Its bottom-row sum is t and its top-row sum is alpha. -/
def matrixOfCuspParameters (N : ℕ) (t k alpha a : ℤ)
    (hbez : a * t - (N : ℤ) * k * alpha = 1) : SL(2, ℤ) :=
  ⟨!![a, alpha - a; (N : ℤ) * k, t - (N : ℤ) * k], by
    rw [Matrix.det_fin_two_of]
    nlinarith [hbez]⟩

theorem matrixOfCuspParameters_mem_gamma0 (N : ℕ) (t k alpha a : ℤ)
    (hbez : a * t - (N : ℤ) * k * alpha = 1) :
    matrixOfCuspParameters N t k alpha a hbez ∈
      CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_iff_level_dvd_c]
  exact ⟨k, rfl⟩

theorem matrixOfCuspParameters_rows (N : ℕ) (t k alpha a : ℤ)
    (hbez : a * t - (N : ℤ) * k * alpha = 1) :
    matrixOfCuspParameters N t k alpha a hbez 1 0 +
        matrixOfCuspParameters N t k alpha a hbez 1 1 = t ∧
    matrixOfCuspParameters N t k alpha a hbez 0 0 +
        matrixOfCuspParameters N t k alpha a hbez 0 1 = alpha := by
  simp [matrixOfCuspParameters] <;> ring

/-- The parameter construction recovers every actual Gamma0(N) matrix.
Together with the constructor, this is the integer-matrix parametrization
underlying the cusp-pair double coset calculation. -/
theorem gamma_reconstruct (N : ℕ) (gamma : SL(2, ℤ))
    (hgamma : gamma ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ k : ℤ,
      ∃ hbez : gamma 0 0 * (gamma 1 0 + gamma 1 1) -
          (N : ℤ) * k * (gamma 0 0 + gamma 0 1) = 1,
        matrixOfCuspParameters N (gamma 1 0 + gamma 1 1) k
          (gamma 0 0 + gamma 0 1) (gamma 0 0) hbez = gamma := by
  obtain ⟨k, hk, hbez⟩ := cusp_parameters_bezout N gamma hgamma
  refine ⟨k, hbez, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfCuspParameters, hk] <;> ring

/-- The classical inverse residue relation: (-N*k)*alpha = 1 mod t.
It is derived from the determinant, rather than assumed as a normalization. -/
theorem cusp_inverse_residue (N : ℕ) (gamma : SL(2, ℤ))
    (hgamma : gamma ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ k : ℤ, gamma 1 0 = (N : ℤ) * k ∧
      (gamma 1 0 + gamma 1 1) ∣
        (-(N : ℤ) * k) * (gamma 0 0 + gamma 0 1) - 1 := by
  obtain ⟨k, hk, hbez⟩ := cusp_parameters_bezout N gamma hgamma
  refine ⟨k, hk, -(gamma 0 0), ?_⟩
  nlinarith [hbez]

/-- The two entries of the new Kloosterman phase are alpha/t and -k/t.
The Bezout lemma above supplies their inverse-residue congruence. -/
theorem new_normalized_coordinates (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (k : ℤ)
    (hk : gamma 1 0 = (N : ℤ) * k)
    (ht : gamma 1 0 + gamma 1 1 ≠ 0) :
    newCuspProduct N gamma 0 0 / newCuspProduct N gamma 1 0 =
        ((gamma 0 0 + gamma 0 1 : ℤ) : ℝ) /
          ((gamma 1 0 + gamma 1 1 : ℤ) : ℝ) ∧
    newCuspProduct N gamma 1 1 / newCuspProduct N gamma 1 0 =
        -(k : ℝ) / ((gamma 1 0 + gamma 1 1 : ℤ) : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have htr : ((gamma 1 0 + gamma 1 1 : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast ht
  have hkR : (gamma 1 0 : ℝ) = (N : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  constructor
  · rw [(newCuspProduct_entries N gamma).1,
      (newCuspProduct_entries N gamma).2.1]
    push_cast
    field_simp [hs, htr]
  · rw [(newCuspProduct_entries N gamma).2.2,
      (newCuspProduct_entries N gamma).2.1, hkR]
    push_cast
    field_simp [hs, htr, hNr.ne']
    nlinarith [hsqr]

/-- The two denominators C coincide; their D/C coordinates differ by 1/N.
The positive modulus is sqrt(N)*t when t=c+d>0. -/
theorem old_lower_ratio_eq_new_add_inv_level (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (ht : gamma 1 0 + gamma 1 1 ≠ 0) :
    oldCuspProduct N gamma 1 1 / oldCuspProduct N gamma 1 0 =
      newCuspProduct N gamma 1 1 / newCuspProduct N gamma 1 0 +
        1 / (N : ℝ) := by
  rw [(oldCuspProduct_entries N gamma).2.2,
    (oldCuspProduct_entries N gamma).2.1,
    (newCuspProduct_entries N gamma).2.2,
    (newCuspProduct_entries N gamma).2.1]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have htr : (gamma 1 0 : ℝ) + (gamma 1 1 : ℝ) ≠ 0 := by
    exact_mod_cast ht
  field_simp [hs, htr, hNr.ne']
  nlinarith [hsqr]

/-- The literal Kloosterman exponential using a/c and d/c gains e(n/N)
when the old cusp-1 scaling replaces the new one. This is the same phase
direction as the established old/new Fourier coefficient relation. -/
theorem old_kloosterman_phase_eq_level_phase_mul_new
    (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ))
    (ht : gamma 1 0 + gamma 1 1 ≠ 0) (m n : ℤ) :
    P3Period64NativeReconstructionSourceOnly.e
      ((m : ℝ) * (oldCuspProduct N gamma 0 0 /
          oldCuspProduct N gamma 1 0) +
       (n : ℝ) * (oldCuspProduct N gamma 1 1 /
          oldCuspProduct N gamma 1 0)) =
      P3Period64NativeReconstructionSourceOnly.e ((n : ℝ) / (N : ℝ)) *
        P3Period64NativeReconstructionSourceOnly.e
          ((m : ℝ) * (newCuspProduct N gamma 0 0 /
              newCuspProduct N gamma 1 0) +
           (n : ℝ) * (newCuspProduct N gamma 1 1 /
              newCuspProduct N gamma 1 0)) := by
  have hA : oldCuspProduct N gamma 0 0 / oldCuspProduct N gamma 1 0 =
      newCuspProduct N gamma 0 0 / newCuspProduct N gamma 1 0 := by
    rw [(oldCuspProduct_entries N gamma).1,
      (oldCuspProduct_entries N gamma).2.1,
      (newCuspProduct_entries N gamma).1,
      (newCuspProduct_entries N gamma).2.1]
  have hD := old_lower_ratio_eq_new_add_inv_level N hN gamma ht
  have harg :
      (m : ℝ) * (oldCuspProduct N gamma 0 0 /
          oldCuspProduct N gamma 1 0) +
        (n : ℝ) * (oldCuspProduct N gamma 1 1 /
          oldCuspProduct N gamma 1 0) =
      (n : ℝ) / (N : ℝ) +
        ((m : ℝ) * (newCuspProduct N gamma 0 0 /
            newCuspProduct N gamma 1 0) +
         (n : ℝ) * (newCuspProduct N gamma 1 1 /
            newCuspProduct N gamma 1 0)) := by
    rw [hA, hD]
    ring
  rw [harg, P3Period64NativeReconstructionSourceOnly.e_add]

end
end ImbalancedChen.Part3.CuspKloostermanMatrixSourceOnly
