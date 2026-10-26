import ImbalancedChen.Part3PrimeScatteringLocalIdentities
import ImbalancedChen.Part3OrdinaryCentralFourierMeans

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Both incoming families are actual ordinary continued Gamma0(p) functions:
E_infinity(s,z) and E_infinity(s,W_p z). Both observation charts are the
literal identity and Fricke charts. Their four unit-period Fourier means
identify every entry of the displayed 2x2 coefficient matrix. Nonzero
critical parameters use the native zeta zero-free theorem. The central
ordinary family is the existing analytic pole-removed family, whose value
is zero; its coefficients use the true residue-based scalar value -1.
The matrix adjoint identities follow from the proved two-channel Gram
identities, rather than a single-entry estimate or a unitarity premise.
No all-level matrix or spectral completeness assertion is made.
-/

noncomputable section
open Set Complex
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.OrdinaryCentralFourierMeans20261026b
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.PrimePhysicalScattering20261026b

theorem criticalParameter_ne_half {t : ℝ} (ht : t ≠ 0) :
    criticalParameter t ≠ (1 / 2 : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  exact ht (by simpa using hi)

/-- The domain is proved on this actual line. No global zeta zero-free
claim is used for the pole-removed reciprocal denominator. -/
theorem criticalParameter_mem_centralDomain (t : ℝ) :
    criticalParameter t ∈ centralNormalizationDomain := by
  by_cases ht : t = 0
  · subst t
    simpa [criticalParameter] using center_mem_centralNormalizationDomain
  have hc := criticalParameter_ne_half ht
  have hs : 0 < (criticalParameter t).re := by rw [criticalParameter_re]; norm_num
  refine ⟨hs, ?_, ?_⟩
  · intro h
    have hr := congrArg Complex.re h
    rw [criticalParameter_re] at hr
    norm_num at hr
  · rw [reciprocalDenominator_eq_completion _ hs hc,
      completionFactor_eq_completedZeta_of_re_pos _ hs]
    refine mul_ne_zero ?_ (critical_completed_denominator_ne_zero t)
    unfold polePolynomial
    apply mul_ne_zero
    · intro h
      have hr := congrArg Complex.re h
      simp [criticalParameter] at hr
    · intro h
      apply hc
      linear_combination (1 / 2 : ℂ) * h

theorem primeDiagonal_half {p : ℕ} (hp : p.Prime) :
    primeDiagonal p (1 / 2) = 1 := by
  have hd := prime_local_denominator_ne_zero hp (s := (1 / 2 : ℂ)) (by norm_num)
  rw [primeRatio_sq hp, show (-2 : ℂ) * (1 / 2) = -1 by norm_num,
    Complex.cpow_neg_one] at hd
  rw [primeDiagonal, primeRatio_sq hp,
    show (-2 : ℂ) * (1 / 2) = -1 by norm_num, Complex.cpow_neg_one]
  apply (div_eq_one_iff_eq hd).mpr
  rw [sub_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero), one_mul]

theorem primeOffDiagonal_half {p : ℕ} (hp : p.Prime) :
    primeOffDiagonal p (1 / 2) = 0 := by
  rw [primeOffDiagonal, primeRatio_sq hp,
    show (-2 : ℂ) * (1 / 2) = -1 by norm_num, Complex.cpow_neg_one,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero), sub_self, mul_zero, zero_div]

def primeCriticalDiagonal (p : ℕ) (t : ℝ) : ℂ :=
  criticalScattering t * primeDiagonal p (criticalParameter t)

def primeCriticalOffDiagonal (p : ℕ) (t : ℝ) : ℂ :=
  criticalScattering t * primeOffDiagonal p (criticalParameter t)

def primeScatteringMatrix (p : ℕ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![primeCriticalDiagonal p t, primeCriticalOffDiagonal p t;
     primeCriticalOffDiagonal p t, primeCriticalDiagonal p t]

/-- The second incoming family is the actual Fricke transform. -/
def primeOrdinaryChannel (p : ℕ) (hp : p.Prime) (j : Fin 2)
    (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  if j = 0 then centralOrdinaryLevel p s z
  else centralOrdinaryLevel p s (frickeSL p hp.pos • z)

def primeCuspPoint (p : ℕ) (hp : p.Prime) (i : Fin 2)
    (y : ℝ) (hy : 0 < y) (x : ℝ) : UpperHalfPlane :=
  if i = 0 then horizontalPoint y hy x
  else frickeSL p hp.pos • horizontalPoint y hy x

private theorem critical_scalar_eq_completed (t : ℝ) (ht : t ≠ 0) :
    criticalScattering t = completedScattering (criticalParameter t) := by
  rw [criticalScattering_of_ne_zero t ht]
  exact (completedScattering_eq_complexScattering _
    (by rw [criticalParameter_re]; norm_num) (critical_gamma_shift_legal t ht)).symm

/-- Actual infinity observation of the first physical incoming channel. -/
theorem prime_ordinary_infinity_mean {p : ℕ} (hp : p.Prime) (t : ℝ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      centralOrdinaryLevel p (criticalParameter t) (horizontalPoint y hy x)) =
      (y : ℂ) ^ criticalParameter t +
        primeCriticalDiagonal p t * (y : ℂ) ^ (1 - criticalParameter t) := by
  by_cases ht : t = 0
  · subst t
    simp [criticalParameter, primeCriticalDiagonal, primeDiagonal_half hp,
      criticalScattering_zero, centralOrdinaryLevel_center]
  have hc := criticalParameter_ne_half ht
  have hs : 0 < (criticalParameter t).re := by rw [criticalParameter_re]; norm_num
  have hd := critical_completed_denominator_ne_zero t
  rw [ordinary_infinity_mean p _ y hy, completedInfinityConstant_eq p _ hs hc y hy,
    ← primeDiagonal_eq_infinity_moment hp,
    inverseCompletion_eq_actual_reciprocal _ (criticalParameter_mem_centralDomain t) hc,
    completionFactor_eq_completedZeta_of_re_pos _ hs,
    primeCriticalDiagonal, critical_scalar_eq_completed t ht, completedScattering]
  field_simp [hd]
  <;> ring

/-- Actual Fricke observation of the first physical incoming channel. -/
theorem prime_ordinary_zero_mean {p : ℕ} (hp : p.Prime) (t : ℝ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, centralOrdinaryLevel p (criticalParameter t)
      (frickeSL p hp.pos • horizontalPoint y hy x)) =
        primeCriticalOffDiagonal p t * (y : ℂ) ^ (1 - criticalParameter t) := by
  by_cases ht : t = 0
  · subst t
    simp [criticalParameter, primeCriticalOffDiagonal, primeOffDiagonal_half hp,
      centralOrdinaryLevel_center]
  have hc := criticalParameter_ne_half ht
  have hs : 0 < (criticalParameter t).re := by rw [criticalParameter_re]; norm_num
  have hd := critical_completed_denominator_ne_zero t
  rw [ordinary_zeroCusp_mean p hp.pos _ (criticalParameter_mem_centralDomain t) y hy,
    completedReflectedConstant_eq_moments p _ hc y hy,
    reflected_incoming_moment_zero p hp.one_lt, mul_zero, zero_add,
    ← primeOffDiagonal_eq_reflected_moment hp,
    inverseCompletion_eq_actual_reciprocal _ (criticalParameter_mem_centralDomain t) hc,
    completionFactor_eq_completedZeta_of_re_pos _ hs,
    primeCriticalOffDiagonal, critical_scalar_eq_completed t ht, completedScattering]
  field_simp [hd]
  <;> ring

/-- ALL FOUR entries are genuine physical Fourier coefficients. Row i is
the observation chart, column j the incoming family. The Fricke involution
proves the second column, rather than assuming matrix symmetry. At t=0 the
same formula uses the true analytic ordinary zero and residue extension. -/
theorem prime_physical_four_means {p : ℕ} (hp : p.Prime) (t : ℝ)
    (i j : Fin 2) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, primeOrdinaryChannel p hp j (criticalParameter t)
      (primeCuspPoint p hp i y hy x)) =
      (if i = j then (y : ℂ) ^ criticalParameter t else 0) +
        primeScatteringMatrix p t i j * (y : ℂ) ^ (1 - criticalParameter t) := by
  fin_cases i <;> fin_cases j
  · simpa [primeOrdinaryChannel, primeCuspPoint, primeScatteringMatrix] using
      prime_ordinary_infinity_mean hp t y hy
  · simpa [primeOrdinaryChannel, primeCuspPoint, primeScatteringMatrix] using
      prime_ordinary_zero_mean hp t y hy
  · simpa [primeOrdinaryChannel, primeCuspPoint, primeScatteringMatrix] using
      prime_ordinary_zero_mean hp t y hy
  · simpa [primeOrdinaryChannel, primeCuspPoint, primeScatteringMatrix,
      frickeSL_action_involutive p hp.pos] using prime_ordinary_infinity_mean hp t y hy

theorem primeScatteringMatrix_center {p : ℕ} (hp : p.Prime) :
    primeScatteringMatrix p 0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeScatteringMatrix, primeCriticalDiagonal, primeCriticalOffDiagonal,
      criticalParameter, primeDiagonal_half hp, primeOffDiagonal_half hp]

theorem prime_critical_full_gram {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeCriticalDiagonal p t * conj (primeCriticalDiagonal p t) +
      primeCriticalOffDiagonal p t * conj (primeCriticalOffDiagonal p t) = 1 := by
  have hscalar : criticalScattering t * conj (criticalScattering t) = 1 := by
    rw [Complex.mul_conj', criticalScattering_norm]
    norm_num
  unfold primeCriticalDiagonal primeCriticalOffDiagonal
  simp only [map_mul]
  calc
    _ = (criticalScattering t * conj (criticalScattering t)) *
      (primeDiagonal p (criticalParameter t) * conj (primeDiagonal p (criticalParameter t)) +
        primeOffDiagonal p (criticalParameter t) *
          conj (primeOffDiagonal p (criticalParameter t))) := by ring
    _ = 1 := by rw [hscalar, prime_critical_gram hp t, one_mul]

theorem prime_critical_full_cross {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeCriticalDiagonal p t * conj (primeCriticalOffDiagonal p t) +
      primeCriticalOffDiagonal p t * conj (primeCriticalDiagonal p t) = 0 := by
  unfold primeCriticalDiagonal primeCriticalOffDiagonal
  simp only [map_mul]
  calc
    _ = (criticalScattering t * conj (criticalScattering t)) *
      (primeDiagonal p (criticalParameter t) * conj (primeOffDiagonal p (criticalParameter t)) +
        primeOffDiagonal p (criticalParameter t) *
          conj (primeDiagonal p (criticalParameter t))) := by ring
    _ = 0 := by rw [prime_critical_cross hp t, mul_zero]

/-- Unitarity of the identified physical 2x2 matrix, including the center. -/
theorem primeScatteringMatrix_mul_conjTranspose {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeScatteringMatrix p t * (primeScatteringMatrix p t).conjTranspose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [primeScatteringMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply] using
      prime_critical_full_gram hp t
  · simpa [primeScatteringMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply] using
      prime_critical_full_cross hp t
  · simpa [primeScatteringMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply, add_comm] using
      prime_critical_full_cross hp t
  · simpa [primeScatteringMatrix, Matrix.mul_fin_two, Matrix.conjTranspose_apply, add_comm] using
      prime_critical_full_gram hp t

theorem primeScatteringMatrix_conjTranspose_mul {p : ℕ} (hp : p.Prime) (t : ℝ) :
    (primeScatteringMatrix p t).conjTranspose * primeScatteringMatrix p t = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 2))).mp
    (primeScatteringMatrix_mul_conjTranspose hp t)

end ImbalancedChen.Part3.PrimePhysicalScattering20261026b
