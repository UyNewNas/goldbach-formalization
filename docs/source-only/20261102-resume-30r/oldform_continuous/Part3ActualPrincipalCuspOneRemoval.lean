import ImbalancedChen.Part3ActualPrincipalOldformRemoval
import ImbalancedChen.Part3ActualFrickeCuspPhase

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, R22, 2026-11-02.

Bind the actual completed incoming level Eisenstein family to the original
normalized cusp-one section. The existing sigmaOne = T W_N T_(1/N)
identity supplies the signed phase, and the genuine normalized Haar
Fourier coefficient is converted to the already proved physical integral.

This supplies the cusp-one phase association for the PRINCIPAL completed
family only. Neither the completed K amplitude nor its pointwise square
is renamed as the raw Whittaker coefficient or the full continuous norm.
General character-pair fibers, their formal norms, and the trace measure
remain separate obligations.
-/

namespace ImbalancedChen.Part3.ActualPrincipalCuspOneRemoval20261102r

noncomputable section

open Set MeasureTheory Complex
open scoped BigOperators UpperHalfPlane MatrixGroups
open ActualPrincipalOldformRemoval20261102r
open ActualFrickeCuspPhase20261025a
open ActualCuspFourierSectionSourceOnly
open AllLevelContinuedMaass20261026a
open LevelOldformScattering20261026a
open CriticalEisensteinScattering20261025a
open ActualFrickeNonzeroFourier20261026b
open CompletedKWeightedIntegral20261026b
open PrimitiveEisensteinFourierParameterAnalytic
open FrickeNormalizer
open ComplexOrderKBridgeSourceOnly
open NormalizedEisensteinPrimeAmplitude20261026b
open OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102
open OriginalRowOldformArithmetic20261102

/-- The required automorphy of this concrete critical-line family is
supplied from its existing native continuation theorem. -/
theorem actualCriticalLevelInvariant (N : ℕ) (hN : 0 < N) (t : ℝ) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ w : ℍ,
      completedLevelOldform N (criticalParameter t) (γ • w) =
        completedLevelOldform N (criticalParameter t) w := by
  intro γ hγ w
  exact completedLevelOldform_Gamma0_invariant N hN _
    (criticalParameter_mem_completedRegularDomain N t) ⟨γ, hγ⟩ w

def principalFrickeFourierCoeff (N : ℕ) (hN : 0 < N) (t y : ℝ)
    (hy : 0 < y) (j : ℤ) : ℂ :=
  frickeFourierCoeff N hN (completedLevelOldform N (criticalParameter t))
    (actualCriticalLevelInvariant N hN t) y hy j

def principalCuspOneFourierCoeff (N : ℕ) (hN : 0 < N) (t y : ℝ)
    (hy : 0 < y) (j : ℤ) : ℂ :=
  _root_.fourierCoeff
    (sigmaOneSection N hN (completedLevelOldform N (criticalParameter t))
      (actualCriticalLevelInvariant N hN t) y hy) j

/-- The exact signed scaling phase in the original cusp-one chart. -/
def sourceCuspPhase (N : ℕ) (j : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (N : ℂ))

theorem principalCuspOneFourierCoeff_eq_phase (N : ℕ) (hN : 0 < N)
    (t y : ℝ) (hy : 0 < y) (j : ℤ) :
    principalCuspOneFourierCoeff N hN t y hy j =
      sourceCuspPhase N j * principalFrickeFourierCoeff N hN t y hy j :=
  sigmaOne_fourierCoeff_fricke_phase N hN
    (completedLevelOldform N (criticalParameter t))
    (actualCriticalLevelInvariant N hN t) y hy j

/-- Reconcile the genuine period-one Haar coefficient with the exact
physical integral. Its Fourier sign is minus the requested frequency. -/
theorem principalFrickeFourierCoeff_eq_integral (N : ℕ) (hN : 0 < N)
    (t y : ℝ) (hy : 0 < y) (j : ℤ) :
    principalFrickeFourierCoeff N hN t y hy j =
      ∫ x in (0 : ℝ)..1,
        completedLevelOldform N (criticalParameter t)
          (frickeSL N hN • horizontalPoint y hy x) * integerPhase (-j) x := by
  unfold principalFrickeFourierCoeff frickeFourierCoeff
  rw [_root_.fourierCoeff_eq_intervalIntegral _ j (0 : ℝ)]
  simp only [div_one, one_smul, zero_add, smul_eq_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  change _root_.fourier (-j) (x : AddCircle (1 : ℝ)) *
      completedLevelOldform N (criticalParameter t)
        (frickeSL N hN • horizontal y hy x) = _
  have hhor : horizontal y hy x = horizontalPoint y hy x := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [horizontal, horizontalPoint]
  have hphase : _root_.fourier (-j) (x : AddCircle (1 : ℝ)) =
      integerPhase (-j) x := by
    rw [_root_.fourier_coe_apply]
    unfold integerPhase
    simp only [div_one]
    congr 1
    push_cast
    ring
  rw [hhor, hphase, mul_comm]

theorem principalFrickeFourierCoeff_eq_amplitude
    (N : ℕ) (hN : 0 < N) (t y : ℝ) (hy : 0 < y)
    (r : ℕ) (hr : 0 < r) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    principalFrickeFourierCoeff N hN t y hy (ε * (r : ℤ)) =
      2 * (Real.sqrt y : ℂ) * principalReflectedAmplitude N r (criticalParameter t) *
        complexOrderK (criticalParameter t - 1 / 2) (2 * Real.pi * r * y) := by
  have hneg : -ε = 1 ∨ -ε = -1 := by
    rcases hε with rfl | rfl <;> norm_num
  rw [principalFrickeFourierCoeff_eq_integral]
  simp only [← neg_mul]
  rw [completed_fricke_nonzero_integral_critical N hN t r hr y hy (-ε) hneg,
    reflectedNonzeroCoefficient_eq_principalAmplitude N hN r hr (criticalParameter t) y]

/-- Explicit completed K amplitude in the ORIGINAL normalized cusp-one
chart, derived from the actual section by the following theorem. -/
def principalCuspOneAmplitude (N : ℕ) (t : ℝ) (ε : ℤ) (r : ℕ) : ℂ :=
  sourceCuspPhase N (ε * (r : ℤ)) *
    principalReflectedAmplitude N r (criticalParameter t)

theorem principalCuspOneFourierCoeff_eq_amplitude
    (N : ℕ) (hN : 0 < N) (t y : ℝ) (hy : 0 < y)
    (r : ℕ) (hr : 0 < r) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    principalCuspOneFourierCoeff N hN t y hy (ε * (r : ℤ)) =
      2 * (Real.sqrt y : ℂ) * principalCuspOneAmplitude N t ε r *
        complexOrderK (criticalParameter t - 1 / 2) (2 * Real.pi * r * y) := by
  rw [principalCuspOneFourierCoeff_eq_phase,
    principalFrickeFourierCoeff_eq_amplitude N hN t y hy r hr ε hε]
  unfold principalCuspOneAmplitude
  ring

theorem sourceCuspPhase_neg_mul_self (N : ℕ) (j : ℤ) :
    sourceCuspPhase N (-j) * sourceCuspPhase N j = 1 := by
  unfold sourceCuspPhase
  rw [← Complex.exp_add]
  have hzero : 2 * Real.pi * Complex.I * ((-j : ℤ) : ℂ) / (N : ℂ) +
      2 * Real.pi * Complex.I * (j : ℂ) / (N : ℂ) = 0 := by
    push_cast
    ring
  rw [hzero, Complex.exp_zero]

theorem sourceCuspPhase_norm (N : ℕ) (j : ℤ) : ‖sourceCuspPhase N j‖ = 1 := by
  unfold sourceCuspPhase
  rw [Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * (j : ℂ) / (N : ℂ)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The retained geometric cusp phase cancels BEFORE index removal.
The right side keeps the phase at the residual signed n, independently
of height, the multiplier, and every future m/c label. -/
theorem principal_cuspOne_phase_removal
    (N : ℕ) (hN : 0 < N) (a n : ℕ) (haN : a.Coprime N)
    (han : a.Coprime n) (t : ℝ) (ε : ℤ) :
    sourceCuspPhase N (-(ε * ((a * n : ℕ) : ℤ))) *
        principalCuspOneAmplitude N t ε (a * n) =
      normalizedDivisorAmplitude a (criticalParameter t) *
        (sourceCuspPhase N (-(ε * (n : ℤ))) * principalCuspOneAmplitude N t ε n) := by
  unfold principalCuspOneAmplitude
  rw [← mul_assoc, sourceCuspPhase_neg_mul_self, one_mul,
    ← mul_assoc (sourceCuspPhase N (-(ε * (n : ℤ)))),
    sourceCuspPhase_neg_mul_self, one_mul,
    principalReflectedAmplitude_mul_of_coprime N hN a n haN han]

/-- The same phase removal is instantiated at the original primary row;
both coprimality conditions come from Q20, not from new fields. -/
theorem original_row_principal_cuspOne_phase_removal
    (D : OriginalData) (key : BlockKey) (z : Row D key)
    {n : ℕ} (hn : n ∈ nCarrier D key z.val) (t : ℝ) (ε : ℤ) :
    sourceCuspPhase z.val (-(ε * (((D.block.atom.residue.natAbs * key.1) * n : ℕ) : ℤ))) *
        principalCuspOneAmplitude z.val t ε ((D.block.atom.residue.natAbs * key.1) * n) =
      normalizedDivisorAmplitude (D.block.atom.residue.natAbs * key.1) (criticalParameter t) *
        (sourceCuspPhase z.val (-(ε * (n : ℤ))) * principalCuspOneAmplitude z.val t ε n) :=
  principal_cuspOne_phase_removal z.val (levelCarrier_licensed D key z.property).1
    _ n (original_abl_argument_coprime_level D key z)
    (original_index_coprime_abl_argument D key z hn).symm t ε

end

end ImbalancedChen.Part3.ActualPrincipalCuspOneRemoval20261102r
