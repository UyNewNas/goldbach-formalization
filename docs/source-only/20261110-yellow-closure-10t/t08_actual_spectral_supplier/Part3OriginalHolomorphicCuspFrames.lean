import ImbalancedChen.Part3NativeHolomorphicFourierNormalization
import ImbalancedChen.Part3ActualCuspBasisWhittakerCoefficients
import ImbalancedChen.Part3OriginalSignedTraceInput

/-!
The fixed scaling matrices of the original two-cusp trace, applied by
the weight-2r slash action to one actual holomorphic cusp form.  The
strict unit period is proved by the original integral parabolic deck
transformation. These coefficients use the native q-expansion and the
published holomorphic normalization at each cusp.
-/
namespace ImbalancedChen.Part3.OriginalHolomorphicCuspFrames20261110

noncomputable section
open Matrix SpecialLinearGroup GeneralLinearGroup UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane ModularForm Pointwise BigOperators
open Gamma0ActualCuspsSourceOnly Gamma0GeneralCuspWidth20261025a
open Gamma0GeneralCuspUnitPeriod20261025a NativeHolomorphicFourierNormalization20261102s
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalCommonPoissonLanes20261102
open P3NativePeriod64SamplingSourceOnly (D4)

abbrev levelGroup (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

def frameGL (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  mapGL ℝ (normalizedScaling N hN g)

def frameGroup (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ) :=
  ConjAct.toConjAct (frameGL N hN g)⁻¹ • levelGroup N

private theorem realIntegral_mapGL (g : SL(2, ℤ)) :
    mapGL ℝ (integralReal g) = mapGL ℝ g := by
  apply Units.ext
  ext i j
  simp [integralReal, mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe]

private theorem translationGL_one :
    upperRightHom (1 : ℝ) = mapGL ℝ (integerTranslationReal 1) := by
  rw [integerTranslationReal, realIntegral_mapGL, zpow_one]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperRightHom_apply, mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe,
      ModularGroup.coe_T]

/-- Membership is exact in the translated group of the native cusp form.
No period or automorphy of an unweighted pullback is assumed. -/
theorem normalized_frame_unit_strictPeriod (N : ℕ) (hN : 0 < N) (g : SL(2, ℤ)) :
    (1 : ℝ) ∈ (frameGroup N hN g).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, frameGroup,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    inv_inv, ConjAct.toConjAct_smul]
  let d := g * ModularGroup.T ^ ((cuspWidth N g : ℤ)*1) * g⁻¹
  have hd : d ∈ CongruenceSubgroup.Gamma0 N := width_multiple_mem_gamma0 N hN g 1
  change frameGL N hN g * upperRightHom (1 : ℝ) * (frameGL N hN g)⁻¹ ∈
    (CongruenceSubgroup.Gamma0 N).map (mapGL ℝ)
  apply Subgroup.mem_map.mpr
  refine ⟨d, hd, ?_⟩
  rw [translationGL_one]
  have h := congrArg (mapGL ℝ) (normalizedScaling_conj_translation N hN g 1)
  simpa only [d, frameGL, map_mul, map_inv, realIntegral_mapGL] using h.symm

def frameForm (N : ℕ) (hN : 0 < N) (r : ℕ)
    (f : CuspForm (levelGroup N) (2*(r : ℤ))) (g : SL(2, ℤ)) :
    CuspForm (frameGroup N hN g) (2*(r : ℤ)) :=
  CuspForm.translate f (frameGL N hN g)

/-- The determinant is one. The weight multiplier of the actual slash
action remains in the formula at cusp one. -/
theorem frameForm_apply (N : ℕ) (hN : 0 < N) (r : ℕ)
    (f : CuspForm (levelGroup N) (2*(r : ℤ))) (g : SL(2, ℤ)) (w : ℍ) :
    frameForm N hN r f g w =
      f (frameGL N hN g • w) * denom (frameGL N hN g) w ^ (-(2*(r : ℤ))) := by
  change (⇑f ∣[2*(r : ℤ)] frameGL N hN g) w = _
  simp [ModularForm.slash_apply, frameGL, UpperHalfPlane.σ]

def frameR (N : ℕ) (hN : 0 < N) (r : ℕ)
    (f : CuspForm (levelGroup N) (2*(r : ℤ))) (g : SL(2, ℤ)) (n : ℕ) : ℂ :=
  holomorphicR r (frameForm N hN r f g) n

theorem frame_holomorphic_fourier_integral (N : ℕ) (hN : 0 < N) (r : ℕ)
    (f : CuspForm (levelGroup N) (2*(r : ℤ))) (g : SL(2, ℤ)) (n : ℕ)
    {y : ℝ} (hy : 0 < y) :
    (∫ u in (0 : ℝ)..1, 1 / Periodic.qParam 1 (u + y*Complex.I)^n *
      (f (frameGL N hN g • ⟨u + y*Complex.I, by simpa using hy⟩) *
        denom (frameGL N hN g) ⟨u + y*Complex.I, by simpa using hy⟩ ^
          (-(2*(r : ℤ))))) =
      holomorphicRho r (frameForm N hN r f g) n * holomorphicScale r n := by
  simpa only [frameForm_apply] using
    native_holomorphic_fourier_integral r (frameForm N hN r f g)
      (normalized_frame_unit_strictPeriod N hN g) n hy

theorem frame_holomorphic_expansion (N : ℕ) (hN : 0 < N) (r : ℕ)
    (f : CuspForm (levelGroup N) (2*(r : ℤ))) (g : SL(2, ℤ)) (w : ℍ) :
    HasSum (fun n : ℕ => holomorphicRho r (frameForm N hN r f g) n *
      holomorphicScale r n * Periodic.qParam 1 (w : ℂ)^n)
      (f (frameGL N hN g • w) * denom (frameGL N hN g) w ^ (-(2*(r : ℤ)))) := by
  rw [← frameForm_apply]
  exact native_holomorphic_normalized_hasSum r (frameForm N hN r f g)
    (normalized_frame_unit_strictPeriod N hN g) w

/-- Both inputs use this very same f on the two manuscript matrices. -/
theorem two_actual_frames (N : ℕ) (hN : 0 < N) :
    frameGL N hN 1 = 1 ∧
      frameGL N hN cuspOneMatrix =
        mapGL ℝ (P3ActualCuspScalingSourceOnly.oldSL (N : ℝ) (by exact_mod_cast hN)) := by
  letI : NeZero N := ⟨hN.ne'⟩
  constructor
  · rw [frameGL, ActualCuspBasisWhittakerCoefficients20261102.basis_scaling_infinity N hN, map_one]
  · rw [frameGL, ActualCuspBasisWhittakerCoefficients20261102.basis_scaling_one N hN]

/-- The scaled native q-coefficient in the regular holomorphic large
sieve. The scalar (4π)^r compares this profile to Drappeau R, at either
actual cusp and every positive frequency. -/
def sieveCoeff (N : ℕ) (hN : 0 < N) (r : ℕ)
    (f : CuspForm (levelGroup N) (2*(r : ℤ))) (g : SL(2, ℤ)) (n : ℕ) : ℂ :=
  (((n : ℝ) ^ (-(2*(r : ℝ)-1)/2) : ℝ) : ℂ) *
    (UpperHalfPlane.qExpansion 1 (frameForm N hN r f g)).coeff n

theorem sieveCoeff_eq_scaled_R (N : ℕ) (hN : 0 < N) (r : ℕ)
    (f : CuspForm (levelGroup N) (2*(r : ℤ))) (g : SL(2, ℤ)) {n : ℕ} (hn : 0 < n) :
    sieveCoeff N hN r f g n = ((4*Real.pi : ℝ) : ℂ)^r * frameR N hN r f g n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (-(2*(r : ℝ)-1)/2) = Real.sqrt n / (n : ℝ)^r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hnR]
    congr 1
    ring
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold sieveCoeff frameR
  rw [hpow, holomorphicR_eq_qExpansion]
  simp only [holomorphicScale, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_mul, Complex.ofReal_ofNat, mul_pow]
  field_simp [hnC, hpi] <;> ring

/-- On every actual positive-sign source pair, the large-sieve bilinear
coefficient and the trace bilinear coefficient differ by (4π)^(2r).
The first coefficient is conjugated, the second is at the signed original
frequency on its actual source branch. -/
theorem original_positive_holomorphic_product (D : OriginalData) (k : BlockKey)
    (negativeM : Bool) (ha : D.block.atom.residue ≠ 0)
    (hsign : traceNegative D k negativeM = false) (z : ℕ) (hz : 0 < z)
    (r : ℕ) (f : CuspForm (levelGroup z) (2*(r : ℤ))) (J j : ℕ) {m n : ℕ}
    (hm : m ∈ commonMBlock J j) (hn : n ∈ nCarrier D k z) :
    let h := traceIndex D k negativeM z n
    (h.natAbs : ℤ) = h ∧
      starRingEnd ℂ (sieveCoeff z hz r f 1 m) * sieveCoeff z hz r f cuspOneMatrix h.natAbs =
        (((4*Real.pi : ℝ) : ℂ)^(2*r)) *
          (starRingEnd ℂ (frameR z hz r f 1 m) * frameR z hz r f cuspOneMatrix h.natAbs) := by
  have hp : 0 < m := lt_of_lt_of_le (pow_pos (by norm_num : 0 < (2 : ℕ)) j)
    (Finset.mem_Ico.mp hm).1
  have hn' := traceIndex_natAbs_pos D k negativeM z hn ha
  dsimp only
  constructor
  · rw [traceIndex_eq_signedY, hsign]
    simp [ImbalancedChen.P3ZActualPrimaryShortEndpoint.signedY]
  · rw [sieveCoeff_eq_scaled_R z hz r f 1 hp,
      sieveCoeff_eq_scaled_R z hz r f cuspOneMatrix hn', map_mul, map_pow,
      Complex.conj_ofReal, two_mul, pow_add]
    ring

end
end ImbalancedChen.Part3.OriginalHolomorphicCuspFrames20261110
