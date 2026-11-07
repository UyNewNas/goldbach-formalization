import ImbalancedChen.Part3Gamma0GeneralCuspWidth
import ImbalancedChen.Part3ActualCuspFourierSection

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Unit-period normalization of every ACTUAL integral Gamma0 cusp using
gamma*diag(sqrt(w),1/sqrt(w)), where w is the computed primitive width.
Both sqrt factors remain explicit. All actual stabilizers act as integer
translations in this chart, modulo the central sign, and invariant
functions have period-one horizontal traces. No Fourier-coefficient
Jacobian, spectral measure, or raw-dt normalization identity is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0GeneralCuspUnitPeriod20261025a
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup UpperHalfPlane
open Gamma0GeneralCuspWidth20261025a
open Gamma0ActualCuspsSourceOnly
open ActualCuspFourierSectionSourceOnly

def integralReal (gamma : SL(2, ℤ)) : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) gamma

def integerTranslationReal (k : ℤ) : SL(2, ℝ) := integralReal (ModularGroup.T ^ k)

def widthDiagonal (w : ℕ) (hw : 0 < w) : SL(2, ℝ) :=
  ⟨!![Real.sqrt (w : ℝ), 0; 0, 1 / Real.sqrt (w : ℝ)], by
    have hwR : (0 : ℝ) < w := by exact_mod_cast hw
    have hs : Real.sqrt (w : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hwR).ne'
    simp [Matrix.det_fin_two_of, hs]⟩

def normalizedScaling (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ)) : SL(2, ℝ) :=
  integralReal gamma * widthDiagonal (cuspWidth N gamma) (cuspWidth_pos N hN gamma)

/-- Literal sqrt(width) and reciprocal-sqrt(width) factors of the actual
scaling matrix; they are not absorbed into an unspecified normalization. -/
theorem normalizedScaling_entries (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ)) :
    (normalizedScaling N hN gamma : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(gamma 0 0 : ℝ) * Real.sqrt (cuspWidth N gamma : ℝ),
          (gamma 0 1 : ℝ) / Real.sqrt (cuspWidth N gamma : ℝ);
        (gamma 1 0 : ℝ) * Real.sqrt (cuspWidth N gamma : ℝ),
          (gamma 1 1 : ℝ) / Real.sqrt (cuspWidth N gamma : ℝ)] := by
  simp [normalizedScaling, integralReal, widthDiagonal, coe_mul,
    Matrix.mul_fin_two, Matrix.SpecialLinearGroup.map_apply_coe, div_eq_mul_inv]

/-- The actual c=1 cusp matrix recovers the ORIGINAL old scaling chart,
with width N and both original sqrt(N) factors. -/
theorem normalizedScaling_cuspOne (N : ℕ) (hN : 0 < N) :
    normalizedScaling N hN cuspOneMatrix =
      P3ActualCuspScalingSourceOnly.oldSL (N : ℝ) (by exact_mod_cast hN) := by
  apply Subtype.ext
  rw [normalizedScaling_entries]
  simp [cuspWidth_cuspOne, cuspOneMatrix,
    P3ActualCuspScalingSourceOnly.oldSL, P3ActualCuspScalingSourceOnly.oldScaling]

theorem widthDiagonal_conj_translation (w : ℕ) (hw : 0 < w) (k : ℤ) :
    widthDiagonal w hw * integerTranslationReal k * (widthDiagonal w hw)⁻¹ =
      integerTranslationReal ((w : ℤ) * k) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hs : Real.sqrt (w : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hwR).ne'
  have hsqr : Real.sqrt (w : ℝ) ^ 2 = (w : ℝ) := Real.sq_sqrt hwR.le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [widthDiagonal, integerTranslationReal, integralReal, SL2_inv_expl,
      ModularGroup.coe_T_zpow, coe_mul, Matrix.mul_fin_two,
      Matrix.SpecialLinearGroup.map_apply_coe] <;>
    field_simp [hs] <;> nlinarith [hsqr]

/-- Conjugating a unit-coordinate integer translation gives exactly the
cast of the genuine integral width-multiple cusp stabilizer. -/
theorem normalizedScaling_conj_translation (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (k : ℤ) :
    normalizedScaling N hN gamma * integerTranslationReal k *
        (normalizedScaling N hN gamma)⁻¹ =
      integralReal (gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * k) * gamma⁻¹) := by
  unfold normalizedScaling
  calc
    (integralReal gamma * widthDiagonal (cuspWidth N gamma) (cuspWidth_pos N hN gamma)) *
        integerTranslationReal k *
        (integralReal gamma * widthDiagonal (cuspWidth N gamma) (cuspWidth_pos N hN gamma))⁻¹ =
      integralReal gamma *
        (widthDiagonal (cuspWidth N gamma) (cuspWidth_pos N hN gamma) * integerTranslationReal k *
          (widthDiagonal (cuspWidth N gamma) (cuspWidth_pos N hN gamma))⁻¹) *
        (integralReal gamma)⁻¹ := by group
    _ = integralReal gamma * integerTranslationReal ((cuspWidth N gamma : ℤ) * k) *
        (integralReal gamma)⁻¹ := by rw [widthDiagonal_conj_translation]
    _ = integralReal (gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * k) * gamma⁻¹) := by
      simp [integralReal, integerTranslationReal]

theorem normalizedScaling_deck (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ)) (k : ℤ) :
    integralReal (gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * k) * gamma⁻¹) *
        normalizedScaling N hN gamma =
      normalizedScaling N hN gamma * integerTranslationReal k := by
  rw [← normalizedScaling_conj_translation N hN gamma k]
  group

theorem integralReal_smul (gamma : SL(2, ℤ)) (z : ℍ) : integralReal gamma • z = gamma • z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [integralReal, Matrix.SpecialLinearGroup.map_apply_coe]

/-- Actual integral stabilizer action in the normalized chart. -/
theorem normalizedScaling_deck_action (N : ℕ) (hN : 0 < N)
    (gamma : SL(2, ℤ)) (k : ℤ) (z : ℍ) :
    (gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * k) * gamma⁻¹) •
        (normalizedScaling N hN gamma • z) =
      normalizedScaling N hN gamma • (ModularGroup.T ^ k • z) := by
  rw [← integralReal_smul]
  rw [← mul_smul, normalizedScaling_deck, mul_smul]
  exact congrArg (fun w : ℍ => normalizedScaling N hN gamma • w)
    (integralReal_smul (ModularGroup.T ^ k) z)

/-- Conversely EVERY actual Gamma0 element fixing this actual cusp acts
by an integer translation in the same chart, including the central sign. -/
theorem normalized_stabilizer_action (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ))
    (g : CongruenceSubgroup.Gamma0 N)
    (hg : FixesIntegralCusp gamma (g : SL(2, ℤ))) :
    ∃ k : ℤ, ∀ z : ℍ, (g : SL(2, ℤ)) • (normalizedScaling N hN gamma • z) =
      normalizedScaling N hN gamma • (ModularGroup.T ^ k • z) := by
  obtain ⟨k, hk | hk⟩ := gamma0_cusp_stabilizer_classification N hN gamma g hg
  · exact ⟨k, fun z => by rw [hk]; exact normalizedScaling_deck_action N hN gamma k z⟩
  · exact ⟨k, fun z => by rw [hk, UpperHalfPlane.SL_neg_smul]; exact normalizedScaling_deck_action N hN gamma k z⟩

theorem normalized_stabilizer_real_action (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ))
    (g : CongruenceSubgroup.Gamma0 N) (hg : FixesIntegralCusp gamma (g : SL(2, ℤ))) :
    ∃ k : ℤ, ∀ z : ℍ, (g : SL(2, ℤ)) • (normalizedScaling N hN gamma • z) =
      normalizedScaling N hN gamma • ((k : ℝ) +ᵥ z) := by
  obtain ⟨k, hk⟩ := normalized_stabilizer_action N hN gamma g hg
  exact ⟨k, fun z => by simpa only [ModularGroup.modular_T_zpow_smul] using hk z⟩

theorem real_vadd_re (t : ℝ) (z : ℍ) : (t +ᵥ z).re = t + z.re := by
  have h : ((t +ᵥ z : ℍ) : ℂ) = (t : ℂ) + (z : ℂ) := by
    simp [UpperHalfPlane.coe_vadd]
  have hr := congrArg Complex.re h
  simpa using hr

/-- No fractional real period can be effected by an actual cusp
stabilizer in the normalized chart. -/
theorem normalized_no_fractional_period (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ))
    (g : CongruenceSubgroup.Gamma0 N) (hg : FixesIntegralCusp gamma (g : SL(2, ℤ)))
    (t : ℝ) (ht : ∀ z : ℍ, (g : SL(2, ℤ)) • (normalizedScaling N hN gamma • z) =
      normalizedScaling N hN gamma • (t +ᵥ z)) : ∃ k : ℤ, t = (k : ℝ) := by
  obtain ⟨k, hk⟩ := normalized_stabilizer_real_action N hN gamma g hg
  let z : ℍ := ⟨⟨0, 1⟩, by norm_num⟩
  have hscaled : normalizedScaling N hN gamma • (t +ᵥ z) =
      normalizedScaling N hN gamma • ((k : ℝ) +ᵥ z) := (ht z).symm.trans (hk z)
  have hcoord : t +ᵥ z = (k : ℝ) +ᵥ z := by
    have h := congrArg (fun u : ℍ => (normalizedScaling N hN gamma)⁻¹ • u) hscaled
    simpa only [← smul_smul, inv_mul_cancel, one_smul] using h
  have hre := congrArg UpperHalfPlane.re hcoord
  rw [real_vadd_re, real_vadd_re] at hre
  exact ⟨k, add_right_cancel hre⟩

/-- Unit real period is attained by a displayed actual Gamma0 matrix.
Together with no fractional period, this is exact normalized width one. -/
theorem normalized_width_exactly_one (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ)) :
    ∃ g : CongruenceSubgroup.Gamma0 N, FixesIntegralCusp gamma (g : SL(2, ℤ)) ∧
      ∀ z : ℍ, (g : SL(2, ℤ)) • (normalizedScaling N hN gamma • z) =
        normalizedScaling N hN gamma • ((1 : ℝ) +ᵥ z) := by
  let g : CongruenceSubgroup.Gamma0 N :=
    ⟨gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * 1) * gamma⁻¹,
      width_multiple_mem_gamma0 N hN gamma 1⟩
  refine ⟨g, ?_, ?_⟩
  · change (gamma⁻¹ *
      (gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * 1) * gamma⁻¹) * gamma) 1 0 = 0
    have heq : gamma⁻¹ *
        (gamma * ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * 1) * gamma⁻¹) * gamma =
        ModularGroup.T ^ ((cuspWidth N gamma : ℤ) * 1) := by group
    rw [heq]
    simp [ModularGroup.coe_T_zpow]
  · intro z
    simpa only [ModularGroup.modular_T_zpow_smul, Int.cast_one] using
      normalizedScaling_deck_action N hN gamma 1 z

theorem horizontal_unit_translation (y : ℝ) (hy : 0 < y) (x : ℝ) :
    horizontal y hy (x + 1) = ModularGroup.T ^ (1 : ℤ) • horizontal y hy x := by
  apply UpperHalfPlane.ext
  rw [ModularGroup.coe_T_zpow_smul_eq]
  simp [horizontal, add_assoc, add_comm, add_left_comm]

def normalizedTrace (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ))
    (f : ℍ → ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  f (normalizedScaling N hN gamma • horizontal y hy x)

/-- Period ONE follows from true Gamma0 invariance and the actual width
membership theorem, with no postulated periodicity of a renamed trace. -/
theorem normalizedTrace_periodic (N : ℕ) (hN : 0 < N) (gamma : SL(2, ℤ)) (f : ℍ → ℂ)
    (hf : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, f (g • z) = f z)
    (y : ℝ) (hy : 0 < y) : Function.Periodic (normalizedTrace N hN gamma f y hy) 1 := by
  intro x
  change f (normalizedScaling N hN gamma • horizontal y hy (x + 1)) =
    f (normalizedScaling N hN gamma • horizontal y hy x)
  rw [horizontal_unit_translation, ← normalizedScaling_deck_action]
  exact hf _ (width_multiple_mem_gamma0 N hN gamma 1) _

end
end ImbalancedChen.Part3.Gamma0GeneralCuspUnitPeriod20261025a
