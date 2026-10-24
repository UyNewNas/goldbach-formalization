import ImbalancedChen.Part3Gamma0CuspMeasure
import ImbalancedChen.Part3Gamma0ActualCusps
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / no acceptance credit, 2026-10-24.

The preceding cusp-measure draft exhibits one parabolic translating the
scaled cusp-one coordinate by one.  Here the converse is proved.  An actual
integral SL2 matrix fixing cusp one is conjugated to an upper-triangular
matrix.  The determinant restricts its diagonal to ±1.  Its upper-right
entry is the integer cusp period, and the explicit lower-left entry after
conjugation is its negative.  Gamma0 membership forces that period to be
divisible by N.  The `newSL N` chart therefore has *exactly* integer deck
translations, including one, modulo the central sign.

The final pointwise and lintegral identities apply to genuine Gamma0-
invariant functions on the upper half-plane.  They concern the parabolic
cusp chart; no measure on the full Gamma0 orbit quotient is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0CuspMinimalWidth20261024zz

noncomputable section

open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0CuspMeasure20261024zz
open P3ActualCuspScalingSourceOnly

/-- Cusp one is fixed precisely when the matrix conjugated by the integral
cusp-one matrix fixes infinity, i.e. has lower-left entry zero. -/
def FixesCuspOne (g : SL(2, ℤ)) : Prop :=
  (cuspOneMatrix⁻¹ * g * cuspOneMatrix) 1 0 = 0

/-- The projective stabilizer condition written in literal integer entries.
This calculation also pins the sign of the lower-left cusp period. -/
theorem cuspOne_conjugated_c (g : SL(2, ℤ)) :
    (cuspOneMatrix⁻¹ * g * cuspOneMatrix) 1 0 =
      g 1 0 + g 1 1 - g 0 0 - g 0 1 := by
  simp [cuspOneMatrix, SL2_inv_expl, coe_mul, Matrix.mul_fin_two] <;> ring

theorem fixesCuspOne_iff_entries (g : SL(2, ℤ)) :
    FixesCuspOne g ↔ g 0 0 + g 0 1 = g 1 0 + g 1 1 := by
  rw [FixesCuspOne, cuspOne_conjugated_c]
  omega

/-- Integral determinant-one upper triangular matrices are translations
up to the central negative identity.  This strengthens the point-action
classification in Mathlib by retaining the matrix equality. -/
private theorem upperTriangular_signed_translation (h : SL(2, ℤ))
    (hc : h 1 0 = 0) :
    ∃ j : ℤ, h = ModularGroup.T ^ j ∨ h = -(ModularGroup.T ^ j) := by
  have had := h.det_coe
  replace had : h 0 0 * h 1 1 = 1 := by
    rw [Matrix.det_fin_two, hc] at had
    lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with
      (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · refine ⟨h 0 1, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, ModularGroup.coe_T_zpow,
        show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · refine ⟨-(h 0 1), Or.inr ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, ModularGroup.coe_T_zpow,
        show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

/-- Every actual Gamma0 matrix fixing cusp one is, up to the central sign,
the integral cusp-one translation through a multiple of N.  The level
divisibility is derived from its *actual* lower-left matrix entry. -/
theorem gamma0_cuspOne_stabilizer_classification (N : ℕ)
    (g : CongruenceSubgroup.Gamma0 N)
    (hg : FixesCuspOne (g : SL(2, ℤ))) :
    ∃ k : ℤ,
      (g : SL(2, ℤ)) =
        cuspOneMatrix * ModularGroup.T ^ ((N : ℤ) * k) * cuspOneMatrix⁻¹ ∨
      (g : SL(2, ℤ)) =
        -(cuspOneMatrix * ModularGroup.T ^ ((N : ℤ) * k) * cuspOneMatrix⁻¹) := by
  let h : SL(2, ℤ) := cuspOneMatrix⁻¹ * (g : SL(2, ℤ)) * cuspOneMatrix
  have hc : h 1 0 = 0 := hg
  obtain ⟨j, hj⟩ := upperTriangular_signed_translation h hc
  have hrecover : (g : SL(2, ℤ)) = cuspOneMatrix * h * cuspOneMatrix⁻¹ := by
    dsimp [h]
    group
  have hcdiv : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
    (gamma0_mem_iff_level_dvd_c N (g : SL(2, ℤ))).mp g.property
  rcases hj with hpos | hneg
  · have heq : (g : SL(2, ℤ)) =
        cuspOneMatrix * ModularGroup.T ^ j * cuspOneMatrix⁻¹ := by
      simpa only [hpos] using hrecover
    have hjdiv : (N : ℤ) ∣ j := by
      simpa [heq, cuspOne_conj_translation_c] using hcdiv
    obtain ⟨k, rfl⟩ := hjdiv
    exact ⟨k, Or.inl heq⟩
  · have heq : (g : SL(2, ℤ)) =
        -(cuspOneMatrix * ModularGroup.T ^ j * cuspOneMatrix⁻¹) := by
      rw [hneg] at hrecover
      simpa only [mul_neg, neg_mul] using hrecover
    have hjdiv : (N : ℤ) ∣ j := by
      simpa [heq, cuspOne_conj_translation_c] using hcdiv
    obtain ⟨k, rfl⟩ := hjdiv
    exact ⟨k, Or.inr heq⟩

/-- The integral translation of length N at cusp one is exactly the
parabolic matrix from the preceding Gamma0 cusp-measure module. -/
theorem cuspDeckSL_eq_cuspOne_conjugate (N : ℕ) :
    cuspDeckSL N =
      cuspOneMatrix * ModularGroup.T ^ (N : ℤ) * cuspOneMatrix⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspDeckSL, cuspDeckMatrix, cuspOneMatrix, SL2_inv_expl,
      ModularGroup.coe_T_zpow, coe_mul, Matrix.mul_fin_two] <;> ring

theorem cuspOne_conjugate_level_period_eq_deck_zpow (N : ℕ) (k : ℤ) :
    cuspOneMatrix * ModularGroup.T ^ ((N : ℤ) * k) * cuspOneMatrix⁻¹ =
      (cuspDeckSL N) ^ k := by
  rw [cuspDeckSL_eq_cuspOne_conjugate N, conj_zpow, zpow_mul]

private theorem integralSL_smul_eq_real (g : SL(2, ℤ))
    (w : UpperHalfPlane) :
    g • w = SpecialLinearGroup.map (algebraMap ℤ ℝ) g • w := by
  rfl

/-- The real matrix translation of one is Mathlib's integral modular T
after scalar extension. -/
private theorem translationSL_one_eq_realT :
    translationSL 1 =
      SpecialLinearGroup.map (algebraMap ℤ ℝ) ModularGroup.T := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translationSL, translation, ModularGroup.coe_T,
      Matrix.SpecialLinearGroup.map_apply_coe]

private theorem translationSL_one_zpow_smul (k : ℤ)
    (w : UpperHalfPlane) :
    (translationSL 1) ^ k • w = (k : ℝ) +ᵥ w := by
  rw [translationSL_one_eq_realT, ← map_zpow]
  change (ModularGroup.T ^ k) • w = (k : ℝ) +ᵥ w
  exact ModularGroup.modular_T_zpow_smul w k

/-- All powers of the actual Gamma0 parabolic act as the corresponding
integer horizontal translations in the `newSL N` chart. -/
theorem cuspDeck_zpow_scaled_action (N : ℕ) (hN : 0 < (N : ℝ))
    (k : ℤ) (w : UpperHalfPlane) :
    (cuspDeckSL N) ^ k • (newSL (N : ℝ) hN • w) =
      newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w) := by
  have hconj : cuspDeckReal N =
      newSL (N : ℝ) hN * translationSL 1 *
        (newSL (N : ℝ) hN)⁻¹ := by
    calc
      cuspDeckReal N =
          (cuspDeckReal N * newSL (N : ℝ) hN) *
            (newSL (N : ℝ) hN)⁻¹ := by group
      _ = newSL (N : ℝ) hN * translationSL 1 *
            (newSL (N : ℝ) hN)⁻¹ := by
          rw [cuspDeckReal_mul_newSL N hN]
  have hpow : (cuspDeckReal N) ^ k * newSL (N : ℝ) hN =
      newSL (N : ℝ) hN * (translationSL 1) ^ k := by
    rw [hconj, conj_zpow]
    group
  calc
    (cuspDeckSL N) ^ k • (newSL (N : ℝ) hN • w) =
        SpecialLinearGroup.map (algebraMap ℤ ℝ) ((cuspDeckSL N) ^ k) •
          (newSL (N : ℝ) hN • w) :=
      integralSL_smul_eq_real _ _
    _ = (cuspDeckReal N) ^ k • (newSL (N : ℝ) hN • w) := by
      simp [cuspDeckReal]
    _ = ((cuspDeckReal N) ^ k * newSL (N : ℝ) hN) • w := by
      rw [mul_smul]
    _ = newSL (N : ℝ) hN • ((translationSL 1) ^ k • w) := by
      rw [hpow, mul_smul]
    _ = newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w) := by
      rw [translationSL_one_zpow_smul]

/-- The full actual Gamma0 stabilizer of cusp one has no fractional
periods in this normalized chart.  The sign from `SL2` disappears in its
upper-half-plane action. -/
theorem gamma0_cuspOne_stabilizer_scaled_action (N : ℕ)
    (hN : 0 < (N : ℝ)) (g : CongruenceSubgroup.Gamma0 N)
    (hg : FixesCuspOne (g : SL(2, ℤ))) :
    ∃ k : ℤ, ∀ w : UpperHalfPlane,
      (g : SL(2, ℤ)) • (newSL (N : ℝ) hN • w) =
        newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w) := by
  obtain ⟨k, hpos | hneg⟩ :=
    gamma0_cuspOne_stabilizer_classification N g hg
  · refine ⟨k, ?_⟩
    intro w
    rw [hpos, cuspOne_conjugate_level_period_eq_deck_zpow]
    exact cuspDeck_zpow_scaled_action N hN k w
  · refine ⟨k, ?_⟩
    intro w
    rw [hneg, cuspOne_conjugate_level_period_eq_deck_zpow,
      UpperHalfPlane.SL_neg_smul]
    exact cuspDeck_zpow_scaled_action N hN k w

private theorem re_real_vadd (t : ℝ) (w : UpperHalfPlane) :
    (t +ᵥ w).re = t + w.re := by
  have h : (((t +ᵥ w : UpperHalfPlane) : ℂ)) =
      (t : ℂ) + (w : ℂ) := by
    simp [UpperHalfPlane.coe_vadd]
  have hr := congrArg Complex.re h
  simpa using hr

/-- Any real translation effected by an actual Gamma0 cusp-one stabilizer
in the normalized chart must be an integer.  This rules out fractional
periods, rather than merely exhibiting one period. -/
theorem gamma0_cuspOne_no_fractional_period (N : ℕ)
    (hN : 0 < (N : ℝ)) (g : CongruenceSubgroup.Gamma0 N)
    (hg : FixesCuspOne (g : SL(2, ℤ))) (t : ℝ)
    (ht : ∀ w : UpperHalfPlane,
      (g : SL(2, ℤ)) • (newSL (N : ℝ) hN • w) =
        newSL (N : ℝ) hN • (t +ᵥ w)) :
    ∃ k : ℤ, t = (k : ℝ) := by
  obtain ⟨k, hk⟩ := gamma0_cuspOne_stabilizer_scaled_action N hN g hg
  let w : UpperHalfPlane := ⟨⟨0, 1⟩, by norm_num⟩
  have hscaled : newSL (N : ℝ) hN • (t +ᵥ w) =
      newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w) := by
    exact (ht w).symm.trans (hk w)
  have hcoord : t +ᵥ w = (k : ℝ) +ᵥ w := by
    have h := congrArg
      (fun u : UpperHalfPlane => (newSL (N : ℝ) hN)⁻¹ • u) hscaled
    simpa only [← smul_smul, inv_mul_cancel, one_smul] using h
  have hre := congrArg UpperHalfPlane.re hcoord
  rw [re_real_vadd, re_real_vadd] at hre
  exact ⟨k, add_right_cancel hre⟩

/-- Conversely the period one is realized by the displayed actual Gamma0
matrix, establishing minimal positive chart width one. -/
theorem gamma0_cuspOne_width_exactly_one (N : ℕ)
    (hN : 0 < (N : ℝ)) :
    FixesCuspOne (cuspDeck N : SL(2, ℤ)) ∧
      ∀ w : UpperHalfPlane,
        (cuspDeck N : SL(2, ℤ)) • (newSL (N : ℝ) hN • w) =
          newSL (N : ℝ) hN • ((1 : ℝ) +ᵥ w) := by
  constructor
  · rw [fixesCuspOne_iff_entries]
    simp [cuspDeck, cuspDeckSL, cuspDeckMatrix]
  · exact cuspDeck_smul_newSL_vadd N hN

/-- A function invariant under Mathlib's actual Gamma0 action becomes
integer-periodic in the scaled cusp chart. -/
theorem invariant_function_integer_period (N : ℕ)
    (hN : 0 < (N : ℝ)) (F : UpperHalfPlane → ℂ)
    (hF : ∀ g : CongruenceSubgroup.Gamma0 N,
      ∀ w : UpperHalfPlane, F ((g : SL(2, ℤ)) • w) = F w)
    (k : ℤ) (w : UpperHalfPlane) :
    F (newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w)) =
      F (newSL (N : ℝ) hN • w) := by
  have hinv := hF ((cuspDeck N) ^ k) (newSL (N : ℝ) hN • w)
  have hcoerce : (((cuspDeck N) ^ k : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (cuspDeckSL N) ^ k := rfl
  rw [hcoerce] at hinv
  change F ((cuspDeckSL N) ^ k • (newSL (N : ℝ) hN • w)) =
    F (newSL (N : ℝ) hN • w) at hinv
  rwa [cuspDeck_zpow_scaled_action N hN k w] at hinv

/-- Horizontal integer representatives give the same nonnegative
hyperbolic energy integral on the finite half-open cusp strip.  This is an
identity of integrands for genuine Gamma0-invariant functions, independent
of any unproved full-orbit quotient measure. -/
theorem invariant_function_horizontal_energy (N : ℕ)
    (hN : 0 < (N : ℝ)) (F : UpperHalfPlane → ℂ)
    (hF : ∀ g : CongruenceSubgroup.Gamma0 N,
      ∀ w : UpperHalfPlane, F ((g : SL(2, ℤ)) • w) = F w)
    (k : ℤ) :
    (∫⁻ w in highStripIco,
        ENNReal.ofReal (‖F (newSL (N : ℝ) hN • ((k : ℝ) +ᵥ w))‖ ^ 2)
        ∂(volume : Measure UpperHalfPlane)) =
      ∫⁻ w in highStripIco,
        ENNReal.ofReal (‖F (newSL (N : ℝ) hN • w)‖ ^ 2)
        ∂(volume : Measure UpperHalfPlane) := by
  apply lintegral_congr
  intro w
  rw [invariant_function_integer_period N hN F hF k w]

end
end ImbalancedChen.Part3.Gamma0CuspMinimalWidth20261024zz
