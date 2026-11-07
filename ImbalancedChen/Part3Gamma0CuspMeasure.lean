import ImbalancedChen.Part3ActualCuspScalingSourceOnly
import ImbalancedChen.Part3ModularFundamentalFiniteMeasure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / no acceptance credit, 2026-10-24.

This module connects the *actual* level-N congruence subgroup to a scaled
period-one cusp chart.  The integer matrix below is in Gamma0 N and acts in
the `newSL` chart by the literal translation matrix `translationSL 1`.
The high width-one strip in that chart has finite invariant hyperbolic
measure, because its unscaled copy lies in Mathlib's modular domain.

This is a parabolic cusp chart and a finite-measure strip.  No assertion of
injectivity into the full Gamma0 orbit quotient, a quotient measure formula,
or an automorphic spectral decomposition is made here.
-/

namespace ImbalancedChen.Part3.Gamma0CuspMeasure20261024zz

noncomputable section

open Set MeasureTheory
open scoped MatrixGroups UpperHalfPlane Pointwise
open P3ActualCuspScalingSourceOnly
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z

/-- The genuine integral parabolic at the cusp represented by `newSL N`.
Its lower-left entry is `-N`, exactly the Gamma0 congruence condition. -/
def cuspDeckMatrix (N : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1 - (N : ℤ), (N : ℤ); -(N : ℤ), 1 + (N : ℤ)]

theorem cuspDeckMatrix_det (N : ℕ) : Matrix.det (cuspDeckMatrix N) = 1 := by
  simp [cuspDeckMatrix, Matrix.det_fin_two_of] <;> ring

def cuspDeckSL (N : ℕ) : SL(2, ℤ) :=
  ⟨cuspDeckMatrix N, cuspDeckMatrix_det N⟩

theorem cuspDeckSL_mem_gamma0 (N : ℕ) :
    cuspDeckSL N ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  change ((-(N : ℤ) : ℤ) : ZMod N) = 0
  simp

/-- A concrete element of Mathlib's actual Gamma0 subgroup. -/
def cuspDeck (N : ℕ) : CongruenceSubgroup.Gamma0 N :=
  ⟨cuspDeckSL N, cuspDeckSL_mem_gamma0 N⟩

def cuspDeckReal (N : ℕ) : SL(2, ℝ) :=
  SpecialLinearGroup.map (algebraMap ℤ ℝ) (cuspDeckSL N)

/-- Exact conjugacy: `gamma_N * sigma_N = sigma_N * T_1` in SL(2,R).
Thus translation by one is a period in the `newSL N` coordinate. -/
theorem cuspDeckReal_mul_newSL (N : ℕ) (hN : 0 < (N : ℝ)) :
    cuspDeckReal N * newSL (N : ℝ) hN =
      newSL (N : ℝ) hN * translationSL 1 := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hN)
  have hsq : (N : ℝ) = Real.sqrt (N : ℝ) ^ 2 :=
    (Real.sq_sqrt hN.le).symm
  have hmul : (N : ℝ) * (1 / Real.sqrt (N : ℝ)) =
      Real.sqrt (N : ℝ) := by
    rw [hsq]
    field_simp [hs] <;> ring
  apply Subtype.ext
  change
    !![1 - (N : ℝ), (N : ℝ); -(N : ℝ), 1 + (N : ℝ)] *
      !![Real.sqrt (N : ℝ), -(1 / Real.sqrt (N : ℝ));
         Real.sqrt (N : ℝ), 0] =
    !![Real.sqrt (N : ℝ), -(1 / Real.sqrt (N : ℝ));
       Real.sqrt (N : ℝ), 0] * !![1, 1; 0, 1]
  simp only [Matrix.mul_fin_two]
  simp [hmul] <;> ring

/-- The integral and real actions agree after the canonical scalar map. -/
private theorem cuspDeckSL_smul_eq_real (N : ℕ) (w : UpperHalfPlane) :
    cuspDeckSL N • w = cuspDeckReal N • w := by
  rfl

/-- The actual Gamma0 element identifies consecutive translates of the
scaled cusp chart.  This uses the real scaling matrix, not an abstract
quotient-action parameter. -/
theorem cuspDeck_smul_newSL (N : ℕ) (hN : 0 < (N : ℝ))
    (w : UpperHalfPlane) :
    (cuspDeck N : SL(2, ℤ)) • (newSL (N : ℝ) hN • w) =
      newSL (N : ℝ) hN • (translationSL 1 • w) := by
  change cuspDeckSL N • (newSL (N : ℝ) hN • w) = _
  rw [cuspDeckSL_smul_eq_real]
  rw [← mul_smul, cuspDeckReal_mul_newSL N hN, mul_smul]

/-- The right-hand matrix in the conjugacy is literally horizontal
translation by one on the upper half-plane. -/
theorem translationSL_one_smul (w : UpperHalfPlane) :
    translationSL 1 • w = (1 : ℝ) +ᵥ w := by
  ext
  simp [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_vadd,
    translationSL, translation]

theorem cuspDeck_smul_newSL_vadd (N : ℕ) (hN : 0 < (N : ℝ))
    (w : UpperHalfPlane) :
    (cuspDeck N : SL(2, ℤ)) • (newSL (N : ℝ) hN • w) =
      newSL (N : ℝ) hN • ((1 : ℝ) +ᵥ w) := by
  rw [cuspDeck_smul_newSL N hN w, translationSL_one_smul]

/-- A width-one high strip.  Its closed vertical edges may be identified
by the parabolic; their overlap is harmless for the finite-volume claim. -/
def highStrip : Set UpperHalfPlane :=
  {w | |w.re| ≤ (1 : ℝ) / 2 ∧ 1 ≤ w.im}

theorem highStrip_subset_modularFD : highStrip ⊆ modularFD := by
  intro w hw
  change 1 ≤ Complex.normSq (w : ℂ) ∧ |w.re| ≤ (1 : ℝ) / 2
  refine ⟨?_, hw.1⟩
  rw [Complex.normSq_apply]
  have hy : 1 ≤ w.im := hw.2
  nlinarith [sq_nonneg w.re, mul_nonneg (sub_nonneg.mpr hy) (by linarith : 0 ≤ w.im + 1)]

theorem highStrip_finite :
    (volume : Measure UpperHalfPlane) highStrip < ∞ :=
  lt_of_le_of_lt (measure_mono highStrip_subset_modularFD) modularFD_finite

/-- Half-open representatives remove the duplicate vertical edge. -/
def highStripIco : Set UpperHalfPlane :=
  {w | w.re ∈ Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2) ∧ 1 ≤ w.im}

theorem highStripIco_subset_highStrip : highStripIco ⊆ highStrip := by
  intro w hw
  exact ⟨abs_le.mpr ⟨hw.1.1, hw.1.2.le⟩, hw.2⟩

theorem highStripIco_finite :
    (volume : Measure UpperHalfPlane) highStripIco < ∞ :=
  lt_of_le_of_lt (measure_mono highStripIco_subset_highStrip) highStrip_finite

/-- The horizontal interval is an exact fundamental interval for integer
translation: every real coordinate has one and only one representative. -/
theorem highStripIco_unique_horizontal_period (w : UpperHalfPlane) :
    ∃! n : ℤ,
      w.re - (n : ℝ) ∈ Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
  simpa [zsmul_eq_mul, show -(1 : ℝ) / 2 + 1 = (1 : ℝ) / 2 by ring] using
    (existsUnique_sub_zsmul_mem_Ico (show (0 : ℝ) < 1 by norm_num)
      w.re (-(1 : ℝ) / 2))

/-- The actual image of the period-one strip under the cusp scaling matrix. -/
def scaledHighStrip (N : ℕ) (hN : 0 < (N : ℝ)) : Set UpperHalfPlane :=
  newSL (N : ℝ) hN • highStripIco

/-- Hyperbolic volume is invariant under the actual scaling matrix. -/
theorem scaledHighStrip_measure (N : ℕ) (hN : 0 < (N : ℝ)) :
    (volume : Measure UpperHalfPlane) (scaledHighStrip N hN) =
      (volume : Measure UpperHalfPlane) highStripIco := by
  change (volume : Measure UpperHalfPlane)
    ((SpecialLinearGroup.mapGL ℝ (newSL (N : ℝ) hN)) • highStripIco) =
      (volume : Measure UpperHalfPlane) highStripIco
  exact measure_smul (volume : Measure UpperHalfPlane)
    (SpecialLinearGroup.mapGL ℝ (newSL (N : ℝ) hN)) highStripIco

theorem scaledHighStrip_finite (N : ℕ) (hN : 0 < (N : ℝ)) :
    (volume : Measure UpperHalfPlane) (scaledHighStrip N hN) < ∞ := by
  rw [scaledHighStrip_measure]
  exact highStripIco_finite

/-- Every point of this genuine scaled finite-volume strip advances by one
chart period under the displayed element of Gamma0 N. -/
theorem cuspDeck_period_on_scaledHighStrip (N : ℕ)
    (hN : 0 < (N : ℝ)) {u : UpperHalfPlane}
    (hu : u ∈ scaledHighStrip N hN) :
    ∃ w ∈ highStripIco,
      u = newSL (N : ℝ) hN • w ∧
      (cuspDeck N : SL(2, ℤ)) • u =
        newSL (N : ℝ) hN • (translationSL 1 • w) := by
  obtain ⟨w, hw, rfl⟩ := hu
  exact ⟨w, hw, rfl, cuspDeck_smul_newSL N hN w⟩

end
end ImbalancedChen.Part3.Gamma0CuspMeasure20261024zz
