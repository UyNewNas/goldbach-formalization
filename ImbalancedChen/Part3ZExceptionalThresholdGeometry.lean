import ImbalancedChen.Part3ActualPoissonNormalizedFScalar
import ImbalancedChen.Part3ZExceptionalParameter
import Mathlib.Tactic

/-!
# P3 actual spectral geometry and exceptional threshold

Source-written, uncompiled. The sibling parameter module must be staged on
the same Lean source path. The real 4*pi normalization is retained throughout.
-/

namespace ImbalancedChen.P3ZExceptionalThresholdGeometry

noncomputable section

def threshold (V Z : ℝ) : ℝ := max V (Z ^ 2 / V)

def comparisonThreshold (V Z : ℝ) : ℝ := (V + Z) ^ 2 / V

def weight (X Z L : ℝ) : ℝ := (1 + X / Real.sqrt (1 + Z / L)) ^ 2

def spectralWeight (A V U Z C L : ℝ) : ℝ :=
  weight (1 / ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.spectralScale A V U Z C) Z L

def ratioBound (A nu L V Z C : ℝ) : ℝ :=
  2 / threshold V Z +
    8 * (C ^ 2 * Z / (16 * Real.pi ^ 2 * A * nu * (L + Z) * (V + Z) ^ 2))

theorem threshold_pos {V Z : ℝ} (hV : 0 < V) : 0 < threshold V Z := by
  exact lt_of_lt_of_le hV (le_max_left _ _)

theorem comparisonThreshold_pos {V Z : ℝ} (hV : 0 < V) (hZ : 0 < Z) :
    0 < comparisonThreshold V Z := by
  unfold comparisonThreshold
  positivity

theorem threshold_le_comparison {V Z : ℝ} (hV : 0 < V) (hZ : 0 < Z) :
    threshold V Z ≤ comparisonThreshold V Z := by
  unfold threshold comparisonThreshold
  apply max_le
  · apply (le_div_iff₀ hV).mpr
    have hcross : 0 ≤ V * Z := mul_nonneg hV.le hZ.le
    nlinarith only [hcross, sq_nonneg Z]
  · apply (div_le_iff₀ hV).mpr
    rw [div_mul_cancel₀ _ hV.ne']
    have hcross : 0 ≤ V * Z := mul_nonneg hV.le hZ.le
    nlinarith only [hcross, sq_nonneg V]

theorem comparison_le_four_threshold {V Z : ℝ} (hV : 0 < V) (hZ : 0 < Z) :
    comparisonThreshold V Z ≤ 4 * threshold V Z := by
  have hVM : V ≤ threshold V Z := le_max_left _ _
  have hZM : Z ^ 2 / V ≤ threshold V Z := le_max_right _ _
  have hV2 : V ^ 2 ≤ threshold V Z * V := by
    have h := mul_le_mul_of_nonneg_right hVM hV.le
    nlinarith only [h]
  have hZ2 : Z ^ 2 ≤ threshold V Z * V := (div_le_iff₀ hV).mp hZM
  unfold comparisonThreshold
  apply (div_le_iff₀ hV).mpr
  nlinarith only [hV2, hZ2, sq_nonneg (V - Z)]

theorem actual_spectralScale_pos {A V U Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hU : 0 < U) (hZ : 0 < Z) (hC : 0 < C) :
    0 < ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.spectralScale A V U Z C := by
  unfold ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.spectralScale
  positivity

/-- Exact positive-scale identity with U=nu*L. The 16*pi^2 in the actual
spectralScale square is retained. -/
theorem inverse_scale_ratio {A V nu L Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hnu : 0 < nu) (hL : 0 < L)
    (hZ : 0 < Z) (hC : 0 < C) :
    (1 / ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.spectralScale
        A V (nu * L) Z C) ^ 2 / (1 + Z / L) / comparisonThreshold V Z =
      C ^ 2 * Z / (16 * Real.pi ^ 2 * A * nu * (L + Z) * (V + Z) ^ 2) := by
  have hnormalizer : 1 + Z / L ≠ 0 := (show 0 < 1 + Z / L by positivity).ne'
  have hLZ : L + Z ≠ 0 := (add_pos hL hZ).ne'
  have hVZ : V + Z ≠ 0 := (add_pos hV hZ).ne'
  rw [div_pow, one_pow,
    ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.spectralScale_sq
      hA hV (mul_pos hnu hL) hZ hC]
  unfold comparisonThreshold
  field_simp [hA.ne', hV.ne', hnu.ne', hL.ne', hZ.ne', hC.ne',
    Real.pi_ne_zero, hnormalizer, hLZ, hVZ] <;> ring

/-- The same identity in the literal dictionary L=U/nu. -/
theorem inverse_scale_ratio_divisor {A V U nu Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hU : 0 < U) (hnu : 0 < nu)
    (hZ : 0 < Z) (hC : 0 < C) :
    (1 / ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.spectralScale A V U Z C) ^ 2 /
        (1 + Z / (U / nu)) / comparisonThreshold V Z =
      C ^ 2 * Z / (16 * Real.pi ^ 2 * A * nu * (U / nu + Z) * (V + Z) ^ 2) := by
  have hcancel : nu * (U / nu) = U := by field_simp [hnu.ne'] <;> ring
  simpa only [hcancel] using inverse_scale_ratio hA hV hnu (div_pos hU hnu) hZ hC

theorem weight_pos {X Z L : ℝ} (hX : 0 ≤ X) (hZ : 0 < Z) (hL : 0 < L) :
    0 < weight X Z L := by
  have hroot : 0 < Real.sqrt (1 + Z / L) := Real.sqrt_pos.mpr (by positivity)
  unfold weight
  exact sq_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hX hroot.le))

/-- The only estimate on the enlarged weight is (1+q)^2<=2+2*q^2.
Threshold comparability then supplies the factor 8 in the second term. -/
theorem weight_ratio_le {X V Z L : ℝ}
    (hV : 0 < V) (hZ : 0 < Z) (hL : 0 < L) :
    weight X Z L / threshold V Z ≤
      2 / threshold V Z + 8 * (X ^ 2 / (1 + Z / L) / comparisonThreshold V Z) := by
  have hT : 0 < threshold V Z := threshold_pos hV
  have hQ : 0 < comparisonThreshold V Z := comparisonThreshold_pos hV hZ
  have hK : 0 < 1 + Z / L := by positivity
  have hsqrt : Real.sqrt (1 + Z / L) ^ 2 = 1 + Z / L := Real.sq_sqrt hK.le
  have hweight : weight X Z L ≤ 2 + 2 * (X ^ 2 / (1 + Z / L)) := by
    have hsq := sq_nonneg (1 - X / Real.sqrt (1 + Z / L))
    have hquot : (X / Real.sqrt (1 + Z / L)) ^ 2 = X ^ 2 / (1 + Z / L) := by
      rw [div_pow, hsqrt]
    unfold weight
    nlinarith only [hsq, hquot]
  have hcomp := comparison_le_four_threshold hV hZ
  have hB : 0 ≤ X ^ 2 / (1 + Z / L) := div_nonneg (sq_nonneg X) hK.le
  have hterm : (2 * (X ^ 2 / (1 + Z / L))) / threshold V Z ≤
      (8 * (X ^ 2 / (1 + Z / L))) / comparisonThreshold V Z := by
    apply (div_le_div_iff₀ hT hQ).mpr
    have h := mul_le_mul_of_nonneg_left hcomp (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hB)
    nlinarith only [h]
  calc
    weight X Z L / threshold V Z ≤ (2 + 2 * (X ^ 2 / (1 + Z / L))) / threshold V Z := by
      exact (div_le_div_iff₀ hT hT).mpr
        (mul_le_mul_of_nonneg_right hweight hT.le)
    _ = 2 / threshold V Z + (2 * (X ^ 2 / (1 + Z / L))) / threshold V Z := by ring
    _ ≤ 2 / threshold V Z + (8 * (X ^ 2 / (1 + Z / L))) / comparisonThreshold V Z :=
      add_le_add_left hterm _
    _ = 2 / threshold V Z + 8 * (X ^ 2 / (1 + Z / L) / comparisonThreshold V Z) := by ring

/-- Explicit actual-geometry bound. There is no suppressed pi constant. -/
theorem spectral_weight_ratio_le {A V nu L Z C : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hnu : 0 < nu) (hL : 0 < L)
    (hZ : 0 < Z) (hC : 0 < C) :
    spectralWeight A V (nu * L) Z C L / threshold V Z ≤ ratioBound A nu L V Z C := by
  have h := weight_ratio_le
    (X := 1 / ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.spectralScale
      A V (nu * L) Z C) hV hZ hL
  rw [inverse_scale_ratio hA hV hnu hL hZ hC] at h
  exact h

/-- Connection to the separately proved tau threshold transport. The
eigenvalue lower bound remains an explicit hypothesis. -/
theorem spectral_tau_weight_le {A V nu L Z C lambda : ℝ}
    (hA : 0 < A) (hV : 0 < V) (hnu : 0 < nu) (hL : 0 < L)
    (hZ : 0 < Z) (hC : 0 < C) (hlambda : (975 : ℝ) / 4096 ≤ lambda) :
    spectralWeight A V (nu * L) Z C L ^ P3ZExceptionalParameter.tau lambda ≤
      max 1 (ratioBound A nu L V Z C ^ ((7 : ℝ) / 32)) *
        threshold V Z ^ P3ZExceptionalParameter.tau lambda := by
  have hscale := actual_spectralScale_pos hA hV (mul_pos hnu hL) hZ hC
  have hW : 0 < spectralWeight A V (nu * L) Z C L :=
    weight_pos (div_nonneg (by norm_num) hscale.le) hZ hL
  have hT : 0 < threshold V Z := threshold_pos hV
  have hratio := spectral_weight_ratio_le hA hV hnu hL hZ hC
  have hmono :
      max 1 ((spectralWeight A V (nu * L) Z C L / threshold V Z) ^ ((7 : ℝ) / 32)) ≤
        max 1 (ratioBound A nu L V Z C ^ ((7 : ℝ) / 32)) := by
    apply max_le_max le_rfl
    exact Real.rpow_le_rpow (div_nonneg hW.le hT.le) hratio (by norm_num)
  calc
    _ ≤ max 1 ((spectralWeight A V (nu * L) Z C L / threshold V Z) ^ ((7 : ℝ) / 32)) *
        threshold V Z ^ P3ZExceptionalParameter.tau lambda :=
      P3ZExceptionalParameter.tau_rpow_le_threshold hW hT hlambda
    _ ≤ max 1 (ratioBound A nu L V Z C ^ ((7 : ℝ) / 32)) *
        threshold V Z ^ P3ZExceptionalParameter.tau lambda :=
      mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hT.le _)

end

end ImbalancedChen.P3ZExceptionalThresholdGeometry
