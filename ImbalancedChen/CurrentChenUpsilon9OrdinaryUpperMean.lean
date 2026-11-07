import ImbalancedChen.CurrentChenUpsilon9HarmonicMean
import ImbalancedChen.CurrentChenUpsilon9SwitchedUpperDensity

/-!
# The actual ordinary ninth upper mean

The finite switched count, the leading-one true-li transport, the genuine
prime-box harmonic limit and the ordinary factor eight are proved inputs.
Their errors are paid after the Pan exponent has been fixed.  Positivity
is proved for the actual li mass and the actual limiting integral before
any upper estimates are multiplied.  The signed Rosser density does not
need a sign hypothesis.  The resulting integral and factor eight are kept
literal; no adopted manuscript constant is asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

theorem eventually_currentChenUpsilon9LiMainMass_nonneg :
    ∀ᶠ N : ℕ in atTop, 0 ≤ currentChenUpsilon9LiMainMass N := by
  filter_upwards [eventually_currentChenUpsilon9_li_arguments_two] with N hN
  unfold currentChenUpsilon9LiMainMass
  apply Finset.sum_nonneg
  intro a ha
  exact MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
    (2 / Real.log 2) (by positivity) (hN a ha)

theorem currentChenUpsilon9HarmonicIntegral_nonneg :
    0 ≤ currentChenUpsilon9HarmonicIntegral := by
  apply ge_of_tendsto tendsto_currentChenUpsilon9LogTotientMass
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact currentChenUpsilon9LogTotientMass_nonneg hN

private theorem currentChenUpsilon9_ordinary_error_budget
    {J δ ε : ℝ} (hJ : 0 ≤ J) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hcost : δ * (20 + 10 * J) ≤ ε) :
    (1 + δ) * (J + δ) * (8 + δ) + δ ≤ 8 * J + ε := by
  have hsq : δ * δ ≤ δ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1 hδ
  have hinner : (1 + δ) * (J + δ) ≤ J + δ * (J + 2) := by
    nlinarith only [hsq]
  have houter := mul_le_mul_of_nonneg_right hinner
    (show 0 ≤ 8 + δ by linarith only [hδ])
  have hsqcost := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ J + 2 by linarith only [hJ])
  nlinarith only [houter, hsqcost, hcost, hδ]

/-- The actual ninth count has the ordinary switched upper mean with its
genuine two-dimensional harmonic integral and its proved factor eight. -/
theorem eventually_currentChenUpsilon9_le_ordinary_upper_mean
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (8 * currentChenUpsilon9HarmonicIntegral + ε) * singularNormalization N := by
  obtain ⟨B, _hB, hpaid⟩ := exists_currentChenUpsilon9_le_switched_density_main
  let J : ℝ := currentChenUpsilon9HarmonicIntegral
  have hJ : 0 ≤ J := currentChenUpsilon9HarmonicIntegral_nonneg
  let δ : ℝ := min 1 (ε / (20 + 10 * J))
  have hden : 0 < 20 + 10 * J := by linarith only [hJ]
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hcost : δ * (20 + 10 * J) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have htotal := currentChenUpsilon9_ordinary_error_budget hJ hδ.le hδ1 hcost
  have hnear : ∀ᶠ N : ℕ in atTop, currentChenUpsilon9LogTotientMass N < J + δ :=
    tendsto_currentChenUpsilon9LogTotientMass.eventually
      (Iio_mem_nhds (show currentChenUpsilon9HarmonicIntegral < J + δ by
        dsimp only [J]
        linarith only [hδ]))
  filter_upwards [hpaid δ hδ, eventually_currentChenUpsilon9LiMainMass_nonneg,
    eventually_currentChenUpsilon9_liMainMass_le_logTotientMass δ hδ,
    eventually_currentChenUpsilon9_switched_density_le_eight B δ hδ,
    hnear, eventually_ge_atTop (2 : ℕ)]
    with N hfinite hli0 hli hdensity hnearN hN
  intro hEven
  let D : ℝ := currentChenUpsilon9SwitchedUpperDensity B N
    (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) ((N : ℝ) ^ (1 / 5 : ℝ))
  let A : ℝ := currentChenUpsilon9LiMainMass N * Real.log (N : ℝ) / (N : ℝ)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog := Real.log_pos hN1
  have hSS := singularSeries_pos N
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg hSS.le hNp.le) (sq_nonneg _)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hli0 hlog.le) hNp.le
  have hdensityN : D * Real.log (N : ℝ) / singularSeries N ≤ 8 + δ := hdensity hEven
  have hprofile : A * (D * Real.log (N : ℝ) / singularSeries N) ≤
      (1 + δ) * (J + δ) * (8 + δ) := by
    calc
      _ ≤ A * (8 + δ) := mul_le_mul_of_nonneg_left hdensityN hA
      _ ≤ ((1 + δ) * currentChenUpsilon9LogTotientMass N) * (8 + δ) :=
        mul_le_mul_of_nonneg_right hli (by linarith only [hδ])
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnearN.le (by linarith only [hδ]))
        (by linarith only [hδ])
  have hidentity : currentChenUpsilon9LiMainMass N * D =
      (A * (D * Real.log (N : ℝ) / singularSeries N)) * singularNormalization N := by
    dsimp only [A]
    unfold singularNormalization
    field_simp [hSS.ne', hlog.ne', hNp.ne']
  have hmain : currentChenUpsilon9LiMainMass N * D ≤
      ((1 + δ) * (J + δ) * (8 + δ)) * singularNormalization N := by
    rw [hidentity]
    exact mul_le_mul_of_nonneg_right hprofile hH
  have hfiniteN : currentChenUpsilon9 N ≤
      currentChenUpsilon9LiMainMass N * D + δ * singularNormalization N :=
    hfinite (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)))
  have hbudget := mul_le_mul_of_nonneg_right htotal hH
  change currentChenUpsilon9 N ≤ (8 * J + ε) * singularNormalization N
  nlinarith only [hfiniteN, hmain, hbudget]

end

end ImbalancedChen
