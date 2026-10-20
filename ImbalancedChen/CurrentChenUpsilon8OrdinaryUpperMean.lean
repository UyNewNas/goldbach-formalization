import ImbalancedChen.CurrentChenUpsilon8FiniteMean
import ImbalancedChen.CurrentChenUpsilon8HarmonicMean
import ImbalancedChen.CurrentChenUpsilon9SwitchedUpperDensity

/-!
# The actual ordinary eighth upper mean

The literal eighth finite count, its genuine leading-one li transport,
its prime-box harmonic limit and the same switched density with factor
eight are proved inputs. The li estimate is normalized explicitly before
it is combined with the density. Positivity is proved for the actual li
mass and its limiting harmonic integral; no sign assumption is imposed on
the signed Rosser density. The Pan exponent is fixed before the errors,
and the finite all-cap estimate is specialized only after its threshold.

The conclusion retains the genuine eighth integral and the ordinary
factor eight. It does not assert the current enhanced switching constant
or an adopted-mask Chen lower bound.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

theorem eventually_currentChenUpsilon8LiMainMass_nonneg :
    ∀ᶠ N : ℕ in atTop, 0 ≤ currentChenUpsilon8LiMainMass N := by
  filter_upwards [eventually_currentChenUpsilon8_li_arguments_two] with N hN
  unfold currentChenUpsilon8LiMainMass
  apply Finset.sum_nonneg
  intro a ha
  exact MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
    (2 / Real.log 2) (by positivity) (hN a ha)

theorem currentChenUpsilon8HarmonicIntegral_nonneg :
    0 ≤ currentChenUpsilon8HarmonicIntegral := by
  apply ge_of_tendsto tendsto_currentChenUpsilon8LogTotientMass
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact currentChenUpsilon8LogTotientMass_nonneg hN

private theorem currentChenUpsilon8_ordinary_error_budget
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

/-- The actual eighth count has the ordinary switched upper mean with
its original two-dimensional integral and its proved density factor eight. -/
theorem eventually_currentChenUpsilon8_le_ordinary_upper_mean
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon8 N ≤
        (8 * currentChenUpsilon8HarmonicIntegral + ε) * singularNormalization N := by
  obtain ⟨B, _hB, hpaid⟩ := exists_currentChenUpsilon8_le_switched_density_main
  let J : ℝ := currentChenUpsilon8HarmonicIntegral
  have hJ : 0 ≤ J := currentChenUpsilon8HarmonicIntegral_nonneg
  let δ : ℝ := min 1 (ε / (20 + 10 * J))
  have hden : 0 < 20 + 10 * J := by linarith only [hJ]
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hcost : δ * (20 + 10 * J) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have htotal := currentChenUpsilon8_ordinary_error_budget hJ hδ.le hδ1 hcost
  have hnear : ∀ᶠ N : ℕ in atTop, currentChenUpsilon8LogTotientMass N < J + δ :=
    tendsto_currentChenUpsilon8LogTotientMass.eventually
      (Iio_mem_nhds (show currentChenUpsilon8HarmonicIntegral < J + δ by
        dsimp only [J]
        linarith only [hδ]))
  filter_upwards [hpaid δ hδ, eventually_currentChenUpsilon8LiMainMass_nonneg,
    eventually_currentChenUpsilon8_liMainMass_le_logTotientMass δ hδ,
    eventually_currentChenUpsilon9_switched_density_le_eight B δ hδ,
    hnear, eventually_ge_atTop (2 : ℕ)]
    with N hfinite hli0 hli hdensity hnearN hN
  intro hEven
  let D : ℝ := currentChenUpsilon9SwitchedUpperDensity B N
    (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) ((N : ℝ) ^ (1 / 5 : ℝ))
  let A : ℝ := currentChenUpsilon8LiMainMass N * Real.log (N : ℝ) / (N : ℝ)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog := Real.log_pos hN1
  have hSS := singularSeries_pos N
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg hSS.le hNp.le) (sq_nonneg _)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hli0 hlog.le) hNp.le
  have hliNormalized : A ≤ (1 + δ) * currentChenUpsilon8LogTotientMass N := by
    dsimp only [A]
    apply (div_le_iff₀ hNp).mpr
    calc
      _ ≤ ((1 + δ) * ((N : ℝ) / Real.log (N : ℝ)) *
          currentChenUpsilon8LogTotientMass N) * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_right hli hlog.le
      _ = ((1 + δ) * currentChenUpsilon8LogTotientMass N) * (N : ℝ) := by
        calc
          _ = ((1 + δ) * currentChenUpsilon8LogTotientMass N) *
              (((N : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ)) := by ring
          _ = _ := by rw [div_mul_cancel₀ _ hlog.ne']
  have hdensityN : D * Real.log (N : ℝ) / singularSeries N ≤ 8 + δ := hdensity hEven
  have hprofile : A * (D * Real.log (N : ℝ) / singularSeries N) ≤
      (1 + δ) * (J + δ) * (8 + δ) := by
    calc
      _ ≤ A * (8 + δ) := mul_le_mul_of_nonneg_left hdensityN hA
      _ ≤ ((1 + δ) * currentChenUpsilon8LogTotientMass N) * (8 + δ) :=
        mul_le_mul_of_nonneg_right hliNormalized (by linarith only [hδ])
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnearN.le (by linarith only [hδ]))
        (by linarith only [hδ])
  have hidentity : currentChenUpsilon8LiMainMass N * D =
      (A * (D * Real.log (N : ℝ) / singularSeries N)) * singularNormalization N := by
    dsimp only [A]
    unfold singularNormalization
    field_simp [hSS.ne', hlog.ne', hNp.ne']
  have hmain : currentChenUpsilon8LiMainMass N * D ≤
      ((1 + δ) * (J + δ) * (8 + δ)) * singularNormalization N := by
    rw [hidentity]
    exact mul_le_mul_of_nonneg_right hprofile hH
  have hfiniteN : currentChenUpsilon8 N ≤
      currentChenUpsilon8LiMainMass N * D + δ * singularNormalization N :=
    hfinite (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)))
  have hbudget := mul_le_mul_of_nonneg_right htotal hH
  change currentChenUpsilon8 N ≤ (8 * J + ε) * singularNormalization N
  nlinarith only [hfiniteN, hmain, hbudget]

end

end ImbalancedChen
