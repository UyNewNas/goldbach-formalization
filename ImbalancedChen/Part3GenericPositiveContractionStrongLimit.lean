import ImbalancedChen.Part3PositiveContractionResolventCalculus
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
Strong stability of the survival powers of any injective positive
self-adjoint contraction on an arbitrary complex Hilbert space. Dense
range is derived from symmetry and injectivity; the quantitative estimate
on range R is proved by scalar CFC. No spectral measure, strong-limit or
dense-range premise is used. SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.GenericPositiveContractionStrongLimit20261025a

noncomputable section

open Filter Topology Set
open scoped BigOperators
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem denseRange_of_selfAdjoint_injective (R : H →L[ℂ] H)
    (hSA : IsSelfAdjoint R) (hinj : Function.Injective R) : DenseRange R := by
  change Dense (R.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply R.range.topologicalClosure_eq_top_iff.mpr
  have hker : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  rw [ContinuousLinearMap.orthogonal_range, hSA.adjoint_eq, hker]

theorem scalar_survival_rate {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    t * (1 - t) ^ n ≤ 1 / ((n : ℝ) + 1) := by
  let s : ℝ := 1 - t
  have hs0 : 0 ≤ s := sub_nonneg.mpr ht.2
  have hs1 : s ≤ 1 := by dsimp [s]; linarith [ht.1]
  have hsum : ((n : ℝ) + 1) * (t * s ^ n) ≤
      ∑ k ∈ Finset.range (n + 1), t * s ^ k := by
    calc
      _ = ∑ _k ∈ Finset.range (n + 1), t * s ^ n := by simp [Nat.cast_add, Nat.cast_one]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hs0 hs1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) ht.1
  have hgeom := mul_neg_geom_sum s (n + 1)
  have hs : 1 - s = t := by dsimp [s]; ring
  rw [hs] at hgeom
  have hweighted : (∑ k ∈ Finset.range (n + 1), t * s ^ k) = 1 - s ^ (n + 1) := by
    rw [← Finset.mul_sum]
    exact hgeom
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  change t * s ^ n * ((n : ℝ) + 1) ≤ 1
  nlinarith [pow_nonneg hs0 (n + 1)]

variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)

theorem cfc_survival : cfc (fun t : ℝ => 1 - t) R = 1 - R := by
  rw [cfc_sub, cfc_const_one ℝ R hSA, cfc_id' ℝ R hSA]

theorem cfc_survival_pow (n : ℕ) :
    cfc (fun t : ℝ => (1 - t) ^ n) R = (1 - R) ^ n := by
  rw [cfc_pow (fun t : ℝ => 1 - t) n R (ha := hSA), cfc_survival R hSA]

theorem cfc_survival_pow_mul (n : ℕ) :
    cfc (fun t : ℝ => (1 - t) ^ n * t) R = (1 - R) ^ n * R := by
  rw [cfc_mul, cfc_survival_pow R hSA, cfc_id' ℝ R hSA]

theorem survival_pow_opNorm_le_one (n : ℕ) : ‖(1 - R) ^ n‖ ≤ 1 := by
  rw [← cfc_survival_pow R hSA]
  apply norm_cfc_le zero_le_one
  intro t ht
  have h := spectrum_mem_unitInterval R hpos hnorm ht
  have h0 : 0 ≤ 1 - t := sub_nonneg.mpr h.2
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 n)]
  exact pow_le_one₀ h0 (by linarith [h.1])

theorem survival_pow_mul_opNorm_le (n : ℕ) :
    ‖(1 - R) ^ n * R‖ ≤ 1 / ((n : ℝ) + 1) := by
  rw [← cfc_survival_pow_mul R hSA]
  apply norm_cfc_le (by positivity)
  intro t ht
  have h := spectrum_mem_unitInterval R hpos hnorm ht
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr h.2) n) h.1)]
  simpa only [mul_comm] using scalar_survival_rate h n

theorem survival_pow_norm_le (n : ℕ) (f : H) : ‖((1 - R) ^ n) f‖ ≤ ‖f‖ :=
  (((1 - R) ^ n).le_opNorm f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (survival_pow_opNorm_le_one R hSA hpos hnorm n) (norm_nonneg f))

theorem survival_pow_on_range_norm_le (n : ℕ) (f : H) :
    ‖((1 - R) ^ n) (R f)‖ ≤ (1 / ((n : ℝ) + 1)) * ‖f‖ :=
  (((1 - R) ^ n * R).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (survival_pow_mul_opNorm_le R hSA hpos hnorm n)
      (norm_nonneg f))

theorem tendsto_survival_pow_on_range (f : H) :
    Tendsto (fun n : ℕ => ((1 - R) ^ n) (R f)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hb : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * ‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul tendsto_const_nhds
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => survival_pow_on_range_norm_le R hSA hpos hnorm n f) hb

theorem tendsto_survival_pow (hinj : Function.Injective R) (f : H) :
    Tendsto (fun n : ℕ => ((1 - R) ^ n) f) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  obtain ⟨y, hy, hnear⟩ := (denseRange_of_selfAdjoint_injective R hSA hinj).exists_dist_lt f
    (show 0 < epsilon / 2 by positivity)
  obtain ⟨g, rfl⟩ := hy
  have hdiff : ‖f - R g‖ < epsilon / 2 := by simpa only [dist_eq_norm] using hnear
  have hlimit : Tendsto (fun n : ℕ => ‖((1 - R) ^ n) (R g)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (tendsto_survival_pow_on_range R hSA hpos hnorm g).norm
  have hrange : ∀ᶠ n : ℕ in atTop, ‖((1 - R) ^ n) (R g)‖ < epsilon / 2 :=
    hlimit.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity))
  filter_upwards [hrange] with n hn
  rw [dist_zero_right]
  have hsplit : ((1 - R) ^ n) f = ((1 - R) ^ n) (f - R g) + ((1 - R) ^ n) (R g) := by
    rw [map_sub, sub_add_cancel]
  calc
    ‖((1 - R) ^ n) f‖ ≤ ‖((1 - R) ^ n) (f - R g)‖ + ‖((1 - R) ^ n) (R g)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ ‖f - R g‖ + ‖((1 - R) ^ n) (R g)‖ :=
      add_le_add_right (survival_pow_norm_le R hSA hpos hnorm n _) _
    _ < epsilon := by linarith

end

end ImbalancedChen.Part3.GenericPositiveContractionStrongLimit20261025a
