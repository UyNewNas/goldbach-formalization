import ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass
import MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform

/-!
At the actual frozen Gamma5 cutoff, the nonunit rough count has a
uniform upper bound for every real height up to N. For a partial prime
tuple of product D ≥ 2 its remaining height 2N/D is in that range.
The imported uniform estimate supplies both sides of the transition.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient

noncomputable section
open Filter Real LiLiuPrereqBuchstab
open P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent cutExponent_pos norm)
open scoped Topology

/-- One target threshold precedes the real height. The unit is excluded
also when the height is below the actual cutoff. -/
theorem eventually_nonunit_card_le :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 ≤ x → x ≤ (N : ℝ) →
      (((roughNumbers x (cut N)).erase 1).card : ℝ) ≤
        (2 / cutExponent) * (x / log (N : ℝ)) := by
  obtain ⟨T, hT4, H⟩ := Wu2008DoubleSieve.NonunitRoughUniform.uniform_upper
    cutExponent_pos (zero_lt_one : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop T] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  have hcut : 1 < cut N := one_lt_rpow hNr cutExponent_pos
  have hL : log (cut N) = cutExponent * log (N : ℝ) := log_rpow hN0 _
  intro x hx hxN
  obtain ⟨hempty, hcount⟩ := H N hN x (cut N) hxN (le_refl _)
  by_cases hy : cut N ≤ x
  · have hu := Wu2008DoubleSieve.NonunitRoughUniform.log_ratio_ge_one hcut hy
    have hb : buchstab (log x / log (cut N)) + 1 ≤ 2 := by
      linarith only [buchstab_le_one hu]
    calc
      _ ≤ _ := hcount hy
      _ ≤ 2 * x / log (cut N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hx) (log_pos hcut).le
      _ = _ := by
        rw [hL]
        field_simp [cutExponent_pos.ne', hlog.ne'] <;> ring
  · rw [hempty (lt_of_not_ge hy), Nat.cast_zero]
    exact mul_nonneg (div_nonneg (by norm_num) cutExponent_pos.le) (div_nonneg hx hlog.le)

/-- The original log N / N normalization gives an inverse-product
weight, with a constant fixed before N or the partial product D. -/
theorem eventually_nonunit_quotient_le :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, 2 ≤ D →
      norm N * (((roughNumbers (2 * (N : ℝ) / (D : ℝ)) (cut N)).erase 1).card : ℝ) ≤
        (4 / cutExponent) / (D : ℝ) := by
  filter_upwards [eventually_nonunit_card_le, eventually_gt_atTop (1 : ℕ)]
    with N H hN
  intro D hD
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith only [hDr]
  have hcap : 2 * (N : ℝ) / (D : ℝ) ≤ (N : ℝ) := by
    apply (div_le_iff₀ hD0).mpr
    calc
      _ ≤ (D : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right hDr hN0.le
      _ = _ := mul_comm _ _
  have hu := H (2 * (N : ℝ) / (D : ℝ))
    (div_nonneg (mul_nonneg (by norm_num) hN0.le) hD0.le) hcap
  have hn : 0 ≤ norm N := div_nonneg hlog.le hN0.le
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hu hn
    _ = _ := by
      unfold norm
      field_simp [hN0.ne', hlog.ne', hD0.ne', cutExponent_pos.ne'] <;> ring

end
end ImbalancedChen.P2FiniteMarkedGamma5NonunitQuotient
