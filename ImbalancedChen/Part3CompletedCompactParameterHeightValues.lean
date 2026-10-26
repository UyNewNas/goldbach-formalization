import ImbalancedChen.Part3CompletedEisensteinMeromorphic
import ImbalancedChen.Part3CompletedActualEisensteinIdentity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
Actual full-level completed Eisenstein values on compact spectral sets and
compact positive height bands. The two genuine completed-zeta constants
are bounded jointly with height away from their exceptional parameters;
the actual nonconstant series is bounded by its existing summable K-series
majorant. No spatial or spectral bound for the target family is assumed.
-/
namespace ImbalancedChen.Part3.CompletedCompactParameterHeightValues20261026b
noncomputable section
open Set Complex Metric
open scoped Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

private def rawConstant (p : ℂ × ℝ) : ℂ :=
  completedRiemannZeta (2 * p.1) * (p.2 : ℂ) ^ p.1 +
    completedRiemannZeta (2 * p.1 - 1) * (p.2 : ℂ) ^ (1 - p.1)

/-- Joint continuity is proved for the literal two-Lambda expression on
its true regular locus; the central removable value is handled separately
by the maximum principle, rather than by a false totalized raw formula. -/
theorem rawConstant_continuousOn (K : Set ℂ) {a b : ℝ} (ha : 0 < a)
    (hK : ∀ s ∈ K, s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 1 / 2) :
    ContinuousOn rawConstant (K ×ˢ Icc a b) := by
  intro p hp
  have hy : 0 < p.2 := lt_of_lt_of_le ha hp.2.1
  have hz := hK p.1 hp.1
  have h20 : 2 * p.1 ≠ (0 : ℂ) := mul_ne_zero (by norm_num) hz.1
  have h21 : 2 * p.1 ≠ (1 : ℂ) := by
    intro h
    apply hz.2.2
    linear_combination (1 / 2 : ℂ) * h
  have hm0 : 2 * p.1 - 1 ≠ (0 : ℂ) := by
    intro h
    apply hz.2.2
    linear_combination (1 / 2 : ℂ) * h
  have hm1 : 2 * p.1 - 1 ≠ (1 : ℂ) := by
    intro h
    apply hz.2.1
    linear_combination (1 / 2 : ℂ) * h
  have hc1 : ContinuousAt (fun q : ℂ × ℝ => completedRiemannZeta (2 * q.1)) p :=
    (differentiableAt_completedZeta h20 h21).continuousAt.comp
      (continuousAt_const.mul continuousAt_fst)
  have hc2 : ContinuousAt (fun q : ℂ × ℝ => completedRiemannZeta (2 * q.1 - 1)) p :=
    (differentiableAt_completedZeta hm0 hm1).continuousAt.comp
      ((continuousAt_const.mul continuousAt_fst).sub continuousAt_const)
  have hb : ContinuousAt (fun q : ℂ × ℝ => (q.2 : ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
  have hp1 := hb.cpow continuousAt_fst (Complex.ofReal_mem_slitPlane.mpr hy)
  have hp2 := hb.cpow (continuousAt_const.sub continuousAt_fst)
    (Complex.ofReal_mem_slitPlane.mpr hy)
  exact ((hc1.mul hp1).add (hc2.mul hp2)).continuousWithinAt

/-- A uniform bound for the ACTUAL completed family on an entire compact
parameter set and positive height band, with every horizontal point. -/
theorem exists_completedFourier_compact_height_bound (K : Set ℂ) (hK : IsCompact K)
    (M : ℕ) (hM : ∀ s ∈ K, |s.re| ≤ (M : ℝ)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hregular : ∀ s ∈ K, s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ y ∈ Icc a b, ∀ x : ℝ,
      ‖completedEisensteinFourier s y x‖ ≤ C := by
  obtain ⟨B, hB⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (rawConstant_continuousOn K ha hregular)
  let U : ℕ → ℝ := fun n => 2 * majorant M a n
  have hU : Summable U := (majorant_summable M ha).const_mul 2
  have hUn : ∀ n, 0 ≤ U n := by
    intro n
    exact (norm_nonneg (nonzeroFrequencyPair n (0 : ℂ) a 0)).trans
      (nonzeroFrequencyPair_norm_bound M ha n (by simp) le_rfl 0)
  have hmass : 0 ≤ ∑' n, U n := tsum_nonneg hUn
  let C := max B 0 + (2 * Real.sqrt b) * (∑' n, U n) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s hs y hy x
  have hypos : 0 < y := lt_of_lt_of_le ha hy.1
  have hc : ‖completedConstant y s‖ ≤ max B 0 := by
    rw [completedConstant_eq_raw y s (hregular s hs).2.2]
    exact (hB (s, y) ⟨hs, hy⟩).trans (le_max_left B 0)
  have hsum : ‖∑' n, nonzeroFrequencyPair n s y x‖ ≤ ∑' n, U n :=
    tsum_of_norm_bounded hU.hasSum (fun n =>
      nonzeroFrequencyPair_norm_bound M ha n (hM s hs) hy.1 x)
  have hfac : ‖(2 : ℂ) * (Real.sqrt y : ℂ)‖ = 2 * Real.sqrt y := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]
  calc
    ‖completedEisensteinFourier s y x‖ ≤ ‖completedConstant y s‖ +
        ‖(2 : ℂ) * (Real.sqrt y : ℂ)‖ * ‖∑' n, nonzeroFrequencyPair n s y x‖ := by
      unfold completedEisensteinFourier
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ max B 0 + (2 * Real.sqrt b) * (∑' n, U n) := by
      rw [hfac]
      exact add_le_add hc (mul_le_mul (by gcongr; exact hy.2) hsum
        (norm_nonneg _) (by positivity))
    _ ≤ C := by dsimp [C]; linarith

end
end ImbalancedChen.Part3.CompletedCompactParameterHeightValues20261026b
