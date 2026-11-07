import ImbalancedChen.Part3RoughThinEulerHorizontal
import ImbalancedChen.Part3RoughWeightedPrimeMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Uniform O_kappa(1) comparison of the ACTUAL finite Euler correction in the
thin left strip with its value at Re(s)=1. The genuine weighted-prime
Chebyshev/Abel supplier is discharged here, so no prime-mass, left-strip
norm or zero-free bound is assumed. Both correction and reciprocal are
retained, for every original character including principal and p|q.
-/

namespace ImbalancedChen.Part3.RoughThinEulerUniformComparison20261026b
noncomputable section
open Classical Finset Complex Set
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open RoughFiniteEulerBounds20261026b RoughThinEulerFactors20261026b
open RoughThinEulerHorizontal20261026b RoughWeightedPrimeMass20261026b

private theorem logPrimeMass_bound_all {z : ℝ} (hz : 0≤z) :
    logPrimeMass z≤primeMassConstant*Real.log (max 2 z) := by
  by_cases hz2 : 2≤z
  · exact logPrimeMass_le hz2
  have hempty : smallPrimes z=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    have hpz := ((mem_smallPrimes hz).mp hp).2
    have hp2 : (2 : ℝ)≤p := by exact_mod_cast (smallPrimes_prime hp).two_le
    linarith
  have hlog : 0≤Real.log (max 2 z) := Real.log_nonneg
    (le_trans (by norm_num : (1 : ℝ)≤2) (le_max_left _ _))
  simpa only [logPrimeMass,hempty,Finset.sum_empty] using
    mul_nonneg primeMassConstant_pos.le hlog

def universalEulerCost : ℝ := primeMassConstant/(1-primeRadius)

theorem universalEulerCost_pos : 0<universalEulerCost :=
  div_pos primeMassConstant_pos (by linarith [primeRadius_lt_one])

/-- This constant depends only on the fixed thin-strip cap kappa, before
the original level, character, cutoff, width, real part and height. -/
def thinComparison (κ : ℝ) : ℝ := Real.exp (universalEulerCost*κ*Real.exp κ)

theorem thinComparison_pos (κ : ℝ) : 0<thinComparison κ := Real.exp_pos _

theorem integrated_cost_le {z δ κ σ : ℝ} (hz : 0≤z) (hδ : 0≤δ)
    (hκ : δ*Real.log (max 2 z)≤κ) (hσ : 1-δ≤σ) (hσ1 : σ≤1) :
    thinLogCost κ z*(1-σ)≤universalEulerCost*κ*Real.exp κ := by
  have hmargin : 0<1-primeRadius := by linarith [primeRadius_lt_one]
  have hlog : 0≤Real.log (max 2 z) := Real.log_nonneg
    (le_trans (by norm_num : (1 : ℝ)≤2) (le_max_left _ _))
  have hwidth : 1-σ≤δ := by linarith
  calc
    thinLogCost κ z*(1-σ) ≤
        (Real.exp κ/(1-primeRadius))*(primeMassConstant*Real.log (max 2 z))*δ := by
      unfold thinLogCost
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (logPrimeMass_bound_all hz) (by positivity)
      · exact hwidth
      · exact sub_nonneg.mpr hσ1
      · positivity
    _ = (universalEulerCost*Real.exp κ)*(δ*Real.log (max 2 z)) := by
      unfold universalEulerCost
      ring
    _ ≤ (universalEulerCost*Real.exp κ)*κ :=
      mul_le_mul_of_nonneg_left hκ (mul_nonneg universalEulerCost_pos.le (Real.exp_pos κ).le)
    _ = universalEulerCost*κ*Real.exp κ := by ring

/-- The actual prime logarithmic mass has been paid, yielding a genuine
constant ratio in the thin left strip. No logarithmic loss in z occurs. -/
theorem finiteCorrection_uniform_thin_ratios {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ κ σ : ℝ} (hz : 0≤z) (hδ : 0≤δ) (hδ1 : δ≤1/4)
    (hκ : δ*Real.log (max 2 z)≤κ) (hσ : 1-δ≤σ) (hσ1 : σ≤1) (t : ℝ) :
    ‖finiteCorrection χ z ((σ : ℂ)+I*t)/finiteCorrection χ z ((1 : ℂ)+I*t)‖ ≤
        thinComparison κ ∧
      ‖finiteCorrection χ z ((1 : ℂ)+I*t)/finiteCorrection χ z ((σ : ℂ)+I*t)‖ ≤
        thinComparison κ := by
  have hr := finiteCorrection_horizontal_ratios χ hz hδ hδ1 hκ hσ hσ1 t
  have hpay : Real.exp (thinLogCost κ z*(1-σ))≤thinComparison κ :=
    Real.exp_le_exp.mpr (integrated_cost_le hz hδ hκ hσ hσ1)
  exact ⟨hr.1.trans hpay,hr.2.trans hpay⟩

theorem finiteCorrection_uniform_thin_envelopes {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ κ σ : ℝ} (hz : 0≤z) (hδ : 0≤δ) (hδ1 : δ≤1/4)
    (hκ : δ*Real.log (max 2 z)≤κ) (hσ : 1-δ≤σ) (hσ1 : σ≤1) (t : ℝ) :
    ‖finiteCorrection χ z ((σ : ℂ)+I*t)‖≤thinComparison κ*plusEnvelope z ∧
      ‖(finiteCorrection χ z ((σ : ℂ)+I*t))⁻¹‖≤thinComparison κ*inverseEnvelope z := by
  have hr := finiteCorrection_horizontal_envelopes χ hz hδ hδ1 hκ hσ hσ1 t
  have hpay : Real.exp (thinLogCost κ z*(1-σ))≤thinComparison κ :=
    Real.exp_le_exp.mpr (integrated_cost_le hz hδ hκ hσ hσ1)
  have hplus : 0≤plusEnvelope z := by
    unfold plusEnvelope
    apply Finset.prod_nonneg
    intro p hp
    positivity
  have hinv : 0≤inverseEnvelope z :=
    (norm_nonneg ((finiteCorrection (1 : DirichletCharacter ℂ 1) z 1)⁻¹)).trans
      (finiteCorrection_bounds (1 : DirichletCharacter ℂ 1) z (s:=1) (by simp)).2.2
  exact ⟨hr.1.trans (mul_le_mul_of_nonneg_right hpay hplus),
    hr.2.trans (mul_le_mul_of_nonneg_right hpay hinv)⟩

/-- A fixed kappa has one positive constant before all arithmetic and
geometric parameters, including arbitrary height and original modulus. -/
theorem exists_uniform_thin_Euler_comparison (κ : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q)
      (z δ σ t : ℝ),0≤z → 0≤δ → δ≤1/4 → δ*Real.log (max 2 z)≤κ →
      1-δ≤σ → σ≤1 →
      ‖finiteCorrection χ z ((σ : ℂ)+I*t)/finiteCorrection χ z ((1 : ℂ)+I*t)‖≤C ∧
      ‖finiteCorrection χ z ((1 : ℂ)+I*t)/finiteCorrection χ z ((σ : ℂ)+I*t)‖≤C ∧
      ‖finiteCorrection χ z ((σ : ℂ)+I*t)‖≤C*plusEnvelope z ∧
      ‖(finiteCorrection χ z ((σ : ℂ)+I*t))⁻¹‖≤C*inverseEnvelope z := by
  refine ⟨thinComparison κ,thinComparison_pos κ,?_⟩
  intro q χ z δ σ t hz hδ hδ1 hκ hσ hσ1
  exact ⟨(finiteCorrection_uniform_thin_ratios χ hz hδ hδ1 hκ hσ hσ1 t).1,
    (finiteCorrection_uniform_thin_ratios χ hz hδ hδ1 hκ hσ hσ1 t).2,
    finiteCorrection_uniform_thin_envelopes χ hz hδ hδ1 hκ hσ hσ1 t⟩

end
end ImbalancedChen.Part3.RoughThinEulerUniformComparison20261026b
