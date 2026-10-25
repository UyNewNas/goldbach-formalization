import ImbalancedChen.Part3ActualGreenCompactForcing
import ImbalancedChen.Part3GeneralIOrderHolomorphy
import ImbalancedChen.Part3ComplexOrderKUniformStripDecay
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual I/K Green majorants on compact order and radial sets

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The I bound is derived from the literal Gamma coefficients and a summable
factorial majorant; its complex-power prefactor is bounded on the actual
compact parameter product. The K bound is the proved uniform strip bound.
Their product supplies an actual integrable majorant for compact forcing.
No normal-convergence, analytic-kernel, inverse-equality or spectral premise
is introduced. Only the open interior order strip is treated here.
-/

namespace ImbalancedChen.Part3.ActualGreenCompactOrderMajorant20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly
open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ComplexOrderKBridgeSourceOnly ComplexOrderKEntire20261025a
open ComplexOrderKRadialRegularitySourceOnly ComplexOrderKUniformStripDecay20261025a
open ActualGreenCompactForcing20261025a

def interiorOrderStrip : Set ℂ := {nu | 0 < nu.re ∧ nu.re < 1}

theorem isOpen_interiorOrderStrip : IsOpen interiorOrderStrip := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem actualGreen_analyticAt_order {nu : ℂ} (hnu : -1 < nu.re) (s r : ℝ) :
    AnalyticAt ℂ (fun z => actualRadialGreen z s r) nu := by
  exact (analyticAt_generalI_order nu hnu (Real.exp_pos (min r s))).mul
    ((complexOrderK_differentiable_all (Real.exp_pos (max r s))).analyticAt nu)

/-- The actual I-series has a uniform bound for orders in a genuine compact
subset of the interior strip and radial variables in a fixed closed interval. -/
theorem exists_radialI_compact_order_bound
    (S : Set ℂ) (hS : IsCompact S) (hstrip : S ⊆ interiorOrderStrip)
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ nu ∈ S, ∀ t ∈ Icc (-R) R, ‖radialI nu t‖ ≤ C := by
  have hgamma : Continuous (fun nu : ℂ => (Complex.Gamma (nu + 1))⁻¹) :=
    (Complex.differentiable_one_div_Gamma.comp
      (differentiable_id.add (differentiable_const 1))).continuous
  obtain ⟨G0, hG0⟩ := hS.exists_bound_of_continuousOn hgamma.continuousOn
  let G : ℝ := max G0 0
  have hG : 0 ≤ G := le_max_right _ _
  have hpref : Continuous (fun p : ℂ × ℝ =>
      (((Real.exp p.2 / 2 : ℝ) : ℂ) ^ p.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hbase : Real.exp p.2 / 2 ≠ 0 := ne_of_gt (by positivity)
    exact (Complex.continuousAt_ofReal_cpow (Real.exp p.2 / 2) p.1
      (Or.inr hbase)).comp (by fun_prop)
  obtain ⟨P0, hP0⟩ := (hS.prod (isCompact_Icc : IsCompact (Icc (-R) R))).exists_bound_of_continuousOn
    hpref.continuousOn
  let P : ℝ := max P0 0
  have hP : 0 ≤ P := le_max_right _ _
  let Z : ℝ := (Real.exp R / 2) ^ 2
  let u : ℕ → ℝ := fun n => G * (Z ^ n / (n.factorial : ℝ))
  have hu : Summable u := (Real.summable_pow_div_factorial Z).mul_left G
  have hu0 : 0 ≤ ∑' n, u n := tsum_nonneg (fun n => by dsimp only [u, Z]; positivity)
  refine ⟨P * ∑' n, u n, mul_nonneg hP hu0, ?_⟩
  intro nu hnu t ht
  have hnu0 : 0 < nu.re := (hstrip hnu).1
  have hnu' : -1 < nu.re := by linarith only [hnu0]
  have hGamma : ‖(Complex.Gamma (nu + 1))⁻¹‖ ≤ G :=
    (hG0 nu hnu).trans (le_max_left _ _)
  have hcoeff (n : ℕ) : ‖generalICoeff nu n‖ ≤ G / (n.factorial : ℝ) := by
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hpow : 1 ≤ (nu.re + 1) ^ n := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith only [hnu0] : 1 ≤ nu.re + 1) n
    have hden : (n.factorial : ℝ) ≤ (nu.re + 1) ^ n * (n.factorial : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hf.le
    calc
      _ ≤ ‖(Complex.Gamma (nu + 1))⁻¹‖ /
          ((nu.re + 1) ^ n * (n.factorial : ℝ)) := generalICoeff_norm_le hnu' n
      _ ≤ G / ((nu.re + 1) ^ n * (n.factorial : ℝ)) :=
        div_le_div_of_nonneg_right hGamma (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left hG hf hden
  have hz : ‖(((Real.exp t / 2 : ℝ) : ℂ)) ^ 2‖ ≤ Z := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ht.2) (by norm_num)) 2
  have hcore : ‖generalICore nu ((((Real.exp t / 2 : ℝ) : ℂ)) ^ 2)‖ ≤ ∑' n, u n := by
    apply tsum_of_norm_bounded hu.hasSum
    intro n
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (G / (n.factorial : ℝ)) * Z ^ n :=
        mul_le_mul (hcoeff n) (pow_le_pow_left₀ (norm_nonneg _) hz n)
          (pow_nonneg (norm_nonneg _) n) (by positivity)
      _ = u n := by dsimp only [u]; ring
  have hpower : ‖(((Real.exp t / 2 : ℝ) : ℂ)) ^ nu‖ ≤ P :=
    (hP0 (nu, t) ⟨hnu, ht⟩).trans (le_max_left _ _)
  unfold radialI generalI
  rw [norm_mul]
  exact mul_le_mul hpower hcore (norm_nonneg _) hP

theorem exists_actualGreen_compact_order_bound
    (S : Set ℂ) (hS : IsCompact S) (hstrip : S ⊆ interiorOrderStrip) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ nu ∈ S, ∀ s ∈ Icc (-R) R, ∀ r ∈ Icc (-R) R,
      ‖actualRadialGreen nu s r‖ ≤ C := by
  obtain ⟨CI, hCI, hI⟩ := exists_radialI_compact_order_bound S hS hstrip R
  let CK : ℝ := stripDecayConstant 0 (Real.exp (-R)) 1
  have hCK : 0 ≤ CK := (stripDecayConstant_pos 0 (Real.exp (-R)) 1).le
  refine ⟨CI * CK, mul_nonneg hCI hCK, ?_⟩
  intro nu hnu s hs r hr
  have hmin : min r s ∈ Icc (-R) R :=
    ⟨le_min hr.1 hs.1, (min_le_left _ _).trans hr.2⟩
  have hmax : max r s ∈ Icc (-R) R :=
    ⟨hr.1.trans (le_max_left _ _), max_le hr.2 hs.2⟩
  have hnuAbs : |nu.re| ≤ 1 := by
    rw [abs_of_pos (hstrip hnu).1]
    exact (hstrip hnu).2.le
  have hk := complexOrderK_uniform_exp_bound (Real.exp_pos (-R))
    (Real.exp_le_exp.mpr hmax.1) hnuAbs
  have hk' : ‖radialK nu (max r s)‖ ≤ CK := by
    apply hk.trans
    exact mul_le_of_le_one_right hCK (Real.exp_le_one_iff.mpr (by positivity))
  unfold actualRadialGreen kernel
  rw [norm_mul]
  exact mul_le_mul (hI nu hnu (min r s) hmin) hk' (norm_nonneg _) hCI

/-- The majorant is an actual continuous compactly supported function of
the two integration variables, independent of nu throughout the compact set. -/
theorem exists_actualGreen_forcing_integrable_majorant
    (S : Set ℂ) (hS : IsCompact S) (hstrip : S ⊆ interiorOrderStrip)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ bound : ℝ × ℝ → ℝ, Integrable bound ((volume : Measure ℝ).prod volume) ∧
      ∀ nu ∈ S, ∀ p : ℝ × ℝ,
        ‖actualRadialGreen nu p.1 p.2 * f p.1 * g p.2‖ ≤ bound p := by
  obtain ⟨R, hR, hRbound⟩ := (hfc.isCompact.union hgc.isCompact).isBounded.exists_pos_norm_le
  obtain ⟨C, hC, hkernel⟩ := exists_actualGreen_compact_order_bound S hS hstrip R
  let bound : ℝ × ℝ → ℝ := fun p => C * ‖f p.1‖ * ‖g p.2‖
  have hc : HasCompactSupport bound := by
    apply HasCompactSupport.intro (hfc.isCompact.prod hgc.isCompact)
    intro p hp
    by_cases hpf : p.1 ∈ tsupport f
    · have hpg : p.2 ∉ tsupport g := fun hpg => hp ⟨hpf, hpg⟩
      simp only [bound, image_eq_zero_of_notMem_tsupport hpg, norm_zero, mul_zero]
    · simp only [bound, image_eq_zero_of_notMem_tsupport hpf, norm_zero, mul_zero, zero_mul]
  have hcont : Continuous bound :=
    (continuous_const.mul (hf.comp continuous_fst).norm).mul (hg.comp continuous_snd).norm
  refine ⟨bound, hcont.integrable_of_hasCompactSupport hc, ?_⟩
  intro nu hnu p
  by_cases hpf : f p.1 = 0
  · simp [hpf, bound]
  by_cases hpg : g p.2 = 0
  · simp [hpg, bound]
  have hsNorm := hRbound p.1 (Or.inl (subset_tsupport f hpf))
  have hrNorm := hRbound p.2 (Or.inr (subset_tsupport g hpg))
  have hs : p.1 ∈ Icc (-R) R := by
    rw [Real.norm_eq_abs] at hsNorm
    exact abs_le.mp hsNorm
  have hr : p.2 ∈ Icc (-R) R := by
    rw [Real.norm_eq_abs] at hrNorm
    exact abs_le.mp hrNorm
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hkernel nu hnu p.1 hs p.2 hr) (norm_nonneg _)) (norm_nonneg _)

end
end ImbalancedChen.Part3.ActualGreenCompactOrderMajorant20261025a
