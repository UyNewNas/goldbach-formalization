import ImbalancedChen.Part3ActualComplexMacdonaldQuarterHolomorphic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual Macdonald formula on the strict quarter-sector in each
argument. The jointly L1 double integral is bound to the actual single
K_nu(z*w/t) fiber and to its already supplied positive-real value.
The quarter-sector is proved convex. A positive-real sequence with a
punctured interior accumulation point supplies the identity theorem;
it is applied once in each argument to the actual separately proved
holomorphic functions. No analytic-continuation identity is assumed.

This proves only |Im(z)|<Re(z), |Im(w)|<Re(w). The larger printed domain
of DLMF 10.32.18 and continuation to a cut-plane K model remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualComplexMacdonaldQuarterIdentity20261026b

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open ComplexOrderKBridgeSourceOnly
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualKMacdonaldPositive20261026b
open ActualComplexArgumentKLaplace20261026b ActualComplexArgumentKHolomorphic20261026b
open ActualComplexMacdonaldQuarterL120261026b ActualComplexMacdonaldQuarterHolomorphic20261026b

def complexMacdonaldKernel (nu z w : ℂ) (t : ℝ) : ℂ :=
  ((t⁻¹ : ℝ) : ℂ) *
    Complex.exp (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ)) *
      complexArgumentK nu (z * w * ((t⁻¹ : ℝ) : ℂ))

theorem complexMacdonaldJoint_factor (nu z w : ℂ) (v t : ℝ) :
    complexMacdonaldJoint nu z w v t =
      (((t⁻¹ : ℝ) : ℂ) *
        Complex.exp (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ))) *
        (Complex.exp (-(z * w * ((t⁻¹ : ℝ) : ℂ)) * (Real.cosh v : ℂ)) *
          Complex.cosh (nu * (v : ℂ))) := by
  have he : complexMacdonaldExponent z w v t =
      (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ)) +
        (-(z * w * ((t⁻¹ : ℝ) : ℂ)) * (Real.cosh v : ℂ)) := by
    unfold complexMacdonaldExponent
    push_cast
    simp only [div_eq_mul_inv]
    ring
  unfold complexMacdonaldJoint
  rw [he, Complex.exp_add]
  ring

theorem complexMacdonaldJoint_integral_v (nu z w : ℂ) (t : ℝ) :
    (∫ v in Ioi (0 : ℝ), complexMacdonaldJoint nu z w v t) =
      complexMacdonaldKernel nu z w t := by
  simp_rw [complexMacdonaldJoint_factor]
  rw [integral_const_mul, ← complexArgumentK_eq_integral]
  rfl

/-- Actual absolute convergence of the surviving complex single kernel. -/
theorem complexMacdonaldKernel_integrable (nu : ℂ) {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    Integrable (complexMacdonaldKernel nu z w) positiveMeasure := by
  have h := (complexMacdonaldJoint_integrable nu hz hw).integral_prod_right
  apply h.congr
  exact Eventually.of_forall fun t => complexMacdonaldJoint_integral_v nu z w t

theorem complexMacdonaldValue_eq_single (nu : ℂ) {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    complexMacdonaldValue nu z w =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), complexMacdonaldKernel nu z w t := by
  unfold complexMacdonaldValue
  congr 1
  rw [integral_prod_symm _ (complexMacdonaldJoint_integrable nu hz hw)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => complexMacdonaldJoint_integral_v nu z w t

theorem positive_real_mem_sector {x : ℝ} (hx : 0 < x) : (x : ℂ) ∈ strictQuarterSector := by
  simpa only [strictQuarterSector, mem_setOf_eq, Complex.ofReal_im, abs_zero,
    Complex.ofReal_re] using hx

theorem complexMacdonaldKernel_real (nu : ℂ) (x y t : ℝ) :
    complexMacdonaldKernel nu (x : ℂ) (y : ℂ) t = macdonaldKernel nu x y t := by
  have harg : (x : ℂ) * (y : ℂ) * ((t⁻¹ : ℝ) : ℂ) = ((x * y / t : ℝ) : ℂ) := by
    push_cast
    simp only [div_eq_mul_inv]
  have he : (((-t / 2 : ℝ) : ℂ) - ((x : ℂ) ^ 2 + (y : ℂ) ^ 2) * ((1 / (2 * t) : ℝ) : ℂ)) =
      ((-t / 2 - (x ^ 2 + y ^ 2) / (2 * t) : ℝ) : ℂ) := by
    push_cast
    simp only [div_eq_mul_inv, one_mul]
  unfold complexMacdonaldKernel macdonaldKernel macdonaldWeight
  rw [harg, complexArgumentK_real, he, ← Complex.ofReal_exp]
  push_cast
  ring

theorem complexMacdonaldValue_positive (nu : ℂ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    complexMacdonaldValue nu (x : ℂ) (y : ℂ) =
      complexArgumentK nu (x : ℂ) * complexArgumentK nu (y : ℂ) := by
  rw [complexMacdonaldValue_eq_single nu (positive_real_mem_sector hx) (positive_real_mem_sector hy)]
  simp_rw [complexMacdonaldKernel_real]
  rw [complexArgumentK_real, complexArgumentK_real]
  exact (actual_K_macdonald_positive_kernel nu hx hy).symm

theorem strictQuarterSector_convex : Convex ℝ strictQuarterSector := by
  intro z hz w hw a b ha hb hab
  rcases strictQuarterSector_split hz with ⟨hzp, hzm⟩
  rcases strictQuarterSector_split hw with ⟨hwp, hwm⟩
  have hcombine : ∀ x y : ℝ, 0 < x → 0 < y → 0 < a * x + b * y := by
    intro x y hx hy
    rcases eq_or_lt_of_le ha with (rfl | hap)
    · have hb1 : b = 1 := by linarith
      simpa only [zero_mul, zero_add, hb1, one_mul] using hy
    · have hpos := mul_pos hap hx
      have hnonneg := mul_nonneg hb hy.le
      linarith
  have hp := hcombine _ _ hzp hwp
  have hm := hcombine _ _ hzm hwm
  change |(a • z + b • w).im| < (a • z + b • w).re
  simp only [Complex.add_im, Complex.add_re, Complex.smul_im, Complex.smul_re]
  apply abs_lt.mpr
  constructor <;> nlinarith

/-- Identity principle with a genuinely accumulating positive-real set,
proved from the analytic identity theorem rather than assumed as a
continuation principle for a particular K/product transform. -/
theorem eqOn_sector_of_positive_real {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f strictQuarterSector) (hg : AnalyticOnNhd ℂ g strictQuarterSector)
    (hreal : ∀ x : ℝ, 0 < x → f (x : ℂ) = g (x : ℂ)) :
    EqOn f g strictQuarterSector := by
  let sequence : ℕ → ℂ := fun n => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_natCast_atTop_atTop.add_const 1).const_div_atTop 1
  have hrealLim : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).add hinv
  have hlim : Tendsto sequence atTop (𝓝 (1 : ℂ)) := by
    simpa only [sequence, Function.comp_def, Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hrealLim
  have hpunctured : Tendsto sequence atTop (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlim, Eventually.of_forall fun n => ?_⟩
    change sequence n ≠ 1
    intro heq
    have hr : 1 + 1 / ((n : ℝ) + 1) = 1 := by
      exact Complex.ofReal_injective (by simpa only [sequence, Complex.ofReal_one] using heq)
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hseqEq : ∃ᶠ n : ℕ in atTop, f (sequence n) = g (sequence n) := by
    apply Filter.Eventually.frequently
    exact Eventually.of_forall fun n => hreal _ (by positivity)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg strictQuarterSector_convex.isPreconnected
    (positive_real_mem_sector (by norm_num : (0 : ℝ) < 1)) (hpunctured.frequently hseqEq)

theorem complexArgumentK_analyticOnNhd_sector (nu : ℂ) :
    AnalyticOnNhd ℂ (complexArgumentK nu) strictQuarterSector :=
  (complexArgumentK_analyticOnNhd nu).mono (fun _ hz => strictQuarterSector_re_pos hz)

theorem complexMacdonaldValue_eq_product_real_right (nu : ℂ) {y : ℝ} (hy : 0 < y)
    {z : ℂ} (hz : z ∈ strictQuarterSector) :
    complexMacdonaldValue nu z (y : ℂ) = complexArgumentK nu z * complexArgumentK nu (y : ℂ) := by
  have hF := complexMacdonaldValue_analyticOnNhd_left nu (positive_real_mem_sector hy)
  have hG : AnalyticOnNhd ℂ (fun z => complexArgumentK nu z * complexArgumentK nu (y : ℂ))
      strictQuarterSector := (complexArgumentK_analyticOnNhd_sector nu).mul analyticOnNhd_const
  exact eqOn_sector_of_positive_real hF hG (fun x hx => complexMacdonaldValue_positive nu hx hy) hz

/-- The actual quarter-sector product identity, obtained by applying the
proved identity principle in each variable to actual analytic functions. -/
theorem complexMacdonaldValue_eq_product (nu : ℂ) {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    complexMacdonaldValue nu z w = complexArgumentK nu z * complexArgumentK nu w := by
  have hF := complexMacdonaldValue_analyticOnNhd_right nu hz
  have hG : AnalyticOnNhd ℂ (fun w => complexArgumentK nu z * complexArgumentK nu w)
      strictQuarterSector := analyticOnNhd_const.mul (complexArgumentK_analyticOnNhd_sector nu)
  exact eqOn_sector_of_positive_real hF hG
    (fun y hy => complexMacdonaldValue_eq_product_real_right nu hy hz) hw

theorem complexMacdonaldKernel_eq_display (nu z w : ℂ) (t : ℝ) :
    complexMacdonaldKernel nu z w t =
      Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
        complexArgumentK nu (z * w / (t : ℂ)) / (t : ℂ) := by
  have he : (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ)) =
      -(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ)) := by
    push_cast
    simp only [div_eq_mul_inv, one_mul]
  unfold complexMacdonaldKernel
  rw [he]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- Separately proved absolute convergence of the displayed complex
quarter-sector Macdonald density. -/
theorem actual_K_macdonald_quarter_integrable (nu : ℂ) {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    IntegrableOn (fun t =>
      Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
        complexArgumentK nu (z * w / (t : ℂ)) / (t : ℂ)) (Ioi 0) := by
  apply (complexMacdonaldKernel_integrable nu hz hw).congr
  exact Eventually.of_forall (complexMacdonaldKernel_eq_display nu z w)

/-- Actual Macdonald formula for two independently varying complex
arguments in the strict quarter-sector. The larger DLMF domain is OPEN. -/
theorem actual_K_macdonald_quarter (nu : ℂ) {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    complexArgumentK nu z * complexArgumentK nu w =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
        Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
          complexArgumentK nu (z * w / (t : ℂ)) / (t : ℂ) := by
  rw [← complexMacdonaldValue_eq_product nu hz hw, complexMacdonaldValue_eq_single nu hz hw]
  simp_rw [complexMacdonaldKernel_eq_display]

end
end ImbalancedChen.Part3.ActualComplexMacdonaldQuarterIdentity20261026b
