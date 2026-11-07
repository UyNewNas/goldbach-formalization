import ImbalancedChen.Part3HeightMellinUnitary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The unshifted multiplier is exactly exp(-epsilon*u). A genuine lower
support and raw planar-line L2 membership imply L1 AND L2 after every
positive damping. L1 follows from the native L2 Holder product with the
actual exponential tail, whose squared integral is explicitly paid.
No integrability, unitary or Abel bound is assumed as an output premise.
-/

namespace ImbalancedChen.Part3.LowerSupportedExponentialDamping20261026b
noncomputable section
open Set Filter MeasureTheory
open AngularFourierUnitary20261026b
open HeightMellinUnitary20261026b

def LowerSupported (G : ℝ → ℂ) (u0 : ℝ) : Prop :=
  ∀ᵐ u ∂(volume : Measure ℝ), u<u0 → G u=0

def damped (ε : ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ := (Real.exp (-ε*u) : ℂ)*G u

def exponentialTail (ε u0 : ℝ) : ℝ → ℂ :=
  (Ici u0).indicator (fun u => (Real.exp (-ε*u) : ℂ))

theorem exponentialTail_square (ε u0 u : ℝ) :
    ‖exponentialTail ε u0 u‖^2 = (Ici u0).indicator (fun u => Real.exp ((-2*ε)*u)) u := by
  by_cases hu : u∈Ici u0
  · simp only [exponentialTail,indicator_of_mem hu,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · simp only [exponentialTail,indicator_of_notMem hu,norm_zero,zero_pow (by norm_num : 2≠0)]

theorem exponentialTail_memLp {ε : ℝ} (hε : 0<ε) (u0 : ℝ) :
    MemLp (exponentialTail ε u0) 2 volume := by
  have hcont : Continuous (fun u : ℝ => (Real.exp (-ε*u) : ℂ)) := by fun_prop
  have hm := hcont.aestronglyMeasurable.indicator measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : IntegrableOn (fun u : ℝ => Real.exp ((-2*ε)*u)) (Ici u0) :=
    integrableOn_Ici_iff_integrableOn_Ioi.mpr (integrableOn_exp_mul_Ioi (by linarith) u0)
  exact ((integrable_indicator_iff measurableSet_Ici).mpr hi).congr
    (Eventually.of_forall fun u => (exponentialTail_square ε u0 u).symm)

theorem exponentialTail_square_integral {ε : ℝ} (hε : 0<ε) (u0 : ℝ) :
    (∫ u : ℝ, ‖exponentialTail ε u0 u‖^2)=Real.exp (-2*ε*u0)/(2*ε) := by
  simp_rw [exponentialTail_square]
  rw [integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (by linarith : -2*ε<0) u0]
  field_simp [ne_of_gt hε]
  <;> ring

theorem damped_aestronglyMeasurable {G : ℝ → ℂ} (hG : MemLp G 2 volume) (ε : ℝ) :
    AEStronglyMeasurable (damped ε G) volume := by
  have hcont : Continuous (fun u : ℝ => (Real.exp (-ε*u) : ℂ)) := by fun_prop
  exact hcont.aestronglyMeasurable.mul hG.aestronglyMeasurable

theorem damped_memLp {G : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) {ε : ℝ} (hε : 0≤ε) : MemLp (damped ε G) 2 volume := by
  apply hG.of_le_mul (damped_aestronglyMeasurable hG ε)
  filter_upwards [hs] with u hu
  by_cases hlow : u<u0
  · simp only [damped,hu hlow,mul_zero,norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  · have heu : -ε*u≤-ε*u0 := by nlinarith [mul_nonneg hε (sub_nonneg.mpr (le_of_not_gt hlow))]
    rw [damped,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr heu) (norm_nonneg _)

theorem exponentialTail_mul_ae_damped {G : ℝ → ℂ} {u0 : ℝ}
    (hs : LowerSupported G u0) (ε : ℝ) :
    (fun u => exponentialTail ε u0 u*G u)=ᵐ[volume] damped ε G := by
  filter_upwards [hs] with u hu
  by_cases hlow : u<u0
  · simp only [damped,hu hlow,mul_zero]
  · simp only [exponentialTail,indicator_of_mem (le_of_not_gt hlow),damped]

/-- Native L2 Holder/Cauchy-Schwarz with the actual exponential tail
pays absolute integrability of the unshifted damped function. -/
theorem damped_integrable {G : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) {ε : ℝ} (hε : 0<ε) : Integrable (damped ε G) volume :=
  (MemLp.integrable_mul (p := 2) (q := 2) (exponentialTail_memLp hε u0) hG).congr
    (exponentialTail_mul_ae_damped hs ε)

theorem damped_integrable_memLp {G : ℝ → ℂ} {u0 : ℝ} (hG : MemLp G 2 volume)
    (hs : LowerSupported G u0) {ε : ℝ} (hε : 0<ε) :
    Integrable (damped ε G) volume ∧ MemLp (damped ε G) 2 volume :=
  ⟨damped_integrable hG hs hε,damped_memLp hG hs hε.le⟩

end
end ImbalancedChen.Part3.LowerSupportedExponentialDamping20261026b
