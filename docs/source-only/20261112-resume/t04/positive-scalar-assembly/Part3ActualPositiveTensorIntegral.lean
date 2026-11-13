import ImbalancedChen.Part3ActualPositiveCompactTensor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute integration of the common compact tensor cutoff against a
physical scalar kernel. Only the preimage of its actual height box is used. -/
namespace ImbalancedChen.Part3.ActualPositiveTensorIntegral20261112
noncomputable section
open Filter Set MeasureTheory Complex
open scoped Topology ContDiff
open PrescribedLogTensorCoefficients20261112 PrescribedLogTensorWindows20261112
open PrescribedLogTensorExpansion20261112 (productAt product_bound)
open ActualPositiveCompactTensor20261112 OriginalPositiveHeightTest20261112
open RadialSchrodingerL2Form20261025a

abbrev coeff (η H : RadialTest) (R : ℝ) := coefficient (logHeight η H R)

theorem physical (η H : RadialTest) (R a b : ℝ) :
    HasSum (fun v => coeff η H R v*productAt v a b) (height η H R a b) := by
  by_cases p : 0<a ∧ 0<b
  · simpa only [Real.exp_log p.1,Real.exp_log p.2,height,if_pos p] using
      reconstruct _ (log_smooth η H R) (log_compact η H R) (Real.log a) (Real.log b)
  · have e (v : Modes) : productAt v a b=0 := by
      rcases not_and_or.mp p with x|y <;> simp [productAt,pattern,rightPattern,*]
    simp [height,p,e]

theorem coeff_summable (η H : RadialTest) (R : ℝ) : Summable (fun v => ‖coeff η H R v‖) :=
  absolute _ (log_smooth η H R) (log_compact η H R)

def covers (η H : RadialTest) (R B : ℝ) := ∀ v : Modes,coeff η H R v≠0 → ∀ a b,productAt v a b≠0 →
    a∈Icc (Real.exp (-B)) (Real.exp B) ∧ b∈Icc (Real.exp (-B)) (Real.exp B)

theorem box (η H : RadialTest) (R : ℝ) : ∃ B : ℝ,0≤B ∧ covers η H R B :=
  active_box (log_compact η H R)

theorem exchange {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (η H : RadialTest) (R : ℝ) (a b : X→ℝ) (W : X→ℂ) (maj : X→ℝ)
    (ma : Measurable a) (mb : Measurable b) (mw : AEStronglyMeasurable W μ)
    (I : Integrable maj μ) (nn : ∀ x,0≤maj x)
    (bound : ∀ v,coeff η H R v≠0 → ∀ x,productAt v (a x) (b x)≠0 → ‖W x‖≤maj x) :
    Integrable (fun x => height η H R (a x) (b x)*W x) μ ∧
    (∀ v,Integrable (fun x => coeff η H R v*(productAt v (a x) (b x)*W x)) μ) ∧
    HasSum (fun v => coeff η H R v*∫ x,productAt v (a x) (b x)*W x ∂μ)
      (∫ x,height η H R (a x) (b x)*W x ∂μ) := by
  let c := coeff η H R
  let T := fun (v : Modes) (x : X) => c v*(productAt v (a x) (b x)*W x)
  let f := fun x : X => height η H R (a x) (b x)*W x
  have sm (v : Modes) : AEStronglyMeasurable (T v) μ :=
    aestronglyMeasurable_const.mul (((pattern_test _ _).1.measurable.comp ma).aestronglyMeasurable.mul
      (((right_test _ _).1.measurable.comp mb).aestronglyMeasurable.star) |>.mul mw)
  have hc := coeff_summable η H R
  have d (v : Modes) (x : X) : ‖T v x‖≤‖c v‖*maj x := by
    by_cases c0 : c v=0
    · simp [T,c0]
    by_cases p0 : productAt v (a x) (b x)=0
    · simpa only [T,p0,zero_mul,mul_zero,norm_zero] using mul_nonneg (norm_nonneg (c v)) (nn x)
    rw [T,norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul (product_bound _ _ _) (bound v c0 x p0) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) (norm_nonneg _)
  have meas (v : Modes) : Integrable (T v) μ := (I.const_mul ‖c v‖).mono' (sm v) (ae_of_all _ (d v))
  have S : Summable (fun v => ∫ x,‖T v x‖ ∂μ) :=
    (hc.mul_right (∫ x,maj x ∂μ)).of_nonneg_of_le (fun v => integral_nonneg fun _ => norm_nonneg _) (fun v => by
      simpa only [integral_const_mul] using integral_mono (meas v).norm (I.const_mul ‖c v‖) (d v))
  have P (x : X) : HasSum (fun v => T v x) (f x) :=
    ((physical η H R (a x) (b x)).mul_right (W x)).congr_fun (fun v => by dsimp [T,c]; ring)
  have EQ : (fun x => ∑' v,T v x)=f := funext fun x => (P x).tsum_eq
  have M : AEStronglyMeasurable f μ := EQ ▸ (AEMeasurable.tsum (fun v => (meas v).aemeasurable)).aestronglyMeasurable
  have L := hasSum_integral_of_summable_integral_norm meas S
  rw [EQ] at L
  refine ⟨(I.const_mul (∑' v,‖c v‖)).mono' M (ae_of_all _ fun x => ?_),meas,L.congr_fun (fun v => by dsimp [T,c]; rw [integral_const_mul])⟩
  rw [←(P x).tsum_eq,←tsum_mul_right]
  exact (norm_tsum_le_tsum_norm ((hc.mul_right _).of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => d v x))).trans
    (((hc.mul_right _).of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => d v x)).tsum_le_tsum (fun v => d v x) (hc.mul_right _))

end
end ImbalancedChen.Part3.ActualPositiveTensorIntegral20261112
