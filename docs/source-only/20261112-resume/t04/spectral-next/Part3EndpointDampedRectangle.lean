import ImbalancedChen.Part3ActualIncompleteResidualContour
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The corner polynomial cancels a first-power distance-to-the-left-edge
loss. A diagonal Gaussian, of strength (π+2)/T, tends to 1 on both
vertical sides while killing exp(π T) on the two horizontal sides. -/
namespace ImbalancedChen.Part3.EndpointDampedRectangle20261112

noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped Interval
open NativeCuspCompactMellinSynthesis20261027 CompactHeightMellinInversion20261027

private def κ : ℝ := Real.pi+2
private def corner (T : ℝ) (s : ℂ) := 1+((s-(1/2 : ℂ))/(T : ℂ))^2
private def gauss (T : ℝ) (s : ℂ) := Complex.exp (((κ/T : ℝ) : ℂ)*((s-1)^2-1/4))
private def weight (T : ℝ) (s : ℂ) := gauss T s*corner T s

def flux (F : ℂ → ℂ) (T : ℝ) :=
  Complex.I*((∫ x : ℝ in (1/2)..(3/2),F (verticalParameter x T)) -
    ∫ x : ℝ in (1/2)..(3/2),F (verticalParameter x (-T)))

theorem rect (F : ℂ → ℂ) (D : DifferentiableOn ℂ F {s : ℂ | 1/2 ≤ s.re}) (T : ℝ) :
    (∫ t : ℝ in (-T)..T,F (verticalParameter (3/2) t)) -
      (∫ t : ℝ in (-T)..T,F (verticalParameter (1/2) t)) = -flux F T := by
  let R := ∫ t : ℝ in (-T)..T,F (verticalParameter (3/2) t)
  let L := ∫ t : ℝ in (-T)..T,F (verticalParameter (1/2) t)
  let A := ∫ x : ℝ in (1/2)..(3/2),F (verticalParameter x T)
  let B := ∫ x : ℝ in (1/2)..(3/2),F (verticalParameter x (-T))
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    (⟨1/2,-T⟩ : ℂ) (⟨3/2,T⟩ : ℂ)
    (D.mono (fun z hz => (show z.re ∈ [[(1/2 : ℝ),3/2]] from hz.1).1.trans' (by norm_num)))
  have J : B-A+Complex.I*R-Complex.I*L = 0 := by
    simpa only [A,B,R,L,verticalParameter,Complex.real_smul,smul_eq_mul] using H
  have X : Complex.I*(R-L) = A-B := by linear_combination J
  change R-L = -(Complex.I*(A-B))
  rw [← X,← mul_assoc,Complex.I_mul_I,neg_one_mul,neg_neg]

private theorem norm_shift (x t : ℝ) :
    ‖verticalParameter x t-(1/2 : ℂ)‖ ≤ |x-1/2|+|t| := by
  have e : verticalParameter x t-(1/2 : ℂ) = ((x-1/2 : ℝ) : ℂ)+(t : ℂ)*I := by
    unfold verticalParameter
    push_cast
    ring
  rw [e]
  simpa only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] using
    norm_add_le (((x-1/2 : ℝ) : ℂ)) ((t : ℂ)*I)

private theorem gauss_le {T x t : ℝ} (hT : 0 < T) (hx : x ∈ Icc (1/2 : ℝ) (3/2)) :
    ‖gauss T (verticalParameter x t)‖ ≤ Real.exp (-(κ/T)*t^2) := by
  have hκ : 0 ≤ κ/T := div_nonneg (by dsimp [κ]; positivity) hT.le
  have V : ((verticalParameter x t-1)^2-1/4 : ℂ).re = (x-1)^2-t^2-1/4 := by
    norm_num [verticalParameter,pow_two,Complex.mul_re,Complex.mul_im] <;> ring
  rw [gauss,Complex.norm_exp,Complex.re_ofReal_mul,V]
  apply Real.exp_le_exp.mpr
  have X : (x-1)^2-t^2-1/4 ≤ -t^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
  nlinarith [mul_le_mul_of_nonneg_left X hκ]

private theorem vertical_weight {T c t : ℝ} (hT : 1 ≤ T) (hc : c ∈ Icc (1/2 : ℝ) (3/2))
    (ht : |t| ≤ T) : ‖weight T (verticalParameter c t)‖ ≤ 5 := by
  have hT' := zero_lt_one.trans_le hT
  have G : ‖gauss T (verticalParameter c t)‖ ≤ 1 := (gauss_le hT' hc).trans
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (by dsimp [κ]; positivity) hT'.le)) (sq_nonneg t)))
  have hdelta : |c-1/2| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hc.1)]; linarith [hc.2]
  have hnorm : ‖(verticalParameter c t-(1/2 : ℂ))/(T : ℂ)‖ ≤ 2 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hT'.le]
    apply (div_le_iff₀ hT').mpr
    linarith [norm_shift c t]
  have C : ‖corner T (verticalParameter c t)‖ ≤ 5 := by
    unfold corner
    apply (norm_add_le _ _).trans
    rw [norm_one,norm_pow]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hnorm 2]
  rw [weight,norm_mul]
  exact (mul_le_mul G C (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem horizontal_corner {T x t : ℝ} (hT : 1 ≤ T) (hx : x ∈ Icc (1/2 : ℝ) (3/2))
    (ht : |t| = T) : ‖corner T (verticalParameter x t)‖ ≤ 3*(x-1/2) := by
  let u := (x-1/2)/T
  let v := t/T
  have hT' := zero_lt_one.trans_le hT
  have h₀ : 0 ≤ u := div_nonneg (sub_nonneg.mpr hx.1) hT'.le
  have hu : u ≤ x-1/2 := div_le_self (sub_nonneg.mpr hx.1) hT
  have hu₁ : u ≤ 1 := by linarith [hx.2]
  have hv : |v| = 1 := by simp [v,abs_div,ht,abs_of_pos hT',hT'.ne']
  have hvs : (v : ℂ)^2 = 1 := by
    exact_mod_cast (show v^2=1 by nlinarith [sq_abs v,congrArg (fun r : ℝ => r^2) hv])
  have e : (verticalParameter x t-(1/2 : ℂ))/(T : ℂ) = (u : ℂ)+(v : ℂ)*I := by
    dsimp [u,v,verticalParameter]
    push_cast
    ring
  have H : corner T (verticalParameter x t) = (u : ℂ)*((u : ℂ)+2*(v : ℂ)*I) := by
    rw [corner,e]
    calc
      _ = (1-(v : ℂ)^2)+(u : ℂ)*((u : ℂ)+2*(v : ℂ)*I) := by rw [add_sq,mul_pow,Complex.I_sq]; ring
      _ = _ := by rw [hvs]; ring
  rw [H,norm_mul,Complex.norm_real,Real.norm_of_nonneg h₀]
  have L := norm_add_le (u : ℂ) (2*(v : ℂ)*I)
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg h₀,hv] at L
  nlinarith [mul_le_mul_of_nonneg_left L h₀,mul_nonneg h₀ (sub_nonneg.mpr hu₁)]

private theorem weight_tendsto (s : ℂ) : Tendsto (fun T : ℝ => weight T s) atTop (𝓝 1) := by
  have H : Tendsto (fun T : ℝ => ((T⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  have Q := ((tendsto_const_nhds.mul H).mul_const ((s-1)^2-1/4) :
    Tendsto (fun T : ℝ => ((κ : ℂ)*((T⁻¹ : ℝ) : ℂ))*((s-1)^2-1/4)) atTop _)
  have R := (tendsto_const_nhds.add ((tendsto_const_nhds.mul H).pow 2) :
    Tendsto (fun T : ℝ => 1+((s-(1/2 : ℂ))*((T⁻¹ : ℝ) : ℂ))^2) atTop _)
  simpa [weight,gauss,corner,div_eq_mul_inv] using (Complex.continuous_exp.continuousAt.tendsto.comp Q).mul R

private theorem vertical_limit {F : ℂ → ℂ} {c : ℝ} (hc : c ∈ Icc (1/2 : ℝ) (3/2))
    (J : Integrable (fun t : ℝ => F (verticalParameter c t))) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T, weight T (verticalParameter c t)*F (verticalParameter c t))
      atTop (𝓝 (∫ t : ℝ,F (verticalParameter c t))) := by
  let V := fun T t : ℝ => weight T (verticalParameter c t)*F (verticalParameter c t)
  let K := fun T : ℝ => Ioc (-T) T
  let p := fun T : ℝ => (K T).indicator (V T)
  have H := tendsto_integral_filter_of_dominated_convergence (l := atTop (α := ℝ))
    (F := p) (f := fun t => F (verticalParameter c t)) (fun t => 5*‖F (verticalParameter c t)‖)
    (Eventually.of_forall (fun T => (show AEStronglyMeasurable (V T) from
      (show Continuous (fun t => weight T (verticalParameter c t)) by
        unfold weight gauss corner verticalParameter; fun_prop).aestronglyMeasurable.mul J.aestronglyMeasurable
      ).indicator measurableSet_Ioc))
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      apply Eventually.of_forall
      intro t
      by_cases ht : t ∈ K T
      · rw [p,indicator_of_mem ht]
        exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right
          (vertical_weight hT hc (abs_le.mpr ⟨ht.1.le,ht.2⟩)) (norm_nonneg _))
      · simp [p,ht] <;> positivity)
    (J.norm.const_mul 5) (by
      apply Eventually.of_forall
      intro t
      have W := (weight_tendsto (verticalParameter c t)).mul_const (F (verticalParameter c t))
      apply (show Tendsto (fun T : ℝ => V T t) atTop (𝓝 (F (verticalParameter c t))) by simpa [V] using W).congr'
      filter_upwards [eventually_gt_atTop |t|] with T hT
      have ht : t ∈ K T := ⟨by linarith [neg_abs_le t],(le_abs_self t).trans hT.le⟩
      simp [p,ht])
  apply H.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [p,integral_indicator measurableSet_Ioc,intervalIntegral.integral_of_le (by linarith : -T ≤ T)] <;> rfl

private theorem horizontal_limit {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (J : ∀ x ∈ Icc (1/2 : ℝ) (3/2), ∀ t : ℝ, 1 ≤ |t| →
      (x-1/2)*‖F (verticalParameter x t)‖ ≤ C*Real.exp (Real.pi*|t|)) (sgn : Bool) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (1/2)..(3/2), weight T (verticalParameter x (if sgn then T else -T))*
      F (verticalParameter x (if sgn then T else -T))) atTop (𝓝 0) := by
  have L : Tendsto (fun T : ℝ => (3*C)*Real.exp (-2*T)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))).const_mul (3*C)
  apply squeeze_zero_norm' _ L
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  let t := if sgn then T else -T
  have hT' := zero_lt_one.trans_le hT
  have ht : |t| = T := by unfold t; split <;> simp [abs_of_pos hT']
  have HH (x : ℝ) (hx : x ∈ Icc (1/2 : ℝ) (3/2)) :
      ‖weight T (verticalParameter x t)*F (verticalParameter x t)‖ ≤ (3*C)*Real.exp (-2*T) := by
    have t₂ : t^2 = T^2 := by rw [← ht,sq_abs]
    have H := gauss_le (t := t) hT' hx
    rw [t₂,show -(κ/T)*T^2 = -κ*T by field_simp [hT'.ne']] at H
    have X := J x hx t (by simpa only [ht] using hT)
    rw [ht] at X
    have Y := mul_le_mul_of_nonneg_right (horizontal_corner hT hx ht) (norm_nonneg (F (verticalParameter x t)))
    have Z : ‖corner T (verticalParameter x t)‖*‖F (verticalParameter x t)‖ ≤
        3*(C*Real.exp (Real.pi*T)) := by linarith [Y.trans_eq (mul_assoc _ _ _),X]
    rw [weight,norm_mul,norm_mul,mul_assoc]
    apply (mul_le_mul H Z (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le).trans_eq
    rw [show Real.exp (-κ*T)*(3*(C*Real.exp (Real.pi*T))) =
      (3*C)*(Real.exp (-κ*T)*Real.exp (Real.pi*T)) by ring,← Real.exp_add]
    congr 2
    unfold κ
    ring
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1/2 : ℝ)) (b := 3/2)
    (fun x hx => HH x (Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 3/2)] using hx)))
  simpa only [t,show |(3/2 : ℝ)-1/2|=1 by norm_num,mul_one] using H

/-- The analysis lemma used below on the actual regularized scalar.
The majorant is first power in the distance to the left side; the
individual horizontal integral need not admit its reciprocal as an
integrable majorant up to that side. -/
theorem vertical_equality (F : ℂ → ℂ) (D : DifferentiableOn ℂ F {s : ℂ | 1/2 ≤ s.re})
    (L : Integrable (fun t : ℝ => F (verticalParameter (1/2) t)))
    (R : Integrable (fun t : ℝ => F (verticalParameter (3/2) t)))
    (J : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (1/2 : ℝ) (3/2), ∀ t : ℝ, 1 ≤ |t| →
      (x-1/2)*‖F (verticalParameter x t)‖ ≤ C*Real.exp (Real.pi*|t|)) :
    (∫ t : ℝ,F (verticalParameter (3/2) t)) = ∫ t : ℝ,F (verticalParameter (1/2) t) := by
  obtain ⟨C,hC,H⟩ := J
  have A := horizontal_limit (F := F) hC H true
  have B := horizontal_limit (F := F) hC H false
  have G : Tendsto (fun T : ℝ => -flux (fun s => weight T s*F s) T) atTop (𝓝 0) := by
    simpa [flux] using ((A.sub B).const_mul I).neg
  have E := (vertical_limit (F := F) (c := 3/2) (by norm_num) R).sub
    (vertical_limit (F := F) (c := 1/2) (by norm_num) L)
  apply sub_eq_zero.mp
  apply tendsto_nhds_unique_of_eventuallyEq E G
  apply Eventually.of_forall
  intro T
  apply rect
  exact (show Differentiable ℂ (weight T) by unfold weight gauss corner; fun_prop).differentiableOn.mul D

end
end ImbalancedChen.Part3.EndpointDampedRectangle20261112
