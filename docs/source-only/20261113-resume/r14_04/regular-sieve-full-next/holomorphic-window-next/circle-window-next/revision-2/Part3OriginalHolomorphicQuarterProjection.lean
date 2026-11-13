import ImbalancedChen.Part3OriginalHolomorphicCircleProjection
import ImbalancedChen.Part3OriginalHolomorphicLongModulus

/-! Integration by parts and the two reflections turn the circle Poisson
kernel into the exact quarter-circle amplitude of the physical estimate. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicQuarterProjection20261113
open Real Set MeasureTheory
open OriginalHolomorphicOddWindow20261113 (amplitude correctedAmplitude)
open OriginalHolomorphicLongModulus20261113 (rawWindow)
open OriginalHolomorphicWindowMoment20261113 (amplitude_continuous)
open OriginalHolomorphicCircleProjection20261113

private def primitive (u y : ℝ) := radius u*sin y/denominator u y
private def part (u x y : ℝ) := radius u*(sin y)^2/denominator u y*cos (x*cos y)

private theorem rational_cont {u : ℝ} (hu : 0<u) : Continuous (rational u) :=
  ((continuous_const.mul continuous_cos).sub continuous_const).div
    ((continuous_const.sub (continuous_const.mul continuous_cos)).pow 2)
    (fun y => (sq_pos_of_pos (den_positive hu y)).ne')

private theorem part_cont {u : ℝ} (hu : 0<u) (x : ℝ) : Continuous (part u x) :=
  ((continuous_const.mul (continuous_sin.pow 2)).div
    (continuous_const.sub (continuous_const.mul continuous_cos)) (fun y => (den_positive hu y).ne')).mul
    (continuous_cos.comp (continuous_const.mul continuous_cos))

private theorem primitive_deriv {u : ℝ} (hu : 0<u) (y : ℝ) :
    HasDerivAt (primitive u) (rational u y) y := by
  have hD := (hasDerivAt_const y (1+(radius u)^2)).sub
    ((hasDerivAt_cos y).const_mul (2*radius u))
  apply (((hasDerivAt_sin y).const_mul (radius u)).div hD (den_positive hu y).ne').congr_deriv
  dsimp only [rational,denominator]
  congr 1
  linear_combination -(2*(radius u)^2)*sin_sq_add_cos_sq y

private theorem full_circle {u : ℝ} (hu : 0<u) (x : ℝ) :
    imaginaryHeight u x = (1/(2*π))*x*∫ y in (0:ℝ)..2*π, part u x y := by
  let G := fun y => sin (x*cos y)
  let G' := fun y => -(x*sin y)*cos (x*cos y)
  have DG (y : ℝ) : HasDerivAt G (G' y) y := by
    apply (((hasDerivAt_cos y).const_mul x).sin).congr_deriv
    dsimp only [G']; ring
  have CG : Continuous G' := (continuous_const.mul continuous_sin).neg.mul
    (continuous_cos.comp (continuous_const.mul continuous_cos))
  have P := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a:=(0:ℝ)) (b:=2*π) (u:=G) (u':=G') (v:=primitive u) (v':=rational u)
    (fun y _ => DG y) (fun y _ => primitive_deriv hu y)
    (CG.intervalIntegrable 0 _) ((rational_cont hu).intervalIntegrable 0 _)
  have P0 : primitive u 0=0 := by simp [primitive]
  have P1 : primitive u (2*π)=0 := by simp [primitive]
  rw [P0,P1,mul_zero,mul_zero,sub_zero,zero_sub] at P
  let f := fun y => rational u y*sin (x*cos y)
  have equal : (∫ y in (0:ℝ)..2*π, f y)=x*∫ y in (0:ℝ)..2*π, part u x y := by
    calc
      _ = ∫ y in (0:ℝ)..2*π,G y*rational u y :=
        intervalIntegral.integral_congr (fun _ _ => mul_comm _ _)
      _ = _ := by
        rw [P,←intervalIntegral.integral_neg,←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only [G',primitive,part]
        ring
  rw [native_circle_integral hu x]
  change (∫ y in (0:ℝ)..1,f ((2*π)*y))=_
  rw [intervalIntegral.integral_comp_mul_left f (by positivity : 2*π≠0),mul_zero,mul_one,equal]
  simp only [smul_eq_mul,one_div]
  ring

private theorem quarter_pair {u : ℝ} (hu : 0<u) (x y : ℝ) :
    part u x y+part u x (π-y)=amplitude u y*cos (x*cos y) := by
  let r := radius u
  let c := cos y
  let s := sin y
  let D := 1+r^2-2*r*c
  let D' := 1+r^2+2*r*c
  have d : 0<D := den_positive hu y
  have d' : 0<D' := by
    have h := den_positive hu (π-y)
    dsimp only [denominator] at h
    rw [cos_pi_sub] at h
    dsimp only [D',r,c]
    linarith only [h]
  have hyp := cosh_sq_sub_sinh_sq u
  have trig : s^2+c^2=1 := sin_sq_add_cos_sq y
  have den : 0<(sinh u)^2+s^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (sinh_pos_iff.mpr hu)) (sq_nonneg _)
  have id : 1+r^2=2*r*cosh u := by
    have h : Real.exp u*r=1 := by dsimp only [r,radius]; rw [←exp_add]; simp
    rw [Real.cosh_eq]
    dsimp only [r,radius] at h ⊢
    nlinarith only [h]
  have prod : D*D'=4*r^2*((sinh u)^2+s^2) := by
    dsimp only [D,D']
    rw [id]
    linear_combination 4*r^2*hyp - 4*r^2*trig
  have sum : D'+D=4*r*cosh u := by dsimp only [D,D']; nlinarith only [id]
  have core : r*s^2/D+r*s^2/D'=amplitude u y := by
    calc
      _ = r*s^2*(D'+D)/(D*D') := by field_simp [d.ne',d'.ne'] <;> ring
      _ = _ := by
        rw [sum,prod]
        dsimp only [amplitude]
        have rp : 0<r := exp_pos _
        change _=cosh u*s^2/((sinh u)^2+s^2)
        field_simp [rp.ne',den.ne'] <;> ring
  dsimp only [part,denominator]
  rw [sin_pi_sub,cos_pi_sub,mul_neg,cos_neg]
  change r*s^2/D*cos (x*c)+r*s^2/(1+r^2-2*r*(-c))*cos (x*c)=_
  rw [show 1+r^2-2*r*(-c)=D' by dsimp only [D']; ring,←add_mul,core]

private theorem reflections {u : ℝ} (hu : 0<u) (x : ℝ) :
    (∫ y in (0:ℝ)..2*π, part u x y) =
      2*∫ y in (0:ℝ)..π/2, amplitude u y*cos (x*cos y) := by
  let p := part u x
  have co : Continuous p := part_cont hu x
  have reflect (y : ℝ) : p (2*π-y)=p y := by
    dsimp only [p,part,denominator]
    rw [sin_two_pi_sub,cos_two_pi_sub,neg_sq]
  have first := intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=π) p (2*π)
  rw [show 2*π-π=π by ring,sub_zero] at first
  simp only [reflect] at first
  have halves := intervalIntegral.integral_add_adjacent_intervals
    (co.intervalIntegrable 0 π) (co.intervalIntegrable π (2*π))
  have second := intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=π/2) p π
  rw [show π-π/2=π/2 by ring,sub_zero] at second
  have quarters := intervalIntegral.integral_add_adjacent_intervals
    (co.intervalIntegrable 0 (π/2)) (co.intervalIntegrable (π/2) π)
  have refc : Continuous (fun y : ℝ => p (π-y)) := co.comp (continuous_const.sub continuous_id)
  have Q : (∫ y in (0:ℝ)..π/2,p y)+(∫ y in (0:ℝ)..π/2,p (π-y)) =
      ∫ y in (0:ℝ)..π/2,amplitude u y*cos (x*cos y) := by
    rw [←intervalIntegral.integral_add (co.intervalIntegrable _ _) (refc.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun y _ => quarter_pair hu x y)
  change (∫ y in (0:ℝ)..2*π,p y)=_
  linarith only [first,halves,second,quarters,Q]

theorem native_quarter {u : ℝ} (hu : 0<u) (x : ℝ) :
    imaginaryHeight u x=(x/π)*(∫ y in (0:ℝ)..π/2,amplitude u y*cos (x*cos y)) := by
  rw [full_circle hu x,reflections hu x]
  ring

/-- The exact corrected odd Petersson Bessel window at every x and
0<t. The original trace sign is -2 times the selected imaginary part. -/
theorem corrected_native_window {t : ℝ} (ht : 0<t) (x : ℝ) :
    -2*(imaginaryHeight t x-exp (2-t)*imaginaryHeight 2 x)= -(2/π)*rawWindow t x := by
  have c : Continuous (fun y => cos (x*cos y)) := continuous_cos.comp (continuous_const.mul continuous_cos)
  have a := ((amplitude_continuous ht).mul c).intervalIntegrable (0:ℝ) (π/2)
  have b := ((amplitude_continuous (by norm_num : (0:ℝ)<2)).mul c).intervalIntegrable (0:ℝ) (π/2)
  rw [native_quarter ht,native_quarter (by norm_num : (0:ℝ)<2)]
  simp only [rawWindow,correctedAmplitude,sub_mul,mul_assoc]
  rw [intervalIntegral.integral_sub a (b.const_mul _),intervalIntegral.integral_const_mul]
  ring

end ImbalancedChen.Part3.OriginalHolomorphicQuarterProjection20261113
end
