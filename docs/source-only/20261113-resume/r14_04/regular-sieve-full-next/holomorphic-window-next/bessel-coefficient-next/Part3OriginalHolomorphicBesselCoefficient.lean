import ImbalancedChen.Part3ActualGeneralJBessel
import ImbalancedChen.Part3CompletedKWeightedIntegral

/-! Jacobi--Anger at the exact nonnegative integer order of the native
Petersson kernel. The Fourier coefficient is on the unit-period circle. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicBesselCoefficient20261113
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly (generalJ generalJTerm generalJ_hasSum)
open GeneralComplexISeriesSourceOnly (generalICoeff)
open CompletedKWeightedIntegral20261026b
  (integerPhase integerPhase_norm integerPhase_integral integerPhase_continuous)

private def et (w : ℂ) (n : ℕ) : ℂ := w^n/(n.factorial:ℂ)

private theorem exponential (w : ℂ) : HasSum (et w) (exp w) := by
  simpa only [et,Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w

private theorem et_norm (w : ℂ) :
    Summable (fun n => ‖et w n‖) := by
  have h : HasSum (fun n : ℕ => ‖w‖^n/(n.factorial:ℝ)) (Real.exp ‖w‖) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ‖w‖
  simpa only [et,norm_div,norm_pow,Complex.norm_natCast] using h.summable

private def z (x : ℝ) : ℂ := ((x/2:ℝ):ℂ)*I

private def diagonal (h : ℕ) (x : ℝ) (j : ℕ) :=
  et (z x) j*et (z x) (h+j)

private theorem diagonal_bessel (h : ℕ) (x : ℝ) :
    HasSum (diagonal h x) (I^h*generalJ (h:ℂ) x) := by
  apply ((generalJ_hasSum (by simp : -1<(h:ℂ).re) x).mul_left (I^h)).congr_fun
  intro j
  have H : Gamma ((j:ℂ)+(h:ℂ)+1) = ((h+j).factorial:ℂ) := by
    simpa only [Nat.cast_add,add_comm (h:ℂ) j] using Gamma_nat_eq_factorial (h+j)
  have p : I^j * I^j=(-1:ℂ)^j := by rw [←mul_pow,←sq,I_sq]
  dsimp only [diagonal,et,z]
  rw [generalJTerm,Complex.cpow_natCast,generalICoeff,H]
  simp only [mul_pow,pow_add,pow_mul]
  rw [show ((((x/2:ℝ):ℂ)^2)^j)=(((x/2:ℝ):ℂ)^j)^2 by rw [←pow_mul,←pow_mul,Nat.mul_comm 2 j]]
  rw [←p]
  ring

private def F (h : ℕ) (x : ℝ) (ij : ℕ×ℕ) (y : ℝ) : ℂ :=
  (et (z x) ij.1*et (z x) ij.2)*integerPhase ((ij.2:ℤ)-(ij.1:ℤ)-(h:ℤ)) y

private theorem phases (h j k : ℕ) (y : ℝ) :
    integerPhase (-1) y ^ j * integerPhase 1 y ^ k * integerPhase (-(h:ℤ)) y =
      integerPhase ((k:ℤ)-(j:ℤ)-(h:ℤ)) y := by
  unfold integerPhase
  rw [←exp_nat_mul,←exp_nat_mul,←exp_add,←exp_add]
  congr 1
  push_cast <;> ring

private theorem F_eq (h : ℕ) (x y : ℝ) (ij : ℕ×ℕ) :
    F h x ij y = et (z x*integerPhase (-1) y) ij.1*
      et (z x*integerPhase 1 y) ij.2*integerPhase (-(h:ℤ)) y := by
  dsimp only [F,et]
  rw [←phases]
  simp only [mul_pow]
  ring

def wave (x y : ℝ) : ℂ := exp ((x*Real.cos (2*Real.pi*y):ℝ)*I)

private theorem sum_at (h : ℕ) (x y : ℝ) :
    (∑' ij : ℕ×ℕ, F h x ij y)=wave x y*integerPhase (-(h:ℤ)) y := by
  simp only [F_eq,tsum_mul_right]
  rw [←tsum_mul_tsum_of_summable_norm (et_norm _) (et_norm _),
    (exponential _).tsum_eq,(exponential _).tsum_eq,←exp_add]
  have p : integerPhase (-1) y + integerPhase 1 y = 2*(Real.cos (2*Real.pi*y):ℂ) := by
    have n : 2*Real.pi*((-1:ℤ):ℝ)*y= -(2*Real.pi*y) := by push_cast <;> ring
    have o : 2*Real.pi*((1:ℤ):ℝ)*y=2*Real.pi*y := by push_cast <;> ring
    simp only [integerPhase,n,o,Complex.ofReal_neg,exp_mul_I,cos_neg,sin_neg,ofReal_cos]
    ring
  rw [←mul_add,p]
  unfold wave z
  apply congrArg (fun w : ℂ => exp w*integerPhase (-(h:ℤ)) y)
  push_cast <;> ring

private theorem F_integral (h : ℕ) (x : ℝ) (ij : ℕ×ℕ) :
    (∫ y in (0:ℝ)..1, F h x ij y) =
      if ij.2=h+ij.1 then et (z x) ij.1*et (z x) ij.2 else 0 := by
  rw [F,intervalIntegral.integral_const_mul,integerPhase_integral]
  by_cases e : ij.2=h+ij.1
  · have i : (ij.2:ℤ)-(ij.1:ℤ)-(h:ℤ)=0 := by omega
    rw [if_pos i,if_pos e,mul_one]
  · have i : (ij.2:ℤ)-(ij.1:ℤ)-(h:ℤ)≠0 := by omega
    rw [if_neg i,if_neg e,mul_zero]

/-- Exact coefficient of the compensated angular exponential, including
the phase I^h and the original complex generalJ at order h=k−1. -/
theorem integer_bessel_coefficient (h : ℕ) (x : ℝ) :
    (∫ y in (0:ℝ)..1, wave x y*integerPhase (-(h:ℤ)) y)=I^h*generalJ (h:ℂ) x := by
  let T := fun ij : ℕ×ℕ => et (z x) ij.1*et (z x) ij.2
  have major : Summable (fun ij : ℕ×ℕ => ‖T ij‖) :=
    (et_norm (z x)).mul_norm (et_norm (z x))
  have hint (ij : ℕ×ℕ) : Integrable (F h x ij) (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((continuous_const.mul (integerPhase_continuous _)).intervalIntegrable (0:ℝ) 1).1
  have masses (ij : ℕ×ℕ) : (∫ y in Ioc (0:ℝ) 1, ‖F h x ij y‖)=‖T ij‖ := by
    rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    simp only [F,norm_mul,integerPhase_norm,mul_one,T]
    simp
  have H : Summable (fun ij : ℕ×ℕ => ∫ y in Ioc (0:ℝ) 1, ‖F h x ij y‖) := by
    simpa only [masses] using major
  let K := fun ij : ℕ×ℕ => if ij.2=h+ij.1 then T ij else 0
  have S : Summable K := by
    have Hnorm : Summable (fun ij => ‖K ij‖) := by
      apply major.of_nonneg_of_le (fun _ => norm_nonneg _)
      intro ij
      dsimp only [K]
      split
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (T ij)
    exact Hnorm.of_norm
  calc
    _ = ∫ y in Ioc (0:ℝ) 1, ∑' ij : ℕ×ℕ, F h x ij y := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      simp only [sum_at]
    _ = ∑' ij : ℕ×ℕ, ∫ y in Ioc (0:ℝ) 1, F h x ij y :=
      (integral_tsum_of_summable_integral_norm hint H).symm
    _ = ∑' ij, K ij := by
      apply tsum_congr
      intro ij
      rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      exact F_integral h x ij
    _ = ∑' j, diagonal h x j := by
      rw [S.tsum_prod]
      apply tsum_congr
      intro j
      simp only [K,tsum_ite_eq,T,diagonal]
    _ = _ := (diagonal_bessel h x).tsum_eq

end ImbalancedChen.Part3.OriginalHolomorphicBesselCoefficient20261113
end
