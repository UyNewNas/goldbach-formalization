import ImbalancedChen.Part3FixedMarkEulerSummability
import ImbalancedChen.Part3OriginalNonzeroCuspOneSource
import ImbalancedChen.Part3GeneralJSymmetricPoissonIntegral

/-! The original Γ₀(z) infinity/cusp-one matrix sum, at the original positive
moduli d√z. The geometric weight-two series only; no unfolding theorem. -/
noncomputable section
namespace ImbalancedChen.Part3.FixedMarkTail
open Classical Set OriginalSmoothPoissonTail OriginalNonzeroCuspOneSource20261102
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open scoped BigOperators Interval

theorem cusp_one_le (z d : ℕ) [NeZero d] (hz : 0<z) (hc : z.Coprime d) (m n : ℤ) :
    ‖cuspOneMatrixSum z d hc m n‖ ≤ majorant m d := by
  rw [cuspOneMatrixSum_eq_phase_mul_kloosterman z d hz hc, norm_mul,
    P3Period64NativeReconstructionSourceOnly.norm_e, one_mul]
  have hu : IsUnit ((z : ℤ) : ZMod d) :=
    (Physical.isUnit_intCast_iff_natAbs_coprime (c := d) (z : ℤ)).mpr (by simpa using hc)
  apply physical_unit_le_majorant
  simpa [inverseResidue] using hu.inv

/-- The order-one Gamma prefactor need not be evaluated to prove absolute
convergence. The resulting global bound is linear in its argument. -/
def orderOneConstant : ℝ :=
  ‖((Real.sqrt Real.pi : ℂ) * Complex.Gamma ((1:ℂ)+1/2))⁻¹‖

theorem generalJ_one_norm_le {q : ℝ} (hq : 0<q) :
    ‖generalJ 1 q‖ ≤ q * orderOneConstant := by
  let F (t : ℝ) : ℂ := Complex.exp (Complex.I * (q:ℂ) * (t:ℂ)) *
    (1-(t:ℂ)^(2:ℕ)) ^ ((1:ℂ)-1/2)
  have hf (t : ℝ) (ht : t ∈ Ι (-1:ℝ) 1) : ‖F t‖ ≤ 1 := by
    have ht' : t ∈ Ioc (-1:ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using ht
    have hb : 0 ≤ 1-t^2 := by nlinarith [mul_nonneg (show 0 ≤ 1+t by linarith [ht'.1]) (show 0 ≤ 1-t by linarith [ht'.2])]
    have he : ‖Complex.exp (Complex.I * (q:ℂ) * (t:ℂ))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    unfold F
    rw [norm_mul, he, one_mul]
    have castb : (1-(t:ℂ)^(2:ℕ)) = ((1-t^2:ℝ):ℂ) := by push_cast <;> ring
    rw [castb, Complex.norm_cpow_eq_rpow_re_of_nonneg hb (by norm_num)]
    exact Real.rpow_le_one hb (by nlinarith [sq_nonneg t]) (by norm_num)
  have hI : ‖∫ t in (-1:ℝ)..1, F t‖ ≤ 2 := by
    convert intervalIntegral.norm_integral_le_of_norm_le_const hf using 1 <;> norm_num
  rw [generalJ_eq_symmetric_poisson_integral (nu := (1:ℂ)) (by norm_num) hq,
    Complex.cpow_one, div_eq_mul_inv, norm_mul, norm_mul]
  change (‖((q/2:ℝ):ℂ)‖ * orderOneConstant) * ‖∫ t in (-1:ℝ)..1, F t‖ ≤ _
  rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ q/2)]
  have hc : 0 ≤ orderOneConstant := norm_nonneg _
  calc
    _ ≤ (q/2 * orderOneConstant)*2 := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

def geometric (z : ℕ) (m h : ℤ) (A : ℝ) (d : ℕ) : ℂ :=
  if hd : d=0 then 0 else
    letI : NeZero d := ⟨hd⟩
    if hzd : z.Coprime d then
      let C : ℝ := (d:ℝ) * Real.sqrt (z:ℝ)
      cuspOneMatrixSum z d hzd m h / (C:ℂ) * generalJ 1 (A/C)
    else 0

theorem summable_original_geometric (z : ℕ) (hz : 0<z) {m : ℤ} (hm : m≠0)
    (h : ℤ) (A : ℝ) (hA : 0<A) :
    Summable (fun d : ℕ => ‖geometric z m h A d‖) := by
  let K := A * orderOneConstant / (z:ℝ)
  have hJ : 0 ≤ orderOneConstant := norm_nonneg _
  have hzR : 0 < (z:ℝ) := by exact_mod_cast hz
  have hs := (summable_majorant_price hm (δ:=0) (by norm_num)).mul_left K
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro d
  by_cases hd : d=0
  · simp [hd, geometric, price_zero]
  letI : NeZero d := ⟨hd⟩
  have hdR : 0 < (d:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hc : 0 < (d:ℝ)*Real.sqrt (z:ℝ) := mul_pos hdR (Real.sqrt_pos.mpr hzR)
  by_cases hzd : z.Coprime d
  · simp only [geometric, dif_neg hd, dif_pos hzd, norm_mul, norm_div,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
    have hprice : price m 0 d = majorant m d / (d:ℝ)^2 := by
      simp [price, hd, Real.rpow_neg hdR.le, Real.rpow_two, div_eq_mul_inv]
    rw [hprice]
    calc
      _ ≤ (majorant m d / ((d:ℝ)*Real.sqrt (z:ℝ))) *
            ((A/((d:ℝ)*Real.sqrt (z:ℝ)))*orderOneConstant) := by
        exact mul_le_mul (div_le_div_of_nonneg_right (cusp_one_le z d hz hzd m h) hc.le)
          (generalJ_one_norm_le (div_pos hA hc)) (norm_nonneg _)
          (div_nonneg (majorant_nonneg _ _) hc.le)
      _ = (A * orderOneConstant * majorant m d) /
          ((d:ℝ)^2 * (Real.sqrt (z:ℝ))^2) := by
        field_simp [hdR.ne', (Real.sqrt_pos.mpr hzR).ne'] <;> ring
      _ = _ := by
        rw [Real.sq_sqrt hzR.le]
        unfold K
        field_simp [hdR.ne', hzR.ne'] <;> ring
  · simp only [geometric, dif_neg hd, dif_neg hzd, norm_zero]
    exact mul_nonneg (by dsimp [K]; positivity) (price_nonneg _ _ _)

/-- Literal Petersson weight-two Bessel argument for positive markings. -/
theorem original_weight_two_absolute (z : ℕ) (hz : 0<z) (m h : ℤ) (hm : 0<m) (hh : 0<h) :
    Summable (fun d : ℕ => ‖geometric z m h
      (4 * Real.pi * Real.sqrt ((m:ℝ)*(h:ℝ))) d‖) := by
  apply summable_original_geometric z hz hm.ne'
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hhR : 0 < (h:ℝ) := by exact_mod_cast hh
  positivity

end ImbalancedChen.Part3.FixedMarkTail
