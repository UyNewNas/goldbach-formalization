import ImbalancedChen.Part3OriginalSwitchedSeparatedNativeSlots

/-! Uniform odd-order moment budget on every inverse switching scale
and every radial Fourier mode of the real four-variable expansion. -/
namespace ImbalancedChen.Part3.OriginalSwitchedUniformHolBudget20261113
noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators
open P3Period64NativeReconstructionSourceOnly (spectralMode spectralTest norm_e)
open OriginalSwitchedCutoffModes20261113 (mode)
open ActualPositiveHolomorphicWeights20261112
open OriginalFullModulusTestJets20261102 (spectralTest_div_q_integrable spectralTest_tsupport_strict)

private def bill (V : ℝ) := ∫ x in Ioi (0:ℝ),‖spectralTest (mode 0) V x/(x:ℂ)‖

private theorem scale_bill {V : ℝ} (vp : 0<V) : bill V=bill 1 := by
  let F := fun x : ℝ => ‖spectralTest (mode 0) V x/(x:ℂ)‖
  have h := integral_comp_mul_left_Ioi' F 0 vp
  rw [mul_zero] at h
  change (∫ x in Ioi (0:ℝ),F x)=_
  rw [←h,←integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have cancel : V*x/V=x := by field_simp [vp.ne']
  simp only [F,bill,spectralTest,cancel,div_one,smul_eq_mul,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hx,abs_of_pos (mul_pos vp hx)]
  field_simp [vp.ne',hx.ne'] <;> ring

private def K := 4*expMass 16*bill 1

private theorem kp : 0≤K := mul_nonneg (mul_nonneg (by norm_num) (expMass_nonneg _))
  (integral_nonneg fun _ => norm_nonneg _)

private theorem odd (l : ℤ) {Y : ℝ} (y1 : 1≤Y) (h : ℕ) :
    ‖holWeight h (spectralTest (mode l) Y⁻¹)‖≤K*(8:ℝ)^(2*h+1)/((2*h+1).factorial:ℝ) := by
  let V := Y⁻¹
  have yp : 0<Y := zero_lt_one.trans_le y1
  have vp : 0<V := inv_pos.mpr yp
  have v1 : V≤1 := by
    change Y⁻¹≤1
    rw [←one_div]
    exact (div_le_one yp).mpr y1
  let n := 2*h+1
  let D := ((8:ℝ)^n/(n.factorial:ℝ))*expMass 16
  have di : 0≤D := mul_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) (expMass_nonneg _)
  let F := fun x : ℝ => ‖spectralTest (mode 0) V x/(x:ℂ)‖
  have E : ‖moment n (spectralTest (mode l) V)‖≤D*bill 1 := by
    calc
      _ ≤ ∫ x in Ioi (0:ℝ),D*F x := by
        apply norm_integral_le_of_norm_le (((spectralTest_div_q_integrable (mode 0) vp).norm.integrableOn
          (s:=Ioi (0:ℝ))).const_mul D)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        by_cases z : spectralTest (mode l) V x=0
        · simp only [z,mul_zero,zero_div,norm_zero]
          exact mul_nonneg di (norm_nonneg _)
        · have cap := (spectralTest_tsupport_strict _ vp (subset_tsupport _ z)).2
          have j := intJ_bound n hx.le (show x≤16 by linarith only [cap,v1])
          rw [mul_div_assoc,norm_mul]
          have e : ‖spectralTest (mode l) V x/(x:ℂ)‖=F x := by
            simp only [F,spectralTest,spectralMode,norm_div,norm_mul,norm_e,mul_one]
          rw [e]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          simpa only [show (16:ℝ)/2=8 by norm_num,D] using j
      _ = D*bill 1 := by rw [integral_const_mul,←scale_bill vp] <;> rfl
  have P := mul_le_mul_of_nonneg_left E (by norm_num : (0:ℝ)≤4)
  simpa only [holWeight,norm_mul,norm_pow,Complex.norm_I,one_pow,Complex.norm_ofNat,mul_one,V,n]
    using (P.trans_eq (by change 4*(D*bill 1)=K*(8:ℝ)^n/(n.factorial:ℝ);dsimp only [K,D];ring))

/-- Paying an entire single-weight sieve at height 2h+1 costs a
quadratic factor. The common majorant already includes that factor. -/
theorem uniform_order_budget :
    ∃ b : ℕ→ℝ,Summable b ∧ (∀ h,0≤b h) ∧ ∀ (l : ℤ) (Y : ℝ),1≤Y → ∀ h : ℕ,
      ((2*h+1:ℕ):ℝ)^2*‖holWeight h (spectralTest (mode l) Y⁻¹)‖≤b h := by
  let b := fun h : ℕ => K*(32:ℝ)^(2*h+1)/((2*h+1).factorial:ℝ)
  have S := (Real.summable_pow_div_factorial (32:ℝ)).comp_injective
    (show Function.Injective (fun h : ℕ => 2*h+1) from fun _ _ p => by omega)
  refine ⟨b,by simpa only [b,mul_div_assoc] using S.mul_left K,
    fun h => div_nonneg (mul_nonneg kp (by positivity)) (Nat.cast_nonneg _),?_⟩
  intro l Y y1 h
  let n := 2*h+1
  have natbound (v : ℕ) : v≤2^v := by
    induction v with
    | zero => decide
    | succ v ih =>
      rw [pow_succ]
      have := Nat.pow_pos (by decide : 0<(2:ℕ)) v
      omega
  have v0 : (n:ℝ)≤(2:ℝ)^n := by exact_mod_cast natbound n
  have sqn : (n:ℝ)^2≤(4:ℝ)^n := (pow_le_pow_left₀ (Nat.cast_nonneg n) v0 2).trans_eq (by
    rw [←pow_mul,Nat.mul_comm n 2,pow_mul,show (2:ℝ)^2=4 by norm_num])
  have H := mul_le_mul_of_nonneg_left (odd l y1 h) (sq_nonneg (n:ℝ))
  let W := K*(8:ℝ)^n/(n.factorial:ℝ)
  have wp : 0≤W := div_nonneg (mul_nonneg kp (by positivity)) (Nat.cast_nonneg _)
  calc
    _ ≤ (n:ℝ)^2*W := H
    _ ≤ (4:ℝ)^n*W := mul_le_mul_of_nonneg_right sqn wp
    _ = b h := by
      change (4:ℝ)^n*(K*8^n/(n.factorial:ℝ))=K*32^n/(n.factorial:ℝ)
      rw [show (32:ℝ)=4*8 by norm_num,mul_pow];ring

end
end ImbalancedChen.Part3.OriginalSwitchedUniformHolBudget20261113
