import ImbalancedChen.Part3OriginalSwitchedSchwartzPrices

/-! A polynomial price in the period frequency for the cubically
weighted regular transform at each fixed positive physical scale. -/
namespace ImbalancedChen.Part3.OriginalSwitchedRegularModePrice20261113
noncomputable section
open Set Complex FourierTransform
open scoped FourierTransform Topology BigOperators ContDiff
open OriginalSwitchedSchwartzPrices20261113
open OriginalSwitchedCutoffModes20261113 (mode)
open OriginalFullModulusTestJets20261102 (nativePhase nativePhase_contDiff nativePhase_iteratedDeriv)
open ActualExceptionalJLargeTransform20261102 (modeFrequency modeFrequency_norm_le)
open P3Period64NativeReconstructionSourceOnly (spectralMode spectralTest e norm_e)
open ActualPositiveCosineProfile20261112 (testDiv cosineTest profile)
open ActualPrescribedPositiveJ20261112 (weightSchwartz regular_transform positiveWeight)
open KHeightSchwartzP3SourceOnly KFullLineFourierBridgeSourceOnly
open private physical evenDiv frequency div_compact div_smooth from ImbalancedChen.Part3ActualPositiveCosineProfile

private def wave (k : ℤ) (Y x : ℝ) := nativePhase (mode k) (Y⁻¹*x)

private theorem wave_smooth (k : ℤ) (Y : ℝ) : ContDiff ℝ ∞ (wave k Y) :=
  (nativePhase_contDiff _).comp (contDiff_const.mul contDiff_id)

private theorem wave_price (k : ℤ) {Y : ℝ} (yp : 0<Y) (b : ℕ) (x : ℝ) :
    ‖iteratedDeriv b (wave k Y) x‖≤(Y⁻¹*(2*Real.pi))^b*(weight k)^b := by
  have f : ‖modeFrequency (mode k)‖≤2*Real.pi*weight k := by
    apply (modeFrequency_norm_le (mode k)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simp only [mode,ite_true,weight]
    linarith
  change ‖iteratedDeriv b (fun x : ℝ => nativePhase (mode k) (Y⁻¹*x)) x‖≤_
  rw [show (fun x : ℝ => nativePhase (mode k) (Y⁻¹*x))=
      (fun x : ℝ => nativePhase (mode k) (Y⁻¹ • x)) by rfl,
    iteratedDeriv_comp_const_smul ((nativePhase_contDiff _).of_le (by simp)),
    nativePhase_iteratedDeriv]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr yp.le) _),
    norm_mul,norm_pow,nativePhase,norm_e,mul_one]
  calc
    Y⁻¹^b*‖modeFrequency (mode k)‖^b ≤ Y⁻¹^b*(2*Real.pi*weight k)^b :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) f b) (by positivity)
    _ = _ := by ring

private def front (k : ℤ) {Y : ℝ} (yp : 0<Y) : Space :=
  (div_compact (mode k) yp).toSchwartzMap (div_smooth (mode k) yp)

private theorem factor (k : ℤ) {Y : ℝ} (yp : 0<Y) :
    (front k yp:ℝ→ℂ)=(front 0 yp:ℝ→ℂ)*wave k Y := by
  funext x
  change spectralTest (mode k) Y x/(x:ℂ)=spectralTest (mode 0) Y x/(x:ℂ)*nativePhase (mode k) (Y⁻¹*x)
  simp only [spectralTest,spectralMode,nativePhase,mode,ite_true,Int.cast_zero,zero_div,zero_mul]
  simp only [e,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one,div_eq_mul_inv]
  rw [mul_comm x Y⁻¹]
  ring

private theorem front_control {Y : ℝ} (yp : 0<Y) : Controlled (fun k => front k yp) := by
  intro a b
  let K := Y⁻¹*(2*Real.pi)
  let A := fun i : ℕ => ((b.choose i:ℝ)*SchwartzMap.seminorm ℂ a i (front 0 yp))*K^(b-i)
  have nn (i : ℕ) : 0≤A i := by dsimp [A,K];positivity
  refine ⟨b,∑ i ∈ Finset.range (b+1),A i,Finset.sum_nonneg (fun i _ => nn i),fun k => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℂ a b _ (mul_nonneg (Finset.sum_nonneg fun i _ => nn i)
    (pow_nonneg (by linarith [w_one k]) b))
  intro x
  rw [factor k yp,iteratedDeriv_mul ((front 0 yp).smooth b).contDiffAt
    ((wave_smooth k Y).of_le (by simp)).contDiffAt]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg _) a)).trans
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul,Complex.norm_natCast]
  have p := SchwartzMap.le_seminorm' ℂ a i (front 0 yp) x
  have h := wave_price k yp (b-i) x
  have e := pow_le_pow_right₀ (w_one k) (Nat.sub_le b i)
  calc
    _ = ((b.choose i:ℝ)*(|x|^a*‖iteratedDeriv i (front 0 yp) x‖))*‖iteratedDeriv (b-i) (wave k Y) x‖ := by ring
    _ ≤ ((b.choose i:ℝ)*SchwartzMap.seminorm ℂ a i (front 0 yp))*(K^(b-i)*(weight k)^(b-i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left p (Nat.cast_nonneg _)) h (norm_nonneg _) (by positivity)
    _ ≤ A i*(weight k)^b := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_left e (nn i)

private theorem transform_control {Y : ℝ} (yp : 0<Y) :
    Controlled (fun k => weightSchwartz (mode k) yp) := by
  let neg : Space→L[ℂ]Space := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E:=ℝ))
  have H := front_control yp
  have P : Controlled (fun k => physical (mode k) yp) := by
    have A := add_control H (map_control H neg)
    have E (k : ℤ) : physical (mode k) yp=front k yp+neg (front k yp) := by ext x; rfl
    simpa only [E] using A
  let T : Space→L[ℂ]Space := (1/2:ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ frequency).comp (fourierCLM ℂ Space)
  have C : Controlled (fun k => cosineTest (mode k) yp) := map_control P T
  let W : Space→L[ℂ]Space := (4:ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ heightFrequencyEquiv).comp (fourierCLM ℂ Space)
  exact map_control (hyperbolic_control C) W

/-- The polynomial degree and coefficient precede all period modes,
the real spectral parameter, the quotient level and the Fourier marks.
The numerical coefficient may depend on the fixed scale. -/
theorem regular_mode_price {Y : ℝ} (yp : 0<Y) :
    ∃ (r : ℕ) (C : ℝ),0≤C ∧ ∀ (k : ℤ) (t : ℝ),
      (1+|t|)^3*‖positiveWeight (spectralTest (mode k) Y) t‖ ≤ C*(weight k)^r := by
  let U := fun k : ℤ => weightSchwartz (mode k) yp
  obtain ⟨r,C,c,B⟩ := price_scale (price_add (transform_control yp 0 0) (transform_control yp 3 0))
    (show 0≤(8:ℝ) by norm_num)
  refine ⟨r,C,c,fun k t => ?_⟩
  rw [(regular_transform (mode k) yp t).2]
  have p := SchwartzMap.norm_le_seminorm ℂ (U k) t
  have q := SchwartzMap.norm_pow_mul_le_seminorm ℂ (U k) 3 t
  change (1+|t|)^3*‖U k t‖≤_
  apply le_trans _ (B k)
  simp only [Real.norm_eq_abs] at q
  by_cases h : |t|≤1
  · have e : (1+|t|)^3≤(2:ℝ)^3 := by gcongr;linarith
    have v := mul_le_mul e p (norm_nonneg _) (by positivity)
    linarith only [v,show 0≤SchwartzMap.seminorm ℂ 3 0 (U k) from apply_nonneg _ _]
  · have e : (1+|t|)^3≤(2*|t|)^3 := by gcongr;linarith
    have v := mul_le_mul_of_nonneg_right e (norm_nonneg (U k t))
    nlinarith only [v,q,show 0≤SchwartzMap.seminorm ℂ 0 0 (U k) from apply_nonneg _ _]

end
end ImbalancedChen.Part3.OriginalSwitchedRegularModePrice20261113
