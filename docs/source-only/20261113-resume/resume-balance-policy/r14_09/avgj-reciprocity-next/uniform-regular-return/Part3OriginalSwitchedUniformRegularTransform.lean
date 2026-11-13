import ImbalancedChen.Part3OriginalSwitchedHyperbolicBudget
import ImbalancedChen.Part3OriginalSwitchedModeTransforms

/-! A joint principal-series bound for the two physical tests at every
switching scale Y≥1 and every real spectral parameter. -/
namespace ImbalancedChen.Part3.OriginalSwitchedUniformRegularTransform20261113
noncomputable section
open Set MeasureTheory Complex FourierTransform
open scoped FourierTransform Topology
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPrescribedPositiveJ20261112 (positiveWeight weightSchwartz regular_transform)
open ActualPositiveCosineProfile20261112 (profile)
open OriginalSwitchedCutoffModes20261113 (mode mode_budget coefficient)
open OriginalSwitchedSchwartzPrices20261113 (weight w_one)
open OriginalSwitchedHyperbolicBudget20261113 (profile_integrals)
open OriginalSwitchedModeTransforms20261113 (tested_transforms)
open KHeightSchwartzP3SourceOnly (heightFrequencyEquiv heightFrequencyEquiv_apply)

private theorem fourier_pair (F : SchwartzMap ℝ ℂ) (t : ℝ) :
    ‖(𝓕 (F:ℝ→ℂ)) (t/Real.pi)‖≤∫ u,‖F u‖ ∧
    (2*|t|)^3*‖(𝓕 (F:ℝ→ℂ)) (t/Real.pi)‖≤∫ u,‖iteratedDeriv 3 F u‖ := by
  have price (f : ℝ→ℂ) : ‖(𝓕 f) (t/Real.pi)‖≤∫ u,‖f u‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) f _
  refine ⟨price F,?_⟩
  let D := SchwartzMap.derivCLM ℂ ℂ
  have integ (n : ℕ) (G : SchwartzMap ℝ ℂ) : Integrable (iteratedDeriv n G) := by
    induction n generalizing G with
    | zero => simpa only [iteratedDeriv_zero] using G.integrable
    | succ n ih =>
      rw [iteratedDeriv_succ']
      exact ih (D G)
  have E := congrFun (Real.fourier_iteratedDeriv (f:= (F:ℝ→ℂ)) (n:=3) (N:=3) (F.smooth 3)
    (fun n _ => integ n F) (by norm_num)) (t/Real.pi)
  have p := price (iteratedDeriv 3 F)
  rw [E] at p
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_div,abs_of_pos Real.pi_pos,Complex.norm_ofNat,mul_one] at p
  simpa only [mul_one,show (2*Real.pi)*(|t|/Real.pi)=2*|t| by field_simp [Real.pi_ne_zero]] using p

theorem mode_uniform :
    ∃ (r : ℕ) (C : ℝ),0≤C ∧ ∀ (k : ℤ) (Y : ℝ),1≤Y → ∀ t : ℝ,
      (1+|t|)^3*‖positiveWeight (spectralTest (mode k) Y⁻¹) t‖≤
        C*(1+Real.log (2*Y)^2)*(weight k)^r := by
  obtain ⟨r,C,c,H⟩ := profile_integrals
  refine ⟨r,32*C,by positivity,fun k Y y1 t => ?_⟩
  let vp := inv_pos.mpr (zero_lt_one.trans_le y1)
  let F := profile (mode k) vp
  have W : positiveWeight (spectralTest (mode k) Y⁻¹) t=(4:ℂ)*(𝓕 (F:ℝ→ℂ)) (t/Real.pi) := by
    rw [(regular_transform _ vp t).2]
    change (4:ℂ)*((𝓕 F:SchwartzMap ℝ ℂ):ℝ→ℂ) (heightFrequencyEquiv t)=_
    rw [SchwartzMap.fourier_coe,heightFrequencyEquiv_apply]
  rw [W,norm_mul,Complex.norm_ofNat]
  have costs := H k Y y1
  obtain ⟨p,z⟩ := fourier_pair F t
  by_cases ht : |t|≤1
  · have b : (1+|t|)^3≤8 := by
      calc
        _ ≤ (2:ℝ)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ = _ := by norm_num
    have A := mul_le_mul_of_nonneg_right b (norm_nonneg ((𝓕 (F:ℝ→ℂ)) (t/Real.pi)))
    nlinarith only [A,p.trans costs.1]
  · have b : (1+|t|)^3≤(2*|t|)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    have A := mul_le_mul_of_nonneg_right b (norm_nonneg ((𝓕 (F:ℝ→ℂ)) (t/Real.pi)))
    have B := A.trans (z.trans costs.2)
    have np : 0≤C*(1+Real.log (2*Y)^2)*(weight k)^r :=
      mul_nonneg (mul_nonneg c (by positivity)) (pow_nonneg ((by norm_num : (0:ℝ)≤1).trans (w_one k)) _)
    nlinarith only [B,np]

/-- Both the unreflected single bump and Φ(Yx)Φ(L/(Yx)) have this
one price before the level, both Fourier marks and the switch ratio. -/
theorem regular_return :
    ∃ C : ℝ,0≤C ∧ ∀ (Y : ℝ),1≤Y → ∀ (s : Bool) (L t : ℝ),
      (1+|t|)^3*‖positiveWeight
        (fun x => OriginalSwitchedCutoffFamily20261113.profile s L (Y*x)) t‖≤
        C*(1+Real.log (2*Y)^2) := by
  obtain ⟨r,K,kp,B⟩ := mode_uniform
  obtain ⟨A,ap,U⟩ := mode_budget r
  refine ⟨K*A,mul_nonneg kp ap.le,fun Y y1 s L t => ?_⟩
  let H := K*(1+Real.log (2*Y)^2)
  let D := (1+|t|)^3
  let c := coefficient s L
  let W := fun k : ℤ => positiveWeight (spectralTest (mode k) Y⁻¹) t
  have hp : 0≤H := mul_nonneg kp (by positivity)
  have dp : 0<D := by dsimp only [D];positivity
  have v := (tested_transforms s L Y (zero_lt_one.trans_le y1)).1 t
  let g := fun k : ℤ => (weight k)^r*‖c k‖
  have sg : Summable g := (U s L).1
  have point (k : ℤ) : D*‖c k*W k‖≤H*g k := by
    rw [norm_mul]
    have E := mul_le_mul_of_nonneg_left (B k Y y1 t) (norm_nonneg (c k))
    dsimp only [D,H,g,W];dsimp only [c] at E ⊢
    nlinarith only [E]
  have S := v.summable.norm.mul_left D
  have h := S.tsum_le_tsum point (sg.mul_left H)
  rw [tsum_mul_left,tsum_mul_left] at h
  rw [←v.tsum_eq]
  change D*‖∑' k,c k*W k‖≤_
  apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm v.summable.norm) dp.le).trans
  apply h.trans
  have e := mul_le_mul_of_nonneg_left (U s L).2 hp
  change H*(∑' k,g k)≤H*A at e
  apply e.trans_eq
  dsimp only [H];ring

end
end ImbalancedChen.Part3.OriginalSwitchedUniformRegularTransform20261113
