import ImbalancedChen.Part3ActualPositiveTestedKBoundary

/-! The actual same-sign J transform in (4.10), including its removable
value at t=0, the complementary numerator, and real Schwartz decay. -/
namespace ImbalancedChen.Part3.ActualPrescribedPositiveJ20261112

noncomputable section
open Set Filter MeasureTheory Complex FourierTransform
open scoped FourierTransform Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveCosineProfile20261112 ActualPositiveJRotationPair20261112
open ActualPositiveTestedKBoundary20261112 KHeightSchwartzP3SourceOnly KFullLineFourierBridgeSourceOnly
open ActualJLocalOrderHolomorphic20261026a

def positiveWeight (Φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ q in Ioi (0:ℝ),regularKernel q t*Φ q/(q:ℂ)

def exceptionalWeight (Φ : ℝ → ℂ) (a : ℝ) : ℂ :=
  ∫ q in Ioi (0:ℝ),complementaryKernel q a*Φ q/(q:ℂ)

def weightSchwartz (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) : SchwartzMap ℝ ℂ :=
  (4:ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ heightFrequencyEquiv (𝓕 (profile ell hY))

theorem regular_transform (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (t : ℝ) :
    IntegrableOn (fun q => regularKernel q t*spectralTest ell Y q/(q:ℂ)) (Ioi (0:ℝ)) ∧
      positiveWeight (spectralTest ell Y) t=weightSchwartz ell hY t := by
  let ν := 2*I*(t:ℂ)
  have hν : ν=0 ∨ (0<ν.re ∧ ν.re<1) ∨ (ν.re=0 ∧ ν.im≠0) := by
    by_cases z : t=0
    · left; simp [ν,z]
    · right; right; constructor
      · simp [ν,Complex.mul_re]
      · simpa [ν,Complex.mul_im,Complex.mul_re] using mul_ne_zero (by norm_num : (2:ℝ)≠0) z
  have A := boundary ν hν ell hY
  have E : (fun q : ℝ => regularKernel q t*spectralTest ell Y q/(q:ℂ))=ᵐ[volume.restrict (Ioi 0)]
      (fun q => 4*(rotated ν q*testDiv ell Y q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    rw [← regular_rotation hq t,testDiv]; dsimp [ν]; ring
  refine ⟨(A.1.const_mul 4).congr E.symm,?_⟩
  rw [positiveWeight,integral_congr_ae E,integral_const_mul,A.2]
  have H (u : ℝ) : Complex.cosh (ν*(u:ℂ))=(Real.cos (2*t*u):ℂ) := by
    rw [show ν*(u:ℂ)=(((2*t*u:ℝ):ℂ)*I) by dsimp [ν]; push_cast; ring,Complex.cosh_mul_I,← Complex.ofReal_cos]
  simp_rw [H]
  have even (u : ℝ) : profile ell hY (-u)=profile ell hY u := by simp only [profile_apply,Real.cosh_neg]
  rw [cosine_integral_eq_half_fourier _ (profile ell hY).integrable even]
  change _=(4:ℂ)*((𝓕 (profile ell hY):SchwartzMap ℝ ℂ):ℝ → ℂ) (heightFrequencyEquiv t)
  rw [SchwartzMap.fourier_coe,heightFrequencyEquiv_apply]
  ring

theorem exceptional_transform (ell : D4 → ℤ) {Y a : ℝ} (hY : 0<Y) (h0 : 0≤a) (h1 : a<1/2) :
    IntegrableOn (fun q => complementaryKernel q a*spectralTest ell Y q/(q:ℂ)) (Ioi (0:ℝ)) ∧
      exceptionalWeight (spectralTest ell Y) a=
        8*∫ u in Ioi (0:ℝ),(Real.cosh (2*a*u):ℂ)*profile ell hY u := by
  let ν := 2*(a:ℂ)
  have hν : ν=0 ∨ (0<ν.re ∧ ν.re<1) ∨ (ν.re=0 ∧ ν.im≠0) := by
    rcases h0.eq_or_lt with z|z
    · left; simp [ν,← z]
    · right; left; simp [ν]; constructor <;> linarith
  have A := boundary ν hν ell hY
  have E : (fun q : ℝ => complementaryKernel q a*spectralTest ell Y q/(q:ℂ))=ᵐ[volume.restrict (Ioi 0)]
      (fun q => 4*(rotated ν q*testDiv ell Y q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    rw [← complementary_rotation hq h0 h1,testDiv]; dsimp [ν]; ring
  refine ⟨(A.1.const_mul 4).congr E.symm,?_⟩
  rw [exceptionalWeight,integral_congr_ae E,integral_const_mul,A.2,← mul_assoc]
  norm_num only [Nat.reduceMul,show (4:ℂ)*2=8 by norm_num]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun u => by rw [Complex.ofReal_cosh]; push_cast; rfl

theorem zero_weight (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    positiveWeight (spectralTest ell Y) 0=
      -8*∫ q in Ioi (0:ℝ),actualJOrderDerivative 0 q*testDiv ell Y q := by
  rw [positiveWeight,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  rw [regular_threshold hq,testDiv]; ring

theorem fixed_regular_decay (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t : ℝ, ‖positiveWeight (spectralTest ell Y) t‖*(1+|t|)^n≤C := by
  let W := weightSchwartz ell hY
  let a := SchwartzMap.seminorm ℂ 0 0 W
  let b := SchwartzMap.seminorm ℂ n 0 W
  refine ⟨2^n*(a+b),by dsimp [a,b]; positivity,fun t => ?_⟩
  have A := SchwartzMap.le_seminorm' ℂ 0 0 W t
  have B := SchwartzMap.le_seminorm' ℂ n 0 W t
  simp only [pow_zero,one_mul,iteratedDeriv_zero,Real.norm_eq_abs] at A B
  rw [(regular_transform ell hY t).2]
  change ‖W t‖*(1+|t|)^n≤_
  have aa : 0≤a := (norm_nonneg _).trans A
  have bb : 0≤b := (mul_nonneg (pow_nonneg (abs_nonneg t) n) (norm_nonneg (W t))).trans B
  by_cases h : |t|≤1
  · have e : (1+|t|)^n≤2^n := by gcongr; linarith
    calc
      _ ≤ a*2^n := mul_le_mul A e (pow_nonneg (by positivity) _) aa
      _ ≤ _ := by nlinarith only [mul_nonneg (by positivity : (0:ℝ)≤2^n) bb]
  · have e : (1+|t|)^n≤2^n*|t|^n := by rw [← mul_pow]; gcongr; linarith
    have eb := mul_le_mul_of_nonneg_left e (norm_nonneg (W t))
    have mb := mul_le_mul_of_nonneg_left B (by positivity : (0:ℝ)≤2^n)
    nlinarith only [eb,mb,mul_nonneg (by positivity : (0:ℝ)≤2^n) aa]

end
end ImbalancedChen.Part3.ActualPrescribedPositiveJ20261112

