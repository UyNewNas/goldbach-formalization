import ImbalancedChen.Part3ActualRoughFiniteContour

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The left shift delta and right Perron offset xi are independent. The
right offset obeys xi*log X<=1, e.g. xi=1/log X, so its truncation error
costs eX rather than X^(1+delta). The exact actual contour is derived
inside the genuine rectangle, including all original L/Euler/frequency
data. No hContour, hzero, edge norm or desired saving is assumed.
-/

namespace ImbalancedChen.Part3.ActualRoughAsymmetricContour20261026b
noncomputable section
open Classical Complex Set MeasureTheory
open ActualRoughContourHolomorphic20261026b
open RoughSlotSmoothedPerron20261026b RoughSlotPerronTruncation20261026b

private theorem segment_eq_vertical {q : ℕ} [NeZero q]
    (useMu : Bool) (χ : DirichletCharacter ℂ q) {z U : ℝ}
    (hz : 0≤z) (hU : 0<U) (τ : ℝ) (ν : ℝ → ℝ) (ε X σ T : ℝ)
    (hσ : 1<σ) (hT : 0≤T) :
    rightSegment useMu χ z τ U ν ε X σ T=
      VIntegral' (roughPerronIntegrand useMu χ z τ U ν ε X) σ (-T) T := by
  rw [rightSegment_eq_actual_LFunction useMu χ hz hU τ ν ε X σ T hσ]
  dsimp only [VIntegral',VIntegral]
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T),← integral_Icc_eq_integral_Ioc]
  simp only [smul_eq_mul]
  push_cast
  field_simp
  ring

theorem right_power_le_exp_mul {X ξ : ℝ} (hX : 0<X)
    (hξ : ξ*Real.log X≤1) : X^(1+ξ)≤Real.exp 1*X := by
  rw [Real.rpow_add hX,Real.rpow_one]
  have hp : X^ξ≤Real.exp 1 := by
    rw [Real.rpow_def_of_pos hX]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hξ)
  exact (mul_le_mul_of_nonneg_left hp hX.le).trans_eq (mul_comm _ _)

/-- The actual asymmetric contour with its quantitative right-line tail.
The original frequency is reflected in the zero-free height T+abs(tau).
All geometric offsets remain explicit until the real parameter supplier
sets xi=1/log X and delta=d/log(actual rough cutoff). -/
theorem exists_actual_asymmetric_rough_contour (η : ℝ) (hη : 0<η) :
    ∃ c A : ℝ,0<c ∧ 0<A ∧ ∀ (ν : ℝ → ℝ),
      ContDiff ℝ 1 ν → (∀ x>0,0≤ν x) → Function.support ν⊆Icc (1/2) 2 →
      (∫ x in Ioi (0 : ℝ),ν x/x)=1 → ∃ C : ℝ,0<C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ (useMu : Bool) (z τ U T X ε δ ξ : ℝ),
      0≤z → 0<U → 0<T → 0<X → 0<ε → ε<1 → 0<δ →
      δ≤conductorWidth c A η χ (T+|τ|) → 0<ξ → ξ≤δ → ξ*Real.log X≤1 →
      let a:=1-δ/2
      let b:=1+ξ
      let f:=roughPerronIntegrand useMu χ z τ U ν ε X
      (∑ n ∈ smoothCarrier ν ε X,coefficient useMu χ z τ U n*Smooth1 ν ε (n/X)) =
        VIntegral' f a (-T) T + HIntegral' f a b T-HIntegral' f a b (-T) +
          rightTail useMu χ z τ U ν ε X b T ∧
      ‖rightTail useMu χ z τ U ν ε X b T‖≤
        Real.exp 1*(1+1/ξ)*X*(C/ε)/(Real.pi*T) := by
  obtain ⟨c,A,hc,hA,hhol⟩ := exists_actual_rough_contour_holomorphic η hη
  refine ⟨c,A,hc,hA,?_⟩
  intro ν hν hnonneg hsupp hmass
  obtain ⟨C,hC,htrunc⟩ := exists_finite_rough_Perron_truncation hν hnonneg hsupp hmass
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ useMu z τ U T X ε δ ξ hz hU hT hX hε hε1 hδ hδwidth hξ hξδ hξlog
  dsimp only
  let δ0:=conductorWidth c A η χ (T+|τ|)
  let a:=1-δ/2
  let b:=1+ξ
  let f:=roughPerronIntegrand useMu χ z τ U ν ε X
  have hδmax : δ≤1/4 := hδwidth.trans (conductorWidth_le_quarter c A η χ (T+|τ|))
  have hab : a≤b := by dsimp [a,b]; linarith
  have hb : 1<b := by dsimp [b]; linarith
  have hb2 : b≤2 := by dsimp [b]; linarith
  let l : ℂ := (a : ℂ)+(-T)*I
  let r : ℂ := (b : ℂ)+T*I
  have hrect : Rectangle l r=Icc a b ×ℂ Icc (-T) T := by
    simp [Rectangle,l,r,Set.uIcc_of_le hab,Set.uIcc_of_le (by linarith : -T≤T)]
  have hsubset : Rectangle l r⊆contourBox δ0 T := by
    intro s hs
    rw [hrect,Complex.mem_reProdIm] at hs
    refine ⟨?_,?_,abs_le.mpr hs.2⟩
    · have hlo:=hs.1.1
      dsimp only [a] at hlo
      linarith
    · have hhi:=hs.1.2
      dsimp only [b] at hhi
      linarith
  have hzero : RectangleIntegral f l r=0 :=
    (hhol q χ hχ useMu z τ U T X ε hT.le hX hε hε1 ν hν hnonneg hsupp hmass)
      .vanishesOnRectangle hsubset
  have hsplit : VIntegral' f b (-T) T=
      VIntegral' f a (-T) T+HIntegral' f a b T-HIntegral' f a b (-T) := by
    have he : HIntegral f a b (-T)-HIntegral f a b T+
        VIntegral f b (-T) T-VIntegral f a (-T) T=0 := by
      simpa only [RectangleIntegral,l,r,add_re,ofReal_re,mul_re,I_re,mul_zero,
        ofReal_im,I_im,mul_one,sub_self,add_zero,add_im,mul_im,zero_add] using hzero
    have hv : VIntegral f b (-T) T=
        VIntegral f a (-T) T+HIntegral f a b T-HIntegral f a b (-T) := by
      linear_combination he
    simp only [VIntegral',HIntegral',smul_eq_mul]
    rw [hv]
    ring
  have ht:=htrunc useMu q χ z τ U ε X b T hε hε1 hX hb hb2 hT
  constructor
  · rw [ht.1,segment_eq_vertical useMu χ hz hU τ ν ε X b T hb hT.le,hsplit]
  · have hpower:=right_power_le_exp_mul hX hξlog
    have hpay : (1+1/(b-1))*X^b*(C/ε)/(Real.pi*T)≤
        Real.exp 1*(1+1/ξ)*X*(C/ε)/(Real.pi*T) := by
      dsimp only [b]
      simp only [add_sub_cancel_left]
      calc
        _ ≤ (1+1/ξ)*(Real.exp 1*X)*(C/ε)/(Real.pi*T) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring
    exact ht.2.trans hpay

end
end ImbalancedChen.Part3.ActualRoughAsymmetricContour20261026b
