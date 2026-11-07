import ImbalancedChen.Part3ActualRoughContourHolomorphic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact finite shifted contour for the actual roughOne/roughMobius smooth
sum, with literal Mellin phase, original character and all finite Euler
corrections. Holomorphy is supplied unconditionally by the preceding
primitive Siegel/induction construction. All three shifted edges and the
explicit right-line tail are retained; no hContour or edge bound is input.
-/

namespace ImbalancedChen.Part3.ActualRoughFiniteContour20261026b
noncomputable section
open Classical Complex Set MeasureTheory
open ActualRoughContourHolomorphic20261026b
open RoughSlotSmoothedPerron20261026b RoughSlotPerronTruncation20261026b

private theorem actual_rightSegment_eq_VIntegral {q : ℕ} [NeZero q]
    (useMu : Bool) (χ : DirichletCharacter ℂ q) {z U : ℝ}
    (hz : 0≤z) (hU : 0<U) (τ : ℝ) (ν : ℝ → ℝ) (ε X σ T : ℝ)
    (hσ : 1<σ) (hT : 0≤T) :
    rightSegment useMu χ z τ U ν ε X σ T =
      VIntegral' (roughPerronIntegrand useMu χ z τ U ν ε X) σ (-T) T := by
  rw [rightSegment_eq_actual_LFunction useMu χ hz hU τ ν ε X σ T hσ]
  dsimp only [VIntegral',VIntegral]
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T),← integral_Icc_eq_integral_Ioc]
  simp only [smul_eq_mul]
  push_cast
  field_simp
  ring

/-- One actual finite sum equals the left vertical edge, both horizontal
edges and a proved right-line remainder. Constants c,A are fixed before
the bump; C_nu is fixed before every original arithmetic/frequency choice. -/
theorem exists_actual_finite_rough_contour (η : ℝ) (hη : 0<η) :
    ∃ c A : ℝ,0<c ∧ 0<A ∧ ∀ (ν : ℝ → ℝ),
      ContDiff ℝ 1 ν → (∀ x>0,0≤ν x) → Function.support ν⊆Icc (1/2) 2 →
      (∫ x in Ioi (0 : ℝ),ν x/x)=1 → ∃ C : ℝ,0<C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ (useMu : Bool) (z τ U T X ε : ℝ),0≤z → 0<U → 0<T → 0<X → 0<ε → ε<1 →
      let δ:=conductorWidth c A η χ (T+|τ|)
      let a:=1-δ/2
      let b:=1+δ
      let f:=roughPerronIntegrand useMu χ z τ U ν ε X
      (∑ n ∈ smoothCarrier ν ε X,coefficient useMu χ z τ U n*Smooth1 ν ε (n/X)) =
        VIntegral' f a (-T) T + HIntegral' f a b T - HIntegral' f a b (-T) +
          rightTail useMu χ z τ U ν ε X b T ∧
      ‖rightTail useMu χ z τ U ν ε X b T‖≤
        (1+1/(b-1))*X^b*(C/ε)/(Real.pi*T) := by
  obtain ⟨c,A,hc,hA,hhol⟩ := exists_actual_rough_contour_holomorphic η hη
  refine ⟨c,A,hc,hA,?_⟩
  intro ν hν hnonneg hsupp hmass
  obtain ⟨C,hC,htrunc⟩ := exists_finite_rough_Perron_truncation hν hnonneg hsupp hmass
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ useMu z τ U T X ε hz hU hT hX hε hε1
  dsimp only
  let δ:=conductorWidth c A η χ (T+|τ|)
  let a:=1-δ/2
  let b:=1+δ
  let f:=roughPerronIntegrand useMu χ z τ U ν ε X
  have hδpos : 0<δ := conductorWidth_pos hc hA χ (by positivity)
  have hδ : δ≤1/4 := conductorWidth_le_quarter c A η χ (T+|τ|)
  have hab : a≤b := by dsimp [a,b]; linarith
  have hb : 1<b := by dsimp [b]; linarith
  have hb2 : b≤2 := by dsimp [b]; linarith
  let l : ℂ := (a : ℂ)+(-T)*I
  let r : ℂ := (b : ℂ)+T*I
  have hrect : Rectangle l r=Icc a b ×ℂ Icc (-T) T := by
    simp [Rectangle,l,r,Set.uIcc_of_le hab,Set.uIcc_of_le (by linarith : -T≤T)]
  have hsubset : Rectangle l r⊆contourBox δ T := by
    intro s hs
    rw [hrect,Complex.mem_reProdIm] at hs
    exact ⟨hs.1.1,hs.1.2,abs_le.mpr hs.2⟩
  have hzero : RectangleIntegral f l r=0 :=
    (hhol q χ hχ useMu z τ U T X ε hT.le hX hε hε1 ν hν hnonneg hsupp hmass)
      .vanishesOnRectangle hsubset
  have hsplit : VIntegral' f b (-T) T =
      VIntegral' f a (-T) T + HIntegral' f a b T-HIntegral' f a b (-T) := by
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
  have ht' := htrunc useMu q χ z τ U ε X b T hε hε1 hX hb hb2 hT
  constructor
  · rw [ht'.1,actual_rightSegment_eq_VIntegral useMu χ hz hU τ ν ε X b T hb hT.le,hsplit]
  · exact ht'.2

end
end ImbalancedChen.Part3.ActualRoughFiniteContour20261026b
