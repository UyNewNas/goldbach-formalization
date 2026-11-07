import ImbalancedChen.Part3ActualRoughContourIntegrandBounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual left-vertical and horizontal rough Perron edges, with all original
L/Euler and Mellin-frequency costs supplied by25. The left edge costs
amplitude*X^(1-delta/2); the sum of horizontal edges costs
amplitude*eX*(delta/2+xi)/(pi*T^2). The right offset is independent of the
left shift and obeys xi*log X<=1. No norm of an unknown integrand is input.
-/

namespace ImbalancedChen.Part3.ActualRoughContourEdges20261026b
noncomputable section
open Classical Complex Set MeasureTheory
open ActualRoughContourHolomorphic20261026b RoughQuadraticLowRectangle20261026b
open ActualRoughContourIntegrandBounds20261026b
open ActualRoughAsymmetricContour20261026b RoughSlotSmoothedPerron20261026b

private theorem norm_prefactor : ‖(1/(2*Real.pi*I) : ℂ)‖=1/(2*Real.pi) := by
  simp [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]

private theorem norm_vertical (f : ℂ → ℂ) (a l r : ℝ) :
    ‖VIntegral' f a l r‖=(1/(2*Real.pi))*‖∫ t in l..r,f ((a : ℂ)+t*I)‖ := by
  rw [VIntegral',norm_smul,norm_prefactor,VIntegral,norm_smul,Complex.norm_I,one_mul]

private theorem norm_horizontal (f : ℂ → ℂ) (a b t : ℝ) :
    ‖HIntegral' f a b t‖=(1/(2*Real.pi))*‖∫ β in a..b,f ((β : ℂ)+t*I)‖ := by
  rw [HIntegral',norm_smul,norm_prefactor]
  rfl

private theorem norm_vertical_point_sq (β t : ℝ) :
    ‖((β : ℂ)+t*I)‖^2=β^2+t^2 := by
  simp [Complex.sq_norm,Complex.normSq_apply] <;> ring

/-- All constants in the amplitude are fixed before every original
character/cutoff/frequency/height. The inequalities integrate the actual
Smooth1 kernel and full original-level L/Euler integrand, rather than a
postulated majorant. -/
theorem exists_actual_rough_contour_edge_bounds (η : ℝ) (hη : 0<η) :
    ∃ c A E : ℝ,0<c ∧ 0<A ∧ 0<E ∧ ∀ (ν : ℝ → ℝ),
      ContDiff ℝ 1 ν → Function.support ν⊆Icc (1/2) 2 → ∃ C : ℝ,0<C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),χ≠1 →
      ∀ (useMu : Bool) (z τ U T X ε δ κ ξ : ℝ),
      0≤z → 0<T → 1≤X → 0<ε → ε<1 → 0<δ → 0≤κ →
      δ≤conductorWidth c A η χ (T+|τ|) → δ≤1/rectangleLog q (T+|τ|) →
      δ*Real.log (max 2 z)≤κ → 0<ξ → ξ≤δ → ξ*Real.log X≤1 →
      let a:=1-δ/2
      let b:=1+ξ
      let P:=contourAmplitude E C q (T+|τ|) δ κ z ε
      let f:=roughPerronIntegrand useMu χ z τ U ν ε X
      ‖VIntegral' f a (-T) T‖≤P*X^a ∧
      ‖HIntegral' f a b T‖+‖HIntegral' f a b (-T)‖≤
        P*Real.exp 1*X*(δ/2+ξ)/(Real.pi*T^2) := by
  obtain ⟨c,A,E,hc,hA,hE,hbound⟩:=exists_actual_rough_integrand_bounds η hη
  refine ⟨c,A,E,hc,hA,hE,?_⟩
  intro ν hν hsupp
  obtain ⟨C,hC,hpoint⟩:=hbound ν hν hsupp
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ useMu z τ U T X ε δ κ ξ hz hT hX hε hε1 hδ hκ hwidth hsmall hcap hξ hξδ hξlog
  dsimp only
  let a:=1-δ/2
  let b:=1+ξ
  let P:=contourAmplitude E C q (T+|τ|) δ κ z ε
  let f:=roughPerronIntegrand useMu χ z τ U ν ε X
  have hXpos : 0<X:=lt_of_lt_of_le zero_lt_one hX
  have hδ1 : δ≤1/4:=hwidth.trans (conductorWidth_le_quarter c A η χ (T+|τ|))
  have ha : (3/4 : ℝ)≤a:=by dsimp [a]; linarith
  have hab : a≤b:=by dsimp [a,b]; linarith
  have hP : 0≤P:=by
    have hD : 0<rectangleLog q (T+|τ|):=
      lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q (T+|τ|))
    have hlog : 0≤Real.log (max 2 z):=Real.log_nonneg
      (le_trans (by norm_num : (1 : ℝ)≤2) (le_max_left _ _))
    dsimp [P,contourAmplitude,ActualOriginalLContourBounds20261026b.originalReciprocalCost,
      RoughThinEulerUniformComparison20261026b.thinComparison]
    positivity
  have hpoint':=hpoint q χ hχ useMu z τ U T X ε δ κ hz hT.le hXpos hε hε1 hδ hκ hwidth hsmall hcap
  have hleft : ∀ t : ℝ,t∈Ioc (-T) T →
      ‖f ((a : ℂ)+t*I)‖≤(2*P*X^a)*(1+t^2)⁻¹:=by
    intro t ht
    have htabs : |t|≤T:=abs_le.mpr ⟨ht.1.le,ht.2⟩
    have hp:=hpoint' ((a : ℂ)+t*I) (by simp [a])
      (by simp [a]; linarith) (by simpa using htabs)
    have hden : (1+t^2)/2≤‖((a : ℂ)+t*I)‖^2:=by
      rw [norm_vertical_point_sq]
      nlinarith [sq_nonneg (a-3/4),sq_nonneg t]
    calc
      _ ≤ P*X^a/‖((a : ℂ)+t*I)‖^2:=by simpa [f,P] using hp
      _ ≤ P*X^a/((1+t^2)/2):=
        div_le_div_of_nonneg_left (mul_nonneg hP (Real.rpow_nonneg hXpos.le _)) (by positivity) hden
      _ = _:=by
        field_simp [show (1+t^2)≠0 by positivity]
        ring
  have hrawLeft : ‖∫ t in (-T)..T,f ((a : ℂ)+t*I)‖≤2*P*X^a*Real.pi:=by
    have hi:=intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T≤T)
      (Eventually.of_forall hleft)
      ((integrable_inv_one_add_sq.const_mul (2*P*X^a)).intervalIntegrable)
    have hk : (∫ t in (-T)..T,(1+t^2)⁻¹)≤Real.pi:=by
      rw [integral_inv_one_add_sq,Real.arctan_neg]
      linarith [Real.arctan_lt_pi_div_two T]
    rw [intervalIntegral.integral_const_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hk (by positivity))
  have hhorizontal : ∀ y : ℝ,|y|=T →
      ‖HIntegral' f a b y‖≤(1/(2*Real.pi))*(P*Real.exp 1*X/T^2)*(b-a):=by
    intro y hy
    have hraw : ‖∫ β in a..b,f ((β : ℂ)+y*I)‖≤
        (P*Real.exp 1*X/T^2)*(b-a):=by
      have hpbound : ∀ β∈Set.uIoc a b,‖f ((β : ℂ)+y*I)‖≤P*Real.exp 1*X/T^2:=by
        intro β hβ
        rw [Set.uIoc_of_le hab] at hβ
        have hβlo : 1-δ/2≤β:=by dsimp [a] at hβ; linarith [hβ.1]
        have hβhi : β≤1+δ:=by dsimp [b] at hβ; linarith [hβ.2]
        have hp:=hpoint' ((β : ℂ)+y*I) (by simpa using hβlo)
          (by simpa using hβhi) (by simpa [hy])
        have hpower : X^β≤Real.exp 1*X:=
          (Real.rpow_le_rpow_of_exponent_le hX hβ.2).trans (right_power_le_exp_mul hXpos hξlog)
        have hden : T^2≤‖((β : ℂ)+y*I)‖^2:=by
          rw [norm_vertical_point_sq,← hy,sq_abs]
          nlinarith [sq_nonneg β]
        exact (show ‖f ((β : ℂ)+y*I)‖≤P*X^β/‖((β : ℂ)+y*I)‖^2 by
          simpa [f,P] using hp).trans
          (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpower hP)
            (by positivity : 0<T^2) hden)
      simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
        intervalIntegral.norm_integral_le_of_norm_le_const hpbound
    rw [norm_horizontal]
    exact (mul_le_mul_of_nonneg_left hraw (by positivity)).trans_eq (by ring)
  constructor
  · rw [norm_vertical]
    exact (mul_le_mul_of_nonneg_left hrawLeft (by positivity)).trans_eq
      (by field_simp [Real.pi_ne_zero]; ring)
  · have hu:=hhorizontal T (abs_of_pos hT)
    have hl:=hhorizontal (-T) (by rw [abs_neg,abs_of_pos hT])
    apply (add_le_add hu hl).trans_eq
    dsimp [a,b]
    field_simp [Real.pi_ne_zero,hT.ne']
    ring

end
end ImbalancedChen.Part3.ActualRoughContourEdges20261026b
