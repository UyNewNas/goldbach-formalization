import ImbalancedChen.Part3RoughConductorLogReciprocal
import ImbalancedChen.Part3RoughThinEulerUniformComparison
import ImbalancedChen.Part3RoughSlotPerronTruncation
import ImbalancedChen.Part3PrimitiveContinuedLThinTransport
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4SiegelLowerBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual primitive Siegel lower theorem is consumed, before every
original character and height. Its quadratic rectangle and the primary
nonquadratic rectangle are intersected at the ACTUAL primitive conductor.
The genuine induction Euler product transports nonvanishing to the
original character. This discharges holomorphy of the literal rough
Perron integrand; no hContour, hzero, L(1)-bound or SW premise is assumed.
The frequency shift is explicit: the zero-free height is T+abs(tau).
-/

namespace ImbalancedChen.Part3.ActualRoughContourHolomorphic20261026b
noncomputable section
open Classical Complex Set
open AnalyticNumberTheory.LargeSieve
open RoughQuadraticLowRectangle20261026b RoughQuadraticFiniteRectangle20261026b
open RoughFiniteRectangleReciprocal20261026b RoughConductorLogReciprocal20261026b
open RoughThinEulerFactors20261026b RoughFiniteEulerLogDerivative20261026b
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open RoughSlotMellinSeries20261026b RoughSlotSmoothedPerron20261026b
open PrimitiveContinuedLThinTransport20261026b

def conductorWidth (c A η : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (H : ℝ) : ℝ :=
  min (nonquadraticWidth χ.conductor H)
    (quadraticRectangleWidth A η χ.conductor H (c*(χ.conductor : ℝ)^(-η)))

def contourBox (δ T : ℝ) : Set ℂ :=
  {s | 1-δ/2≤s.re ∧ s.re≤1+δ ∧ |s.im|≤T}

theorem conductorWidth_pos {c A η H : ℝ} (hc : 0<c) (hA : 0<A)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hH : 0≤H) :
    0<conductorWidth c A η χ H := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  apply lt_min (nonquadraticWidth_pos χ.conductor H)
  exact quadraticRectangleWidth_pos hA χ.conductor hH
    (mul_pos hc (Real.rpow_pos_of_pos
      (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero) _))

theorem conductorWidth_le_quarter (c A η : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (H : ℝ) : conductorWidth c A η χ H≤1/4 :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- Actual unconditional nonvanishing on the original level, with constants
chosen before modulus, original character and finite enlarged height. -/
theorem exists_original_contour_zero_free (η : ℝ) (hη : 0<η) :
    ∃ c A : ℝ,0<c ∧ 0<A ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q),χ≠1 → ∀ H : ℝ,0≤H → ∀ s : ℂ,
      1-conductorWidth c A η χ H≤s.re → s.re≤2 → |s.im|≤H+1 → χ.LFunction s≠0 := by
  obtain ⟨c,hc,hSiegel⟩ :=
    Bombieri1965Theorem4.exists_uniform_quadratic_LFunction_one_lower_bound η hη
  obtain ⟨A,hA,hquad⟩ := exists_quadratic_finite_rectangle c η hc hη
  refine ⟨c,A,hc,hA,?_⟩
  intro q _ χ hχ H hH s hslo hshi hsim
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter≠1 := DirichletCharacter.primitiveCharacter_ne_one_of_ne_one hχ
  have hprim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hδ := conductorWidth_le_quarter c A η χ H
  have hsThree : (3/4 : ℝ)≤s.re := by linarith
  apply continuedL_ne_zero_of_primitive χ hχ hsThree
  by_cases hsq : χ.primitiveCharacter^2=1
  · apply hquad χ.conductor χ.primitiveCharacter hsq hψ
      (hSiegel χ.conductor χ.primitiveCharacter hprim hψ hsq) H hH s
    · exact le_trans (sub_le_sub_left (min_le_right _ _) 1) hslo
    · exact hshi
    · exact hsim
  · exact nonquadratic_finite_rectangle χ.primitiveCharacter hsq H s
      (le_trans (sub_le_sub_left (min_le_left _ _) 1) hslo) hshi hsim

private theorem finiteCorrection_differentiable {q : ℕ}
    (χ : DirichletCharacter ℂ q) (z : ℝ) : Differentiable ℂ (finiteCorrection χ z) := by
  intro s
  apply DifferentiableAt.fun_finset_prod
  intro p hp
  exact (factor_hasDerivAt χ (smallPrimes_prime hp) s).differentiableAt

/-- The actual full L/Euler and Smooth1 product is holomorphic on the
rectangle used for the finite contour. The moving Mellin phase changes
the required zero-free height to T+abs(tau); it is never suppressed. -/
theorem exists_actual_rough_contour_holomorphic (η : ℝ) (hη : 0<η) :
    ∃ c A : ℝ,0<c ∧ 0<A ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q),χ≠1 → ∀ (useMu : Bool) (z τ U T X ε : ℝ),
      0≤T → 0<X → 0<ε → ε<1 → ∀ ν : ℝ → ℝ,
      ContDiff ℝ 1 ν → (∀ x>0,0≤ν x) → support ν⊆Icc (1/2) 2 →
      (∫ x in Ioi (0 : ℝ),ν x/x)=1 →
      HolomorphicOn (roughPerronIntegrand useMu χ z τ U ν ε X)
        (contourBox (conductorWidth c A η χ (T+|τ|)) T) := by
  obtain ⟨c,A,hc,hA,hzero⟩ := exists_original_contour_zero_free η hη
  refine ⟨c,A,hc,hA,?_⟩
  intro q _ χ hχ useMu z τ U T X ε hT hX hε hε1 ν hν hnonneg hsupp hmass s hs
  let δ := conductorWidth c A η χ (T+|τ|)
  have hδpos : 0<δ := conductorWidth_pos hc hA χ (by positivity)
  have hδ : δ≤1/4 := conductorWidth_le_quarter c A η χ (T+|τ|)
  have hslo : 1-δ/2≤s.re := hs.1
  have hshi : s.re≤1+δ := hs.2.1
  have hheight : |s.im|≤T := hs.2.2
  have hre : 0<s.re := by linarith
  have hshiftre : 1-δ≤(shiftedExponent s τ).re := by rw [shiftedExponent_re]; linarith
  have hshiftThree : (3/4 : ℝ)≤(shiftedExponent s τ).re := by
    rw [shiftedExponent_re]
    linarith
  have hshiftHeight : |(shiftedExponent s τ).im|≤T+|τ|+1 := by
    simp only [shiftedExponent,sub_im,mul_im,I_re,ofReal_im,zero_mul,I_im,ofReal_re,
      one_mul,zero_add]
    exact (abs_sub _ _).trans (by linarith)
  have hLzero : χ.LFunction (shiftedExponent s τ)≠0 :=
    hzero q χ hχ (T+|τ|) (by positivity) (shiftedExponent s τ) hshiftre
      (by rw [shiftedExponent_re]; linarith) hshiftHeight
  have hS : DifferentiableAt ℂ (fun w => shiftedExponent w τ) s := by
    unfold shiftedExponent
    fun_prop
  have hL := (χ.differentiable_LFunction hχ (shiftedExponent s τ)).comp s hS
  have hC := ((finiteCorrection_differentiable χ z) (shiftedExponent s τ)).comp s hS
  have hCzero : finiteCorrection χ z (shiftedExponent s τ)≠0 :=
    finiteCorrection_ne_zero_thin χ z hδ hshiftre
  have htransform : DifferentiableAt ℂ (roughTransform useMu χ z τ U) s := by
    cases useMu
    · exact (hL.mul hC).const_mul _
    · have hInvCorrection :
          (fun w => ∏ p ∈ smallPrimes z,(1-χ p*(p : ℂ)^(-shiftedExponent w τ))⁻¹)=
            fun w => (finiteCorrection χ z (shiftedExponent w τ))⁻¹ := by
        funext w
        simp only [finiteCorrection,Finset.prod_inv_distrib]
      dsimp only [roughTransform]
      simp only [Bool.true_eq_true,if_true]
      rw [hInvCorrection]
      exact ((hL.inv hLzero).mul (hC.inv hCzero)).const_mul _
  have hM := Smooth1MellinDifferentiable hν hsupp ⟨hε,hε1⟩ hnonneg hmass hre
  have hpow : DifferentiableAt ℂ (fun w => (X : ℂ)^w) s := by
    exact (hasDerivAt_id s).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
      |>.differentiableAt
  exact ((htransform.mul hM).mul hpow).differentiableWithinAt

end
end ImbalancedChen.Part3.ActualRoughContourHolomorphic20261026b
