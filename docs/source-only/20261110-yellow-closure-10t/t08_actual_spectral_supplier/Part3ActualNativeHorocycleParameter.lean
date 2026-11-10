import ImbalancedChen.Part3ActualCompletedCurveMeans
import ImbalancedChen.Part3ActualCriticalCuspEvaluation

/-! Parameter regularity after testing the actual Young inverses on a
compact observation path. The finite class coefficients stay inside the
original dilation system, including its level and determinant factors. -/
namespace ImbalancedChen.Part3.ActualNativeHorocycleParameter20261110

noncomputable section
open Set Complex Matrix UpperHalfPlane MeasureTheory
open scoped BigOperators MatrixGroups UpperHalfPlane
open ActualCompletedCurveMeans20261110 ActualCharacterCriticalFamily20261110
open ActualCharacterCuspExpansion20261110 ActualCriticalCuspEvaluation20261110
open ActualYoungCriticalCusps20261110 ActualYoungCriticalD20261110
open ActualYoungDilationInverse20261110 ActualYoungCuspCoefficients20261110
open ActualYoungFormalClass20261110 ActualYoungCriticalProjection20261110
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open Gamma0DegeneracyMapSourceOnly CompletedActualEisensteinIdentity20261025a

private structure Regular (f : ℂ → ℂ) : Prop where
  merom : MeromorphicOn f ({0,1} : Set ℂ)ᶜ
  deriv : ∀ s : ℂ, 1/2 ≤ s.re → s ≠ 1 → DifferentiableAt ℂ f s

private theorem Regular.of_analytic {f : ℂ → ℂ} (H : AnalyticOnNhd ℂ f ({0,1} : Set ℂ)ᶜ) :
    Regular f := by
  refine ⟨fun s h => (H s h).meromorphicAt,?_⟩
  intro s hs h1
  have h0 : s ≠ 0 := by intro e; simp [e] at hs
  exact (H s (by simpa using And.intro h0 h1)).differentiableAt

private theorem Regular.entire {f : ℂ → ℂ} (H : Differentiable ℂ f) : Regular f :=
  ⟨fun s _ => ((analyticOnNhd_univ_iff_differentiable.mpr H) s (mem_univ _)).meromorphicAt,
    fun s _ _ => H s⟩

private theorem Regular.constant (c : ℂ) : Regular (fun _ : ℂ => c) :=
  Regular.entire (differentiable_const c)

private theorem Regular.mul {f g : ℂ → ℂ} (F : Regular f) (G : Regular g) :
    Regular (fun s => f s*g s) :=
  ⟨F.merom.fun_mul G.merom,fun s h h1 => (F.deriv s h h1).mul (G.deriv s h h1)⟩

private theorem Regular.div {f g : ℂ → ℂ} (F : Regular f) (G : Regular g)
    (hg : ∀ s : ℂ, 1/2 ≤ s.re → s ≠ 1 → g s ≠ 0) : Regular (fun s => f s/g s) :=
  ⟨F.merom.fun_div G.merom,fun s h h1 => (F.deriv s h h1).div (G.deriv s h h1) (hg s h h1)⟩

private theorem Regular.sum {ι : Type*} [Fintype ι] {F : ι → ℂ → ℂ}
    (H : ∀ i, Regular (F i)) : Regular (fun s => ∑ i, F i s) :=
  ⟨MeromorphicOn.fun_sum (fun i => (H i).merom),fun s h h1 =>
    DifferentiableAt.fun_sum (fun i _ => (H i).deriv s h h1)⟩

private theorem Regular.det {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ℂ → Matrix ι ι ℂ}
    (H : ∀ i j, Regular (fun s => A s i j)) : Regular (fun s => (A s).det) := by
  simp only [Matrix.det_apply']
  apply Regular.sum
  intro σ
  apply (Regular.constant _).mul
  exact ⟨MeromorphicOn.fun_prod (fun i _ => (H (σ i) i).merom),fun s h h1 =>
    DifferentiableAt.fun_finsetProd (fun i _ => (H (σ i) i).deriv s h h1)⟩

private theorem reciprocal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Regular (fun s : ℂ => reciprocalL χ (2*s)) := by
  have hL : Meromorphic (reciprocalL χ) := by
    have hM {f : ℂ → ℂ} (hd : Differentiable ℂ f) : Meromorphic f :=
      fun u => ((analyticOnNhd_univ_iff_differentiable.mpr hd) u (mem_univ u)).meromorphicAt
    by_cases H : χ = 1
    · simpa only [reciprocalL,if_pos H] using
        (hM (differentiable_id.sub_const (1 : ℂ))).fun_div
          (hM (DirichletCharacter.differentiable_LFunctionTrivChar₁ q))
    · have hd : Differentiable ℂ χ.LFunction :=
        fun u => DirichletCharacter.differentiableAt_LFunction χ u (.inr H)
      exact fun u => by
        simp only [reciprocalL,if_neg H]
        exact ((analyticOnNhd_univ_iff_differentiable.mpr hd) u (mem_univ u)).meromorphicAt.inv
  refine ⟨fun s _ => (hL (2*s)).comp_analyticAt (by fun_prop),?_⟩
  intro s hs _
  have h₂ : 1 ≤ (2*s).re := by simp [Complex.mul_re]; linarith
  exact (reciprocalL_differentiableAt χ _ h₂).comp s (differentiableAt_id.const_mul 2)

private theorem powerReg (c : ℂ) (hc : c ≠ 0) : Regular (fun s : ℂ => c^s) :=
  Regular.entire (fun _ => differentiableAt_id.const_cpow (.inl hc))

private theorem factor_principal : Regular (fun s : ℂ =>
    (Real.pi : ℂ)^s/Complex.Gamma s * reciprocalL (1 : DirichletCharacter ℂ 1) (2*s)) := by
  have H := ((powerReg _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mul
    (Regular.entire Complex.differentiable_one_div_Gamma)).mul (reciprocal _)
  simpa only [div_eq_mul_inv,one_mul] using H

private theorem factor_character {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Regular (uncompletionFactor χ) := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow := (powerReg _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).div (powerReg _ hq)
    (fun s _ _ => Complex.cpow_ne_zero_iff.mpr (.inl hq))
  have H := (((hpow.mul (Regular.constant (ActualCharacterPoissonRows20261110.gauss χ))).mul
    (Regular.entire Complex.differentiable_one_div_Gamma)).mul (reciprocal (χ^2)))
  simpa only [uncompletionFactor,div_eq_mul_inv,one_mul] using H

private theorem ordinary_spatial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Continuous (ordinary χ s) := by
  by_cases h : q = 1
  · simpa only [ordinary,if_pos h,principalOrdinary] using
      (completed_principal_spatial s).const_mul ((Real.pi : ℂ)^s/Complex.Gamma s *
        reciprocalL (1 : DirichletCharacter ℂ 1) (2*s))
  · simpa only [ordinary,if_neg h,primitiveFamily] using
      (completed_character_spatial_all χ s).const_mul (uncompletionFactor χ s)

private theorem ordinary_mean {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : ℝ → ℍ) (hZ : Continuous Z) : Regular (curveMean Z (ordinary χ)) := by
  by_cases h : q = 1
  · simpa only [curveMean,ordinary,if_pos h,principalOrdinary,intervalIntegral.integral_const_mul]
      using factor_principal.mul (Regular.of_analytic (principal_curve_analytic Z hZ))
  · simpa only [curveMean,ordinary,if_neg h,primitiveFamily,intervalIntegral.integral_const_mul]
      using (factor_character χ).mul (Regular.entire (character_curve_entire χ Z hZ))

private theorem coefficient_reg {q L : ℕ} (χ : DirichletCharacter ℂ q) (hL : 0 < L) (j b : Div L) :
    Regular (fun s => dilationCoefficient χ s j b) := by
  classical
  let A := fun s => kernelMatrix χ s L
  have hE (i k : Div L) : Regular (fun s => A s i k) := by
    have ht (n : ℕ) : Regular (fun s => twist χ s n) :=
      Regular.entire (fun s => (((differentiableAt_id.neg).mul_const (Real.log (n : ℝ) : ℂ)).cexp).const_mul _)
    exact (ht _).mul (ht _)
  have hU (i k : Div L) : Regular (fun s => ((A s).updateRow b (Pi.single j 1)) i k) := by
    by_cases e : i = b
    · subst i
      simpa only [Matrix.updateRow_self] using Regular.constant (Pi.single j (1 : ℂ) k)
    · simpa only [Matrix.updateRow_ne e] using hE i k
  have H := (Regular.det hU).div ((Regular.det hE).mul
    (Regular.entire (f := levelFactor (q^2*L) (q*j.1)) (fun _ => (differentiableAt_id.mul_const _).cexp)))
    (fun s h _ => mul_ne_zero (kernel_det_ne_zero χ (by linarith) L hL) (Complex.exp_ne_zero _))
  simpa only [dilationCoefficient,Matrix.adjugate_apply,A] using H

private theorem dilate_cont (d : ℕ+) : Continuous (fun z : ℍ => degeneracyDiagonal d d.pos • z) := by
  change Continuous (fun z : ℍ => Matrix.SpecialLinearGroup.mapGL ℝ (degeneracyDiagonal d d.pos) • z)
  exact continuous_const_smul _

private theorem finite_mean {ι : Type*} [Fintype ι] {F : ι → ℂ → ℍ → ℂ} (c : ι → ℂ → ℂ)
    (Z : ℝ → ℍ) (hZ : Continuous Z) (H : ∀ i s, Continuous (F i s)) :
    curveMean Z (fun s z => ∑ i, c i s*F i s z) = fun s => ∑ i, c i s*curveMean Z (F i) s := by
  funext s
  unfold curveMean
  rw [intervalIntegral.integral_finsetSum (fun i _ => (((H i s).comp hZ).const_mul _).intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_const_mul]

private theorem D_spatial {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hL : 0 < L) (j : Div L) (s : ℂ) : Continuous (criticalD χ hL j s) := by
  have he := funext (D_as_dilations χ hL j s)
  rw [he]
  exact continuous_finsetSum _ (fun b _ => ((ordinary_spatial χ s).comp
    (dilate_cont (dilation hL b))).const_mul _)

private theorem D_mean {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hL : 0 < L) (j : Div L) (Z : ℝ → ℍ) (hZ : Continuous Z) : Regular (curveMean Z (criticalD χ hL j)) := by
  have H : criticalD χ hL j = fun s z =>
      ∑ b : Div L, dilationCoefficient χ s j b*dilationFunction χ hL b s z :=
    funext (fun s => funext (D_as_dilations χ hL j s))
  rw [H,finite_mean _ Z hZ (fun b s => (ordinary_spatial χ s).comp (dilate_cont (dilation hL b)))]
  apply Regular.sum
  intro b
  exact (coefficient_reg χ hL j b).mul (ordinary_mean χ _ ((dilate_cont (dilation hL b)).comp hZ))

private theorem native_mean (N : ℕ) [NeZero N] (a : NativeCusps N)
    (Z : ℝ → ℍ) (hZ : Continuous Z) : Regular (curveMean Z (cuspFamily N a)) := by
  classical
  change Regular (curveMean Z (parameterFamily ((youngCuspEquiv N).symm a)))
  generalize (youngCuspEquiv N).symm a = p
  rcases p with ⟨f,u⟩
  letI : NeZero (band N f.1) := ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos
    (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩
  let λ₀ : ℂ := ((band N f.1).totient : ℂ)⁻¹
  let J := fun (ξ : DirichletCharacter ℂ (band N f.1)) => star (ξ (-(u : ZMod (band N f.1))))
  have HC (ξ : DirichletCharacter ℂ (band N f.1)) (s : ℂ) : Continuous (channelFunction f ξ s) := by
    let i : CharacterSlots N := ⟨f,ξ⟩
    letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
    have H := funext ((originalSlot i).realized s)
    rw [show channelFunction f ξ s = _ from H]
    exact D_spatial _ _ _ s
  have HE : curveMean Z (parameterFamily ⟨f,u⟩) = fun s => λ₀ *
      ∑ ξ : DirichletCharacter ℂ (band N f.1), J ξ * curveMean Z (channelFunction f ξ) s := by
    funext s
    simp only [curveMean,inverse_cusp,intervalIntegral.integral_const_mul]
    dsimp only [λ₀,J]
    rw [intervalIntegral.integral_finsetSum (fun ξ _ => (((HC ξ s).comp hZ).const_mul _).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const_mul]
  rw [HE]
  apply (Regular.constant λ₀).mul
  apply Regular.sum
  intro ξ
  let i : CharacterSlots N := ⟨f,ξ⟩
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  have H := funext (fun s => funext ((originalSlot i).realized s))
  apply (Regular.constant (J ξ)).mul
  rw [show channelFunction f ξ = _ from H]
  exact D_mean _ _ _ Z hZ

/-- Meromorphy of the literal compact path integral on the common
pole-excluded plane and genuine full-complex differentiability at every
regular point on the closed right half-plane Re(s) ≥ 1/2. -/
theorem native_curve_regularity (N : ℕ) [NeZero N] (a : NativeCusps N)
    (Z : ℝ → ℍ) (hZ : Continuous Z) :
    MeromorphicOn (curveMean Z (cuspFamily N a)) ({0,1} : Set ℂ)ᶜ ∧
      ∀ s : ℂ, 1/2 ≤ s.re → s ≠ 1 → DifferentiableAt ℂ (curveMean Z (cuspFamily N a)) s :=
  ⟨(native_mean N a Z hZ).merom,(native_mean N a Z hZ).deriv⟩

end
end ImbalancedChen.Part3.ActualNativeHorocycleParameter20261110
