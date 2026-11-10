import ImbalancedChen.Part3ActualCharacterCompletedFourier
import ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
The entire completed Young character Eisenstein family, identified with
the native lattice on the initial half-plane by physical Fourier inversion.
At a principal square character the reciprocal L factor uses Mathlib's
pole-removed L function, including its actual central value.
-/
namespace ImbalancedChen.Part3.ActualCharacterCriticalFamily20261110

noncomputable section
attribute [local instance] Classical.propDecidable
open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups BigOperators
open ActualCharacterCompletedFourier20261110 ActualCharacterPoissonRows20261110
open ActualCharacterLatticeCompletion20261110 CharacterEisensteinSeries
open CharacterEisensteinAutomorphy CharacterEisensteinRowAction
open PrimitiveEisensteinParameterAnalytic PrimitiveEisensteinHorizontalContinuity
open ActualEisensteinFourierInterchange20261025a PowerSeedFourierLaplaceFubini
open ComplexOrderKBridgeSourceOnly ComplexOrderKUniformStripDecay20261025a
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open OriginalCharacterPairDilation20261102s Gamma0DegeneracyMapSourceOnly

private theorem weightedDivisor_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ)
    (hn : n ≠ 0) (M : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) :
    ‖weightedDivisor χ n s‖ ≤ (n.natAbs : ℝ)^(2*M+2) := by
  let W := ∑ c ∈ n.natAbs.divisors, (c : ℝ)^(1-2*s.re)
  have hw : 0 ≤ W := Finset.sum_nonneg (fun c _ => Real.rpow_nonneg (Nat.cast_nonneg c) _)
  have hD : divisorFactor n.natAbs (2*(s.re : ℂ)) = (W : ℂ) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat,W] using
      divisorFactor_ofReal n.natAbs (2*s.re)
  calc
    _ ≤ ∑ c ∈ n.natAbs.divisors,
        ‖χ (c : ZMod q)*star (χ ((n/(c : ℤ) : ℤ) : ZMod q))*(c : ℂ)^(1-2*s)‖ :=
      norm_sum_le _ _
    _ ≤ W := by
      apply Finset.sum_le_sum
      intro c hc
      have hb : ‖χ (c : ZMod q)‖*‖star (χ ((n/(c : ℤ) : ℤ) : ZMod q))‖ ≤ 1 := by
        rw [norm_star]
        exact (mul_le_mul (χ.norm_le_one _) (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
          (mul_one 1)
      simp only [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_mem_divisors hc)]
      rw [show (1-2*s).re = 1-2*s.re by simp [Complex.mul_re]]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hb
    _ = ‖divisorFactor n.natAbs (2*(s.re : ℂ))‖ := by
      rw [hD,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
    _ ≤ _ := divisorFactor_polynomial_bound (Int.natAbs_pos.mpr hn) M (by simpa using hs)

private def signedBound (M : ℕ) (y : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else (2*Real.sqrt y) * (decayConstant M y *
    (n.natAbs : ℝ)^(3*M+2) * Real.exp (-(Real.pi*y)*(n.natAbs : ℝ)))

private theorem signedBound_summable (M : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable (signedBound M y) := by
  have H := (majorant_summable M hy).mul_left (2*Real.sqrt y)
  have hp : Summable (fun k : ℕ => signedBound M y ((k+1 : ℕ) : ℤ)) := by
    simpa [signedBound,majorant] using H
  have hn : Summable (fun k : ℕ => signedBound M y (-((k+1 : ℕ) : ℤ))) := by
    simpa [signedBound,majorant] using H
  have hp0 : Summable (fun k : ℕ => signedBound M y (k : ℤ)) :=
    (summable_nat_add_iff 1).mp hp
  exact Summable.of_nat_of_neg_add_one hp0 (by simpa only [Nat.cast_add,Nat.cast_one] using hn)

private theorem coefficient_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ)
    (M : ℕ) {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) (y : ℝ) (hy : 0 < y) :
    ‖continuedCoefficient χ n y s‖ ≤ signedBound M y n := by
  by_cases hn : n = 0
  · simp [continuedCoefficient,signedBound,hn]
  have hN := Int.natAbs_pos.mpr hn
  have hN1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast hN
  have hAbs : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  have hq0 : 0 < 2*Real.pi*y := by positivity
  have hq : 2*Real.pi*y ≤ 2*Real.pi*(n.natAbs : ℝ)*y := by
    have H := mul_le_mul_of_nonneg_right hN1 (le_of_lt hq0)
    nlinarith
  have hν : |(s-1/2).re| ≤ (M : ℝ)+1 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hs
    apply abs_le.mpr
    norm_num [Complex.sub_re] <;> constructor <;> linarith
  have HK := complexOrderK_uniform_exp_bound hq0 hq hν
  have HA : ‖amplitude χ n s‖ ≤ (n.natAbs : ℝ)^(3*M+2) := by
    rw [amplitude,norm_mul,← hAbs,Complex.ofReal_natCast]
    calc
      _ ≤ (n.natAbs : ℝ)^M * (n.natAbs : ℝ)^(2*M+2) :=
        mul_le_mul (power_prefactor_bound hN M hs) (weightedDivisor_bound χ n hn M hs)
          (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have HE : -(2*Real.pi*(n.natAbs : ℝ)*y/2) = -(Real.pi*y)*(n.natAbs : ℝ) := by ring
  rw [HE] at HK
  rw [continuedCoefficient,if_neg hn,signedBound,if_neg hn,← hAbs]
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg y)]
  calc
    _ ≤ ((2*Real.sqrt y)*(n.natAbs : ℝ)^(3*M+2)) *
        (decayConstant M y * Real.exp (-(Real.pi*y)*(n.natAbs : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left HA (by positivity)) HK
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem coefficient_norm_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (y : ℝ) (hy : 0 < y) (s : ℂ) :
    Summable (fun n : ℤ => ‖continuedCoefficient χ n y s‖) :=
  (signedBound_summable (Nat.ceil |s.re|) hy).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => coefficient_bound χ n _ (Nat.le_ceil _) y hy)

def completedFamily {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (z : ℍ) : ℂ :=
  ∑' n : ℤ, continuedCoefficient χ n z.im s * fourier n (z.re : UnitAddCircle)

theorem completedFamily_entire {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℍ) :
    Differentiable ℂ (fun s => completedFamily χ s z) := by
  intro s
  let M := Nat.ceil |s.re| + 1
  let U : Set ℂ := {w | |w.re| < (M : ℝ)}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hmem : s ∈ U := by
    have H := Nat.le_ceil |s.re|
    dsimp [U,M]
    push_cast
    linarith
  have hD : DifferentiableOn ℂ (fun w => completedFamily χ w z) U := by
    apply differentiableOn_tsum_of_summable_norm (signedBound_summable M z.im_pos)
      (fun n => ((continuedCoefficient_entire χ n z.im z.im_pos).mul_const _).differentiableOn) hU
    intro n w hw
    simpa only [norm_mul,fourier_apply,Circle.norm_coe,mul_one] using
      coefficient_bound χ n M hw.le z.im z.im_pos
  exact (hD s hmem).differentiableAt (hU.mem_nhds hmem)

private theorem physical_horizontal_continuous {q : ℕ} [NeZero q] (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x => completedPrimitive hq χ s (horizontalPoint y hy x)) := by
  let Y := (q : ℝ)*y
  have hY : 0 < Y := mul_pos (by exact_mod_cast hq) hy
  let f (u : ℝ) := ∑' v : PrimitivePair, primitiveWeight χ v *
    complexSeed (horizontalPoint Y hY u) v s
  have hcF : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro u
    let A := |u|+1
    have hU : TendstoUniformlyOn
        (fun H : Finset PrimitivePair => fun w : ℝ =>
          ∑ v ∈ H, primitiveWeight χ v * complexSeed (horizontalPoint Y hY w) v s)
        f atTop (Icc (-A) A) := by
      apply tendstoUniformlyOn_tsum (horizontalStripMajorant_summable s hs Y hY A)
      intro v w hw
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (characterWeight_norm_le_one χ _ _)).trans
        (complexSeed_horizontal_strip_bound s hs Y hY A v (abs_le.mpr hw))
    have hC : ContinuousOn f (Icc (-A) A) := hU.continuousOn
      (Frequently.of_forall (fun H => continuousOn_finsetSum H
        (fun v _ => (continuous_const.mul (complexSeed_horizontal_continuous Y hY v s)).continuousOn)))
    exact hC.continuousAt (Icc_mem_nhds (by dsimp [A]; linarith [neg_abs_le u])
      (by dsimp [A]; linarith [le_abs_self u]))
  have hz (x : ℝ) : scaledPoint q hq (horizontalPoint y hy x) =
        horizontalPoint Y hY ((q : ℝ)*x) := by
    apply UpperHalfPlane.ext
    rw [scaledPoint_coe]
    apply Complex.ext <;> simp [horizontalPoint,Y,Complex.mul_re,Complex.mul_im]
  simp only [completedPrimitive,characterEisenstein,characterSeed,hz]
  exact continuous_const.mul (continuous_const.mul (continuous_const.mul
    (hcF.comp (continuous_const.mul continuous_id))))

private def physicalCircle {q : ℕ} [NeZero q] (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    C(UnitAddCircle,ℂ) := by
  have hP : Function.Periodic (fun x => completedPrimitive hq χ s (horizontalPoint y hy x)) 1 := by
    intro x
    simp only [completedPrimitive,characterEisenstein_horizontal_periodic hq χ s hs y hy x]
  exact ⟨hP.lift, by
    unfold Function.Periodic.lift
    exact (physical_horizontal_continuous hq χ s hs y hy).quotient_liftOn' _⟩

/-- Pointwise physical identification. This includes the zero mode and both
Fourier signs on the same actual function, with no continuation premise. -/
theorem completedFamily_initial {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    completedFamily χ s z = completedPrimitive hq χ s z := by
  let F := physicalCircle hq χ s hs z.im z.im_pos
  have hF (x : ℝ) : F (x : UnitAddCircle) = completedPrimitive hq χ s
      (horizontalPoint z.im z.im_pos x) := rfl
  have hC : fourierCoeff F = fun n => continuedCoefficient χ n z.im s := by
    funext n
    rw [fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)]
    simp only [div_one,one_smul,zero_add,smul_eq_mul,PowerSeedPeriodization.native_fourier_phase,hF]
    exact physical_completed_coefficient hq h1 χ hχ s hs z.im z.im_pos n
  have hS : Summable (fourierCoeff F) := by
    rw [hC]
    exact (coefficient_norm_summable χ z.im z.im_pos s).of_norm
  have H := (has_pointwise_sum_fourier_series_of_summable (f := F) hS
    (z.re : UnitAddCircle)).tsum_eq
  have hz : horizontalPoint z.im z.im_pos z.re = z := by ext <;> rfl
  simpa only [completedFamily,hC,hF,hz,smul_eq_mul] using H

/-- Actual completed character-pair and all admissible oldforms are automorphic
on the original occupied level at every complex parameter. -/
theorem completed_oldform_invariant {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℕ) (d : ℕ+)
    (hlevel : q^2*(d : ℕ) ∣ N) (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (z : ℍ) (s : ℂ) :
    completedFamily χ s (degeneracyDiagonal d d.pos • (g • z)) =
      completedFamily χ s (degeneracyDiagonal d d.pos • z) := by
  have heq : (fun w => completedFamily χ w (degeneracyDiagonal d d.pos • (g • z))) =ᶠ[𝓝 (2 : ℂ)]
      (fun w => completedFamily χ w (degeneracyDiagonal d d.pos • z)) := by
    have hU : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hU] with w hw
    rw [completedFamily_initial hq h1 χ hχ w hw,completedFamily_initial hq h1 χ hχ w hw]
    unfold completedPrimitive
    exact congrArg (fun a : ℂ => _ * ((χ^2).LFunction (2*w)*a))
      (characterLatticeOldform_invariant N hq χ d hlevel w hw g hg z)
  have hF := (completedFamily_entire χ (degeneracyDiagonal d d.pos • (g • z))).differentiableOn
    (s := (univ : Set ℂ))
  have hG := (completedFamily_entire χ (degeneracyDiagonal d d.pos • z)).differentiableOn
    (s := (univ : Set ℂ))
  exact congrFun ((hF.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hG.analyticOnNhd isOpen_univ) heq) s

def reciprocalL {q : ℕ} [NeZero q] (η : DirichletCharacter ℂ q) (u : ℂ) : ℂ :=
  if η = 1 then (u-1)/DirichletCharacter.LFunctionTrivChar₁ q u else (η.LFunction u)⁻¹

private theorem reciprocalL_eq_inv {q : ℕ} [NeZero q] (η : DirichletCharacter ℂ q)
    {u : ℂ} (hu : u ≠ 1) (hre : 1 ≤ u.re) : reciprocalL η u = (η.LFunction u)⁻¹ := by
  by_cases hη : η = 1
  · subst η
    have hL := DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ q) (.inr hu) hre
    rw [reciprocalL,if_pos rfl,DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hu]
    change (u-1)/((u-1)*(1 : DirichletCharacter ℂ q).LFunction u) = _
    field_simp [sub_ne_zero.mpr hu,hL]
  · simp [reciprocalL,hη]

theorem reciprocalL_differentiableAt {q : ℕ} [NeZero q] (η : DirichletCharacter ℂ q)
    (u : ℂ) (hu : 1 ≤ u.re) : DifferentiableAt ℂ (reciprocalL η) u := by
  by_cases hη : η = 1
  · subst η
    have hden : DirichletCharacter.LFunctionTrivChar₁ q u ≠ 0 := by
      by_cases h : u = 1
      · simpa only [h] using DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
      · rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne h]
        exact mul_ne_zero (sub_ne_zero.mpr h)
          (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (.inr h) hu)
    simpa only [reciprocalL,if_pos rfl] using
      (differentiableAt_id.sub_const (1 : ℂ)).div
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableAt hden
  · simpa only [reciprocalL,if_neg hη] using
      (DirichletCharacter.differentiableAt_LFunction η u (.inr hη)).inv
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re η (.inl hη) hu)

def uncompletionFactor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^s / (q : ℂ)^s * gauss χ / Complex.Gamma s *
    reciprocalL (χ^2) (2*s)

def primitiveFamily {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (z : ℍ) : ℂ :=
  uncompletionFactor χ s * completedFamily χ s z

theorem primitiveFamily_initial {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    primitiveFamily χ s z = characterEisenstein hq χ s z := by
  have h2 : 1 < (2*s).re := by simp [Complex.mul_re]; linarith
  have hne : 2*s ≠ 1 := fun h => (by simpa [h] using h2 : False)
  rw [primitiveFamily,uncompletionFactor,completedFamily_initial hq h1 χ hχ s hs,completedPrimitive,
    reciprocalL_eq_inv _ hne h2.le]
  field_simp [Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hq.ne' : (q : ℂ) ≠ 0)),
    show (Real.pi : ℂ)^s ≠ 0 from Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)),
    Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re),gauss_ne_zero hχ,
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ^2) (.inr hne) h2.le] <;> ring

theorem primitiveFamily_differentiableAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : ℍ) (s : ℂ) (hs : 1/2 ≤ s.re) :
    DifferentiableAt ℂ (fun w => primitiveFamily χ w z) s := by
  have hs0 : 0 < s.re := by linarith
  have hΓ : DifferentiableAt ℂ Complex.Gamma s := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have h := congrArg Complex.re hm
    simp only [Complex.neg_re,Complex.natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have h2 : 1 ≤ (2*s).re := by simp [Complex.mul_re]; linarith
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact (((((differentiableAt_id.const_cpow (.inl hπC)).div
      (differentiableAt_id.const_cpow (.inl hqC)) (Complex.cpow_ne_zero_iff.mpr (.inl hqC))).mul_const
      (gauss χ)).div hΓ (Complex.Gamma_ne_zero_of_re_pos hs0)).mul
      ((reciprocalL_differentiableAt (χ^2) (2*s) h2).comp s (differentiableAt_id.const_mul 2))).mul
      (completedFamily_entire χ z).differentiableAt

/-- For every primitive real character of nontrivial conductor the uncompleted
central value vanishes. This uses the regular reciprocal, with no division
at the pole of the principal-square Dirichlet L function. -/
theorem principalSquare_central {q : ℕ} [NeZero q] (_h1 : q ≠ 1) (χ : DirichletCharacter ℂ q)
    (_hprimitive : χ.IsPrimitive) (hχ : χ^2 = 1) (z : ℍ) : primitiveFamily χ (1/2) z = 0 := by
  norm_num [primitiveFamily,uncompletionFactor,reciprocalL,hχ]

theorem critical_oldform {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℕ) (d : ℕ+)
    (hlevel : q^2*(d : ℕ) ∣ N) (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (t : ℝ) (z : ℍ) :
    primitiveFamily χ (1/2 + Complex.I*t) (degeneracyDiagonal d d.pos • (g • z)) =
      primitiveFamily χ (1/2 + Complex.I*t) (degeneracyDiagonal d d.pos • z) ∧
    DifferentiableAt ℂ (fun s => primitiveFamily χ s (degeneracyDiagonal d d.pos • z))
      (1/2 + Complex.I*t) := by
  constructor
  · simp only [primitiveFamily,completed_oldform_invariant hq h1 χ hχ N d hlevel g hg z]
  · apply primitiveFamily_differentiableAt
    simp [Complex.mul_re]

end
end ImbalancedChen.Part3.ActualCharacterCriticalFamily20261110
