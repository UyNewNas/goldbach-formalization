import ImbalancedChen.Part3ActualParabolicNonzeroRows
import ImbalancedChen.Part3UnitWeightCurveIntegral
import ImbalancedChen.Part3ActualNativeHorocycleParameter
import ImbalancedChen.Part3ActualPhysicalKNonzeroAnchor
import ImbalancedChen.Part3GeneralKRightEndpoint
import Mathlib.Analysis.Normed.Module.Connected

/-! Meromorphic continuation of the signed geometric Fourier coefficient to
each critical point in the two original observing frames. An observation
height is selected at a genuine nonzero value of the physical K kernel.
The continued germ agrees with the absolutely convergent arithmetic series
near s = 2 and its critical value uses Young's original native cusp index. -/
namespace ImbalancedChen.Part3.GeometricCriticalEisenstein20261123

noncomputable section
open Complex Set Filter Topology Matrix MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualParabolicNonzeroRows20261123 UnitWeightCurveIntegral20261123
open ActualCharacterCuspExpansion20261110 ActualYoungCriticalCusps20261110
open ActualYoungFormalClass20261110 ActualYoungCriticalD20261110 ActualYoungCriticalProjection20261110
open ActualCharacterCriticalFamily20261110 ActualCuspDenominatorClasses20261110
open ActualPhysicalKNonzeroAnchor20261026b ActualPhysicalKJets20261026b
open ActualOrdinaryContinuousModes20261110 ActualContinuousClassFourier20261110
open ActualCriticalCuspEvaluation20261110 ActualCompletedCurveMeans20261110
open ActualNativeHorocycleParameter20261110 Gamma0DegeneracyMapSourceOnly
open ActualFrickeCuspPhase20261025a ActualCuspFourierSectionSourceOnly
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a Gamma0ActualCuspsSourceOnly
open NativeCuspComplexPowerFourier20261027 ActualEisensteinFourierInterchange20261025a
open PowerSeedFourierLaplaceFubini ComplexOrderKBridgeSourceOnly ComplexOrderKEntire20261025a
open GeneralKRightEndpoint20261025a

local instance bandNe (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩
local instance conductorNe {N : ℕ} [NeZero N] (i : CharacterSlots N) : NeZero i.2.conductor :=
  ⟨i.2.conductor_ne_zero⟩

private theorem native_spatial_all (N : ℕ) [NeZero N] (a : NativeCusps N) (s : ℂ) :
    Continuous (cuspFamily N a s) := by
  classical
  have ord {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Continuous (ordinary χ s) := by
    by_cases h : q = 1
    · simpa only [ordinary, if_pos h, principalOrdinary] using
        (completed_principal_spatial s).const_mul ((Real.pi : ℂ)^s / Complex.Gamma s *
          reciprocalL (1 : DirichletCharacter ℂ 1) (2*s))
    · simpa only [ordinary, if_neg h, primitiveFamily] using
        (completed_character_spatial_all χ s).const_mul (uncompletionFactor χ s)
  have channel (i : CharacterSlots N) : Continuous (channelFunction i.1 i.2 s) := by
    have H (z : ℍ) := ((originalSlot i).realized s z).trans
      (D_as_dilations i.2.primitiveCharacter (originalSlot i).pos (originalSlot i).j s z)
    rw [funext H]
    apply continuous_finsetSum
    intro b _
    apply Continuous.const_mul
    apply (ord _).comp
    change Continuous (fun z : ℍ => Matrix.SpecialLinearGroup.mapGL ℝ _ • z)
    exact continuous_const_smul _
  change Continuous (parameterFamily ((youngCuspEquiv N).symm a) s)
  generalize (youngCuspEquiv N).symm a = p
  rcases p with ⟨f,u⟩
  change Continuous (fun z => parameterFamily ⟨f,u⟩ s z)
  simp_rw [inverse_cusp]
  exact continuous_const.mul (continuous_finsetSum _ (fun ξ _ =>
    continuous_const.mul (channel (⟨f,ξ⟩ : CharacterSlots N))))

def testedMode (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (n : ℤ) (y : ℝ) (hy : 0 < y)
    (s : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourierPhase n x * cuspFamily N (nativeFrameOrbit N g) s
    (normalizedScaling N (NeZero.pos N) h • horizontalPoint y hy x)

/-- Parameter regularity follows by testing the same meromorphic native
family against three continuous, parameter-independent observation paths. -/
theorem testedMode_regularity (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    MeromorphicOn (testedMode N g h n y hy) ({0,1} : Set ℂ)ᶜ ∧
      ∀ s : ℂ, 1/2 ≤ s.re → s ≠ 1 →
        DifferentiableAt ℂ (testedMode N g h n y hy) s := by
  let Z (x : ℝ) := normalizedScaling N (NeZero.pos N) h • horizontalPoint y hy x
  let U := ({0,1} : Set ℂ)ᶜ
  let a := nativeFrameOrbit N g
  have hZ : Continuous Z := by
    change Continuous (fun x : ℝ => Matrix.SpecialLinearGroup.mapGL ℝ _ • horizontalPoint y hy x)
    apply (continuous_const_smul _).comp
    unfold horizontalPoint
    fun_prop
  have hw : Continuous (fourierPhase n) := by unfold fourierPhase; fun_prop
  obtain ⟨P,Q,c,d,hP,hQ,_,_,H⟩ := unit_weight_curve_formula Z hZ (fourierPhase n) hw
    (fun x => (fourierPhase_norm n x).le)
  have he : testedMode N g h n y hy = fun s =>
      (c : ℂ)*curveMean P (cuspFamily N a) s +
      Complex.I*((d : ℂ)*curveMean Q (cuspFamily N a) s) -
      (2+2*Complex.I)*curveMean Z (cuspFamily N a) s :=
    funext (fun s => H (cuspFamily N a s) (native_spatial_all N a s))
  have p := native_curve_regularity N a P hP
  have q := native_curve_regularity N a Q hQ
  have z := native_curve_regularity N a Z hZ
  have k (w : ℂ) : MeromorphicOn (fun _ : ℂ => w) U := fun _ _ => analyticAt_const.meromorphicAt
  rw [he]
  refine ⟨(((k c).fun_mul p.1).fun_add ((k Complex.I).fun_mul ((k d).fun_mul q.1))).fun_sub
    ((k (2+2*Complex.I)).fun_mul z.1), ?_⟩
  intro s hs h1
  exact (((p.2 s hs h1).const_mul (c : ℂ)).add
    (((q.2 s hs h1).const_mul (d : ℂ)).const_mul Complex.I)).sub
      ((z.2 s hs h1).const_mul _)

def observerFrame (one : Bool) : SL(2,ℤ) := if one then cuspOneMatrix else 1

private theorem inf_scaling (N : ℕ) [NeZero N] :
    normalizedScaling N (NeZero.pos N) (1 : SL(2,ℤ)) = 1 := by
  apply Subtype.ext
  rw [normalizedScaling_entries, cuspWidth_infinity N (NeZero.pos N)]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

theorem critical_physical_mode (N : ℕ) [NeZero N] (a : Parameters N) (one : Bool)
    (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    testedMode N (parameterFrame a) (observerFrame one) n y hy (criticalPoint t) =
      radial n t y * nativeR a one n t := by
  have hc : nativeFrameOrbit N (parameterFrame a) = youngCuspEquiv N a := rfl
  cases one
  · simp only [testedMode, observerFrame, Bool.false_eq_true, if_false, inf_scaling, one_smul, hc]
    exact native_mode a false n hn t y hy
  · have H := native_sigmaOne a n hn t y hy
    rw [fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)] at H
    simp only [div_one,one_smul,zero_add,smul_eq_mul,PowerSeedPeriodization.native_fourier_phase] at H
    have hhor (x : ℝ) : horizontal y hy x = horizontalPoint y hy x := by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp [horizontal, horizontalPoint]
    simp only [testedMode, observerFrame, if_true, hc, cuspFamily, Equiv.symm_apply_apply]
    convert H using 1
    apply intervalIntegral.integral_congr
    intro x _
    change fourierPhase n x * physicalFamily N t a
      (normalizedScaling N (NeZero.pos N) cuspOneMatrix • horizontalPoint y hy x) =
      fourierPhase n x * physicalFamily N t a
      (normalizedScaling N (NeZero.pos N) cuspOneMatrix • horizontal y hy x)
    rw [hhor]

def gammaScale (s : ℂ) : ℂ := (Real.pi : ℂ)^s / Complex.Gamma s

private theorem gammaScale_ne {s : ℂ} (hs : 0 < s.re) : gammaScale s ≠ 0 :=
  div_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gamma_ne_zero_of_re_pos hs)

private theorem signedPower_ne {n : ℤ} (hn : n ≠ 0) (s : ℂ) :
    ((|(n : ℝ)| : ℝ) : ℂ)^(s-1/2) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr (abs_pos.mpr
    (show (n : ℝ) ≠ 0 by exact_mod_cast hn)).ne'))

private theorem kernel_factor (n : ℤ) (y : ℝ) (s : ℂ) :
    nonzeroKExpression y n s =
      (2 * physicalK (s-1/2) (2*Real.pi*|(n : ℝ)|) y) *
        (gammaScale s * ((|(n : ℝ)| : ℝ) : ℂ)^(s-1/2)) := by
  unfold nonzeroKExpression physicalK gammaScale
  ring

private theorem kernel_entire {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (nonzeroKExpression y n) := by
  have hn' : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hpi : Differentiable ℂ (fun s : ℂ => (Real.pi : ℂ)^s) := fun _ =>
    differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hP : Differentiable ℂ (fun s : ℂ => ((|(n : ℝ)| : ℝ) : ℂ)^(s-1/2)) := fun _ =>
    (differentiableAt_id.sub_const (1/2 : ℂ)).const_cpow (.inl (Complex.ofReal_ne_zero.mpr hn'.ne'))
  have hq : 0 < 2*Real.pi*|(n : ℝ)|*y := by positivity
  have hK := (complexOrderK_differentiable_all hq).comp
    (differentiable_id.sub_const (1/2 : ℂ))
  have hG := (hpi.mul Complex.differentiable_one_div_Gamma)
  have H := (((hG.const_mul (2 : ℂ)).mul hP).mul_const (Real.sqrt y : ℂ)).mul hK
  simpa only [nonzeroKExpression, div_eq_mul_inv, one_mul, mul_assoc] using H

/-- Holomorphy of the arithmetic series on its entire initial half-plane.
At a prescribed parameter the physical K asymptotic provides a nonzero
observation height and a neighborhood on which ordinary division is valid. -/
theorem geometric_initial_analytic (N : ℕ) [NeZero N] (g h : SL(2,ℤ))
    (n : ℤ) (hn : n ≠ 0) :
    AnalyticOnNhd ℂ (fun s => geometricCoefficient N g h s n) {s : ℂ | 1 < s.re} := by
  have hop : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hop
  intro s hs
  change 1 < s.re at hs
  have hp : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have ha : 0 < 2*Real.pi*|(n : ℝ)| := by positivity
  obtain ⟨y,hy,hK⟩ := physicalK_nonzero_anchor (s-1/2) ha 0
  have hy0 : 0 < y := zero_lt_one.trans ((le_max_left _ _).trans_lt hy)
  have hden : nonzeroKExpression y n s ≠ 0 := by
    rw [kernel_factor]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hK)
      (mul_ne_zero (gammaScale_ne (by linarith)) (signedPower_ne hn _))
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  have hD := ((testedMode_regularity N g h n y hy0).2 s (by linarith) h1).div
    (kernel_entire hn hy0 s) hden
  apply (hD.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hop.mem_nhds hs, ((kernel_entire hn hy0).continuousAt.eventually_ne hden)]
    with v hv hKv
  change geometricCoefficient N g h v n = testedMode N g h n y hy0 v / nonzeroKExpression y n v
  rw [testedMode, native_initial_fourier N (NeZero.pos N) g h v hv n hn y hy0,
    mul_div_cancel_right₀ _ hKv]

private theorem critical_re (t : ℝ) : (criticalPoint t).re = 1/2 := by
  norm_num [criticalPoint,Complex.mul_re]

private theorem exists_anchor (n : ℤ) (hn : n ≠ 0) (t : ℝ) :
    ∃ y : ℝ, 0 < y ∧ nonzeroKExpression y n (criticalPoint t) ≠ 0 ∧
      nonzeroKExpression y n 2 ≠ 0 := by
  let a := 2 * Real.pi * |(n : ℝ)|
  have hp : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨y,hy,hK⟩ := physicalK_nonzero_anchor (criticalPoint t-1/2) ha 0
  have hy0 : 0 < y := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_left _ _) hy)
  have hK₂ : physicalK ((2 : ℂ)-1/2) a y ≠ 0 := by
    rw [physicalK, show (2 : ℂ)-1/2 = ((3/2 : ℝ) : ℂ) by norm_num, complexOrderK_real]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy0).ne')
      (Complex.ofReal_ne_zero.mpr (actualRealOrderK_pos _ (mul_pos ha hy0)).ne')
  refine ⟨y,hy0,?_,?_⟩
  · rw [kernel_factor]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hK)
      (mul_ne_zero (gammaScale_ne (by rw [critical_re]; norm_num)) (signedPower_ne hn _))
  · rw [kernel_factor]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hK₂)
      (mul_ne_zero (gammaScale_ne (by norm_num)) (signedPower_ne hn _))

private def anchor (n : ℤ) (hn : n ≠ 0) (t : ℝ) := Classical.choose (exists_anchor n hn t)
private theorem anchor_spec (n : ℤ) (hn : n ≠ 0) (t : ℝ) :
    0 < anchor n hn t ∧ nonzeroKExpression (anchor n hn t) n (criticalPoint t) ≠ 0 ∧
      nonzeroKExpression (anchor n hn t) n 2 ≠ 0 :=
  Classical.choose_spec (exists_anchor n hn t)

/-- A representative of the geometric continuation at the requested critical
point. Its numerator is the physical Fourier integral on the same native cusp. -/
def continuedAt (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (n : ℤ) (hn : n ≠ 0)
    (t : ℝ) (s : ℂ) :=
  testedMode N g h n (anchor n hn t) (anchor_spec n hn t).1 s /
    nonzeroKExpression (anchor n hn t) n s

theorem continuedAt_initial_germ (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (n : ℤ)
    (hn : n ≠ 0) (t : ℝ) :
    (continuedAt N g h n hn t) =ᶠ[𝓝 (2 : ℂ)] (fun s => geometricCoefficient N g h s n) := by
  obtain ⟨hy,_,h₂⟩ := anchor_spec n hn t
  have hu : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hu, ((kernel_entire hn hy).continuousAt.eventually_ne h₂)] with s hs hK
  rw [continuedAt, testedMode, native_initial_fourier N (NeZero.pos N) g h s hs n hn _ hy,
    mul_div_cancel_right₀ _ hK]

theorem continuedAt_regular (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (n : ℤ) (hn : n ≠ 0)
    (t : ℝ) :
    MeromorphicOn (continuedAt N g h n hn t) ({0,1} : Set ℂ)ᶜ ∧
      DifferentiableAt ℂ (continuedAt N g h n hn t) (criticalPoint t) := by
  obtain ⟨hy,hK,_⟩ := anchor_spec n hn t
  obtain ⟨hm,hd⟩ := testedMode_regularity N g h n _ hy
  have HK := kernel_entire hn hy
  have hmK : MeromorphicOn (nonzeroKExpression (anchor n hn t) n) ({0,1} : Set ℂ)ᶜ :=
    fun s _ => ((analyticOnNhd_univ_iff_differentiable.mpr HK) s (mem_univ s)).meromorphicAt
  have hs1 : criticalPoint t ≠ 1 := by
    intro H
    have e := congrArg Complex.re H
    rw [critical_re] at e
    norm_num at e
  exact ⟨hm.fun_div hmK, (hd _ (critical_re t).ge hs1).div (HK _) hK⟩

/-- All critical points use the same meromorphic germ. A Bessel zero of a
height selected for another point only changes a removable representative. -/
theorem continuedAt_same_germ (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (n : ℤ)
    (hn : n ≠ 0) (t u : ℝ) (s : ℂ) (hs : s ∈ ({0,1} : Set ℂ)ᶜ) :
    continuedAt N g h n hn t =ᶠ[𝓝[≠] s] continuedAt N g h n hn u := by
  let U := ({0,1} : Set ℂ)ᶜ
  let F := fun v => continuedAt N g h n hn t v - continuedAt N g h n hn u v
  have hF : MeromorphicOn F U := (continuedAt_regular N g h n hn t).1.fun_sub
    (continuedAt_regular N g h n hn u).1
  have hU : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank
      (by simp [Complex.rank_real_complex] : 1 < Module.rank ℝ ℂ)
      (Set.finite_pair (0 : ℂ) 1).countable).isPreconnected
  have h₂ : (2 : ℂ) ∈ U := by norm_num [U]
  have near := (continuedAt_initial_germ N g h n hn t).trans
    (continuedAt_initial_germ N g h n hn u).symm
  have H₂ : meromorphicOrderAt F (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [near.filter_mono nhdsWithin_le_nhds] with v hv
    exact sub_eq_zero.mpr hv
  have H : meromorphicOrderAt F s = ⊤ := by
    by_contra hnontop
    exact (hF.meromorphicOrderAt_ne_top_of_isPreconnected hU hs h₂ hnontop) H₂
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp H] with v hv
  exact sub_eq_zero.mp hv

/-- The manuscript coefficient |n|^(it) times the continued geometric
series. Both signs are used by the physical trace. -/
def printedR {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool) (n : ℤ) (t : ℝ) : ℂ :=
  if hn : n = 0 then 0 else
    ((|(n : ℝ)| : ℝ) : ℂ)^((t : ℂ)*Complex.I) *
      continuedAt N (parameterFrame a) (observerFrame one) n hn t (criticalPoint t)

theorem nativeR_eq_geometric {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool)
    (n : ℤ) (hn : n ≠ 0) (t : ℝ) :
    nativeR a one n t = gammaScale (criticalPoint t) * printedR a one n t := by
  obtain ⟨hy,hK,_⟩ := anchor_spec n hn t
  let y := anchor n hn t
  have H := critical_physical_mode N a one n hn t y hy
  have he : criticalPoint t-1/2 = (t : ℂ)*Complex.I := by unfold criticalPoint; ring
  have hk : nonzeroKExpression y n (criticalPoint t) =
      radial n t y * (gammaScale (criticalPoint t) * ((|(n : ℝ)| : ℝ) : ℂ)^((t : ℂ)*Complex.I)) := by
    rw [kernel_factor]
    dsimp [radial, physicalK]
    rw [he]
    ring
  rw [printedR, dif_neg hn, continuedAt]
  change nativeR a one n t = _ * (_ * (testedMode N (parameterFrame a) (observerFrame one)
    n y hy (criticalPoint t) / nonzeroKExpression y n (criticalPoint t)))
  rw [H]
  field_simp only [ne_eq, hK]
  rw [hk]
  ring

end
end ImbalancedChen.Part3.GeometricCriticalEisenstein20261123
