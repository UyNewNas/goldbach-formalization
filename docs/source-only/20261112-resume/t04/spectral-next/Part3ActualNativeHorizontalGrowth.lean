import ImbalancedChen.Part3ActualYoungHorizontalInverse
import ImbalancedChen.Part3ActualCompletedHorizontalBand
import ImbalancedChen.Part3ActualIncompleteResidualContour
import Batteries.Tactic.OpenPrivate

/-! The quantitative estimate is on the original meromorphic scattering
coefficient and the actual two-seed Gram integrand, at fixed physical
level and arbitrary native cusp frames. -/
namespace ImbalancedChen.Part3.ActualNativeHorizontalGrowth20261112

noncomputable section
open Set Complex Matrix UpperHalfPlane MeasureTheory Filter
open scoped UpperHalfPlane MatrixGroups Classical Interval BigOperators
open ActualYoungHorizontalInverse20261112 ActualCompletedHorizontalBand20261112
open ActualYoungDilationInverse20261110 ActualYoungCriticalD20261110 ActualYoungCriticalCusps20261110
open ActualYoungFormalClass20261110 ActualYoungCriticalProjection20261110 ActualContinuousClassFourier20261110
open ActualCuspDenominatorClasses20261110 ActualCharacterCuspExpansion20261110
open ActualCompletedCurveMeans20261110 ActualCriticalScatteringEntry20261110
open ActualParabolicScatteringRows20261110 ActualEisensteinFourierInterchange20261025a
open Gamma0GeneralCuspUnitPeriod20261025a Gamma0DegeneracyMapSourceOnly
open ActualInfinityCuspAnnihilator20261026b SmoothZeroHeightSeedProfiles20261026b
open ActualIncompleteMellinFactors20261110 ActualIncompleteEisensteinTransform20261110
open ActualIncompleteResidualContour20261110
open private curve_height from ImbalancedChen.Part3ActualCompletedCurveMeans
open private dilate_cont from ImbalancedChen.Part3ActualNativeHorocycleParameter

private def loss (s : ℂ) := Real.exp (Real.pi*|s.im|)/(s.re-1/2)

private def OnPath (F : ℂ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
    ∀ x ∈ Icc (0 : ℝ) 1, ‖F s x‖ ≤ C*loss s

private theorem multiply {F : ℂ → ℝ → ℂ} {c : ℂ → ℂ} (H : OnPath F)
    (J : ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 → ‖c s‖ ≤ A) :
    OnPath (fun s x => c s*F s x) := by
  obtain ⟨A,hA,HA⟩ := J
  obtain ⟨B,hB,HB⟩ := H
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro s hl hr hi x hx
  rw [norm_mul,mul_assoc]
  exact mul_le_mul (HA s hl.le hr) (HB s hl hr hi x hx) (norm_nonneg _) hA

private theorem constant_mul (c : ℂ) {F : ℂ → ℝ → ℂ} (H : OnPath F) :
    OnPath (fun s x => c*F s x) :=
  multiply H ⟨‖c‖,norm_nonneg _,fun _ _ _ => le_rfl⟩

private theorem finite_sum {ι : Type*} [Fintype ι] {F : ι → ℂ → ℝ → ℂ}
    (H : ∀ i, OnPath (F i)) : OnPath (fun s x => ∑ i, F i s x) := by
  classical
  choose B hB J using H
  refine ⟨∑ i, B i,Finset.sum_nonneg (fun i _ => hB i),?_⟩
  intro s hl hr hi x hx
  rw [Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => J i s hl hr hi x hx))

private theorem D_path {q L : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hL : 0 < L)
    (j : Div L) (Z : ℝ → ℍ) (hZ : Continuous Z) : OnPath (fun s x => criticalD χ hL j s (Z x)) := by
  simp only [D_as_dilations]
  apply finite_sum
  intro b
  apply multiply _ (dilation_strip_bound χ hL j b)
  let d := dilation hL b
  let Y := fun x => degeneracyDiagonal d d.pos • Z x
  have hY : Continuous Y := (dilate_cont d).comp hZ
  obtain ⟨a,b',ha,_,J⟩ := curve_height hY
  obtain ⟨C,hC,B⟩ := ordinary_band χ (b := b') ha
  refine ⟨C,hC,?_⟩
  intro s hl hr hi x hx
  change ‖ordinary χ s (Y x)‖ ≤ C*loss s
  rw [loss,← mul_div_assoc]
  exact (le_div_iff₀ (sub_pos.mpr hl)).mpr (by
    simpa only [mul_comm (‖ordinary χ s (Y x)‖)] using B s hl hr hi _ (J x hx))

private theorem all_paths (N : ℕ) [NeZero N] (a : NativeCusps N)
    (Z : ℝ → ℍ) (hZ : Continuous Z) : OnPath (fun s x => cuspFamily N a s (Z x)) := by
  classical
  change OnPath (fun s x => parameterFamily ((youngCuspEquiv N).symm a) s (Z x))
  generalize (youngCuspEquiv N).symm a = p
  rcases p with ⟨f,u⟩
  letI : NeZero (band N f.1) := ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos
    (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩
  simp only [inverse_cusp]
  apply constant_mul
  apply finite_sum
  intro ξ
  apply constant_mul
  let i : CharacterSlots N := ⟨f,ξ⟩
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  have H (s : ℂ) (x : ℝ) := (originalSlot i).realized s (Z x)
  change OnPath (fun s x => channelFunction i.1 i.2 s (Z x))
  simp only [H]
  exact D_path _ _ _ Z hZ

/-- All cusps, all positive levels, actual unit-leading coefficient;
the constant is allowed to depend on this fixed pair of frames. -/
theorem entry_horizontal (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      (s.re-1/2)*‖continuedEntry N (NeZero.pos N) g h s‖ ≤ C*Real.exp (Real.pi*|s.im|) := by
  let Z := fun x => normalizedScaling N (NeZero.pos N) h • horizontalPoint 1 zero_lt_one x
  have hZ : Continuous Z := by
    change Continuous (fun x => Matrix.SpecialLinearGroup.mapGL ℝ (normalizedScaling N (NeZero.pos N) h)
      • horizontalPoint 1 zero_lt_one x)
    apply (continuous_const_smul _).comp
    unfold horizontalPoint
    fun_prop
  obtain ⟨B,hB,J⟩ := all_paths N (nativeFrameOrbit N g) Z hZ
  refine ⟨B+1,by linarith,?_⟩
  intro s hl hr hi
  have M : ‖horocycleMean N (NeZero.pos N) g h 1 zero_lt_one s‖ ≤ B*loss s := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun x => cuspFamily N
      (nativeFrameOrbit N g) s (Z x)) (C := B*loss s) (a := 0) (b := 1) (fun x hx =>
        J s hl hr hi x (Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using hx)))
    simpa only [horocycleMean,curveMean,Z,sub_zero,abs_one,mul_one] using H
  have I₀ : ‖incoming N g h s 1‖ ≤ 1 := by
    classical
    unfold incoming
    split <;> simp
  have leE : 1 ≤ Real.exp (Real.pi*|s.im|) := Real.one_le_exp (by positivity)
  have M' := mul_le_mul_of_nonneg_left M (sub_nonneg.mpr hl.le)
  have E : (s.re-1/2)*(B*loss s) = B*Real.exp (Real.pi*|s.im|) := by
    unfold loss
    field_simp [(sub_pos.mpr hl).ne']
  rw [E] at M'
  unfold continuedEntry
  calc
    _ ≤ (s.re-1/2)*(‖horocycleMean N (NeZero.pos N) g h 1 zero_lt_one s‖+‖incoming N g h s 1‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sub_nonneg.mpr hl.le)
    _ ≤ (B+1)*Real.exp (Real.pi*|s.im|) := by
      have J' := mul_le_mul_of_nonneg_left I₀ (sub_nonneg.mpr hl.le)
      nlinarith

private theorem seed_strip (ψ : HeightSeed) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, -2 ≤ w.re → w.re ≤ 2 → ‖heightMellin ψ w‖ ≤ B := by
  let K := Real.log '' tsupport ψ.toFun
  have hK : IsCompact K := ψ.compact.image_of_continuousOn (fun y hy =>
    (Real.continuousAt_log (ψ.positive hy).ne').continuousWithinAt)
  let F := fun p : ℝ × ℝ => Real.exp (-(p.1*p.2))*‖ψ.toFun (Real.exp p.2)‖
  have C : Continuous F := ((continuous_fst.mul continuous_snd).neg.rexp).mul
    ((ψ.continuous.comp (Real.continuous_exp.comp continuous_snd)).norm)
  obtain ⟨A,H⟩ := ((isCompact_Icc (α := ℝ) (a := -2) (b := 2)).prod hK).exists_bound_of_continuousOn C.continuousOn
  refine ⟨max A 0*(volume : Measure ℝ).real K,by positivity,?_⟩
  intro w hl hr
  let k := fun u : ℝ => Complex.exp (-w*(u : ℂ))*ψ.toFun (Real.exp u)
  have H₀ : (∫ u in K,k u) = heightMellin ψ w := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : ψ.toFun (Real.exp u) = 0 := by
      by_contra e
      exact hu ⟨Real.exp u,subset_tsupport _ e,Real.log_exp _⟩
    simp [k,hz]
  rw [← H₀]
  apply norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
  intro u hu
  have J := H (w.re,u) ⟨⟨hl,hr⟩,hu⟩
  have hnn : 0 ≤ F (w.re,u) := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  simpa only [Real.norm_of_nonneg hnn,F,k,norm_mul,Complex.norm_exp,Complex.re_mul_ofReal,
    Complex.neg_re,neg_mul] using J.trans (le_max_left A 0)

/-- A fixed bound for the genuine contour scalar (both height profiles,
orbit delta, outgoing scattering amplitude and powers unchanged). -/
theorem scalar_horizontal (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1/2 < s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      (s.re-1/2)*‖scalar N g h ψ φ s‖ ≤ C*Real.exp (Real.pi*|s.im|) := by
  obtain ⟨A,hA,M⟩ := seed_strip φ.toHeightSeed
  obtain ⟨B,hB,J⟩ := seed_strip ψ.toHeightSeed
  obtain ⟨D,hD,W⟩ := entry_horizontal N g h
  refine ⟨A*(B+D*B),by positivity,?_⟩
  intro s hl hr hi
  let δ := s.re-1/2
  let E := Real.exp (Real.pi*|s.im|)
  have hδ : 0 ≤ δ := (sub_pos.mpr hl).le
  have h₁ : δ ≤ 1 := by dsimp [δ]; linarith
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have A' := M s (by linarith) (by linarith)
  have BJ (u : ℂ) (hx : -2 ≤ (1-star u).re) (hy : (1-star u).re ≤ 2) : ‖moment ψ.toHeightSeed u‖ ≤ B := by
    rw [moment_conjugated,norm_star]
    exact J _ hx hy
  have B₁ := BJ s (by simp; linarith) (by simp; linarith)
  have B₂ := BJ (1-s) (by simp; linarith) (by simp; linarith)
  let f := if nativeFrameOrbit N h = nativeFrameOrbit N g then moment ψ.toHeightSeed s else 0
  have F : ‖f‖ ≤ B := by dsimp [f]; split <;> simp_all
  let e := continuedEntry N (NeZero.pos N) g h s
  have D' : δ*‖e‖ ≤ D*E := W s hl hr hi
  have F' : δ*‖f‖ ≤ B*E := (mul_le_mul h₁ F (norm_nonneg _) zero_le_one).trans (by
    simpa using le_mul_of_one_le_right hB hE)
  have Q := mul_le_mul D' B₂ (norm_nonneg _) (mul_nonneg hD (zero_le_one.trans hE))
  have U : δ*‖f+e*moment ψ.toHeightSeed (1-s)‖ ≤ (B+D*B)*E := by
    have H := mul_le_mul_of_nonneg_left (norm_add_le f (e*moment ψ.toHeightSeed (1-s))) hδ
    rw [norm_mul] at H
    nlinarith only [H,F',Q]
  have V := mul_le_mul A' U (mul_nonneg hδ (norm_nonneg _)) hA
  change δ*‖heightMellin φ.toHeightSeed s*(f+e*moment ψ.toHeightSeed (1-s))‖ ≤ _
  rw [norm_mul]
  nlinarith only [V]

end
end ImbalancedChen.Part3.ActualNativeHorizontalGrowth20261112
