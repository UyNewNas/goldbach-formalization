import ImbalancedChen.Part3ActualResidualCurveAtOne

/-! The physical simple-pole coefficients of all native normalized
parabolic Eisenstein functions are spatially constant. Reciprocity
identifies the residues of different cusps at the same level. -/
namespace ImbalancedChen.Part3.ActualNativeResidualChannel20261110

noncomputable section
open Set Filter Topology Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualResidualCurveAtOne20261110 ActualCompletedCurveMeans20261110
open ActualCharacterScatteringReflection20261110 ActualCriticalScatteringReciprocity20261110
open ActualCriticalScatteringEntry20261110 ActualCharacterCuspExpansion20261110
open ActualCuspDenominatorClasses20261110 ActualYoungFormalClass20261110
open ActualYoungCriticalCusps20261110 ActualYoungCriticalD20261110 ActualYoungDilationInverse20261110
open ActualYoungCuspCoefficients20261110 ActualYoungCriticalProjection20261110
open ActualContinuousClassFourier20261110 ActualCharacterCriticalFamily20261110
open Gamma0GeneralCuspUnitPeriod20261025a ActualEisensteinFourierInterchange20261025a
open Gamma0DegeneracyMapSourceOnly

local instance (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩
local instance {N : ℕ} [NeZero N] (i : CharacterSlots N) : NeZero i.2.conductor :=
  ⟨i.2.conductor_ne_zero⟩

private theorem coefficient_cont {q L : ℕ} (χ : DirichletCharacter ℂ q) (hL : 0 < L) (j b : Div L) :
    ContinuousAt (fun w : ℂ => dilationCoefficient χ w j b) 1 := by
  let A := fun w : ℂ => kernelMatrix χ w L
  have ht (n : ℕ) : Continuous (fun w : ℂ => twist χ w n) :=
    continuous_const.mul ((continuous_id.neg.mul continuous_const).cexp)
  have hA (i k : Div L) : Continuous (fun w => A w i k) := (ht _).mul (ht _)
  have hc : Continuous A := continuous_pi (fun i => continuous_pi (hA i))
  have hu : Continuous (fun w => (A w).updateRow b (Pi.single j 1)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    by_cases e : i = b
    · subst i
      simpa only [Matrix.updateRow_self] using (continuous_const : Continuous (fun _ : ℂ => Pi.single j (1 : ℂ) k))
    · simpa only [Matrix.updateRow_ne e] using hA i k
  have hl : Continuous (levelFactor (q^2*L) (q*j.1)) := (continuous_id.mul continuous_const).cexp
  have hn : (A 1).det*levelFactor (q^2*L) (q*j.1) 1 ≠ 0 :=
    mul_ne_zero (kernel_det_ne_zero χ (by norm_num : 0 < (1 : ℂ).re) L hL) (Complex.exp_ne_zero _)
  simpa only [dilationCoefficient,Matrix.adjugate_apply,A] using
    hu.matrix_det.continuousAt.div (hc.matrix_det.mul hl).continuousAt hn

private theorem ordinary_spatial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Continuous (ordinary χ s) := by
  by_cases e : q = 1
  · simpa only [show ordinary χ s = fun z => ordinaryScale χ s*completedPart χ s z from
      funext (ordinary_factors χ s),completedPart,if_pos e] using
      (completed_principal_spatial s).const_mul (ordinaryScale χ s)
  · simpa only [show ordinary χ s = fun z => ordinaryScale χ s*completedPart χ s z from
      funext (ordinary_factors χ s),completedPart,if_neg e] using
      (completed_character_spatial_all χ s).const_mul (ordinaryScale χ s)

private theorem finite_curve {ι : Type*} [Fintype ι] (c : ι → ℂ → ℂ) (F : ι → ℂ → ℍ → ℂ)
    (Z : ℝ → ℍ) (hZ : Continuous Z) (hF : ∀ i s, Continuous (F i s)) (r : ι → ℂ)
    (hc : ∀ i, ContinuousAt (c i) 1) (hf : ∀ i, Tendsto (fun s : ℂ => (s-1)*curveMean Z (F i) s)
      (𝓝[≠] 1) (𝓝 (r i))) : Tendsto (fun s : ℂ =>
      (s-1)*curveMean Z (fun w z => ∑ i, c i w*F i w z) s) (𝓝[≠] 1) (𝓝 (∑ i, c i 1*r i)) := by
  have HL := tendsto_finsetSum Finset.univ (fun i _ =>
    ((hc i).tendsto.mono_left nhdsWithin_le_nhds).mul (hf i))
  apply HL.congr'
  exact Eventually.of_forall (fun s => by
    unfold curveMean
    rw [intervalIntegral.integral_finsetSum (fun i _ =>
      (((hF i s).comp hZ).const_mul _).intervalIntegrable 0 1),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    ring)

private def dilate (B : ℕ+) (z : ℍ) : ℍ := degeneracyDiagonal B B.pos • z

private theorem dilate_cont (B : ℕ+) : Continuous (dilate B) := by
  change Continuous (fun z : ℍ => SpecialLinearGroup.mapGL ℝ (degeneracyDiagonal B B.pos) • z)
  exact continuous_const_smul _

def channelResidue {N : ℕ} [NeZero N] (i : CharacterSlots N) : ℂ :=
  ∑ b : Div (originalSlot i).L, dilationCoefficient i.2.primitiveCharacter 1 (originalSlot i).j b*
    dilationResidue i.2.conductor

private theorem channel_rep {N : ℕ} [NeZero N] (i : CharacterSlots N) :
    channelFunction i.1 i.2 = fun w z => ∑ b : Div (originalSlot i).L,
      dilationCoefficient i.2.primitiveCharacter w (originalSlot i).j b*
        ordinary i.2.primitiveCharacter w (dilate (dilation (originalSlot i).pos b) z) := by
  funext w z
  simpa only [dilationFunction,dilate] using ((originalSlot i).realized w z).trans
    (D_as_dilations i.2.primitiveCharacter (originalSlot i).pos (originalSlot i).j w z)

private theorem channel_spatial {N : ℕ} [NeZero N] (i : CharacterSlots N) (s : ℂ) :
    Continuous (channelFunction i.1 i.2 s) := by
  rw [channel_rep i]
  exact continuous_finsetSum _ (fun b _ => ((ordinary_spatial _ _).comp (dilate_cont _)).const_mul _)

theorem channel_curve_residue {N : ℕ} [NeZero N] (i : CharacterSlots N) (Z : ℝ → ℍ) (hZ : Continuous Z) :
    Tendsto (fun s : ℂ => (s-1)*curveMean Z (channelFunction i.1 i.2) s)
      (𝓝[≠] 1) (𝓝 (channelResidue i)) := by
  rw [channel_rep i]
  apply finite_curve _ _ Z hZ (fun b s => (ordinary_spatial _ s).comp (dilate_cont _))
    (fun _ => dilationResidue i.2.conductor) (fun b => coefficient_cont _ (originalSlot i).pos _ b)
  intro b
  exact ordinary_curve_residue i.2.primitiveCharacter _ ((dilate_cont _).comp hZ)

def nativeResidue (N : ℕ) [NeZero N] (p : NativeCusps N) : ℂ :=
  let a := (youngCuspEquiv N).symm p
  ∑ ξ : DirichletCharacter ℂ (band N a.1.1), inverseWeight a.1 a.2 ξ*channelResidue (⟨a.1,ξ⟩ : CharacterSlots N)

/-- The same residue is obtained on every continuous compact observation
path. A constant path and each physical observing horocycle belong
to that class. -/
theorem native_curve_residue (N : ℕ) [NeZero N] (a : NativeCusps N) (Z : ℝ → ℍ) (hZ : Continuous Z) :
    Tendsto (fun s : ℂ => (s-1)*curveMean Z (cuspFamily N a) s) (𝓝[≠] 1) (𝓝 (nativeResidue N a)) := by
  classical
  unfold nativeResidue cuspFamily
  generalize (youngCuspEquiv N).symm a = p
  rcases p with ⟨f,u⟩
  have H : parameterFamily (⟨f,u⟩ : Parameters N) = fun s z =>
      ∑ ξ : DirichletCharacter ℂ (band N f.1), inverseWeight f u ξ*channelFunction f ξ s z := by
    funext s z
    rw [inverse_cusp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    unfold inverseWeight
    ring
  rw [H]
  exact finite_curve _ _ Z hZ (fun ξ s => channel_spatial (⟨f,ξ⟩ : CharacterSlots N) s)
    (fun ξ => channelResidue (⟨f,ξ⟩ : CharacterSlots N)) (fun _ => continuousAt_const)
    (fun ξ => channel_curve_residue (⟨f,ξ⟩ : CharacterSlots N) Z hZ)

theorem native_point_residue (N : ℕ) [NeZero N] (a : NativeCusps N) (z : ℍ) :
    Tendsto (fun s : ℂ => (s-1)*cuspFamily N a s z) (𝓝[≠] 1) (𝓝 (nativeResidue N a)) := by
  simpa [curveMean] using native_curve_residue N a (fun _ => z) continuous_const

theorem scattering_entry_residue (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) :
    Tendsto (fun s : ℂ => (s-1)*continuedEntry N (NeZero.pos N) g h s) (𝓝[≠] 1)
      (𝓝 (nativeResidue N (nativeFrameOrbit N g))) := by
  classical
  let Z := fun x : ℝ => normalizedScaling N (NeZero.pos N) h • horizontalPoint 1 zero_lt_one x
  have hZ : Continuous Z := by
    change Continuous (fun x : ℝ => SpecialLinearGroup.mapGL ℝ (normalizedScaling N (NeZero.pos N) h) •
      horizontalPoint 1 zero_lt_one x)
    apply (continuous_const_smul _).comp
    unfold horizontalPoint
    fun_prop
  have hx : Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using ((continuous_id.sub (continuous_const (y := (1 : ℂ)))).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (1 : ℂ) ≤ 𝓝 1))
  have hI : ∀ s : ℂ, ActualParabolicScatteringRows20261110.incoming N g h s 1 =
      if nativeFrameOrbit N h = nativeFrameOrbit N g then 1 else 0 := fun s => by
    classical
    simp [ActualParabolicScatteringRows20261110.incoming]
  simpa only [continuedEntry,horocycleMean,mul_sub,hI,zero_mul,sub_zero,Z] using
    (native_curve_residue N (nativeFrameOrbit N g) Z hZ).sub (hx.mul
      (tendsto_const_nhds (x := (if nativeFrameOrbit N h = nativeFrameOrbit N g then (1 : ℂ) else 0))))

/-- All entries have the same residue at 1. The symmetry is used on a
deleted neighborhood where the actual functions are regular, and the
separate spatial computation supplies each true one-sided row value. -/
theorem equal_cusp_residues (N : ℕ) [NeZero N] (a b : NativeCusps N) :
    nativeResidue N a = nativeResidue N b := by
  obtain ⟨i,rfl⟩ := (nativeCuspEquiv N).surjective a
  obtain ⟨j,rfl⟩ := (nativeCuspEquiv N).surjective b
  have hnear : {s : ℂ | (1/2 : ℝ) < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  apply tendsto_nhds_unique_of_eventuallyEq (scattering_entry_residue N (classFrame i) (classFrame j))
    (scattering_entry_residue N (classFrame j) (classFrame i))
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnear,self_mem_nhdsWithin] with s hs (h₁ : s ≠ 1)
  rw [entries_symmetric N (NeZero.pos N) (classFrame i) (classFrame j) s hs.le h₁]

end
end ImbalancedChen.Part3.ActualNativeResidualChannel20261110
