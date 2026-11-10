import ImbalancedChen.Part3ActualRegularEisensteinQuotient
import ImbalancedChen.Part3OriginalResidualPoincarePackets

/-! Exact physical transforms of the compact zero-mode generators of the
noncuspidal subspace. The cutoff used in the proof is equal to the true
generalized eigenfunction on the entire support of the unfolded test. -/
namespace ImbalancedChen.Part3.ActualIncompleteEisensteinTransform20261110

noncomputable section
open Set Filter Topology MeasureTheory Complex Matrix UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators Classical
open ActualRegularEisensteinQuotient20261110 ActualCriticalScatteringEntry20261110
open ActualCharacterCuspExpansion20261110 ActualCriticalCuspEvaluation20261110 ActualYoungCriticalCusps20261110
open ActualParabolicScatteringRows20261110 ActualEisensteinFourierInterchange20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0GeneralCuspUnitPeriod20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a ActualPoincareSpectralCoefficient20261026a
open NormalizedCuspCompactPoincare20261026b NormalizedCuspCompactFourierFubini20261026b
open NormalizedCuspCompactQuotientLp20261026b CompactSeedArbitraryQuotientPairing20261026b
open CompactCuspParabolicL220261025a ActualInfinityCuspAnnihilator20261026b
open AllNormalizedCuspAnnihilator20261026b

def zeroPoincare (N : ℕ) [NeZero N] (h : SL(2,ℤ)) (ψ : HeightSeed) : Gamma0OrbitSpace N → ℂ :=
  complexPoincare N (physicalFrameSeed N (NeZero.pos N) h 0 ψ.toFun)

def moment (ψ : HeightSeed) (s : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) • (star (ψ.toFun y)*(y : ℂ)^s)

theorem moment_integrable (ψ : HeightSeed) (s : ℂ) :
    IntegrableOn (fun y : ℝ => ((y⁻¹)^2 : ℝ) • (star (ψ.toFun y)*(y : ℂ)^s)) (Ioi 0) := by
  let F := fun y : ℝ => ((y⁻¹)^2 : ℝ) • (star (ψ.toFun y)*(y : ℂ)^s)
  have H : ContinuousOn F (tsupport ψ.toFun) :=
    ((continuousOn_id.inv₀ (fun y hy => (ψ.positive hy).ne')).pow 2).smul
      (ψ.continuous.star.continuousOn.mul (fun y hy =>
        (Complex.continuousAt_ofReal_cpow_const y s (.inr (ψ.positive hy).ne')).continuousWithinAt))
  have K : Function.support F ⊆ tsupport ψ.toFun := by
    intro y hy
    by_contra e
    exact hy (by simp [F,image_eq_zero_of_notMem_tsupport e])
  exact ((integrableOn_iff_integrable_of_support_subset K).mp
    (ContinuousOn.integrableOn_compact ψ.compact H)).integrableOn

private theorem compact_pair {N : ℕ} [NeZero N] (h : SL(2,ℤ)) (ψ : HeightSeed)
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (fun z : ℍ => U (orbitProjection N z))) :
    Integrable (fun u => star (zeroPoincare N h ψ u)*U u) (carrierPushforward N) ∧
    (∫ u,star (zeroPoincare N h ψ u)*U u ∂carrierPushforward N) =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) • (star (ψ.toFun y)*frameFourier N (NeZero.pos N) h U 0 y) := by
  classical
  let K := frameAction N (NeZero.pos N) h '' cuspSupportK ψ.toFun
  let f := physicalFrameSeed N (NeZero.pos N) h 0 ψ.toFun
  have hK : IsCompact K := (cuspSupportK_isCompact _ ψ.compact ψ.positive).image
    (frameAction_continuous N (NeZero.pos N) h)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hU.continuousOn
  let C := max B 0
  let V := {u : Gamma0OrbitSpace N | ‖U u‖ ≤ C}.indicator U
  have hu : Measurable U := measurable_from_quotient.mpr hU.measurable
  have hv : Measurable V := hu.indicator (measurableSet_le hu.norm measurable_const)
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  have vL : MemLp V 2 (carrierPushforward N) := MemLp.of_bound hv.aestronglyMeasurable C (by
    apply ae_of_all
    intro u
    by_cases H : ‖U u‖ ≤ C
    · simpa [V,H] using H
    · simp [V,H,C])
  have onK {w : ℍ} (hw : w ∈ K) : V (orbitProjection N w) = U (orbitProjection N w) := by
    exact indicator_of_mem ((hB w hw).trans (le_max_left B 0)) _
  have A : (fun w : ℍ => star (f w)*testLift N U w) = fun w => star (f w)*testLift N V w := by
    funext w
    by_cases hw : f w = 0
    · simp [hw]
    · change star (f w)*U (orbitProjection N w) = star (f w)*V (orbitProjection N w)
      rw [onK (physicalFrameSeed_support N _ h 0 _ hw)]
  have Q : (fun u => star (zeroPoincare N h ψ u)*U u) =ᵐ[carrierPushforward N]
      fun u => star (zeroPoincare N h ψ u)*V u := by
    rw [← reducedProjection_map_measure N,(reducedProjection_measurableEmbedding N).ae_map_iff]
    apply ae_of_all
    intro w
    change star (complexPoincare N f (reducedProjection N w))*U (reducedProjection N w) =
      star (complexPoincare N f (reducedProjection N w))*V (reducedProjection N w)
    rw [complexPoincare_projection]
    exact ((compact_pair_full_trace N f U w).symm.trans (congrArg (fun G => complexSeedTrace N G w) A)).trans
      (compact_pair_full_trace N f V w)
  have P := framePoincare_memLp_two N (NeZero.pos N) h 0 ψ.toFun ψ.continuous ψ.compact ψ.positive
  refine ⟨(MemLp.integrable_mul (p := 2) (q := 2) P.star vL).congr Q.symm,?_⟩
  rw [integral_congr_ae Q,zeroPoincare,framePoincare_pairing_eq_fourier N _ h 0 _
    ψ.continuous ψ.compact ψ.positive V vL]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  by_cases e : ψ.toFun y = 0
  · simp [e]
  · have E : frameFourier N (NeZero.pos N) h V 0 y = frameFourier N (NeZero.pos N) h U 0 y := by
      rw [frameFourier_positive_height _ _ _ _ _ hy,frameFourier_positive_height _ _ _ _ _ hy]
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      rw [onK (show frameAction N (NeZero.pos N) h (⟨⟨x,y⟩,hy⟩ : ℍ) ∈ K from
        ⟨_,⟨⟨hx.1,hx.2.le⟩,subset_tsupport _ e⟩,rfl⟩)]
    rw [E]

private theorem zeroth {N : ℕ} [NeZero N] (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1/2 ≤ s.re) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) (y : ℝ) (hy : 0 < y) :
    frameFourier N (NeZero.pos N) h (descended (nativeFrameOrbit N g) s hs₀ hs₁) 0 y =
      ActualParabolicScatteringRows20261110.incoming N g h s y + continuedEntry N (NeZero.pos N) g h s*(y : ℂ)^(1-s) := by
  rw [frameFourier_positive_height _ _ _ _ _ hy,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  simpa only [neg_zero,AddCircle.fourier_zero,Pi.one_apply,one_mul,frameAction,descended_projection,
    horizontalPoint] using actual_constant_term N (NeZero.pos N) g h s hs hs₁ y hy

/-- Physical pairing of every sharp compact zero-mode generator against
a true normalized incoming state, over the full regular closed half-plane. -/
theorem physical_zero_transform (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ : HeightSeed)
    (s : ℂ) (hs : 1/2 ≤ s.re) (hs₁ : s ≠ 1) :
    let hs₀ : s ≠ 0 := by intro e; simp [e] at hs
    let U := descended (nativeFrameOrbit N g) s hs₀ hs₁
    Integrable (fun u => star (zeroPoincare N h ψ u)*U u) (carrierPushforward N) ∧
    (∫ u,star (zeroPoincare N h ψ u)*U u ∂carrierPushforward N) =
      (if nativeFrameOrbit N h = nativeFrameOrbit N g then moment ψ s else 0) +
        continuedEntry N (NeZero.pos N) g h s*moment ψ (1-s) := by
  classical
  let hs₀ : s ≠ 0 := by intro e; simp [e] at hs
  let U := descended (nativeFrameOrbit N g) s hs₀ hs₁
  obtain ⟨H,J⟩ := compact_pair h ψ U (native_regular_profile (nativeFrameOrbit N g) s hs₀ hs₁).1
  refine ⟨H,J.trans ?_⟩
  let c := continuedEntry N (NeZero.pos N) g h s
  let M := fun (v : ℂ) (y : ℝ) => ((y⁻¹)^2 : ℝ) • (star (ψ.toFun y)*(y : ℂ)^v)
  let b : ℂ := if nativeFrameOrbit N h = nativeFrameOrbit N g then 1 else 0
  have gram : (∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) • (star (ψ.toFun y)*frameFourier N (NeZero.pos N) h U 0 y)) =
      ∫ y in Ioi (0 : ℝ), b*M s y+c*M (1-s) y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    rw [show frameFourier N _ h U 0 y = _ from zeroth g h s hs hs₀ hs₁ y hy]
    by_cases e : nativeFrameOrbit N h = nativeFrameOrbit N g <;>
      simp [b,c,M,ActualParabolicScatteringRows20261110.incoming,e,Complex.real_smul] <;> ring
  rw [gram,integral_add ((moment_integrable ψ s).const_mul b) ((moment_integrable ψ (1-s)).const_mul c),
    integral_const_mul,integral_const_mul]
  by_cases e : nativeFrameOrbit N h = nativeFrameOrbit N g <;> simp [b,c,M,moment,e]

end
end ImbalancedChen.Part3.ActualIncompleteEisensteinTransform20261110
