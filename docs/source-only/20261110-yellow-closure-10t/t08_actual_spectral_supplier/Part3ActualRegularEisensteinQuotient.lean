import ImbalancedChen.Part3ActualCriticalScatteringUnitarity
import ImbalancedChen.Part3OriginalFrameZeroSeedMellin
import ImbalancedChen.Part3ActualContinuousPoincarePairing

/-! The continued unit-leading cusp functions on the physical quotient, at
all regular points between the initial and critical Mellin contours.
Compact zero-mode tests below use the actual quotient measurable structure. -/
namespace ImbalancedChen.Part3.ActualRegularEisensteinQuotient20261110

noncomputable section
open Set Filter Topology MeasureTheory Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators Classical
open ActualCharacterCuspExpansion20261110 ActualCompletedCurveMeans20261110
open ActualCharacterCriticalFamily20261110 ActualCharacterOriginalCuspFourier20261110
open ActualYoungCriticalD20261110 ActualYoungCriticalCusps20261110 ActualYoungFormalClass20261110
open ActualYoungCriticalProjection20261110 ActualCriticalCuspEvaluation20261110
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open ActualOrdinaryContinuousModes20261110 ActualContinuousSpatialProfiles20261110
open ActualPrincipalOldformRemoval20261102r
open Gamma0DegeneracyMapSourceOnly CompletedActualEisensteinIdentity20261025a
open FiniteLevelEisensteinOldforms20261025a Gamma0QuotientCellPushforward20261025a

private theorem dilation_props {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (N : ℕ) [NeZero N] (d : ℕ+) (hd : q^2*(d : ℕ) ∣ N)
    (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    let F := fun z : ℍ => ordinary χ s (degeneracyDiagonal d d.pos • z)
    Continuous F ∧ ∀ (γ : CongruenceSubgroup.Gamma0 N) (z : ℍ), F (γ • z) = F z := by
  have hD : Continuous (fun z : ℍ => degeneracyDiagonal d d.pos • z) := by
    change Continuous (fun z : ℍ => Matrix.SpecialLinearGroup.mapGL ℝ
      (degeneracyDiagonal d d.pos) • z)
    exact continuous_const_smul _
  by_cases h : q = 1
  · subst q
    refine ⟨?_,?_⟩
    · simpa only [ordinary,if_pos rfl,principalOrdinary,principalFactor] using
        ((completed_principal_spatial s).comp hD).const_mul (principalFactor s)
    · intro γ z
      simpa only [ordinary,if_pos rfl,principalOrdinary,principalFactor,← pnatDilate_eq_degeneracy] using
        congrArg (fun c : ℂ => principalFactor s*c)
          (principal_dilation_Gamma0_invariant N (NeZero.pos N) d (by simpa using hd) s hs₀ hs₁ γ.val γ.property z)
  · refine ⟨?_,?_⟩
    · simpa only [ordinary,if_neg h,primitiveFamily] using
        ((completed_character_spatial_all χ s).comp hD).const_mul (uncompletionFactor χ s)
    · intro γ z
      simpa only [ordinary,if_neg h,oldform] using
        oldform_invariant (NeZero.pos q) h χ hχ N d hd s γ.val γ.property z

private theorem channel_props {N : ℕ} [NeZero N] (i : CharacterSlots N) (s : ℂ)
    (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    Continuous (channelFunction i.1 i.2 s) ∧ ∀ (γ : CongruenceSubgroup.Gamma0 N) (z : ℍ),
      channelFunction i.1 i.2 s (γ • z) = channelFunction i.1 i.2 s z := by
  let S := originalSlot i
  letI : NeZero i.2.conductor := ⟨i.2.conductor_ne_zero⟩
  have E := funext (fun z => (S.realized s z).trans (D_as_dilations _ S.pos S.j s z))
  have H (b : Div S.L) := dilation_props i.2.primitiveCharacter i.2.primitiveCharacter_isPrimitive
    N (dilation S.pos b) (legal S b) s h₀ h₁
  rw [E]
  constructor
  · exact continuous_finsetSum _ (fun b _ => (H b).1.const_mul _)
  · intro γ z
    exact Finset.sum_congr rfl (fun b _ => congrArg (fun c : ℂ =>
      dilationCoefficient i.2.primitiveCharacter s S.j b*c) ((H b).2 γ z))

theorem native_regular_profile {N : ℕ} [NeZero N] (a : NativeCusps N) (s : ℂ)
    (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    Continuous (cuspFamily N a s) ∧ ∀ (γ : CongruenceSubgroup.Gamma0 N) (z : ℍ),
      cuspFamily N a s (γ • z) = cuspFamily N a s z := by
  classical
  change Continuous (fun z => parameterFamily ((youngCuspEquiv N).symm a) s z) ∧
    ∀ (γ : CongruenceSubgroup.Gamma0 N) (z : ℍ),
      parameterFamily ((youngCuspEquiv N).symm a) s (γ • z) = parameterFamily ((youngCuspEquiv N).symm a) s z
  generalize (youngCuspEquiv N).symm a = p
  rcases p with ⟨f,u⟩
  simp_rw [inverse_cusp]
  constructor
  · apply continuous_const.mul
    exact continuous_finsetSum _ (fun ξ _ => ((channel_props (⟨f,ξ⟩ : CharacterSlots N) s h₀ h₁).1).const_mul _)
  · intro γ z
    congr 1
    apply Finset.sum_congr rfl
    intro ξ _
    rw [(channel_props (⟨f,ξ⟩ : CharacterSlots N) s h₀ h₁).2 γ z]

def descended {N : ℕ} [NeZero N] (a : NativeCusps N) (s : ℂ) (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (cuspFamily N a s) (by
    intro z w h
    obtain ⟨γ,hγ⟩ := MulAction.orbitRel_apply.mp h
    rw [← hγ]
    exact (native_regular_profile a s h₀ h₁).2 γ w)

@[simp] theorem descended_projection {N : ℕ} [NeZero N] (a : NativeCusps N)
    (s : ℂ) (h₀ : s ≠ 0) (h₁ : s ≠ 1) (z : ℍ) :
    descended a s h₀ h₁ (orbitProjection N z) = cuspFamily N a s z := rfl

theorem descended_continuous_measurable {N : ℕ} [NeZero N] (a : NativeCusps N)
    (s : ℂ) (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    Continuous (descended a s h₀ h₁) ∧ Measurable (descended a s h₀ h₁) :=
  ⟨(native_regular_profile a s h₀ h₁).1.quotient_lift _,
    measurable_from_quotient.mpr (native_regular_profile a s h₀ h₁).1.measurable⟩

theorem descended_critical {N : ℕ} [NeZero N] (a : NativeCusps N) (t : ℝ)
    (h₀ : criticalPoint t ≠ 0) (h₁ : criticalPoint t ≠ 1) :
    descended a (criticalPoint t) h₀ h₁ = quotientProfile ((youngCuspEquiv N).symm a) t := by
  funext u
  exact Quotient.inductionOn u (fun _ => rfl)

end
end ImbalancedChen.Part3.ActualRegularEisensteinQuotient20261110
