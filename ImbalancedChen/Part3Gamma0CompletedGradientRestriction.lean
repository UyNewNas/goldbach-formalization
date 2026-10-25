import ImbalancedChen.Part3Gamma0EnergyCompactGradientExtension

/-!
# Coherence of actual completed compact gradients under restriction

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

For K1 subset K2, native measure domination gives the genuine vector L2
restriction, upgraded to a bounded COMPLEX-linear contraction. Its actual
representative is unchanged almost everywhere on K1. The original core
gradients restrict exactly because both are the same weighted geometric
vector field. The genuine dense energy-core extension then proves exact
restriction coherence for every vector in the SAME actual energy
completion. No compatibility conclusion is a caller premise.

This is local vector-valued L2 on H. No global H-L2 gradient, scalar
quotient gradient, adjoint-defect form membership or elliptic regularity
is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0CompletedGradientRestriction20261025a
noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0CompactCoreGradient20261025a
open ImbalancedChen.Part3.Gamma0EnergyCompactGradientExtension20261025a

theorem restrictedVolume_le {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2) :
    (volume : Measure UpperHalfPlane).restrict K1 ≤ volume.restrict K2 :=
  Measure.restrict_mono h12 le_rfl

private def restrictionReal {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2) :
    CompactGradientL2 K2 →L[ℝ] CompactGradientL2 K1 :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using restrictedVolume_le h12)

private theorem restrictionReal_coe_ae {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2)
    (v : CompactGradientL2 K2) :
    restrictionReal h12 v =ᵐ[(volume : Measure UpperHalfPlane).restrict K1] v :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using restrictedVolume_le h12) v

private theorem restrictionReal_norm_le {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2)
    (v : CompactGradientL2 K2) : ‖restrictionReal h12 v‖ ≤ ‖v‖ := by
  have hnorm : ‖restrictionReal h12‖ ≤ 1 := by
    simpa only [restrictionReal,ENNReal.toReal_one,Real.one_rpow] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le (E := GradientFiber) (p := 2) (c := 1)
        (by simp) (by simpa only [one_smul] using restrictedVolume_le h12))
  exact ((restrictionReal h12).le_opNorm v).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))

/-- Native measure restriction with actual complex homogeneity on the
Lp quotient, proved by its genuine AE representatives. -/
private def restrictionLinear {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2) :
    CompactGradientL2 K2 →ₗ[ℂ] CompactGradientL2 K1 where
  toFun := restrictionReal h12
  map_add' := (restrictionReal h12).map_add
  map_smul' c v := by
    apply Lp.ext
    have hAC : (volume : Measure UpperHalfPlane).restrict K1 ≪ volume.restrict K2 :=
      Measure.absolutelyContinuous_of_le (restrictedVolume_le h12)
    filter_upwards [restrictionReal_coe_ae h12 (c • v),restrictionReal_coe_ae h12 v,
      Lp.coeFn_smul c (restrictionReal h12 v),hAC.ae_eq (Lp.coeFn_smul c v)]
      with z hleft hv hright hinput
    rw [hleft,hright,hv,hinput]

def compactGradientRestriction {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2) :
    CompactGradientL2 K2 →L[ℂ] CompactGradientL2 K1 :=
  (restrictionLinear h12).mkContinuous 1 (fun v => by
    simpa only [one_mul] using restrictionReal_norm_le h12 v)

theorem compactGradientRestriction_coe_ae {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2)
    (v : CompactGradientL2 K2) :
    compactGradientRestriction h12 v =ᵐ[(volume : Measure UpperHalfPlane).restrict K1] v :=
  restrictionReal_coe_ae h12 v

theorem compactGradientRestriction_norm_le {K1 K2 : Set UpperHalfPlane} (h12 : K1 ⊆ K2)
    (v : CompactGradientL2 K2) : ‖compactGradientRestriction h12 v‖ ≤ ‖v‖ :=
  restrictionReal_norm_le h12 v

theorem compactGradientRestriction_opNorm_le_one {K1 K2 : Set UpperHalfPlane}
    (h12 : K1 ⊆ K2) : ‖compactGradientRestriction h12‖ ≤ 1 := by
  apply (compactGradientRestriction h12).opNorm_le_bound zero_le_one
  intro v
  simpa only [one_mul] using compactGradientRestriction_norm_le h12 v

/-- Both compact core L2 vectors are literally the SAME actual
weightedCoreGradient on their respective restricted volume measures. -/
theorem coreGradientL2_restriction (N : ℕ) [NeZero N]
    {K1 K2 : Set UpperHalfPlane} (hK1 : IsCompact K1) (hK2 : IsCompact K2)
    (h12 : K1 ⊆ K2) (u : EnergyCore N) :
    compactGradientRestriction h12 (coreGradientL2 N hK2 u) = coreGradientL2 N hK1 u := by
  apply Lp.ext
  have hAC : (volume : Measure UpperHalfPlane).restrict K1 ≪ volume.restrict K2 :=
    Measure.absolutelyContinuous_of_le (restrictedVolume_le h12)
  have h2 : coreGradientL2 N hK2 u =ᵐ[(volume : Measure UpperHalfPlane).restrict K2]
      weightedCoreGradient N u := (weightedCoreGradient_compact_memLp N hK2 u).coeFn_toLp
  have h1 : coreGradientL2 N hK1 u =ᵐ[(volume : Measure UpperHalfPlane).restrict K1]
      weightedCoreGradient N u := (weightedCoreGradient_compact_memLp N hK1 u).coeFn_toLp
  exact ((compactGradientRestriction_coe_ae h12 _).trans (hAC.ae_eq h2)).trans h1.symm

/-- Exact coherence follows from genuine agreement on the actual dense
energy core and the unique continuous completion extension. -/
theorem completedCompactGradient_restriction (N : ℕ) [NeZero N]
    {K1 K2 : Set UpperHalfPlane} (hK1 : IsCompact K1) (hK2 : IsCompact K2)
    (h12 : K1 ⊆ K2) :
    completedCompactGradient N hK1 =
      (compactGradientRestriction h12).comp (completedCompactGradient N hK2) := by
  symm
  apply completedCompactGradient_unique N hK1
  intro u
  change compactGradientRestriction h12 (completedCompactGradient N hK2 (coreEmbedding N u)) = _
  rw [completedCompactGradient_core,coreGradientL2_restriction N hK1 hK2 h12 u]

theorem completedCompactGradient_restriction_apply (N : ℕ) [NeZero N]
    {K1 K2 : Set UpperHalfPlane} (hK1 : IsCompact K1) (hK2 : IsCompact K2)
    (h12 : K1 ⊆ K2) (e : EnergyCompletion N) :
    completedCompactGradient N hK1 e = compactGradientRestriction h12 (completedCompactGradient N hK2 e) :=
  congrArg (fun A : EnergyCompletion N →L[ℂ] CompactGradientL2 K1 => A e)
    (completedCompactGradient_restriction N hK1 hK2 h12)

end
end ImbalancedChen.Part3.Gamma0CompletedGradientRestriction20261025a
