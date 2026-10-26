import ImbalancedChen.Part3GammaGeneratedSectorHeatResolventBlocks

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual generated-sector projection splits the TRUE unbounded native
Gamma0 Friedrichs graph, preserving its full domain and commuting with
its actual output. This is derived from the native shifted resolvent at
one and the already proved resolvent projection commutation. Neither an
operator-domain splitting nor a graph-invariance premise is assumed.
The two sectors retain their literal physical generated definitions;
full cusp/Eisenstein completeness remains OPEN.
-/
namespace ImbalancedChen.Part3.GammaGeneratedSectorNativeGraphReduction20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualConstantMode20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a
open GammaCuspidalEigenSpectralOrthogonality20261026b
open GammaGeneratedSectorHeatResolventBlocks20261026b

/-- The actual positive shifted inverse at one recovers the original
physical R=JJ*, by the native inverse identity on its true domain. -/
theorem actual_shiftedResolvent_one_apply (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualGammaShiftedResolvent N 1 f = actualGammaResolvent N f := by
  have h := actualGammaShiftedResolvent_on_domain N (by norm_num : 0 < (1 : ℝ))
    (actualResolventPoint N f)
  have hi : ((1 : ℝ) : ℂ) • (actualResolventPoint N f : QuotientL2 N) +
      actualGammaFriedrichs N (actualResolventPoint N f) = f := by
    rw [actualGammaFriedrichs_apply_resolvent]
    change (1 : ℂ) • actualGammaResolvent N f + (f - actualGammaResolvent N f) = f
    rw [one_smul]
    abel
  rw [hi] at h
  exact h

theorem generatedSectorProjection_resolvent_commute (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) (f : QuotientL2 N) :
    generatedSectorProjection N s (actualGammaResolvent N f) =
      actualGammaResolvent N (generatedSectorProjection N s f) := by
  have h := generatedSectorProjection_shiftedResolvent_commute N s
    (by norm_num : 0 < (1 : ℝ)) f
  simpa only [actual_shiftedResolvent_one_apply] using h

/-- Exact projection of BOTH input and output in the actual native graph. -/
theorem generatedSectorProjection_preserves_native_graph (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) {u v : QuotientL2 N}
    (huv : (u, v) ∈ (actualGammaFriedrichs N).graph) :
    (generatedSectorProjection N s u, generatedSectorProjection N s v) ∈
      (actualGammaFriedrichs N).graph := by
  apply (actualGammaFriedrichs_mem_graph_iff N).mpr
  calc
    actualGammaResolvent N (generatedSectorProjection N s u + generatedSectorProjection N s v) =
        actualGammaResolvent N (generatedSectorProjection N s (u + v)) := by rw [map_add]
    _ = generatedSectorProjection N s (actualGammaResolvent N (u + v)) :=
      (generatedSectorProjection_resolvent_commute N s (u + v)).symm
    _ = generatedSectorProjection N s u :=
      congrArg (generatedSectorProjection N s) ((actualGammaFriedrichs_mem_graph_iff N).mp huv)

theorem generatedSectorResidual_preserves_native_graph (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) {u v : QuotientL2 N}
    (huv : (u, v) ∈ (actualGammaFriedrichs N).graph) :
    (u - generatedSectorProjection N s u, v - generatedSectorProjection N s v) ∈
      (actualGammaFriedrichs N).graph :=
  (actualGammaFriedrichs N).graph.sub_mem huv
    (generatedSectorProjection_preserves_native_graph N s huv)

/-- Full native graph block equivalence; the residual block is retained. -/
theorem actual_native_graph_iff_generated_sector_blocks (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) (u v : QuotientL2 N) :
    (u, v) ∈ (actualGammaFriedrichs N).graph ↔
      (generatedSectorProjection N s u, generatedSectorProjection N s v) ∈
        (actualGammaFriedrichs N).graph ∧
      (u - generatedSectorProjection N s u, v - generatedSectorProjection N s v) ∈
        (actualGammaFriedrichs N).graph := by
  constructor
  · intro h
    exact ⟨generatedSectorProjection_preserves_native_graph N s h,
      generatedSectorResidual_preserves_native_graph N s h⟩
  · rintro ⟨hp, hr⟩
    have hs := (actualGammaFriedrichs N).graph.add_mem hp hr
    have heq : (generatedSectorProjection N s u, generatedSectorProjection N s v) +
        (u - generatedSectorProjection N s u, v - generatedSectorProjection N s v) = (u, v) := by
      ext <;> dsimp <;> abel
    rwa [heq] at hs

/-- The projected input belongs to the actual original native domain. -/
def generatedSectorNativeDomainPoint (N : ℕ) [NeZero N] (s : GeneratedPhysicalSector)
    (u : (actualGammaFriedrichs N).domain) : (actualGammaFriedrichs N).domain :=
  ⟨generatedSectorProjection N s u,
    LinearPMap.mem_domain_of_mem_graph
      (generatedSectorProjection_preserves_native_graph N s ((actualGammaFriedrichs N).mem_graph u))⟩

/-- Actual unbounded output commutation on every original domain point. -/
theorem actualGammaFriedrichs_generatedSectorNativeDomainPoint (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N (generatedSectorNativeDomainPoint N s u) =
      generatedSectorProjection N s (actualGammaFriedrichs N u) :=
  (actualGammaFriedrichs N).mem_graph_snd_inj
    ((actualGammaFriedrichs N).mem_graph (generatedSectorNativeDomainPoint N s u))
    (generatedSectorProjection_preserves_native_graph N s ((actualGammaFriedrichs N).mem_graph u)) rfl

theorem actualGammaFriedrichs_generatedSector_output_mem (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) (u : (actualGammaFriedrichs N).domain)
    (hu : (u : QuotientL2 N) ∈ generatedSectorSubmodule N s) :
    actualGammaFriedrichs N u ∈ generatedSectorSubmodule N s := by
  have hpu : generatedSectorProjection N s u = (u : QuotientL2 N) :=
    (generatedSectorSubmodule N s).starProjection_eq_self_iff.mpr hu
  have hp := generatedSectorProjection_preserves_native_graph N s ((actualGammaFriedrichs N).mem_graph u)
  rw [hpu] at hp
  have hout : generatedSectorProjection N s (actualGammaFriedrichs N u) =
      actualGammaFriedrichs N u :=
    (actualGammaFriedrichs N).mem_graph_snd_inj hp ((actualGammaFriedrichs N).mem_graph u) rfl
  exact (generatedSectorSubmodule N s).starProjection_eq_self_iff.mp hout

/-- Physical mixed native Friedrichs coefficients vanish on the actual
full-domain cusp point sector against every completed incomplete test. -/
theorem actual_native_friedrichs_physical_sectors_cross_zero (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) {g : QuotientL2 N}
    (hu : (u : QuotientL2 N) ∈ actualInfinityCuspEigenPointSpace N)
    (hg : g ∈ actualIncompleteEisensteinBorelTestSpace N) :
    inner ℂ (actualGammaFriedrichs N u) g = 0 :=
  Submodule.inner_left_of_mem_orthogonal hg
    (actual_cusp_pointSpace_le_incompleteEisenstein_testSpace_orthogonal N
      (actualGammaFriedrichs_generatedSector_output_mem N .cuspEigenPoint u hu))

end
end ImbalancedChen.Part3.GammaGeneratedSectorNativeGraphReduction20261026b
