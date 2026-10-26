import ImbalancedChen.Part3GammaCuspidalEigenSpectralOrthogonality

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two literal physical generated spaces from the preceding module are
invariant under every true real-lambda Borel spectral projection. For the
native cusp point space this follows from proved eigenvector localization;
for the incomplete Eisenstein test-orbit space it follows from the genuine
Borel intersection product law. Continuity passes both laws through the
actual closed spans. Mixed complex spectral coefficients vanish for all
vectors in these spaces, and their actual Laplace scalar measures obey
the full squared-coefficient polarization formula.

These are generated physical sectors. Their equality with the entire
cuspidal/continuous spectrum, all-cusp completeness, and Plancherel density
are not premises or conclusions.
-/
namespace ImbalancedChen.Part3.GammaPhysicalSpectralSectorReduction20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualConstantMode20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open GenericResolventScalarMeasure20261025a
open GenericResolventUnboundedScalarMeasure20261025a
open GenericGlobalBorelProjection20261025a
open GenericGlobalProjectionScalarConsistency20261025a
open GammaMeanCenteredScalarMeasure20261026b
open GammaNativeEigenBorelLocalization20261026b
open GammaCuspidalEigenSpectralOrthogonality20261026b

section ClosedSpan
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Continuity supplies invariance of an actual closed span from its
generators; no invariance property of the completed space is assumed. -/
theorem closed_span_map_mem_of_generators (S : Set H) (T : H →L[ℂ] H)
    (hT : ∀ v ∈ S, T v ∈ Submodule.span ℂ S)
    {u : H} (hu : u ∈ (Submodule.span ℂ S).topologicalClosure) :
    T u ∈ (Submodule.span ℂ S).topologicalClosure := by
  have hspan : Submodule.span ℂ S ≤
      ((Submodule.span ℂ S).topologicalClosure).comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    intro v hv
    exact (Submodule.span ℂ S).le_topologicalClosure (hT v hv)
  exact (Submodule.span ℂ S).topologicalClosure_minimal hspan
    ((Submodule.span ℂ S).isClosed_topologicalClosure.preimage T.continuous) hu
end ClosedSpan

theorem actualLaplaceBorelProjection_comp_inter (N : ℕ) [NeZero N]
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (actualLaplaceBorelProjection N B hB).comp (actualLaplaceBorelProjection N C hC) =
      actualLaplaceBorelProjection N (B ∩ C) (hB.inter hC) := by
  change (globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    ((measurable_spectralLambda (actualGammaResolvent N)) hB)).comp
    (globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
      (spectralLambda (actualGammaResolvent N) ⁻¹' C)
      ((measurable_spectralLambda (actualGammaResolvent N)) hC)) = _
  rw [globalBorelProjection_comp_inter]
  simp only [actualLaplaceBorelProjection, Set.preimage_inter]

theorem actual_cusp_pointSpace_borel_invariant (N : ℕ) [NeZero N]
    (B : Set ℝ) (hB : MeasurableSet B) {f : QuotientL2 N}
    (hf : f ∈ actualInfinityCuspEigenPointSpace N) :
    actualLaplaceBorelProjection N B hB f ∈ actualInfinityCuspEigenPointSpace N := by
  apply closed_span_map_mem_of_generators
    (Set.range (fun e : NativeInfinityCuspEigenvector N => e.vector))
    (actualLaplaceBorelProjection N B hB) ?_ hf
  rintro v ⟨e, rfl⟩
  rw [actual_native_eigenvector_borel_apply N e.vector e.eigenvalue e.native_graph]
  split_ifs
  · exact Submodule.subset_span ⟨e, rfl⟩
  · exact Submodule.zero_mem _

theorem actual_incompleteEisenstein_testSpace_borel_invariant (N : ℕ) [NeZero N]
    (B : Set ℝ) (hB : MeasurableSet B) {f : QuotientL2 N}
    (hf : f ∈ actualIncompleteEisensteinBorelTestSpace N) :
    actualLaplaceBorelProjection N B hB f ∈ actualIncompleteEisensteinBorelTestSpace N := by
  apply closed_span_map_mem_of_generators (actualIncompleteEisensteinBorelTests N)
    (actualLaplaceBorelProjection N B hB) ?_ hf
  rintro v ⟨s, C, hC, rfl⟩
  have hcomp := congrArg (fun T : QuotientL2 N →L[ℂ] QuotientL2 N =>
    T (ActualInfinityCuspAnnihilator20261026b.zeroSeedL2 N s))
    (actualLaplaceBorelProjection_comp_inter N B C hB hC)
  change actualLaplaceBorelProjection N B hB
    (actualLaplaceBorelProjection N C hC (ActualInfinityCuspAnnihilator20261026b.zeroSeedL2 N s)) =
    actualLaplaceBorelProjection N (B ∩ C) (hB.inter hC)
      (ActualInfinityCuspAnnihilator20261026b.zeroSeedL2 N s) at hcomp
  rw [hcomp]
  exact Submodule.subset_span ⟨s, B ∩ C, hB.inter hC, rfl⟩

/-- Self-adjointness of the actual Borel projection also preserves the
orthogonal complement of an invariant physical closed sector. -/
theorem actual_borel_orthogonal_invariant (N : ℕ) [NeZero N]
    (K : Submodule ℂ (QuotientL2 N)) (B : Set ℝ) (hB : MeasurableSet B)
    (hK : ∀ v ∈ K, actualLaplaceBorelProjection N B hB v ∈ K)
    {f : QuotientL2 N} (hf : f ∈ Kᗮ) : actualLaplaceBorelProjection N B hB f ∈ Kᗮ := by
  intro v hv
  have hi := globalBorelProjection_inner (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N)
    (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    ((measurable_spectralLambda (actualGammaResolvent N)) hB) v f
  change inner ℂ (actualLaplaceBorelProjection N B hB v) f =
    inner ℂ v (actualLaplaceBorelProjection N B hB f) at hi
  rw [← hi]
  exact hf _ (hK v hv)

theorem actual_cusp_pointSpace_orthogonal_borel_invariant (N : ℕ) [NeZero N]
    (B : Set ℝ) (hB : MeasurableSet B) {f : QuotientL2 N}
    (hf : f ∈ (actualInfinityCuspEigenPointSpace N)ᗮ) :
    actualLaplaceBorelProjection N B hB f ∈ (actualInfinityCuspEigenPointSpace N)ᗮ :=
  actual_borel_orthogonal_invariant N _ B hB
    (fun _ hv => actual_cusp_pointSpace_borel_invariant N B hB hv) hf

theorem actual_incompleteEisenstein_testSpace_orthogonal_borel_invariant
    (N : ℕ) [NeZero N] (B : Set ℝ) (hB : MeasurableSet B) {f : QuotientL2 N}
    (hf : f ∈ (actualIncompleteEisensteinBorelTestSpace N)ᗮ) :
    actualLaplaceBorelProjection N B hB f ∈ (actualIncompleteEisensteinBorelTestSpace N)ᗮ :=
  actual_borel_orthogonal_invariant N _ B hB
    (fun _ hv => actual_incompleteEisenstein_testSpace_borel_invariant N B hB hv) hf

/-- Vanishing of the full complex Borel coefficient on both actual
completed physical sectors, rather than on individual seeds alone. -/
theorem actual_physical_sector_spectral_cross_zero (N : ℕ) [NeZero N]
    {f g : QuotientL2 N} (hf : f ∈ actualInfinityCuspEigenPointSpace N)
    (hg : g ∈ actualIncompleteEisensteinBorelTestSpace N)
    (B : Set ℝ) (hB : MeasurableSet B) :
    inner ℂ (actualLaplaceBorelProjection N B hB f) g = 0 := by
  have hp := actual_cusp_pointSpace_borel_invariant N B hB hf
  have ho := actual_cusp_pointSpace_le_incompleteEisenstein_testSpace_orthogonal N hp
  exact Submodule.inner_left_of_mem_orthogonal hg ho

theorem actual_physical_sector_projected_cross_zero (N : ℕ) [NeZero N]
    {f g : QuotientL2 N} (hf : f ∈ actualInfinityCuspEigenPointSpace N)
    (hg : g ∈ actualIncompleteEisensteinBorelTestSpace N)
    (B : Set ℝ) (hB : MeasurableSet B) :
    inner ℂ (actualLaplaceBorelProjection N B hB f)
      (actualLaplaceBorelProjection N B hB g) = 0 :=
  actual_physical_sector_spectral_cross_zero N hf
    (actual_incompleteEisenstein_testSpace_borel_invariant N B hB hg) B hB

/-- The same actual unbounded scalar measure is the norm of the true
real-lambda projection. This is derived from its inverse-resolvent map. -/
theorem actualLaplaceMeasure_eq_borel_projection_norm_sq (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (B : Set ℝ) (hB : MeasurableSet B) :
    actualLaplaceMeasure N f B =
      ENNReal.ofReal (‖actualLaplaceBorelProjection N B hB f‖ ^ 2) := by
  change ((scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f).map
    (spectralLambda (actualGammaResolvent N))) B = _
  rw [Measure.map_apply (measurable_spectralLambda (actualGammaResolvent N)) hB]
  exact scalarMeasure_eq_projection_norm_square (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) f
    (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    ((measurable_spectralLambda (actualGammaResolvent N)) hB)

/-- Genuine measure splitting for arbitrary vectors in the two completed
physical generated sectors and arbitrary complex coefficients. -/
theorem actualLaplaceMeasure_physical_sector_linear_combination (N : ℕ) [NeZero N]
    {f g : QuotientL2 N} (hf : f ∈ actualInfinityCuspEigenPointSpace N)
    (hg : g ∈ actualIncompleteEisensteinBorelTestSpace N) (a b : ℂ) :
    actualLaplaceMeasure N (a • f + b • g) =
      ENNReal.ofReal (‖a‖ ^ 2) • actualLaplaceMeasure N f +
        ENNReal.ofReal (‖b‖ ^ 2) • actualLaplaceMeasure N g := by
  apply Measure.ext
  intro B hB
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [actualLaplaceMeasure_eq_borel_projection_norm_sq N _ B hB,
    actualLaplaceMeasure_eq_borel_projection_norm_sq N f B hB,
    actualLaplaceMeasure_eq_borel_projection_norm_sq N g B hB,
    map_add, map_smul, map_smul]
  have hc : inner ℂ (a • actualLaplaceBorelProjection N B hB f)
      (b • actualLaplaceBorelProjection N B hB g) = 0 := by
    rw [inner_smul_left, inner_smul_right,
      actual_physical_sector_projected_cross_zero N hf hg B hB, mul_zero, mul_zero]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hc,
    norm_smul, norm_smul, mul_pow, mul_pow,
    ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)]

end
end ImbalancedChen.Part3.GammaPhysicalSpectralSectorReduction20261026b
