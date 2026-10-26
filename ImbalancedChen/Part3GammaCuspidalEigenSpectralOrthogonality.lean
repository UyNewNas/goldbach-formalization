import ImbalancedChen.Part3GammaNativeEigenBorelLocalization
import ImbalancedChen.Part3ActualInfinityCuspTestCharacterization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Physical infinity-cuspidal native eigenvectors are spectrally orthogonal
to every genuine compact-height incomplete Eisenstein test at infinity.
The cusp condition is the actual horocycle zero coefficient, not a
spectral label. The proof uses actual height-test unfolding, the proved
test characterization, and native eigenvector Borel localization.

The result is extended to the closed span of these actual eigenvectors
and the closed span of actual Borel orbits of those actual test vectors.
No equality with the entire cuspidal or continuous spectrum is asserted.
Other cusps, cusp completeness, and Eisenstein Plancherel remain OPEN.
-/
namespace ImbalancedChen.Part3.GammaCuspidalEigenSpectralOrthogonality20261026b

noncomputable section
open Set MeasureTheory
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open ActualPoincareSpectralCoefficient20261026a
open ActualInfinityCuspAnnihilator20261026b
open ActualInfinityCuspTestCharacterization20261026b
open GenericResolventUnboundedScalarMeasure20261025a
open GenericGlobalBorelProjection20261025a
open GammaMeanCenteredScalarMeasure20261026b
open GammaNativeEigenBorelLocalization20261026b

/-- A physical representative, its actual native graph equation, and its
actual infinity zero mode. None of the fields is spectral orthogonality. -/
structure NativeInfinityCuspEigenvector (N : ℕ) [NeZero N] where
  representative : Gamma0OrbitSpace N → ℂ
  continuous_lift : Continuous (testLift N representative)
  memLp_two : MemLp representative 2 (carrierPushforward N)
  eigenvalue : ℝ
  native_graph : (memLp_two.toLp representative,
      (eigenvalue : ℂ) • memLp_two.toLp representative) ∈ (actualGammaFriedrichs N).graph
  zero_mode : AEZeroInfinityMode N representative

def NativeInfinityCuspEigenvector.vector {N : ℕ} [NeZero N]
    (e : NativeInfinityCuspEigenvector N) : QuotientL2 N :=
  e.memLp_two.toLp e.representative

/-- The true complex mixed Borel spectral coefficient vanishes. The
incomplete Eisenstein vector is the original physical zero-height seed. -/
theorem native_cusp_eigen_incompleteEisenstein_cross_zero (N : ℕ) [NeZero N]
    (e : NativeInfinityCuspEigenvector N) (s : HeightSeed)
    (B : Set ℝ) (hB : MeasurableSet B) :
    inner ℂ (actualLaplaceBorelProjection N B hB (zeroSeedL2 N s)) e.vector = 0 := by
  have hcusp := (continuous_mem_iff_ae_zero_infinity_mode N e.representative
    e.continuous_lift e.memLp_two).mpr e.zero_mode
  have htest := (mem_infinityCuspSubspace_iff N e.vector).mp hcusp s
  change inner ℂ
    (globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
      (spectralLambda (actualGammaResolvent N) ⁻¹' B)
      ((measurable_spectralLambda (actualGammaResolvent N)) hB) (zeroSeedL2 N s))
    e.vector = 0
  rw [globalBorelProjection_inner]
  change inner ℂ (zeroSeedL2 N s) (actualLaplaceBorelProjection N B hB e.vector) = 0
  rw [actual_native_eigenvector_borel_apply N e.vector e.eigenvalue e.native_graph]
  split_ifs
  · exact htest
  · exact inner_zero_right _

theorem native_cusp_eigen_incompleteEisenstein_cross_reverse_zero (N : ℕ) [NeZero N]
    (e : NativeInfinityCuspEigenvector N) (s : HeightSeed)
    (B : Set ℝ) (hB : MeasurableSet B) :
    inner ℂ e.vector (actualLaplaceBorelProjection N B hB (zeroSeedL2 N s)) = 0 := by
  rw [← inner_conj_symm,
    native_cusp_eigen_incompleteEisenstein_cross_zero N e s B hB, map_zero]

/-- Literal Borel orbits of the proved physical incomplete Eisenstein
tests. This is not declared to be the entire continuous spectrum. -/
def actualIncompleteEisensteinBorelTests (N : ℕ) [NeZero N] : Set (QuotientL2 N) :=
  {v | ∃ (s : HeightSeed) (B : Set ℝ) (hB : MeasurableSet B),
    v = actualLaplaceBorelProjection N B hB (zeroSeedL2 N s)}

def actualIncompleteEisensteinBorelTestSpace (N : ℕ) [NeZero N] :
    Submodule ℂ (QuotientL2 N) :=
  (Submodule.span ℂ (actualIncompleteEisensteinBorelTests N)).topologicalClosure

/-- Actual native cusp point vectors, retaining their physical
representatives and zero-mode characterization in the generating data. -/
def actualInfinityCuspEigenPointSpace (N : ℕ) [NeZero N] :
    Submodule ℂ (QuotientL2 N) :=
  (Submodule.span ℂ (Set.range (fun e : NativeInfinityCuspEigenvector N => e.vector))).topologicalClosure

theorem native_cusp_eigen_mem_testSpace_orthogonal (N : ℕ) [NeZero N]
    (e : NativeInfinityCuspEigenvector N) :
    e.vector ∈ (actualIncompleteEisensteinBorelTestSpace N)ᗮ := by
  have hspan : Submodule.span ℂ (actualIncompleteEisensteinBorelTests N) ≤
      (ℂ ∙ e.vector)ᗮ := by
    apply Submodule.span_le.mpr
    rintro v ⟨s, B, hB, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
      (native_cusp_eigen_incompleteEisenstein_cross_zero N e s B hB)
  have hclosure : actualIncompleteEisensteinBorelTestSpace N ≤ (ℂ ∙ e.vector)ᗮ :=
    (Submodule.span ℂ (actualIncompleteEisensteinBorelTests N)).topologicalClosure_minimal
      hspan (Submodule.isClosed_orthogonal _)
  apply ((actualIncompleteEisensteinBorelTestSpace N).mem_orthogonal e.vector).mpr
  intro v hv
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hclosure hv)

/-- Orthogonality survives BOTH closures of the true physical generators.
No continuous/cuspidal completeness conclusion is needed for this step. -/
theorem actual_cusp_pointSpace_le_incompleteEisenstein_testSpace_orthogonal
    (N : ℕ) [NeZero N] :
    actualInfinityCuspEigenPointSpace N ≤ (actualIncompleteEisensteinBorelTestSpace N)ᗮ := by
  apply (Submodule.span ℂ
    (Set.range (fun e : NativeInfinityCuspEigenvector N => e.vector))).topologicalClosure_minimal
    _ (Submodule.isClosed_orthogonal _)
  apply Submodule.span_le.mpr
  rintro v ⟨e, rfl⟩
  exact native_cusp_eigen_mem_testSpace_orthogonal N e

end
end ImbalancedChen.Part3.GammaCuspidalEigenSpectralOrthogonality20261026b
