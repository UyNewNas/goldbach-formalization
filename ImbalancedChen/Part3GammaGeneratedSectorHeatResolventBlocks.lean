import ImbalancedChen.Part3GammaBorelReducingScalarOperators
import ImbalancedChen.Part3Gamma0ActualHeatScalarCoefficient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual heat and positive shifted native resolvents are block diagonal
with respect to each of the two explicitly generated physical sectors.
Every sector and its orthogonal complement is preserved, and its actual
orthogonal projection commutes with both native operator families. The
proof consumes the independently proved actual scalar Laplace integrals.
There is no full cusp/Eisenstein completeness or Plancherel premise.
-/
namespace ImbalancedChen.Part3.GammaGeneratedSectorHeatResolventBlocks20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualConstantMode20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a
open Gamma0ActualHeatGenerator20261025a
open Gamma0ActualHeatScalarCoefficient20261025a
open GammaMeanCenteredScalarMeasure20261026b
open GammaCuspidalEigenSpectralOrthogonality20261026b
open GammaPhysicalSpectralSectorReduction20261026b
open GammaBorelReducingScalarOperators20261026b

/-- Names only for the two literal previously constructed physical spaces. -/
inductive GeneratedPhysicalSector
  | cuspEigenPoint
  | incompleteEisensteinTest

def generatedSectorSubmodule (N : ℕ) [NeZero N] :
    GeneratedPhysicalSector → Submodule ℂ (QuotientL2 N)
  | .cuspEigenPoint => actualInfinityCuspEigenPointSpace N
  | .incompleteEisensteinTest => actualIncompleteEisensteinBorelTestSpace N

theorem generatedSector_closed (N : ℕ) [NeZero N] (s : GeneratedPhysicalSector) :
    IsClosed (generatedSectorSubmodule N s : Set (QuotientL2 N)) := by
  cases s with
  | cuspEigenPoint =>
      exact (Submodule.span ℂ (Set.range
        (fun e : NativeInfinityCuspEigenvector N => e.vector))).isClosed_topologicalClosure
  | incompleteEisensteinTest =>
      exact (Submodule.span ℂ (actualIncompleteEisensteinBorelTests N)).isClosed_topologicalClosure

instance generatedSector_complete (N : ℕ) [NeZero N] (s : GeneratedPhysicalSector) :
    CompleteSpace (generatedSectorSubmodule N s) :=
  (generatedSector_closed N s).completeSpace_coe

theorem generatedSector_borel_invariant (N : ℕ) [NeZero N] (s : GeneratedPhysicalSector)
    (B : Set ℝ) (hB : MeasurableSet B) (f : QuotientL2 N)
    (hf : f ∈ generatedSectorSubmodule N s) :
    actualLaplaceBorelProjection N B hB f ∈ generatedSectorSubmodule N s := by
  cases s with
  | cuspEigenPoint => exact actual_cusp_pointSpace_borel_invariant N B hB hf
  | incompleteEisensteinTest => exact actual_incompleteEisenstein_testSpace_borel_invariant N B hB hf

def generatedSectorProjection (N : ℕ) [NeZero N] (s : GeneratedPhysicalSector) :
    QuotientL2 N →L[ℂ] QuotientL2 N := (generatedSectorSubmodule N s).starProjection

theorem actual_heat_generatedSector_invariant (N : ℕ) [NeZero N] (s : GeneratedPhysicalSector)
    {t : ℝ} (ht : 0 ≤ t) {f : QuotientL2 N} (hf : f ∈ generatedSectorSubmodule N s) :
    actualGammaHeat N t f ∈ generatedSectorSubmodule N s :=
  actual_scalar_integral_operator_invariant N (generatedSectorSubmodule N s)
    (generatedSector_closed N s) (generatedSector_borel_invariant N s)
    (actualGammaHeat N t) (fun λ => (Real.exp (-t * λ) : ℂ))
    (actualHeat_complex_scalar_integral N ht) hf

theorem actual_shiftedResolvent_generatedSector_invariant (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) {a : ℝ} (ha : 0 < a) {f : QuotientL2 N}
    (hf : f ∈ generatedSectorSubmodule N s) :
    actualGammaShiftedResolvent N a f ∈ generatedSectorSubmodule N s :=
  actual_scalar_integral_operator_invariant N (generatedSectorSubmodule N s)
    (generatedSector_closed N s) (generatedSector_borel_invariant N s)
    (actualGammaShiftedResolvent N a) (fun λ => (((a + λ)⁻¹ : ℝ) : ℂ))
    (actualLaplaceMeasure_complex_stieltjes_integral N ha) hf

theorem actual_heat_generatedSector_orthogonal_invariant (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) {t : ℝ} (ht : 0 ≤ t) {f : QuotientL2 N}
    (hf : f ∈ (generatedSectorSubmodule N s)ᗮ) :
    actualGammaHeat N t f ∈ (generatedSectorSubmodule N s)ᗮ :=
  actual_scalar_integral_operator_invariant N (generatedSectorSubmodule N s)ᗮ
    (Submodule.isClosed_orthogonal _)
    (fun B hB v hv => actual_borel_orthogonal_invariant N _ B hB
      (fun w hw => generatedSector_borel_invariant N s B hB w hw) hv)
    (actualGammaHeat N t) (fun λ => (Real.exp (-t * λ) : ℂ))
    (actualHeat_complex_scalar_integral N ht) hf

theorem actual_shiftedResolvent_generatedSector_orthogonal_invariant (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) {a : ℝ} (ha : 0 < a) {f : QuotientL2 N}
    (hf : f ∈ (generatedSectorSubmodule N s)ᗮ) :
    actualGammaShiftedResolvent N a f ∈ (generatedSectorSubmodule N s)ᗮ :=
  actual_scalar_integral_operator_invariant N (generatedSectorSubmodule N s)ᗮ
    (Submodule.isClosed_orthogonal _)
    (fun B hB v hv => actual_borel_orthogonal_invariant N _ B hB
      (fun w hw => generatedSector_borel_invariant N s B hB w hw) hv)
    (actualGammaShiftedResolvent N a) (fun λ => (((a + λ)⁻¹ : ℝ) : ℂ))
    (actualLaplaceMeasure_complex_stieltjes_integral N ha) hf

theorem generatedSectorProjection_heat_commute (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) {t : ℝ} (ht : 0 ≤ t) (f : QuotientL2 N) :
    generatedSectorProjection N s (actualGammaHeat N t f) =
      actualGammaHeat N t (generatedSectorProjection N s f) :=
  actual_scalar_integral_operator_projection_commute N (generatedSectorSubmodule N s)
    (generatedSector_closed N s) (generatedSector_borel_invariant N s)
    (actualGammaHeat N t) (fun λ => (Real.exp (-t * λ) : ℂ))
    (actualHeat_complex_scalar_integral N ht) f

theorem generatedSectorProjection_shiftedResolvent_commute (N : ℕ) [NeZero N]
    (s : GeneratedPhysicalSector) {a : ℝ} (ha : 0 < a) (f : QuotientL2 N) :
    generatedSectorProjection N s (actualGammaShiftedResolvent N a f) =
      actualGammaShiftedResolvent N a (generatedSectorProjection N s f) :=
  actual_scalar_integral_operator_projection_commute N (generatedSectorSubmodule N s)
    (generatedSector_closed N s) (generatedSector_borel_invariant N s)
    (actualGammaShiftedResolvent N a) (fun λ => (((a + λ)⁻¹ : ℝ) : ℂ))
    (actualLaplaceMeasure_complex_stieltjes_integral N ha) f

/-- Actual mixed native heat coefficients vanish throughout the two
generated physical sectors, with no finite-generator restriction. -/
theorem actual_heat_physical_sectors_cross_zero (N : ℕ) [NeZero N]
    {t : ℝ} (ht : 0 ≤ t) {f g : QuotientL2 N}
    (hf : f ∈ actualInfinityCuspEigenPointSpace N)
    (hg : g ∈ actualIncompleteEisensteinBorelTestSpace N) :
    inner ℂ (actualGammaHeat N t f) g = 0 :=
  Submodule.inner_left_of_mem_orthogonal hg
    (actual_cusp_pointSpace_le_incompleteEisenstein_testSpace_orthogonal N
      (actual_heat_generatedSector_invariant N .cuspEigenPoint ht hf))

theorem actual_shiftedResolvent_physical_sectors_cross_zero (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0 < a) {f g : QuotientL2 N}
    (hf : f ∈ actualInfinityCuspEigenPointSpace N)
    (hg : g ∈ actualIncompleteEisensteinBorelTestSpace N) :
    inner ℂ (actualGammaShiftedResolvent N a f) g = 0 :=
  Submodule.inner_left_of_mem_orthogonal hg
    (actual_cusp_pointSpace_le_incompleteEisenstein_testSpace_orthogonal N
      (actual_shiftedResolvent_generatedSector_invariant N .cuspEigenPoint ha hf))

end
end ImbalancedChen.Part3.GammaGeneratedSectorHeatResolventBlocks20261026b
