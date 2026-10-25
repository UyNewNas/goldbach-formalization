import ImbalancedChen.Part3Gamma0ActualClosedMaassNonnegative
import ImbalancedChen.Part3Gamma0ActualMinimalFriedrichsInclusion
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The range B of the unit shift of the ACTUAL minimal closed Gamma0 Maass
operator is a closed subspace. The exact criterion is
  f in B iff (R f,f-R f) belongs to the actual minimal closed graph.
Here R is the genuine actual Gamma0 energy resolvent. The right side is
the preimage of the actual closed graph under a bounded continuous map.

R restricted to B is the bounded inverse into the actual minimal domain;
the image R(B) is exactly that domain. Native orthogonal projection gives
the actual Hilbert splitting H=B+orthogonal(B), with an explicit defect
component. No assertion B=H, no onto claim for the minimal shift, and no
essential self-adjointness or equality with the Friedrichs extension is made.
-/

namespace ImbalancedChen.Part3.Gamma0ActualMinimalShiftRange20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualClosedMaassNonnegative20261025a
open ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalFriedrichsInclusion20261025a

def minimalShiftRange (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (actualClosedGammaShift N).range

def resolventGraphLift (N : ℕ) [NeZero N] :
    QuotientL2 N →L[ℂ] (QuotientL2 N × QuotientL2 N) :=
  (actualGammaResolvent N).prod
    (ContinuousLinearMap.id ℂ (QuotientL2 N)-actualGammaResolvent N)

@[simp] theorem resolventGraphLift_apply (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    resolventGraphLift N f = (actualGammaResolvent N f,f-actualGammaResolvent N f) := rfl

/-- Membership is in the true MINIMAL graph, not merely in the larger
Friedrichs graph, which contains every resolvent pair. -/
theorem mem_minimalShiftRange_iff (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ minimalShiftRange N ↔
      (actualGammaResolvent N f,f-actualGammaResolvent N f) ∈ (actualClosedGammaMaass N).graph := by
  constructor
  · rintro ⟨u,hu⟩
    have hRu : actualGammaResolvent N f = (u : QuotientL2 N) := by
      rw [← hu]
      exact actualGammaResolvent_shift_minimalClosed N u
    have hshift : f = (u : QuotientL2 N)+actualClosedGammaMaass N u := hu.symm
    have hsecond : f-actualGammaResolvent N f = actualClosedGammaMaass N u := by
      rw [hRu,hshift]
      abel
    rw [hsecond,hRu]
    exact LinearPMap.mem_graph _ u
  · intro hf
    obtain ⟨u,hu,hAu⟩ := LinearPMap.mem_graph_iff.mp hf
    refine ⟨u,?_⟩
    rw [actualClosedGammaShift_apply,hu,hAu]
    abel

theorem minimalShiftRange_eq_preimage_graph (N : ℕ) [NeZero N] :
    (minimalShiftRange N : Set (QuotientL2 N)) =
      resolventGraphLift N ⁻¹' ((actualClosedGammaMaass N).graph : Set (QuotientL2 N × QuotientL2 N)) := by
  ext f
  exact mem_minimalShiftRange_iff N f

/-- Closedness follows directly from the actual resolvent criterion and
actual graph closedness, with no range-closedness premise. -/
theorem minimalShiftRange_isClosed (N : ℕ) [NeZero N] :
    IsClosed (minimalShiftRange N : Set (QuotientL2 N)) := by
  rw [minimalShiftRange_eq_preimage_graph]
  exact (actualClosedGammaMaass_isClosed N).preimage (resolventGraphLift N).continuous

theorem resolvent_mem_minimal_domain (N : ℕ) [NeZero N] {f : QuotientL2 N}
    (hf : f ∈ minimalShiftRange N) : actualGammaResolvent N f ∈ (actualClosedGammaMaass N).domain := by
  exact (LinearPMap.mem_domain_iff).mpr ⟨f-actualGammaResolvent N f,
    (mem_minimalShiftRange_iff N f).mp hf⟩

def minimalDomainPoint (N : ℕ) [NeZero N] (f : QuotientL2 N) (hf : f ∈ minimalShiftRange N) :
    (actualClosedGammaMaass N).domain := ⟨actualGammaResolvent N f,resolvent_mem_minimal_domain N hf⟩

theorem minimalDomainPoint_output (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (hf : f ∈ minimalShiftRange N) :
    actualClosedGammaMaass N (minimalDomainPoint N f hf) = f-actualGammaResolvent N f :=
  LinearPMap.mem_graph_snd_inj (actualClosedGammaMaass N)
    (LinearPMap.mem_graph _ (minimalDomainPoint N f hf))
    ((mem_minimalShiftRange_iff N f).mp hf) rfl

/-- The bounded physical R maps precisely B onto the actual minimal
domain. It is not asserted to map all forcing vectors there. -/
theorem resolvent_image_minimalShiftRange (N : ℕ) [NeZero N] :
    actualGammaResolvent N '' (minimalShiftRange N : Set (QuotientL2 N)) =
      ((actualClosedGammaMaass N).domain : Set (QuotientL2 N)) := by
  ext u
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact resolvent_mem_minimal_domain N hf
  · intro hu
    let v : (actualClosedGammaMaass N).domain := ⟨u,hu⟩
    refine ⟨actualClosedGammaShift N v,⟨v,rfl⟩,?_⟩
    exact actualGammaResolvent_shift_minimalClosed N v

def minimalShiftInverseLinear (N : ℕ) [NeZero N] :
    minimalShiftRange N →ₗ[ℂ] (actualClosedGammaMaass N).domain where
  toFun f := minimalDomainPoint N f f.property
  map_add' f g := Subtype.ext ((actualGammaResolvent N).map_add f g)
  map_smul' c f := Subtype.ext ((actualGammaResolvent N).map_smul c f)

/-- The inverse is bounded in the inherited physical domain norm. The
unbounded forward shift is not claimed continuous in that norm. -/
def minimalShiftInverse (N : ℕ) [NeZero N] :
    minimalShiftRange N →L[ℂ] (actualClosedGammaMaass N).domain :=
  (minimalShiftInverseLinear N).mkContinuous 1 (by
    intro f
    change ‖actualGammaResolvent N (f : QuotientL2 N)‖ ≤ 1*‖(f : QuotientL2 N)‖
    simpa only [one_mul] using actualGammaResolvent_norm_le N (f : QuotientL2 N))

@[simp] theorem minimalShiftInverse_coe_apply (N : ℕ) [NeZero N] (f : minimalShiftRange N) :
    ((minimalShiftInverse N f : (actualClosedGammaMaass N).domain) : QuotientL2 N) =
      actualGammaResolvent N (f : QuotientL2 N) := rfl

theorem minimalShiftInverse_right_inverse (N : ℕ) [NeZero N] (f : minimalShiftRange N) :
    actualClosedGammaShift N (minimalShiftInverse N f) = (f : QuotientL2 N) := by
  change actualGammaResolvent N (f : QuotientL2 N)+
    actualClosedGammaMaass N (minimalDomainPoint N f f.property) = (f : QuotientL2 N)
  rw [minimalDomainPoint_output]
  abel

theorem minimalShiftInverse_left_inverse (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).domain) :
    minimalShiftInverse N ⟨actualClosedGammaShift N u,⟨u,rfl⟩⟩ = u := by
  apply Subtype.ext
  exact actualGammaResolvent_shift_minimalClosed N u

instance minimalShiftRange_completeSpace (N : ℕ) [NeZero N] : CompleteSpace (minimalShiftRange N) :=
  (minimalShiftRange_isClosed N).completeSpace_coe

/-- This closed orthogonal subspace records the remaining shift defect.
Its vanishing is NOT inferred from any preceding theorem. -/
def minimalShiftDefect (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (minimalShiftRange N)ᗮ

def minimalRangeProjection (N : ℕ) [NeZero N] : QuotientL2 N →L[ℂ] QuotientL2 N :=
  (minimalShiftRange N).starProjection

theorem minimalRange_isTopCompl_defect (N : ℕ) [NeZero N] :
    Submodule.IsTopCompl (minimalShiftRange N) (minimalShiftDefect N) :=
  (minimalShiftRange N).isTopCompl_orthogonal

/-- Native orthogonal decomposition in the actual quotient Hilbert space.
No claim is made that the displayed defect component is always zero. -/
theorem minimalRange_orthogonal_decomposition (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    minimalRangeProjection N f ∈ minimalShiftRange N ∧
      f-minimalRangeProjection N f ∈ minimalShiftDefect N ∧
      f = minimalRangeProjection N f + (f-minimalRangeProjection N f) := by
  refine ⟨Submodule.starProjection_apply_mem _ _,Submodule.sub_starProjection_mem_orthogonal _ _,?_⟩
  abel

end
end ImbalancedChen.Part3.Gamma0ActualMinimalShiftRange20261025a
