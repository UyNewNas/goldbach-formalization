import ImbalancedChen.Part3GammaInfinityCuspNativeOutputInvariance

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual ambient native Gamma0 Friedrichs operator restricted to the
FULL original infinity-cusp annihilator is a native partial linear map
on that closed physical Hilbert subspace. Its domain is exactly ambient
native-domain membership, and its graph is exactly the ambient native
graph on the two actual subtype coordinates. The proved native output
invariance supplies the codomain, rather than an assumed restriction.
Closedness, symmetry and nonnegativity are inherited and proved.

No density of this restricted domain, self-adjointness of the restriction,
surjectivity of its shifts, resolvent reduction, all-cusp identification,
compact resolvent, or cusp/Eisenstein completeness is asserted.
-/
namespace ImbalancedChen.Part3.GammaInfinityCuspNativeRestriction20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualConstantMode20261025a
open Gamma0ActualFriedrichsOperator20261025a
open ActualInfinityCuspAnnihilator20261026b
open GammaSmoothZeroSeedNativeGraph20261026b
open GammaInfinityCuspNativeOutputInvariance20261026b

abbrev InfinityCuspL2 (N : ℕ) [NeZero N] := infinityCuspSubspace N

instance infinityCuspL2_complete (N : ℕ) [NeZero N] : CompleteSpace (InfinityCuspL2 N) :=
  (infinityCuspSubspace_closed N).completeSpace_coe

/-- Exactly the ambient operator domain pulled back by actual physical
subtype inclusion. No new completion or domain enlargement occurs. -/
def infinityCuspNativeDomain (N : ℕ) [NeZero N] : Submodule ℂ (InfinityCuspL2 N) :=
  (actualGammaFriedrichs N).domain.comap (infinityCuspSubspace N).subtype

def ambientCuspNativeDomainPoint (N : ℕ) [NeZero N]
    (u : infinityCuspNativeDomain N) : (actualGammaFriedrichs N).domain :=
  ⟨((u : InfinityCuspL2 N) : QuotientL2 N), u.property⟩

/-- The genuine native partial operator on the full original infinity
cusp Hilbert subtype, with its codomain justified by actual output invariance. -/
def actualInfinityCuspNativeRestriction (N : ℕ) [NeZero N] :
    InfinityCuspL2 N →ₗ.[ℂ] InfinityCuspL2 N where
  domain := infinityCuspNativeDomain N
  toFun :=
    { toFun := fun u =>
        ⟨actualGammaFriedrichs N (ambientCuspNativeDomainPoint N u),
          actual_friedrichs_infinityCusp_output_mem N (ambientCuspNativeDomainPoint N u)
            (u : InfinityCuspL2 N).property⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        change actualGammaFriedrichs N (ambientCuspNativeDomainPoint N u + ambientCuspNativeDomainPoint N v) =
          actualGammaFriedrichs N (ambientCuspNativeDomainPoint N u) +
            actualGammaFriedrichs N (ambientCuspNativeDomainPoint N v)
        exact (actualGammaFriedrichs N).map_add _ _
      map_smul' := by
        intro c u
        apply Subtype.ext
        change actualGammaFriedrichs N (c • ambientCuspNativeDomainPoint N u) =
          c • actualGammaFriedrichs N (ambientCuspNativeDomainPoint N u)
        exact (actualGammaFriedrichs N).map_smul _ _ }

theorem actualInfinityCuspNativeRestriction_domain (N : ℕ) [NeZero N] :
    (actualInfinityCuspNativeRestriction N).domain =
      (actualGammaFriedrichs N).domain.comap (infinityCuspSubspace N).subtype := rfl

theorem mem_actualInfinityCuspNativeRestriction_domain_iff (N : ℕ) [NeZero N]
    (u : InfinityCuspL2 N) :
    u ∈ (actualInfinityCuspNativeRestriction N).domain ↔
      (u : QuotientL2 N) ∈ (actualGammaFriedrichs N).domain := Iff.rfl

/-- Exact native action through the original ambient native domain. -/
theorem actualInfinityCuspNativeRestriction_apply_coe (N : ℕ) [NeZero N]
    (u : (actualInfinityCuspNativeRestriction N).domain) :
    (actualInfinityCuspNativeRestriction N u : QuotientL2 N) =
      actualGammaFriedrichs N (ambientCuspNativeDomainPoint N u) := rfl

/-- No graph inclusion premise: this is exact equivalence with the
original ambient native graph on the original cusp subtype coordinates. -/
theorem actualInfinityCuspNativeRestriction_mem_graph_iff (N : ℕ) [NeZero N]
    (u v : InfinityCuspL2 N) :
    (u, v) ∈ (actualInfinityCuspNativeRestriction N).graph ↔
      ((u : QuotientL2 N), (v : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph := by
  constructor
  · intro h
    obtain ⟨w, hw, hout⟩ := LinearPMap.mem_graph_iff.mp h
    have hi : (ambientCuspNativeDomainPoint N w : QuotientL2 N) = (u : QuotientL2 N) :=
      congrArg (fun x : InfinityCuspL2 N => (x : QuotientL2 N)) hw
    have ho : actualGammaFriedrichs N (ambientCuspNativeDomainPoint N w) = (v : QuotientL2 N) :=
      congrArg (fun x : InfinityCuspL2 N => (x : QuotientL2 N)) hout
    exact LinearPMap.mem_graph_iff.mpr ⟨ambientCuspNativeDomainPoint N w, hi, ho⟩
  · intro h
    obtain ⟨w, hw, hout⟩ := LinearPMap.mem_graph_iff.mp h
    have hdomain : u ∈ infinityCuspNativeDomain N := by
      change (u : QuotientL2 N) ∈ (actualGammaFriedrichs N).domain
      rw [← hw]
      exact w.property
    apply LinearPMap.mem_graph_iff.mpr
    refine ⟨⟨u, hdomain⟩, rfl, ?_⟩
    apply Subtype.ext
    change actualGammaFriedrichs N (ambientCuspNativeDomainPoint N ⟨u, hdomain⟩) = (v : QuotientL2 N)
    have hp : ambientCuspNativeDomainPoint N ⟨u, hdomain⟩ = w := Subtype.ext hw.symm
    rw [hp, hout]

theorem actualInfinityCuspNativeRestriction_isClosed (N : ℕ) [NeZero N] :
    (actualInfinityCuspNativeRestriction N).IsClosed := by
  change IsClosed ((actualInfinityCuspNativeRestriction N).graph :
    Set (InfinityCuspL2 N × InfinityCuspL2 N))
  have heq : ((actualInfinityCuspNativeRestriction N).graph :
      Set (InfinityCuspL2 N × InfinityCuspL2 N)) =
      (fun p : InfinityCuspL2 N × InfinityCuspL2 N =>
        ((p.1 : QuotientL2 N), (p.2 : QuotientL2 N))) ⁻¹'
          ((actualGammaFriedrichs N).graph : Set (QuotientL2 N × QuotientL2 N)) := by
    ext p
    exact actualInfinityCuspNativeRestriction_mem_graph_iff N p.1 p.2
  rw [heq]
  have hclosed : IsClosed ((actualGammaFriedrichs N).graph :
      Set (QuotientL2 N × QuotientL2 N)) := actualGammaFriedrichs_isClosed N
  exact hclosed.preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- Native symmetry on the exact restricted domain. This does not
assert that the restricted domain is dense or that its adjoint agrees. -/
theorem actualInfinityCuspNativeRestriction_symmetric (N : ℕ) [NeZero N]
    (u v : (actualInfinityCuspNativeRestriction N).domain) :
    inner ℂ (actualInfinityCuspNativeRestriction N u) (v : InfinityCuspL2 N) =
      inner ℂ (u : InfinityCuspL2 N) (actualInfinityCuspNativeRestriction N v) := by
  change inner ℂ (actualGammaFriedrichs N (ambientCuspNativeDomainPoint N u))
      (ambientCuspNativeDomainPoint N v : QuotientL2 N) =
    inner ℂ (ambientCuspNativeDomainPoint N u : QuotientL2 N)
      (actualGammaFriedrichs N (ambientCuspNativeDomainPoint N v))
  exact (actual_native_graph_cross_symmetry N
    ((actualGammaFriedrichs N).mem_graph (ambientCuspNativeDomainPoint N v))
    ((actualGammaFriedrichs N).mem_graph (ambientCuspNativeDomainPoint N u))).symm

theorem actualInfinityCuspNativeRestriction_nonnegative (N : ℕ) [NeZero N]
    (u : (actualInfinityCuspNativeRestriction N).domain) :
    0 ≤ (inner ℂ (u : InfinityCuspL2 N) (actualInfinityCuspNativeRestriction N u)).re :=
  actualGammaFriedrichs_nonneg N (ambientCuspNativeDomainPoint N u)

end
end ImbalancedChen.Part3.GammaInfinityCuspNativeRestriction20261026b
