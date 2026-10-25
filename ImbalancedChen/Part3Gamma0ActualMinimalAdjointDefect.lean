import ImbalancedChen.Part3Gamma0ActualMinimalShiftRange
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The remaining actual minimal/Friedrichs distinction is represented by the
NATIVE negative-one adjoint deficiency fiber. The actual minimal unit-shift
range B has orthogonal complement precisely
  {f | (f,-f) belongs to the native adjoint graph of actualClosedGammaMaass}.
This follows from true dense-domain native adjoint testing, not an hAdjoint
or hDefectZero premise.

An exact CRITERION is then proved: the minimal closed operator equals its
actual Friedrichs extension iff this defect space is zero. Neither side
of that equivalence is asserted. In particular this module does not prove
essential self-adjointness or discard negative-one weak deficiency vectors.
-/

namespace ImbalancedChen.Part3.Gamma0ActualMinimalAdjointDefect20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualClosedMaassNonnegative20261025a
open ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalFriedrichsInclusion20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalShiftRange20261025a

/-- A typed native adjoint fiber, retaining the actual quotient Hilbert
space and actual densely defined minimal differential operator. -/
def minimalAdjointDefect (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  ((actualClosedGammaMaass N).adjoint.graph).comap
    ((LinearMap.id : QuotientL2 N →ₗ[ℂ] QuotientL2 N).prod
      (-(LinearMap.id : QuotientL2 N →ₗ[ℂ] QuotientL2 N)))

@[simp] theorem mem_minimalAdjointDefect_iff (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ minimalAdjointDefect N ↔ (f,-f) ∈ (actualClosedGammaMaass N).adjoint.graph := Iff.rfl

/-- Exact arithmetic-free weak deficiency equation on every vector of
the actual minimal domain. No test density is supplied by the caller. -/
theorem mem_minimalShiftDefect_iff_inner (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ minimalShiftDefect N ↔
      ∀ u : (actualClosedGammaMaass N).domain,
        inner ℂ ((u : QuotientL2 N)+actualClosedGammaMaass N u) f = 0 := by
  rw [show minimalShiftDefect N = (minimalShiftRange N)ᗮ from rfl,
    Submodule.mem_orthogonal]
  constructor
  · intro hf u
    exact hf (actualClosedGammaShift N u) ⟨u,rfl⟩
  · intro hf g hg
    obtain ⟨u,rfl⟩ := hg
    exact hf u

/-- The actual dense-domain theorem identifies the NATIVE adjoint graph
with the adjoint relation of the actual minimal graph. -/
theorem mem_minimalShiftDefect_iff_adjoint_graph (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ minimalShiftDefect N ↔ (f,-f) ∈ (actualClosedGammaMaass N).adjoint.graph := by
  rw [mem_minimalShiftDefect_iff_inner,
    LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGammaMaass_dense_domain N),
    Submodule.mem_adjoint_iff]
  constructor
  · intro hf a b hab
    obtain ⟨u,hu,hAu⟩ := LinearPMap.mem_graph_iff.mp hab
    rw [← hu,← hAu]
    simpa only [inner_add_left,inner_neg_right,sub_neg_eq_add,add_comm] using hf u
  · intro hf u
    have ht := hf (u : QuotientL2 N) (actualClosedGammaMaass N u)
      (LinearPMap.mem_graph _ u)
    simpa only [inner_add_left,inner_neg_right,sub_neg_eq_add,add_comm] using ht

theorem minimalShiftDefect_eq_adjointDefect (N : ℕ) [NeZero N] :
    minimalShiftDefect N = minimalAdjointDefect N := by
  apply SetLike.ext
  intro f
  rw [mem_minimalAdjointDefect_iff]
  exact mem_minimalShiftDefect_iff_adjoint_graph N f

/-- Explicit native adjoint-domain representative of each defect vector.
The eigenvalue is exactly -1, rather than an unspecified spectral defect. -/
theorem mem_minimalShiftDefect_iff_negative_one_fiber (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ minimalShiftDefect N ↔
      ∃ u : (actualClosedGammaMaass N).adjoint.domain,
        (u : QuotientL2 N) = f ∧ (actualClosedGammaMaass N).adjoint u = -f := by
  rw [mem_minimalShiftDefect_iff_adjoint_graph,LinearPMap.mem_graph_iff]

/-- Closedness of B is essential here: zero orthogonal defect forces the
WHOLE shift range, rather than only its topological closure, to be H. -/
theorem minimalShiftRange_eq_top_iff_defect_eq_bot (N : ℕ) [NeZero N] :
    minimalShiftRange N = ⊤ ↔ minimalShiftDefect N = ⊥ := by
  constructor
  · intro hB
    change (minimalShiftRange N)ᗮ = ⊥
    rw [hB]
    exact Submodule.top_orthogonal_eq_bot
  · intro hD
    apply SetLike.ext
    intro f
    constructor
    · intro hf
      trivial
    · intro hf
      obtain ⟨hproj,hdef,hdecomp⟩ := minimalRange_orthogonal_decomposition N f
      rw [hD,Submodule.mem_bot] at hdef
      rw [sub_eq_zero.mp hdef]
      exact hproj

/-- Exact minimal/Friedrichs criterion. It does NOT assert that the
actual deficiency space vanishes; that remains a separate PDE problem. -/
theorem actualMinimal_eq_friedrichs_iff_defect_eq_bot (N : ℕ) [NeZero N] :
    actualClosedGammaMaass N = actualGammaFriedrichs N ↔ minimalShiftDefect N = ⊥ := by
  constructor
  · intro hA
    apply (minimalShiftRange_eq_top_iff_defect_eq_bot N).mp
    apply SetLike.ext
    intro f
    constructor
    · intro hf
      trivial
    · intro hf
      apply (mem_minimalShiftRange_iff N f).mpr
      rw [hA]
      apply (actualGammaFriedrichs_mem_graph_iff N).mpr
      have hsum : actualGammaResolvent N f+(f-actualGammaResolvent N f)=f := by abel
      rw [hsum]
  · intro hD
    have hB : minimalShiftRange N = ⊤ :=
      (minimalShiftRange_eq_top_iff_defect_eq_bot N).mpr hD
    apply le_antisymm (actualClosedGammaMaass_le_friedrichs N)
    apply LinearPMap.le_of_le_graph
    rintro ⟨u,v⟩ huv
    have hR := (actualGammaFriedrichs_mem_graph_iff N).mp huv
    have hmem : u+v ∈ minimalShiftRange N := by rw [hB]; trivial
    have hmin := (mem_minimalShiftRange_iff N (u+v)).mp hmem
    rw [hR] at hmin
    have hsecond : u+v-u=v := by abel
    simpa only [hsecond] using hmin

theorem actualMinimal_eq_friedrichs_iff_native_negative_one_fiber_zero (N : ℕ) [NeZero N] :
    actualClosedGammaMaass N = actualGammaFriedrichs N ↔ minimalAdjointDefect N = ⊥ := by
  rw [← minimalShiftDefect_eq_adjointDefect]
  exact actualMinimal_eq_friedrichs_iff_defect_eq_bot N

end
end ImbalancedChen.Part3.Gamma0ActualMinimalAdjointDefect20261025a
