import ImbalancedChen.Part3Gamma0ActualWeakRieszResolvent
import ImbalancedChen.Part3GenericFriedrichsOperator
import ImbalancedChen.Part3GenericWeakFriedrichsAssociation

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL Gamma0 Friedrichs operator A=R^{-1}-I is a native unbounded
partial linear map on the SAME actual quotient L2 space. R is the genuine
physical J J* obtained from the actual completed shifted Dirichlet form.
Native self-adjointness, closedness, dense domain, exact range-R domain,
and nonnegativity follow from the constructed actual suppliers.

The exact graph is additionally identified with the actual COMPLETED
energy variational relation, and hence with the genuine unshifted
Dirichlet pairing <d,e>_energy-<Jd,Je>_physical. No hSA/hPosF/hWeakGraph
premise or whole-plane relabeling occurs. Inclusion of the minimal closed
geometric operator is owned by a separate module; essential self-adjointness
is not asserted here.
-/

namespace ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open GenericFriedrichsOperator20261025a
open GenericWeakFriedrichsAssociation20261025a

/-- A genuine native unbounded operator on the actual quotient Hilbert
space, constructed from the actual physical energy resolvent. -/
def actualGammaFriedrichs (N : ℕ) [NeZero N] : QuotientL2 N→ₗ.[ℂ]QuotientL2 N :=
  friedrichsR (actualGammaResolvent N)

theorem actualGammaFriedrichs_domain (N : ℕ) [NeZero N] :
    (actualGammaFriedrichs N).domain=(actualGammaResolvent N).range :=
  friedrichsR_domain (actualGammaResolvent N)

/-- Public graph API for the independently owned minimal-closure inclusion. -/
theorem actualGammaFriedrichs_mem_graph_iff (N : ℕ) [NeZero N]
    {u v : QuotientL2 N} :
    (u,v)∈(actualGammaFriedrichs N).graph ↔ actualGammaResolvent N (u+v)=u :=
  friedrichsR_mem_graph_iff (actualGammaResolvent N) (actualGammaResolvent_injective N)

theorem actualGammaFriedrichs_isClosed (N : ℕ) [NeZero N] :
    (actualGammaFriedrichs N).IsClosed :=
  friedrichsR_isClosed (actualGammaResolvent N) (actualGammaResolvent_injective N)

theorem actualGammaFriedrichs_dense_domain (N : ℕ) [NeZero N] :
    Dense ((actualGammaFriedrichs N).domain : Set (QuotientL2 N)) :=
  friedrichsR_dense_domain (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_injective N)

/-- Native self-adjointness of THIS actual Gamma0 operator, not merely
symmetry of the differential core or of an unrelated whole-plane operator. -/
theorem actualGammaFriedrichs_isSelfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (actualGammaFriedrichs N) :=
  friedrichsR_isSelfAdjoint (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_injective N)

theorem actualGammaFriedrichs_nonneg (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    0≤(inner ℂ (u:QuotientL2 N) (actualGammaFriedrichs N u)).re :=
  friedrichsR_nonneg (actualGammaResolvent N) (actualGammaResolvent_injective N)
    (actualGammaResolvent_firm N) u

theorem actualGammaFriedrichs_graph_nonneg (N : ℕ) [NeZero N]
    {u v : QuotientL2 N} (huv : (u,v)∈(actualGammaFriedrichs N).graph) :
    0≤(inner ℂ u v).re :=
  friedrichsR_graph_nonneg (actualGammaResolvent N) (actualGammaResolvent_injective N)
    (actualGammaResolvent_firm N) huv

def actualResolventPoint (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    (actualGammaFriedrichs N).domain := resolventPoint (actualGammaResolvent N) f

theorem actualGammaFriedrichs_apply_resolvent (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualGammaFriedrichs N (actualResolventPoint N f)=f-actualGammaResolvent N f :=
  friedrichsR_apply_image (actualGammaResolvent N) (actualGammaResolvent_injective N) f

theorem actualGammaFriedrichs_shift_surjective (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ∃ u : (actualGammaFriedrichs N).domain,(u:QuotientL2 N)+actualGammaFriedrichs N u=f :=
  friedrichsR_shift_surjective (actualGammaResolvent N) (actualGammaResolvent_injective N) f

/-- The actual closed operator has the same physical resolvent R on
every vector in its true domain, not just the original smooth core. -/
theorem actualGammaResolvent_shift_friedrichs (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaResolvent N ((u:QuotientL2 N)+actualGammaFriedrichs N u)=u :=
  (actualGammaFriedrichs_mem_graph_iff N).mp (LinearPMap.mem_graph _ u)

/-- The shifted-energy relation is on the TRUE E_Gamma and H_Gamma. -/
def actualShiftedEnergyRelation (N : ℕ) [NeZero N] (u v : QuotientL2 N) : Prop :=
  WeakEnergyRelation (physicalProjection N) u v

theorem actualGammaFriedrichs_mem_graph_iff_weakEnergy (N : ℕ) [NeZero N]
    {u v : QuotientL2 N} :
    (u,v)∈(actualGammaFriedrichs N).graph ↔ actualShiftedEnergyRelation N u v := by
  rw [actualGammaFriedrichs_mem_graph_iff]
  exact (weakEnergyRelation_iff_adjointSquare (physicalProjection N) u v).symm

/-- The unshifted ACTUAL closed Dirichlet pairing, expressed using the
genuine shifted-energy completion and its injective physical projection. -/
def actualDirichletRelation (N : ℕ) [NeZero N] (u v : QuotientL2 N) : Prop :=
  ∃ e : EnergyCompletion N,physicalProjection N e=u ∧
    ∀ d : EnergyCompletion N,
      inner ℂ d e-inner ℂ (physicalProjection N d) u=inner ℂ (physicalProjection N d) v

/-- Actual closed-form domain in physical quotient L2. This is range J,
distinguished from the smaller operator domain range R. -/
def actualEnergyFormDomain (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (physicalProjection N).range

def actualDirichletPair (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) : ℂ :=
  inner ℂ d e-inner ℂ (physicalProjection N d) (physicalProjection N e)

theorem actualDirichletPair_nonneg (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    0≤(actualDirichletPair N e e).re := by
  unfold actualDirichletPair
  rw [Complex.sub_re,← InnerProductSpace.norm_sq_eq_re_inner,
    ← InnerProductSpace.norm_sq_eq_re_inner]
  exact sub_nonneg.mpr
    (pow_le_pow_left₀ (norm_nonneg _) (physicalProjection_norm_le N e) 2)

/-- On the actual smooth core the completed form is exactly the genuine
geometric quotient Laplacian pairing, with no independent form supplier. -/
theorem actualDirichletPair_core (N : ℕ) [NeZero N] (u v : EnergyCore N) :
    actualDirichletPair N (coreEmbedding N u) (coreEmbedding N v)=
      inner ℂ (physicalCore N u) (coreLaplacian N v) := by
  rw [actualDirichletPair,physicalProjection_core,physicalProjection_core]
  change inner ℂ (u : UniformSpace.Completion (EnergyCore N))
      (v : UniformSpace.Completion (EnergyCore N))-
      inner ℂ (physicalCore N u) (physicalCore N v)=_
  rw [UniformSpace.Completion.inner_coe,energyInner_apply]
  ring

theorem actualGammaFriedrichs_domain_le_formDomain (N : ℕ) [NeZero N] :
    (actualGammaFriedrichs N).domain≤actualEnergyFormDomain N := by
  intro u hu
  rw [actualGammaFriedrichs_domain] at hu
  obtain ⟨f,rfl⟩ := hu
  exact actualGammaResolvent_mem_energy_range N f

theorem actualShiftedEnergyRelation_iff_Dirichlet (N : ℕ) [NeZero N]
    (u v : QuotientL2 N) :
    actualShiftedEnergyRelation N u v ↔ actualDirichletRelation N u v := by
  constructor
  · rintro ⟨e,he,htest⟩
    refine ⟨e,he,?_⟩
    intro d
    have hh := htest d
    rw [inner_add_right] at hh
    rw [hh]
    ring
  · rintro ⟨e,he,htest⟩
    refine ⟨e,he,?_⟩
    intro d
    rw [inner_add_right]
    have hh := htest d
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

/-- THIS native self-adjoint operator is associated with the ACTUAL
completed closed Dirichlet form, rather than only a bare algebraic graph. -/
theorem actualGammaFriedrichs_mem_graph_iff_Dirichlet (N : ℕ) [NeZero N]
    {u v : QuotientL2 N} :
    (u,v)∈(actualGammaFriedrichs N).graph ↔ actualDirichletRelation N u v :=
  (actualGammaFriedrichs_mem_graph_iff_weakEnergy N).trans
    (actualShiftedEnergyRelation_iff_Dirichlet N u v)

/-- Exact association with the named ACTUAL closed Dirichlet pairing. -/
theorem actualGammaFriedrichs_mem_graph_iff_formPair (N : ℕ) [NeZero N]
    {u v : QuotientL2 N} :
    (u,v)∈(actualGammaFriedrichs N).graph ↔
      ∃ e : EnergyCompletion N,physicalProjection N e=u ∧
        ∀ d : EnergyCompletion N,actualDirichletPair N d e=inner ℂ (physicalProjection N d) v := by
  rw [actualGammaFriedrichs_mem_graph_iff_Dirichlet]
  constructor
  · rintro ⟨e,he,htest⟩
    refine ⟨e,he,?_⟩
    intro d
    rw [actualDirichletPair,he]
    exact htest d
  · rintro ⟨e,he,htest⟩
    refine ⟨e,he,?_⟩
    intro d
    have hh := htest d
    simpa only [actualDirichletPair,he] using hh

end
end ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
