import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator
import ImbalancedChen.Part3ActualGamma0CoreDirichletForm
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The actual closed Dirichlet form in physical Gamma0 quotient L2

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

This module uses the EXISTING actualEnergyFormDomain = range J and the
EXISTING actualDirichletPair on the genuine energy completion. It does
not define a parallel physical submodule, a new form-domain type, or a
different pairing. The proved injectivity of the actual J gives a unique
linear energy lift of that physical domain.

The domain carries an explicit transported Hilbert norm, used only via
local instances below, so the inherited physical subtype norm is not
globally overwritten. In that energy norm the existing domain is
complete, the physical inclusion is continuous and densely ranged, and
the shifted norm equals physical norm squared plus Dirichlet energy.
The existing completed form extends the literal canonical geometric
smooth-core gradient form. No form-closability or domain-density premise
is supplied, and the minimal closed operator domain is not identified
with this form domain.
-/

namespace ImbalancedChen.Part3.Gamma0PhysicalClosedDirichletForm20261025a

noncomputable section
open Set Filter MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open ActualGamma0CoreDirichletForm20261025a

/-- The inverse of the actual injective J, on its already defined
physical form domain. No choice of representative remains ambiguous. -/
def actualEnergyLift (N : ℕ) [NeZero N] :
    actualEnergyFormDomain N ≃ₗ[ℂ] EnergyCompletion N :=
  (LinearEquiv.ofInjective (physicalProjection N).toLinearMap
    (physicalProjection_injective N)).symm

@[simp] theorem actualEnergyLift_projection (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    physicalProjection N (actualEnergyLift N u) = (u : QuotientL2 N) :=
  congrArg (fun v : actualEnergyFormDomain N => (v : QuotientL2 N))
    ((actualEnergyLift N).symm_apply_apply u)

@[simp] theorem actualEnergyLift_symm_val (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    ((actualEnergyLift N).symm e : QuotientL2 N) = physicalProjection N e := rfl

/-- The energy Hilbert inner product transported to the EXISTING
physical form domain, before assigning its energy norm. -/
def formEnergyInnerCore (N : ℕ) [NeZero N] :
    InnerProductSpace.Core ℂ (actualEnergyFormDomain N) where
  inner u v := inner ℂ (actualEnergyLift N u) (actualEnergyLift N v)
  conj_inner_symm u v := inner_conj_symm _ _
  re_inner_nonneg u := inner_self_nonneg
  add_left u v w := by rw [map_add,inner_add_left]
  smul_left u v c := by rw [map_smul,inner_smul_left]
  definite u hu := by
    apply (actualEnergyLift N).injective
    simpa only [map_zero] using inner_self_eq_zero.mp hu

/-- Explicit energy norm on the same physical domain. This is a named
structure, deliberately not a global replacement of the physical norm. -/
def formEnergyNormedAddCommGroup (N : ℕ) [NeZero N] :
    NormedAddCommGroup (actualEnergyFormDomain N) :=
  (formEnergyInnerCore N).toNormedAddCommGroup

/-- The energy Hilbert structure uses exactly the preceding energy norm. -/
def formEnergyInnerProductSpace (N : ℕ) [NeZero N] :
    letI := formEnergyNormedAddCommGroup N
    InnerProductSpace ℂ (actualEnergyFormDomain N) :=
  InnerProductSpace.ofCore (formEnergyInnerCore N).toPreInnerProductSpaceCore

section EnergyTopology

attribute [local instance] formEnergyNormedAddCommGroup formEnergyInnerProductSpace

/-- The existing physical domain, in its energy norm, is isometrically
the genuine completed energy space. -/
def actualEnergyLiftIsometry (N : ℕ) [NeZero N] :
    actualEnergyFormDomain N ≃ₗᵢ[ℂ] EnergyCompletion N where
  toLinearEquiv := actualEnergyLift N
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
    rfl

/-- Closed-form completeness is proved through the actual injective J,
without assuming closability or completeness of its physical range. -/
theorem actualEnergyFormDomain_complete (N : ℕ) [NeZero N] :
    CompleteSpace (actualEnergyFormDomain N) :=
  (actualEnergyLiftIsometry N).toIsometryEquiv.completeSpace

attribute [local instance] actualEnergyFormDomain_complete

theorem form_energy_inner_eq_lifts (N : ℕ) [NeZero N]
    (u v : actualEnergyFormDomain N) :
    inner ℂ u v = inner ℂ (actualEnergyLift N u) (actualEnergyLift N v) := rfl

theorem form_energy_norm_eq_lift (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    ‖u‖ = ‖actualEnergyLift N u‖ := ((actualEnergyLiftIsometry N).norm_map u).symm

/-- Continuous physical inclusion of the actual closed-form domain. -/
def actualFormInclusion (N : ℕ) [NeZero N] :
    actualEnergyFormDomain N →L[ℂ] QuotientL2 N :=
  (physicalProjection N).comp (actualEnergyLiftIsometry N).toLinearIsometry.toContinuousLinearMap

@[simp] theorem actualFormInclusion_apply (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    actualFormInclusion N u = (u : QuotientL2 N) := actualEnergyLift_projection N u

theorem actualFormInclusion_norm_le (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) : ‖actualFormInclusion N u‖ ≤ ‖u‖ := by
  change ‖physicalProjection N (actualEnergyLift N u)‖ ≤ ‖u‖
  rw [form_energy_norm_eq_lift]
  exact physicalProjection_norm_le N _

theorem actualFormInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (actualFormInclusion N) := by
  intro u v huv
  apply Subtype.ext
  simpa only [actualFormInclusion_apply] using huv

theorem actualFormInclusion_denseRange (N : ℕ) [NeZero N] :
    DenseRange (actualFormInclusion N) := by
  apply (physicalProjection_denseRange N).mono
  rintro _ ⟨e,rfl⟩
  exact ⟨(actualEnergyLift N).symm e,by simp only [actualFormInclusion_apply,
    actualEnergyLift_symm_val]⟩

/-- Actual smooth-core inclusion, with its previously proved energy norm. -/
def actualFormCoreEmbedding (N : ℕ) [NeZero N] :
    EnergyCore N →ₗᵢ[ℂ] actualEnergyFormDomain N :=
  (actualEnergyLiftIsometry N).symm.toLinearIsometry.comp (coreEmbedding N)

@[simp] theorem actualEnergyLift_coreEmbedding (N : ℕ) [NeZero N]
    (u : EnergyCore N) :
    actualEnergyLift N (actualFormCoreEmbedding N u) = coreEmbedding N u :=
  (actualEnergyLift N).apply_symm_apply _

@[simp] theorem actualFormCoreEmbedding_physical (N : ℕ) [NeZero N]
    (u : EnergyCore N) :
    actualFormInclusion N (actualFormCoreEmbedding N u) = physicalCore N u := by
  change physicalProjection N (actualEnergyLift N (actualFormCoreEmbedding N u)) = _
  rw [actualEnergyLift_coreEmbedding,physicalProjection_core]

/-- The original energy core is dense in this very physical form domain
for the energy norm, in addition to physical density in the ambient L2. -/
theorem actualFormCoreEmbedding_denseRange (N : ℕ) [NeZero N] :
    DenseRange (actualFormCoreEmbedding N) :=
  ((actualEnergyLiftIsometry N).symm.surjective.denseRange).comp
    (coreEmbedding_denseRange N) (actualEnergyLiftIsometry N).symm.continuous

/-- Exact closed-form norm identity on the original physical range J. -/
theorem actualDirichletPair_energy_norm (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    ‖u‖^2 = ‖(u : QuotientL2 N)‖^2 +
      (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re := by
  rw [form_energy_norm_eq_lift,actualDirichletPair,Complex.sub_re]
  simp only [actualEnergyLift_projection]
  rw [
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  ring

/-- An explicit sequential closedness statement: every energy-Cauchy
sequence has a domain limit and converges physically to that same vector. -/
theorem actual_form_energy_cauchy_complete (N : ℕ) [NeZero N]
    (u : ℕ → actualEnergyFormDomain N) (hu : CauchySeq u) :
    ∃ v : actualEnergyFormDomain N, Tendsto u atTop (𝓝 v) ∧
      Tendsto (fun n => (u n : QuotientL2 N)) atTop (𝓝 (v : QuotientL2 N)) := by
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hu
  refine ⟨v,hv,?_⟩
  simpa only [actualFormInclusion_apply] using
    ((actualFormInclusion N).continuous.tendsto v).comp hv

end EnergyTopology

/-- Physical density is a property of the already defined actual
submodule, independent of which norm is used on its domain subtype. -/
theorem actualEnergyFormDomain_dense (N : ℕ) [NeZero N] :
    Dense (actualEnergyFormDomain N : Set (QuotientL2 N)) :=
  physicalProjection_denseRange N

/-- The shifted norm identity can also be used without activating the
domain's energy topology: both norms here are on the existing E and H. -/
theorem actualEnergyLift_shifted_norm (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    ‖(u : QuotientL2 N)‖^2 +
      (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re =
        ‖actualEnergyLift N u‖^2 := by
  rw [actualDirichletPair,Complex.sub_re]
  simp only [actualEnergyLift_projection]
  rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  ring

theorem actualPhysicalDirichlet_nonneg (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    0 ≤ (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re :=
  actualDirichletPair_nonneg N _

/-- The existing completed pair really extends the canonical geometric
gradient form on every pair of actual smooth-core vectors. -/
theorem actualDirichletPair_core_geometric (N : ℕ) [NeZero N]
    (u v : EnergyCore N) :
    actualDirichletPair N (coreEmbedding N u) (coreEmbedding N v) =
      coreDirichletForm N u v := by
  rw [actualDirichletPair_core,coreDirichletForm_eq_operatorPair]
  rfl

theorem actualDirichletPair_star (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    star (actualDirichletPair N d e) = actualDirichletPair N e d := by
  simp only [actualDirichletPair,map_sub,inner_conj_symm]

theorem actualDirichletPair_add_left (N : ℕ) [NeZero N]
    (d e f : EnergyCompletion N) :
    actualDirichletPair N (d+e) f = actualDirichletPair N d f + actualDirichletPair N e f := by
  simp only [actualDirichletPair,map_add,inner_add_left]
  ring

theorem actualDirichletPair_add_right (N : ℕ) [NeZero N]
    (d e f : EnergyCompletion N) :
    actualDirichletPair N d (e+f) = actualDirichletPair N d e + actualDirichletPair N d f := by
  simp only [actualDirichletPair,map_add,inner_add_right]
  ring

theorem actualDirichletPair_smul_left (N : ℕ) [NeZero N] (c : ℂ)
    (d e : EnergyCompletion N) :
    actualDirichletPair N (c • d) e = star c * actualDirichletPair N d e := by
  simp only [actualDirichletPair,map_smul,inner_smul_left]
  ring

theorem actualDirichletPair_smul_right (N : ℕ) [NeZero N] (c : ℂ)
    (d e : EnergyCompletion N) :
    actualDirichletPair N d (c • e) = c * actualDirichletPair N d e := by
  simp only [actualDirichletPair,map_smul,inner_smul_right]
  ring

/-- Positive semidefinite structure for the existing unshifted form;
no change to the completed shifted-energy Hilbert norm is installed. -/
def actualDirichletPreInner (N : ℕ) [NeZero N] :
    PreInnerProductSpace.Core ℂ (EnergyCompletion N) where
  inner := actualDirichletPair N
  conj_inner_symm d e := actualDirichletPair_star N e d
  re_inner_nonneg := actualDirichletPair_nonneg N
  add_left := actualDirichletPair_add_left N
  smul_left d e c := actualDirichletPair_smul_left N c d e

/-- Global Cauchy--Schwarz for the actual closed Dirichlet pairing,
including vectors beyond the original algebraic smooth core. -/
theorem actualDirichletPair_normSq_le (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    Complex.normSq (actualDirichletPair N d e) ≤
      (actualDirichletPair N d d).re * (actualDirichletPair N e e).re := by
  have h : ‖actualDirichletPair N d e‖ * ‖actualDirichletPair N e d‖ ≤
      (actualDirichletPair N d d).re * (actualDirichletPair N e e).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (F := EnergyCompletion N)
      (c := actualDirichletPreInner N) d e
  have hnorm : ‖actualDirichletPair N e d‖ = ‖actualDirichletPair N d e‖ := by
    rw [← actualDirichletPair_star N d e,norm_star]
  rw [hnorm] at h
  simpa only [Complex.normSq_eq_norm_sq,pow_two] using h

end
end ImbalancedChen.Part3.Gamma0PhysicalClosedDirichletForm20261025a
