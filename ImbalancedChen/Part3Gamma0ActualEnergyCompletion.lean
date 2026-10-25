import ImbalancedChen.Part3ActualGamma0PoincareEnergy
import ImbalancedChen.Part3Gamma0ActualMaassClosedOperator
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The shifted energy space of the ACTUAL Gamma0 quotient smooth Poincare
core. Its inner product is <u,v>_L2 + <u,Delta v>_L2, with the genuine
geometric quotient operator, the proved all-core Green symmetry, and the
proved all-core nonnegative Dirichlet energy. The algebraic core receives
the energy norm before taking its Hilbert completion.

The physical projection is a contraction into the original quotient L2.
Testing against the actual smooth core proves its kernel is zero. This
is form closability, proved here rather than assumed as hClosable. The
existing genuine quotient-core density also proves dense physical range.
No whole-plane Hilbert space is substituted for the Gamma0 quotient.
-/

namespace ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a

noncomputable section
open Set Filter MeasureTheory
open UniformSpace
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualSmoothCoreSymmetry20261025a
open ActualGamma0PoincareEnergy20261025a
open Gamma0ActualMaassClosedOperator20261025a

/-- The actual algebraic core, with a distinct energy norm installed below. -/
def EnergyCore (N : ℕ) [NeZero N] := smoothCore N

instance (N : ℕ) [NeZero N] : AddCommGroup (EnergyCore N) :=
  inferInstanceAs (AddCommGroup (smoothCore N))

instance (N : ℕ) [NeZero N] : Module ℂ (EnergyCore N) :=
  inferInstanceAs (Module ℂ (smoothCore N))

/-- Physical inclusion into the SAME canonical quotient L2 space. -/
def physicalCore (N : ℕ) [NeZero N] : EnergyCore N →ₗ[ℂ] QuotientL2 N :=
  (smoothCore N).subtype

/-- Actual geometric core output; only the input norm will change. -/
def coreLaplacian (N : ℕ) [NeZero N] : EnergyCore N →ₗ[ℂ] QuotientL2 N :=
  actualCoreLaplacian N

def energyPair (N : ℕ) [NeZero N] (u v : EnergyCore N) : ℂ :=
  inner ℂ (physicalCore N u) (physicalCore N v)+
    inner ℂ (physicalCore N u) (coreLaplacian N v)

theorem energyPair_hermitian (N : ℕ) [NeZero N] (u v : EnergyCore N) :
    star (energyPair N v u)=energyPair N u v := by
  have hsym := actualCoreLaplacian_symmetric N u v
  change inner ℂ (coreLaplacian N u) (physicalCore N v)=
    inner ℂ (physicalCore N u) (coreLaplacian N v) at hsym
  simp only [energyPair,map_add,inner_conj_symm]
  rw [hsym]

theorem core_energy_nonneg (N : ℕ) [NeZero N] (u : EnergyCore N) :
    0≤(inner ℂ (physicalCore N u) (coreLaplacian N u)).re :=
  actualCoreLaplacian_nonneg N u

theorem physical_norm_sq_le_energyPair (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖physicalCore N u‖^2≤(energyPair N u u).re := by
  rw [energyPair,Complex.add_re,← InnerProductSpace.norm_sq_eq_re_inner]
  exact le_add_of_nonneg_right (core_energy_nonneg N u)

theorem energyPair_definite (N : ℕ) [NeZero N] (u : EnergyCore N)
    (hu : energyPair N u u=0) : u=0 := by
  have hsq := physical_norm_sq_le_energyPair N u
  rw [hu,Complex.zero_re] at hsq
  have hp : physicalCore N u=0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _)))
  exact Subtype.ext hp

/-- Positive definiteness follows from the physical norm term; positivity
and Hermitian symmetry are the genuine quotient energy theorems. -/
instance energyInnerCore (N : ℕ) [NeZero N] : InnerProductSpace.Core ℂ (EnergyCore N) where
  inner := energyPair N
  conj_inner_symm := energyPair_hermitian N
  re_inner_nonneg u := (sq_nonneg ‖physicalCore N u‖).trans
    (physical_norm_sq_le_energyPair N u)
  add_left u v w := by
    simp only [energyPair,map_add,inner_add_left]
    ring
  smul_left u v c := by
    simp only [energyPair,map_smul,inner_smul_left]
    ring
  definite := energyPair_definite N

instance energyNormedAddCommGroup (N : ℕ) [NeZero N] : NormedAddCommGroup (EnergyCore N) :=
  InnerProductSpace.Core.toNormedAddCommGroup

instance energyInnerProductSpace (N : ℕ) [NeZero N] : InnerProductSpace ℂ (EnergyCore N) :=
  InnerProductSpace.ofCore (energyInnerCore N).toPreInnerProductSpaceCore

theorem energyInner_apply (N : ℕ) [NeZero N] (u v : EnergyCore N) :
    inner ℂ u v=inner ℂ (physicalCore N u) (physicalCore N v)+
      inner ℂ (physicalCore N u) (coreLaplacian N v) := by rfl

theorem energy_norm_sq (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖u‖^2=‖physicalCore N u‖^2+
      (inner ℂ (physicalCore N u) (coreLaplacian N u)).re := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) u,
    energyInner_apply,Complex.add_re,← InnerProductSpace.norm_sq_eq_re_inner]

theorem physical_norm_le_energy_norm (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖physicalCore N u‖≤‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [energy_norm_sq]
  exact le_add_of_nonneg_right (core_energy_nonneg N u)

/-- Complete Hilbert space of the actual shifted quotient energy. -/
abbrev EnergyCompletion (N : ℕ) [NeZero N] := Completion (EnergyCore N)

def coreEmbedding (N : ℕ) [NeZero N] : EnergyCore N →ₗᵢ[ℂ] EnergyCompletion N :=
  Completion.toComplₗᵢ

theorem coreEmbedding_norm (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖coreEmbedding N u‖=‖u‖ := (coreEmbedding N).norm_map u

theorem coreEmbedding_denseRange (N : ℕ) [NeZero N] : DenseRange (coreEmbedding N) :=
  Completion.denseRange_coe

theorem physical_bound_on_completion_core (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ‖physicalCore N u‖≤1*‖coreEmbedding N u‖ := by
  rw [one_mul,coreEmbedding_norm]
  exact physical_norm_le_energy_norm N u

/-- Extend the physical inclusion using the derived energy-norm bound. -/
def physicalProjection (N : ℕ) [NeZero N] : EnergyCompletion N →L[ℂ] QuotientL2 N :=
  (physicalCore N).extendOfNorm (coreEmbedding N).toLinearMap

theorem physicalProjection_core (N : ℕ) [NeZero N] (u : EnergyCore N) :
    physicalProjection N (coreEmbedding N u)=physicalCore N u := by
  exact LinearMap.extendOfNorm_eq (coreEmbedding_denseRange N)
    ⟨1,physical_bound_on_completion_core N⟩ u

theorem physicalProjection_norm_le (N : ℕ) [NeZero N] (w : EnergyCompletion N) :
    ‖physicalProjection N w‖≤‖w‖ := by
  simpa only [one_mul,physicalProjection] using
    (LinearMap.norm_extendOfNorm_apply_le (f := physicalCore N)
      (e := (coreEmbedding N).toLinearMap) (coreEmbedding_denseRange N) 1
      (physical_bound_on_completion_core N) w)

theorem physicalProjection_opNorm_le_one (N : ℕ) [NeZero N] :
    ‖physicalProjection N‖≤1 := by
  apply (physicalProjection N).opNorm_le_bound (by norm_num)
  intro w
  simpa only [one_mul] using physicalProjection_norm_le N w

/-- The actual shifted differential test identity persists in the energy
completion, by continuity in its first variable and genuine core density. -/
theorem physicalProjection_testing (N : ℕ) [NeZero N] (w : EnergyCompletion N)
    (v : EnergyCore N) :
    inner ℂ w (coreEmbedding N v)=
      inner ℂ (physicalProjection N w) (physicalCore N v+coreLaplacian N v) := by
  refine Completion.induction_on w ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const)
      ((physicalProjection N).continuous.inner continuous_const)
  · intro u
    rw [physicalProjection_core]
    change inner ℂ (u : Completion (EnergyCore N)) (v : Completion (EnergyCore N))=_
    rw [Completion.inner_coe,energyInner_apply,inner_add_right]

/-- Form closability: a completed energy vector with physical image zero
annihilates the dense energy core, and hence vanishes. No hClosable input. -/
theorem physicalProjection_kernel_trivial (N : ℕ) [NeZero N]
    (w : EnergyCompletion N) (hw : physicalProjection N w=0) : w=0 := by
  apply (coreEmbedding_denseRange N).eq_zero_of_inner_left ℂ
  intro v
  rw [physicalProjection_testing,hw,inner_zero_left]

theorem physicalProjection_injective (N : ℕ) [NeZero N] :
    Function.Injective (physicalProjection N) := by
  intro w z hwz
  apply sub_eq_zero.mp
  apply physicalProjection_kernel_trivial N (w-z)
  rw [map_sub,hwz,sub_self]

/-- The physical range is dense by the separately proved actual quotient
smooth-core density, rather than a supplied dense-range hypothesis. -/
theorem physicalProjection_denseRange (N : ℕ) [NeZero N] :
    DenseRange (physicalProjection N) := by
  apply (actual_smoothCore_dense N).mono
  intro u hu
  let v : EnergyCore N := (⟨u,hu⟩ : smoothCore N)
  exact ⟨coreEmbedding N v,by simpa only [v,physicalCore] using physicalProjection_core N v⟩

/-- The closed-form domain can now be realized as an actual subspace of
the physical quotient L2 through an injective, densely ranged contraction. -/
theorem actual_energy_completion_embedding (N : ℕ) [NeZero N] :
    Function.Injective (physicalProjection N) ∧ DenseRange (physicalProjection N) ∧
      ‖physicalProjection N‖≤1 :=
  ⟨physicalProjection_injective N,physicalProjection_denseRange N,
    physicalProjection_opNorm_le_one N⟩

end
end ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
