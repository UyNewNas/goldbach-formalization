import ImbalancedChen.Part3ActualInfinityCuspAnnihilator
import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual infinity-cusp annihilator has a closed preimage in the genuine
Gamma energy Hilbert space. This constructs its constrained Riesz solution,
proves actual shifted-form coercivity, and identifies the constrained lift
as the ENERGY orthogonal projection of the original Gamma Riesz lift.
Equality with the original physical resolvent is proved equivalent to the
original output satisfying the actual cusp condition; invariance of that
condition is not assumed or claimed. Other rational cusps remain separate.
-/
namespace ImbalancedChen.Part3.ActualInfinityCuspRestrictedEnergy20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open ActualInfinityCuspAnnihilator20261026b
open GenericHilbertAdjointSquare20261025a

/-- Actual energy vectors whose physical quotient representatives
annihilate every genuine incomplete Eisenstein seed at infinity. -/
def infinityCuspEnergy (N : ℕ) [NeZero N] : Submodule ℂ (EnergyCompletion N) :=
  (infinityCuspSubspace N).comap (physicalProjection N).toLinearMap

theorem infinityCuspEnergy_closed (N : ℕ) [NeZero N] :
    IsClosed (infinityCuspEnergy N : Set (EnergyCompletion N)) := by
  change IsClosed ((physicalProjection N) ⁻¹'
    (infinityCuspSubspace N : Set (QuotientL2 N)))
  exact (infinityCuspSubspace_closed N).preimage (physicalProjection N).continuous

instance infinityCuspEnergy_complete (N : ℕ) [NeZero N] :
    CompleteSpace (infinityCuspEnergy N) :=
  (infinityCuspEnergy_closed N).completeSpace_coe

def infinityCuspEnergyInclusion (N : ℕ) [NeZero N] :
    infinityCuspEnergy N →L[ℂ] QuotientL2 N :=
  (physicalProjection N).comp (infinityCuspEnergy N).subtypeL

theorem infinityCuspEnergyInclusion_apply (N : ℕ) [NeZero N]
    (e : infinityCuspEnergy N) :
    infinityCuspEnergyInclusion N e = physicalProjection N (e : EnergyCompletion N) := rfl

theorem infinityCuspEnergyInclusion_mem (N : ℕ) [NeZero N]
    (e : infinityCuspEnergy N) :
    infinityCuspEnergyInclusion N e ∈ infinityCuspSubspace N := e.property

theorem infinityCuspEnergyInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (infinityCuspEnergyInclusion N) := by
  intro e d h
  apply Subtype.ext
  exact physicalProjection_injective N h

theorem infinityCuspEnergyInclusion_norm_le (N : ℕ) [NeZero N]
    (e : infinityCuspEnergy N) : ‖infinityCuspEnergyInclusion N e‖ ≤ ‖e‖ :=
  physicalProjection_norm_le N (e : EnergyCompletion N)

theorem infinityCuspEnergyInclusion_opNorm_le_one (N : ℕ) [NeZero N] :
    ‖infinityCuspEnergyInclusion N‖ ≤ 1 := by
  apply (infinityCuspEnergyInclusion N).opNorm_le_bound zero_le_one
  intro e
  simpa only [one_mul] using infinityCuspEnergyInclusion_norm_le N e

/-- The original closed Dirichlet form supplies coercivity on this actual
closed cusp energy subspace, with explicit min(1,a), not a spectral gap. -/
theorem actual_cusp_shifted_form_coercive (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0 < a) (e : infinityCuspEnergy N) :
    min 1 a * ‖e‖ ^ 2 ≤ a * ‖infinityCuspEnergyInclusion N e‖ ^ 2 +
      (actualDirichletPair N (e : EnergyCompletion N) (e : EnergyCompletion N)).re := by
  have he : ‖e‖ ^ 2 = ‖infinityCuspEnergyInclusion N e‖ ^ 2 +
      (actualDirichletPair N (e : EnergyCompletion N) (e : EnergyCompletion N)).re := by
    rw [actualDirichletPair, Complex.sub_re,
      ← InnerProductSpace.norm_sq_eq_re_inner, ← InnerProductSpace.norm_sq_eq_re_inner]
    change ‖(e : EnergyCompletion N)‖ ^ 2 =
      ‖physicalProjection N (e : EnergyCompletion N)‖ ^ 2 +
      (‖(e : EnergyCompletion N)‖ ^ 2 - ‖physicalProjection N (e : EnergyCompletion N)‖ ^ 2)
    ring
  have hD := actualDirichletPair_nonneg N (e : EnergyCompletion N)
  have hmD := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) a) hD
  have hmP := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) a)
    (sq_nonneg ‖infinityCuspEnergyInclusion N e‖)
  rw [he]
  nlinarith

def infinityCuspRieszLift (N : ℕ) [NeZero N] :
    QuotientL2 N →L[ℂ] infinityCuspEnergy N :=
  rieszLift (infinityCuspEnergyInclusion N)

def infinityCuspVariationalResolvent (N : ℕ) [NeZero N] :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  adjointSquare (infinityCuspEnergyInclusion N)

theorem infinityCuspRieszLift_weak (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (d : infinityCuspEnergy N) :
    inner ℂ d (infinityCuspRieszLift N f) =
      inner ℂ (infinityCuspEnergyInclusion N d) f :=
  rieszLift_weak (infinityCuspEnergyInclusion N) f d

/-- Every test belongs to the actual completed cusp energy subspace.
No weak-equation supplier is an input. -/
theorem infinityCuspRieszLift_Dirichlet (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (d : infinityCuspEnergy N) :
    inner ℂ (infinityCuspEnergyInclusion N d)
        (infinityCuspVariationalResolvent N f) +
      actualDirichletPair N (d : EnergyCompletion N)
        (infinityCuspRieszLift N f : EnergyCompletion N) =
      inner ℂ (infinityCuspEnergyInclusion N d) f := by
  have hw := infinityCuspRieszLift_weak N f d
  change inner ℂ (d : EnergyCompletion N) (infinityCuspRieszLift N f : EnergyCompletion N) =
    inner ℂ (infinityCuspEnergyInclusion N d) f at hw
  change inner ℂ (physicalProjection N (d : EnergyCompletion N))
      (physicalProjection N (infinityCuspRieszLift N f : EnergyCompletion N)) +
    actualDirichletPair N (d : EnergyCompletion N)
      (infinityCuspRieszLift N f : EnergyCompletion N) = _
  rw [actualDirichletPair]
  linear_combination hw

theorem infinityCuspRieszLift_unique (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (e : infinityCuspEnergy N)
    (he : ∀ d : infinityCuspEnergy N, inner ℂ d e =
      inner ℂ (infinityCuspEnergyInclusion N d) f) :
    e = infinityCuspRieszLift N f :=
  rieszLift_weak_unique (infinityCuspEnergyInclusion N) f e he

theorem infinityCuspVariationalResolvent_mem (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    infinityCuspVariationalResolvent N f ∈ infinityCuspSubspace N :=
  infinityCuspEnergyInclusion_mem N (infinityCuspRieszLift N f)

theorem infinityCuspVariationalResolvent_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (infinityCuspVariationalResolvent N) :=
  adjointSquare_selfAdjoint (infinityCuspEnergyInclusion N)

theorem infinityCuspVariationalResolvent_firm (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    ‖infinityCuspVariationalResolvent N f‖ ^ 2 ≤
      (inner ℂ f (infinityCuspVariationalResolvent N f)).re :=
  adjointSquare_firm (infinityCuspEnergyInclusion N)
    (infinityCuspEnergyInclusion_opNorm_le_one N) f

/-- Exact comparison in the ENERGY Hilbert space, not an unsupported
identification with the physical orthogonal projection. -/
theorem infinityCuspRieszLift_eq_energyProjection (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    (infinityCuspEnergy N).starProjection (actualRieszLift N f) =
      (infinityCuspRieszLift N f : EnergyCompletion N) := by
  apply (infinityCuspEnergy N).eq_starProjection_of_mem_of_inner_eq_zero
    (infinityCuspRieszLift N f).property
  intro w hw
  have h1 := actualRieszLift_weak N f w
  have h2 := infinityCuspRieszLift_weak N f ⟨w, hw⟩
  change inner ℂ w (infinityCuspRieszLift N f : EnergyCompletion N) =
    inner ℂ (physicalProjection N w) f at h2
  have hz : inner ℂ w
      (actualRieszLift N f - (infinityCuspRieszLift N f : EnergyCompletion N)) = 0 := by
    rw [inner_sub_right, h1, h2, sub_self]
  simpa only [inner_conj_symm, star_zero] using congrArg (fun z : ℂ => star z) hz

/-- This equivalence exposes the precise remaining reducing-subspace
obligation for the ORIGINAL actual Gamma resolvent. -/
theorem infinityCuspVariationalResolvent_eq_original_iff (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    infinityCuspVariationalResolvent N f = actualGammaResolvent N f ↔
      actualGammaResolvent N f ∈ infinityCuspSubspace N := by
  constructor
  · intro h
    rw [← h]
    exact infinityCuspVariationalResolvent_mem N f
  · intro h
    have he : actualRieszLift N f ∈ infinityCuspEnergy N := by
      change physicalProjection N (actualRieszLift N f) ∈ infinityCuspSubspace N
      simpa only [← actualGammaResolvent_apply] using h
    have hp := (infinityCuspEnergy N).starProjection_eq_self_iff.mpr he
    have hc : (infinityCuspRieszLift N f : EnergyCompletion N) = actualRieszLift N f :=
      (infinityCuspRieszLift_eq_energyProjection N f).symm.trans hp
    change physicalProjection N (infinityCuspRieszLift N f : EnergyCompletion N) =
      physicalProjection N (actualRieszLift N f)
    exact congrArg (physicalProjection N) hc

end
end ImbalancedChen.Part3.ActualInfinityCuspRestrictedEnergy20261026b
