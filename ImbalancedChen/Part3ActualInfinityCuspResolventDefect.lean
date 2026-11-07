import ImbalancedChen.Part3ActualInfinityCuspRestrictedEnergy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact positive variational splitting of the original Gamma resolvent by
the actual closed infinity-cusp energy constraint. Its difference from
the constrained resolvent is the adjoint square of the genuine energy
Riesz defect. The defect vanishes on a forcing vector exactly when the
ORIGINAL resolvent output satisfies the actual infinity cusp condition.
No identification of this constrained map with the original restricted
resolvent, no density of the constrained form range, and no all-cusp
spectral completeness or gap are asserted.
-/
namespace ImbalancedChen.Part3.ActualInfinityCuspResolventDefect20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open ActualInfinityCuspAnnihilator20261026b
open ActualInfinityCuspRestrictedEnergy20261026b
open GenericHilbertAdjointSquare20261025a

def infinityCuspEmbeddedRieszLift (N : ℕ) [NeZero N] :
    QuotientL2 N →L[ℂ] EnergyCompletion N :=
  (infinityCuspEnergy N).subtypeL.comp (infinityCuspRieszLift N)

def infinityCuspRieszDefect (N : ℕ) [NeZero N] :
    QuotientL2 N →L[ℂ] EnergyCompletion N :=
  actualRieszLift N - infinityCuspEmbeddedRieszLift N

theorem infinityCuspRieszDefect_apply (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    infinityCuspRieszDefect N f = actualRieszLift N f -
      (infinityCuspRieszLift N f : EnergyCompletion N) := rfl

/-- The actual energy defect is orthogonal to EVERY actual constrained
energy vector, from the two genuine variational identities. -/
theorem infinityCuspRieszDefect_inner_cusp (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (e : infinityCuspEnergy N) :
    inner ℂ (infinityCuspRieszDefect N f) (e : EnergyCompletion N) = 0 := by
  have h1 := actualRieszLift_weak N f (e : EnergyCompletion N)
  have h2 := infinityCuspRieszLift_weak N f e
  change inner ℂ (e : EnergyCompletion N) (infinityCuspRieszLift N f : EnergyCompletion N) =
    inner ℂ (physicalProjection N (e : EnergyCompletion N)) f at h2
  have hzero : inner ℂ (e : EnergyCompletion N) (infinityCuspRieszDefect N f) = 0 := by
    rw [infinityCuspRieszDefect_apply, inner_sub_right, h1, h2, sub_self]
  simpa only [inner_conj_symm, star_zero] using congrArg (fun z : ℂ => star z) hzero

/-- The physical difference is the physical projection of the genuine
energy error; this retains the actual form inclusion J. -/
theorem physicalProjection_infinityCuspRieszDefect (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    physicalProjection N (infinityCuspRieszDefect N f) =
      actualGammaResolvent N f - infinityCuspVariationalResolvent N f := by
  rw [infinityCuspRieszDefect_apply, map_sub, ← actualGammaResolvent_apply]
  rfl

/-- Both mixed terms disappear by actual energy orthogonality. -/
theorem actual_cusp_resolvent_defect_inner (N : ℕ) [NeZero N]
    (f g : QuotientL2 N) :
    inner ℂ f (actualGammaResolvent N g - infinityCuspVariationalResolvent N g) =
      inner ℂ (infinityCuspRieszDefect N f) (infinityCuspRieszDefect N g) := by
  have hC := adjointSquare_inner (infinityCuspEnergyInclusion N) f g
  change inner ℂ f (infinityCuspVariationalResolvent N g) =
    inner ℂ (infinityCuspRieszLift N f : EnergyCompletion N)
      (infinityCuspRieszLift N g : EnergyCompletion N) at hC
  have hfg := infinityCuspRieszDefect_inner_cusp N f (infinityCuspRieszLift N g)
  have hgf := infinityCuspRieszDefect_inner_cusp N g (infinityCuspRieszLift N f)
  have hgf' := congrArg (fun z : ℂ => star z) hgf
  simp only [inner_conj_symm, star_zero] at hgf'
  rw [infinityCuspRieszDefect_apply, inner_sub_left] at hfg
  rw [infinityCuspRieszDefect_apply, inner_sub_right] at hgf'
  rw [inner_sub_right, actualGammaResolvent_inner, hC,
    infinityCuspRieszDefect_apply, infinityCuspRieszDefect_apply,
    inner_sub_left, inner_sub_right, inner_sub_right]
  rw [sub_eq_zero.mp hfg, sub_eq_zero.mp hgf']
  ring

/-- An actual operator identity: the positive difference is D*D on the
original quotient L2, where D is its constructed cusp energy defect. -/
theorem actual_cusp_resolvent_difference_eq_adjoint_square (N : ℕ) [NeZero N] :
    actualGammaResolvent N - infinityCuspVariationalResolvent N =
      (infinityCuspRieszDefect N).adjoint.comp (infinityCuspRieszDefect N) := by
  ext g
  apply ext_inner_left ℂ
  intro f
  change inner ℂ f (actualGammaResolvent N g - infinityCuspVariationalResolvent N g) =
    inner ℂ f ((infinityCuspRieszDefect N).adjoint (infinityCuspRieszDefect N g))
  rw [actual_cusp_resolvent_defect_inner]
  exact ((infinityCuspRieszDefect N).adjoint_inner_right f
    (infinityCuspRieszDefect N g)).symm

theorem actual_cusp_resolvent_difference_positive (N : ℕ) [NeZero N] :
    (actualGammaResolvent N - infinityCuspVariationalResolvent N).IsPositive := by
  rw [actual_cusp_resolvent_difference_eq_adjoint_square]
  simpa only [adjointSquare, ContinuousLinearMap.adjoint_adjoint] using
    adjointSquare_positive (infinityCuspRieszDefect N).adjoint

theorem actual_cusp_resolvent_difference_quadratic (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    (inner ℂ f (actualGammaResolvent N f - infinityCuspVariationalResolvent N f)).re =
      ‖infinityCuspRieszDefect N f‖ ^ 2 := by
  rw [actual_cusp_resolvent_defect_inner, ← InnerProductSpace.norm_sq_eq_re_inner]

/-- Variational domination at every actual forcing, with no uniform
strict positivity or cusp spectral-gap claim. -/
theorem actual_cusp_resolvent_quadratic_le_original (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    (inner ℂ f (infinityCuspVariationalResolvent N f)).re ≤
      (inner ℂ f (actualGammaResolvent N f)).re := by
  have h := actual_cusp_resolvent_difference_quadratic N f
  rw [inner_sub_right, Complex.sub_re] at h
  nlinarith [sq_nonneg ‖infinityCuspRieszDefect N f‖]

/-- The energy defect is zero precisely at the unresolved ORIGINAL
infinity-cusp preservation condition for this actual forcing. -/
theorem infinityCuspRieszDefect_eq_zero_iff (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    infinityCuspRieszDefect N f = 0 ↔ actualGammaResolvent N f ∈ infinityCuspSubspace N := by
  have hphys : infinityCuspRieszDefect N f = 0 ↔
      actualGammaResolvent N f = infinityCuspVariationalResolvent N f := by
    constructor
    · intro h
      have hp := physicalProjection_infinityCuspRieszDefect N f
      rw [h, map_zero] at hp
      exact (sub_eq_zero.mp hp.symm)
    · intro h
      apply physicalProjection_injective N
      rw [physicalProjection_infinityCuspRieszDefect, h, sub_self, map_zero]
  rw [hphys, eq_comm]
  exact infinityCuspVariationalResolvent_eq_original_iff N f

end
end ImbalancedChen.Part3.ActualInfinityCuspResolventDefect20261026b
