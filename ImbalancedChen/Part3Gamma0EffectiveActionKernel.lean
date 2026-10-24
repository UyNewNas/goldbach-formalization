import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.

The action of `SL(2, ℤ)` on the upper half-plane has exactly the kernel
`{1, -1}`. In particular, `-1` is in every actual Mathlib `Gamma0 N` and
acts trivially. We form the actual action kernel of `Gamma0 N`, quotient by
it, and give the quotient its faithful permutation action. Its action
preserves Mathlib's exact hyperbolic `volume`.

This module does not claim a fundamental domain, a quotient measure, or a
spectral decomposition.
-/

namespace ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z

noncomputable section

open Set MeasureTheory Matrix
open scoped UpperHalfPlane Pointwise MatrixGroups

private def interiorWitness : UpperHalfPlane :=
  ⟨⟨0, 2⟩, by norm_num⟩

private theorem interiorWitness_mem_fdo :
    interiorWitness ∈ ModularGroup.fdo := by
  constructor <;> norm_num [interiorWitness, ModularGroup.fdo, Complex.normSq_apply]

/-- Fixing every point of `ℍ` forces an integral special-linear matrix to
be one of the two scalar matrices. -/
theorem sl2_fixed_all_iff (g : SL(2, ℤ)) :
    (∀ z : UpperHalfPlane, g • z = z) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    have hfd : g • interiorWitness ∈ ModularGroup.fd := by
      simpa only [h interiorWitness] using
        ModularGroup.fdo_subset_fd interiorWitness_mem_fdo
    exact ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd
      interiorWitness_mem_fdo hfd
  · rintro (rfl | rfl) z
    · simp
    · simp

/-- The kernel of the full modular action is exactly `±1`. -/
theorem sl2_actionKernel_iff (g : SL(2, ℤ)) :
    g ∈ (MulAction.toPermHom SL(2, ℤ) UpperHalfPlane).ker ↔
      g = 1 ∨ g = -1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (sl2_fixed_all_iff g).mp fun z =>
      by simpa using congrArg (fun p : Equiv.Perm UpperHalfPlane => p z) h
  · intro h
    apply Equiv.ext
    intro z
    exact (sl2_fixed_all_iff g).mpr h z

/-- The negative identity belongs to the *actual* level-`N` subgroup. -/
theorem neg_one_mem_gamma0 (N : ℕ) :
    (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem]

def gamma0NegOne (N : ℕ) : CongruenceSubgroup.Gamma0 N :=
  ⟨-1, neg_one_mem_gamma0 N⟩

theorem gamma0NegOne_smul (N : ℕ) (z : UpperHalfPlane) :
    (gamma0NegOne N : SL(2, ℤ)) • z = z := by
  exact (sl2_fixed_all_iff (-1 : SL(2, ℤ))).mpr (Or.inr rfl) z

/-- The actual action homomorphism; no kernel is supplied as a field. -/
def gamma0PermHom (N : ℕ) :
    CongruenceSubgroup.Gamma0 N →* Equiv.Perm UpperHalfPlane :=
  MulAction.toPermHom (CongruenceSubgroup.Gamma0 N) UpperHalfPlane

def gamma0ActionKernel (N : ℕ) : Subgroup (CongruenceSubgroup.Gamma0 N) :=
  (gamma0PermHom N).ker

/-- Inside Gamma0, the full action kernel still consists precisely of
the positive and negative integral identity matrices. -/
theorem gamma0_actionKernel_iff (N : ℕ)
    (g : CongruenceSubgroup.Gamma0 N) :
    g ∈ gamma0ActionKernel N ↔
      (g : SL(2, ℤ)) = 1 ∨ (g : SL(2, ℤ)) = -1 := by
  constructor
  · intro h
    apply (sl2_fixed_all_iff (g : SL(2, ℤ))).mp
    intro z
    have hp : gamma0PermHom N g = 1 :=
      MonoidHom.mem_ker.mp h
    simpa [gamma0PermHom] using
      congrArg (fun p : Equiv.Perm UpperHalfPlane => p z) hp
  · intro h
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro z
    simpa [gamma0PermHom] using
      (sl2_fixed_all_iff (g : SL(2, ℤ))).mpr h z

theorem gamma0NegOne_mem_kernel (N : ℕ) :
    gamma0NegOne N ∈ gamma0ActionKernel N := by
  exact (gamma0_actionKernel_iff N (gamma0NegOne N)).mpr (Or.inr rfl)

/-- The quotient is formed by the genuine kernel of the real action. -/
abbrev effectiveGamma0 (N : ℕ) :=
  CongruenceSubgroup.Gamma0 N ⧸ gamma0ActionKernel N

/-- The first isomorphism theorem embeds the effective group in the
permutation group of `ℍ`. -/
def effectivePermHom (N : ℕ) :
    effectiveGamma0 N →* Equiv.Perm UpperHalfPlane :=
  QuotientGroup.kerLift (gamma0PermHom N)

private instance (N : ℕ) : MulAction (effectiveGamma0 N) UpperHalfPlane :=
  MulAction.compHom UpperHalfPlane (effectivePermHom N)

theorem effective_smul_mk (N : ℕ)
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    (QuotientGroup.mk g : effectiveGamma0 N) • z = g • z := by
  change effectivePermHom N (QuotientGroup.mk g) z = gamma0PermHom N g z
  rw [effectivePermHom, QuotientGroup.kerLift_mk]
  rfl

/-- This quotient action is faithful, rather than merely faithful modulo
an unrecorded scalar ambiguity. -/
theorem effective_action_faithful (N : ℕ)
    (q₁ q₂ : effectiveGamma0 N)
    (h : ∀ z : UpperHalfPlane, q₁ • z = q₂ • z) : q₁ = q₂ := by
  apply QuotientGroup.kerLift_injective (gamma0PermHom N)
  apply Equiv.ext
  intro z
  exact h z

private instance : SMulInvariantMeasure SL(2, ℤ) UpperHalfPlane
    (volume : Measure UpperHalfPlane) where
  measure_preimage_smul g s hs := by
    change (volume : Measure UpperHalfPlane)
        ((fun z : UpperHalfPlane => (SpecialLinearGroup.mapGL ℝ g) • z) ⁻¹' s) =
      (volume : Measure UpperHalfPlane) s
    exact SMulInvariantMeasure.measure_preimage_smul
      (SpecialLinearGroup.mapGL ℝ g) hs

private instance (N : ℕ) : SMulInvariantMeasure
    (CongruenceSubgroup.Gamma0 N) UpperHalfPlane
    (volume : Measure UpperHalfPlane) :=
  Subgroup.smulInvariantMeasure (CongruenceSubgroup.Gamma0 N)

/-- Hyperbolic measure invariance descends to every effective class. -/
theorem effective_measure_smul (N : ℕ) (q : effectiveGamma0 N)
    (s : Set UpperHalfPlane) :
    (volume : Measure UpperHalfPlane) (q • s) =
      (volume : Measure UpperHalfPlane) s := by
  induction q using Quotient.inductionOn' with
  | _ g =>
    have hset :
        (QuotientGroup.mk g : effectiveGamma0 N) • s = g • s := by
      change (fun z : UpperHalfPlane =>
        (QuotientGroup.mk g : effectiveGamma0 N) • z) '' s =
          (fun z : UpperHalfPlane => g • z) '' s
      congr 1
      funext z
      exact effective_smul_mk N g z
    rw [hset]
    exact measure_smul (volume : Measure UpperHalfPlane) g s

end
end ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
