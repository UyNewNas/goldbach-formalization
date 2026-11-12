import ImbalancedChen.Part3OriginalHolomorphicCuspFrames
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace ImbalancedChen.Part3.OriginalHolomorphicFiniteDimension20261112

noncomputable section
open UpperHalfPlane Module
open scoped MatrixGroups ModularForm UpperHalfPlane
open OriginalHolomorphicCuspFrames20261110

private def vanishing (K : ℤ) (s : Finset ℍ) :
    Submodule ℂ (ModularForm 𝒮ℒ K) where
  carrier := {F | ∀ x ∈ s, F x = 0}
  zero_mem' := by simp
  add_mem' hf hg x hx := by simp [hf x hx, hg x hx]
  smul_mem' c F hF x hx := by simp [hF x hx]

/-- A finite set of actual points detects every level-one form of a fixed weight. -/
theorem detecting_points (K : ℤ) :
    ∃ s : Finset ℍ, ∀ F : ModularForm 𝒮ℒ K, (∀ x ∈ s, F x = 0) → F = 0 := by
  classical
  have ex : ∃ d : ℕ, ∃ s : Finset ℍ, finrank ℂ (vanishing K s) = d :=
    ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec ex
  refine ⟨s, fun F hF => ?_⟩
  by_contra hne
  obtain ⟨u, hu⟩ : ∃ u : ℍ, F u ≠ 0 := by
    by_contra! hz
    exact hne (by ext u; simpa using hz u)
  have hlt : vanishing K (insert u s) < vanishing K s := by
    apply lt_of_le_of_ne
    · intro G hG x hx
      exact hG x (Finset.mem_insert_of_mem hx)
    · intro he
      have hm : F ∈ vanishing K (insert u s) := by rw [he]; exact hF
      exact hu (hm u (Finset.mem_insert_self _ _))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hs] at hd
  exact (Nat.not_lt_of_ge (Nat.find_min' ex ⟨insert u s, rfl⟩)) hd

/-- The identity coset contributes the original value in the literal finite norm product. -/
theorem norm_vanishes_at (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (levelGroup N) k) (u : ℍ) (h : f u = 0) :
    ModularForm.norm 𝒮ℒ f u = 0 := by
  classical
  simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk] using
    (show ∃ g : 𝒮ℒ, (SlashInvariantForm.quotientFunc f ⟦g⟧) u = 0 from
      ⟨1, by simpa using h⟩)

/-- Finite dimension of the full original level space, including weight two. -/
theorem finite_forms (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (levelGroup N) k) := by
  classical
  let Q := 𝒮ℒ ⧸ (levelGroup N).subgroupOf 𝒮ℒ
  obtain ⟨s, hs⟩ := detecting_points (k * Nat.card Q)
  let ev : CuspForm (levelGroup N) k →ₗ[ℂ] (↑s → ℂ) :=
    { toFun := fun f x => f x.val
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  apply FiniteDimensional.of_injective ev
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hf' : ev f = 0 := hf
  have hn : ModularForm.norm 𝒮ℒ f = 0 := by
    apply hs
    intro x hx
    exact norm_vanishes_at N k f x (congrFun hf' ⟨x,hx⟩)
  have hz := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp hn
  ext x
  exact congrFun hz x

end
end ImbalancedChen.Part3.OriginalHolomorphicFiniteDimension20261112
