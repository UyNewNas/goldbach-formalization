import ImbalancedChen.Part3Gamma0ActualCusps
import Mathlib.NumberTheory.Modular
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The parabolic primitive is different from full Gamma0/actionKernel
unfolding. Two actual integral determinant-one matrices have equal bottom
rows exactly when one is obtained from the other by LEFT multiplication
by T^k. Equality up to sign is exactly LEFT multiplication by +/-T^k.
The genuine c=0 subgroup inside Gamma0(N) is defined and classified by
these matrices. Its left-multiplication equivalence is therefore the
same as bottom-row equivalence up to sign, and a periodic cusp seed is
independent of such an actual representative.

No abstract quotient bijection, periodic-seed L1(H) assertion, Eisenstein
coset sum, or spectral theorem is inserted as a hypothesis or conclusion.
-/

namespace ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a

noncomputable section

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly

/-- The literal oriented bottom row of an actual integral SL2 matrix. -/
def bottomRow (g : SL(2, ℤ)) : Fin 2 → ℤ := fun j => g 1 j

/-- The determinant supplies an explicit primitive-row Bezout certificate. -/
theorem bottomRow_bezout (g : SL(2, ℤ)) :
    ∃ u v : ℤ, u * bottomRow g 0 + v * bottomRow g 1 = 1 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  refine ⟨-(g 0 1), g 0 0, ?_⟩
  change -(g 0 1) * g 1 0 + g 0 0 * g 1 1 = 1
  linear_combination hdet

theorem bottomRow_left_translation (k : ℤ) (g : SL(2, ℤ)) :
    bottomRow (ModularGroup.T ^ k * g) = bottomRow g := by
  funext j
  fin_cases j <;>
    simp [bottomRow, ModularGroup.coe_T_zpow, coe_mul, Matrix.mul_fin_two]

theorem bottomRow_neg (g : SL(2, ℤ)) : bottomRow (-g) = -bottomRow g := by
  funext j
  simp [bottomRow]

/-- Exact oriented-row classification. The translation parameter is the
upper-right entry of the actual relative matrix h*g^-1. -/
theorem bottomRow_eq_iff_left_translation (g h : SL(2, ℤ)) :
    bottomRow h = bottomRow g ↔
      ∃ k : ℤ, h = ModularGroup.T ^ k * g := by
  constructor
  · intro hrow
    have hc : h 1 0 = g 1 0 := congrFun hrow 0
    have hd : h 1 1 = g 1 1 := congrFun hrow 1
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.det_coe
    let a : SL(2, ℤ) := h * g⁻¹
    have ha10 : a 1 0 = 0 := by
      dsimp [a]
      simp [coe_mul, SL2_inv_expl, Matrix.mul_fin_two, hc, hd] <;> ring
    have ha11 : a 1 1 = 1 := by
      dsimp [a]
      simp [coe_mul, SL2_inv_expl, Matrix.mul_fin_two, hc, hd] <;>
        linear_combination hdet
    have ha00 : a 0 0 = 1 := by
      have hda := a.det_coe
      simpa only [Matrix.det_fin_two, ha10, ha11, mul_one,
        mul_zero, sub_zero] using hda
    have ha : a = ModularGroup.T ^ (a 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ModularGroup.coe_T_zpow, ha00, ha10, ha11]
    refine ⟨a 0 1, ?_⟩
    calc
      h = (h * g⁻¹) * g := by group
      _ = a * g := rfl
      _ = ModularGroup.T ^ (a 0 1) * g := congrArg (fun m : SL(2, ℤ) => m * g) ha
  · rintro ⟨k, rfl⟩
    exact bottomRow_left_translation k g

/-- The actual unoriented primitive-row relation is exactly the parabolic
left relation INCLUDING the central sign. -/
theorem signed_bottomRow_iff_left_signed_translation (g h : SL(2, ℤ)) :
    (bottomRow h = bottomRow g ∨ bottomRow h = -bottomRow g) ↔
      ∃ k : ℤ, h = ModularGroup.T ^ k * g ∨
        h = -(ModularGroup.T ^ k * g) := by
  constructor
  · rintro (hrow | hrow)
    · obtain ⟨k, hk⟩ := (bottomRow_eq_iff_left_translation g h).mp hrow
      exact ⟨k, Or.inl hk⟩
    · have hneg : bottomRow (-h) = bottomRow g := by
        rw [bottomRow_neg, hrow, neg_neg]
      obtain ⟨k, hk⟩ := (bottomRow_eq_iff_left_translation g (-h)).mp hneg
      refine ⟨k, Or.inr ?_⟩
      simpa only [neg_neg] using congrArg (fun a : SL(2, ℤ) => -a) hk
  · rintro ⟨k, hk | hk⟩
    · exact Or.inl ((bottomRow_eq_iff_left_translation g h).mpr ⟨k, hk⟩)
    · right
      rw [hk, bottomRow_neg, bottomRow_left_translation]

/-- The complete integral stabilizer of infinity is +/-T^k. This derives
it from determinant one and the actual bottom-row classification. -/
theorem lowerLeft_zero_iff_signed_translation (g : SL(2, ℤ)) :
    g 1 0 = 0 ↔ ∃ k : ℤ, g = ModularGroup.T ^ k ∨ g = -(ModularGroup.T ^ k) := by
  constructor
  · intro hc
    have had : g 0 0 * g 1 1 = 1 := by
      have h := g.det_coe
      simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using h
    have hrow : bottomRow g = bottomRow (1 : SL(2, ℤ)) ∨
        bottomRow g = -bottomRow (1 : SL(2, ℤ)) := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with
        (⟨_ha, hd⟩ | ⟨_ha, hd⟩)
      · left
        funext j
        fin_cases j <;> simp [bottomRow, hc, hd]
      · right
        funext j
        fin_cases j <;> simp [bottomRow, hc, hd]
    simpa only [mul_one] using
      (signed_bottomRow_iff_left_signed_translation 1 g).mp hrow
  · rintro ⟨k, rfl | rfl⟩ <;> simp [ModularGroup.coe_T_zpow]

/-- Actual parabolic subgroup INSIDE Mathlib's Gamma0(N), not an assumed
external stabilizer or a quotient of the full spatial action kernel. -/
def gammaInfinity (N : ℕ) : Subgroup (CongruenceSubgroup.Gamma0 N) where
  carrier := {g | (g : SL(2, ℤ)) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ((g : SL(2, ℤ)) * (h : SL(2, ℤ))) 1 0 = 0
    simp [coe_mul, Matrix.mul_fin_two, hg, hh]
  inv_mem' := by
    intro g hg
    change ((g : SL(2, ℤ))⁻¹) 1 0 = 0
    simp [SL2_inv_expl, hg]

theorem gammaInfinity_mem_iff (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    g ∈ gammaInfinity N ↔
      ∃ k : ℤ, (g : SL(2, ℤ)) = ModularGroup.T ^ k ∨
        (g : SL(2, ℤ)) = -(ModularGroup.T ^ k) :=
  lowerLeft_zero_iff_signed_translation (g : SL(2, ℤ))

/-- Level divisibility is preserved by the actual signed bottom-row
relation; hence these are genuine parabolic identifications at level N. -/
theorem gamma0_membership_signed_bottomRow (N : ℕ) (g h : SL(2, ℤ))
    (hrow : bottomRow h = bottomRow g ∨ bottomRow h = -bottomRow g) :
    h ∈ CongruenceSubgroup.Gamma0 N ↔ g ∈ CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_iff_level_dvd_c, gamma0_mem_iff_level_dvd_c]
  rcases hrow with hrow | hrow
  · have hc : h 1 0 = g 1 0 := congrFun hrow 0
    rw [hc]
  · have hc : h 1 0 = -(g 1 0) := congrFun hrow 0
    rw [hc]
    simp

/-- Exact actual GammaInfinity left relation, written without any supplied
coset dictionary: h*g^-1 belongs to that subgroup iff the bottom rows
agree up to the central sign. -/
theorem gammaInfinity_left_relation_iff (N : ℕ)
    (g h : CongruenceSubgroup.Gamma0 N) :
    h * g⁻¹ ∈ gammaInfinity N ↔
      bottomRow (h : SL(2, ℤ)) = bottomRow (g : SL(2, ℤ)) ∨
      bottomRow (h : SL(2, ℤ)) = -bottomRow (g : SL(2, ℤ)) := by
  constructor
  · intro hrel
    obtain ⟨k, hk | hk⟩ := (gammaInfinity_mem_iff N (h * g⁻¹)).mp hrel
    · apply (signed_bottomRow_iff_left_signed_translation
        (g : SL(2, ℤ)) (h : SL(2, ℤ))).mpr
      refine ⟨k, Or.inl ?_⟩
      calc
        (h : SL(2, ℤ)) = ((h : SL(2, ℤ)) * (g : SL(2, ℤ))⁻¹) * g := by group
        _ = ModularGroup.T ^ k * g := by rw [hk]
    · apply (signed_bottomRow_iff_left_signed_translation
        (g : SL(2, ℤ)) (h : SL(2, ℤ))).mpr
      refine ⟨k, Or.inr ?_⟩
      calc
        (h : SL(2, ℤ)) = ((h : SL(2, ℤ)) * (g : SL(2, ℤ))⁻¹) * g := by group
        _ = -(ModularGroup.T ^ k * (g : SL(2, ℤ))) := by rw [hk]; simp
  · intro hrow
    obtain ⟨k, hk | hk⟩ := (signed_bottomRow_iff_left_signed_translation
      (g : SL(2, ℤ)) (h : SL(2, ℤ))).mp hrow
    · apply (gammaInfinity_mem_iff N (h * g⁻¹)).mpr
      refine ⟨k, Or.inl ?_⟩
      change (h : SL(2, ℤ)) * (g : SL(2, ℤ))⁻¹ = ModularGroup.T ^ k
      rw [hk]
      group
    · apply (gammaInfinity_mem_iff N (h * g⁻¹)).mpr
      refine ⟨k, Or.inr ?_⟩
      change (h : SL(2, ℤ)) * (g : SL(2, ℤ))⁻¹ = -(ModularGroup.T ^ k)
      rw [hk]
      simp [mul_assoc]
/-- Periodic cusp seeds are independent of ACTUAL parabolic Gamma0
representatives. Periodicity is the primitive seed property; no full
Gamma0 invariance or integrability on all H is assumed. -/
theorem periodic_seed_representative_independence {A : Type*} (N : ℕ)
    (F : UpperHalfPlane → A)
    (hperiod : ∀ k : ℤ, ∀ z : UpperHalfPlane, F ((k : ℝ) +ᵥ z) = F z)
    (g h : CongruenceSubgroup.Gamma0 N)
    (hrel : h * g⁻¹ ∈ gammaInfinity N) (z : UpperHalfPlane) :
    F (h • z) = F (g • z) := by
  have hrows := (gammaInfinity_left_relation_iff N g h).mp hrel
  obtain ⟨k, hk | hk⟩ := (signed_bottomRow_iff_left_signed_translation
    (g : SL(2, ℤ)) (h : SL(2, ℤ))).mp hrows
  · change F ((h : SL(2, ℤ)) • z) = F ((g : SL(2, ℤ)) • z)
    rw [hk, mul_smul, ModularGroup.modular_T_zpow_smul]
    exact hperiod k _
  · change F ((h : SL(2, ℤ)) • z) = F ((g : SL(2, ℤ)) • z)
    rw [hk, UpperHalfPlane.SL_neg_smul, mul_smul,
      ModularGroup.modular_T_zpow_smul]
    exact hperiod k _

end
end ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a