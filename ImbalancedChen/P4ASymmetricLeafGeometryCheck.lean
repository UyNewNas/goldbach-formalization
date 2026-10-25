import ImbalancedChen.P4ASymmetricRange32RawOptionDispatch

/-!
SOURCEONLY / UNCOMPILED. Pure integer geometry for the original below-mu
full symmetric leaves. No integral, bound or real-valued cost is stored.
The original D, T, cutoff, rho and mu inequalities are checked literally.
No ratio<=2 condition is introduced.
-/

namespace ImbalancedChen.P4ASymmetricLeafGeometryCheckSourceOnly

open OriginalThirdSymmetricJensenSourceOnly

def gridD : ℤ := 48000 * 2 ^ 24
def gridT : ℤ := 481573208064
def grid (x : ℤ) : ℚ := (x : ℚ) / (gridD : ℚ)

structure SavedSymmetricLeaf where
  x0 : ℤ
  x1 : ℤ
  z0 : ℤ
  z1 : ℤ
  storedCharge : ℤ
  deriving DecidableEq

/-- Every clause is an integer source-coordinate test. -/
def FullBelowMuGeometry (leaf : SavedSymmetricLeaf) : Prop :=
  leaf.x0 < leaf.x1 ∧ leaf.z0 < leaf.z1 ∧
    gridD ≤ 100 * leaf.z0 ∧ leaf.z1 ≤ leaf.x0 ∧
    96 * leaf.x1 ≤ 19 * gridD ∧
    2 * leaf.x1 + 3 * leaf.z1 ≤ gridT ∧
    128 * leaf.x1 ≤ 25 * gridD

instance (leaf : SavedSymmetricLeaf) : Decidable (FullBelowMuGeometry leaf) := by
  unfold FullBelowMuGeometry
  infer_instance

def fullBelowMuGeometryCheck (leaf : SavedSymmetricLeaf) : Bool :=
  decide (FullBelowMuGeometry leaf)

theorem fullBelowMuGeometryCheck_sound {leaf : SavedSymmetricLeaf}
    (h : fullBelowMuGeometryCheck leaf = true) : FullBelowMuGeometry leaf := by
  exact of_decide_eq_true h

theorem grid_cast (x : ℤ) : (grid x : ℝ) = (x : ℝ) / (gridD : ℝ) := by
  simp only [grid, Rat.cast_div, Rat.cast_intCast]

theorem below_mu_of_geometry {leaf : SavedSymmetricLeaf} (h : FullBelowMuGeometry leaf) :
    (grid leaf.x1 : ℝ) ≤ VariableEnvelope.mu := by
  have hmu : (128 : ℝ) * (leaf.x1 : ℝ) ≤ 25 * (gridD : ℝ) := by
    exact_mod_cast h.2.2.2.2.2.2
  have hD : (0 : ℝ) < (gridD : ℝ) := by norm_num [gridD]
  rw [grid_cast]
  unfold VariableEnvelope.mu
  apply (div_le_iff₀ hD).2
  linarith only [hmu]

/-- Actual real full-leaf geometry follows from the integer check. The
initial grid bindings are definitional and the upper-mu gate is proved. -/
theorem full_geometry_of_integer_geometry {leaf : SavedSymmetricLeaf}
    (h : FullBelowMuGeometry leaf) :
    SymmetricFullBox (grid leaf.x0 : ℝ) (grid leaf.x1 : ℝ)
      (grid leaf.z0 : ℝ) (grid leaf.z1 : ℝ) := by
  obtain ⟨hxy, hzz, hcut, hzy, hrho, hfull, _hmu⟩ := h
  have hD : (0 : ℝ) < (gridD : ℝ) := by norm_num [gridD]
  have hxyR : (leaf.x0 : ℝ) < (leaf.x1 : ℝ) := by exact_mod_cast hxy
  have hzzR : (leaf.z0 : ℝ) < (leaf.z1 : ℝ) := by exact_mod_cast hzz
  have hcutR : (gridD : ℝ) ≤ 100 * (leaf.z0 : ℝ) := by exact_mod_cast hcut
  have hzyR : (leaf.z1 : ℝ) ≤ (leaf.x0 : ℝ) := by exact_mod_cast hzy
  have hrhoR : (96 : ℝ) * (leaf.x1 : ℝ) ≤ 19 * (gridD : ℝ) := by exact_mod_cast hrho
  have hfullR : 2 * (leaf.x1 : ℝ) + 3 * (leaf.z1 : ℝ) ≤ (gridT : ℝ) := by
    exact_mod_cast hfull
  have hT : (gridT : ℝ) = thirdPrefixTheta * (gridD : ℝ) := by
    norm_num [gridT, gridD, thirdPrefixTheta]
  have hmu := below_mu_of_geometry h
  simp only [grid_cast] at hmu ⊢
  refine ⟨div_lt_div_of_pos_right hxyR hD, div_lt_div_of_pos_right hzzR hD,
    ?_, div_le_div_of_nonneg_right hzyR hD.le, ?_, ?_, Or.inl hmu⟩
  · apply (le_div_iff₀ hD).2
    linarith only [hcutR]
  · unfold thirdPrefixRho
    apply (div_le_iff₀ hD).2
    linarith only [hrhoR]
  · have hs : (2 * (leaf.x1 : ℝ) + 3 * (leaf.z1 : ℝ)) / (gridD : ℝ) ≤
        thirdPrefixTheta := by
      apply (div_le_iff₀ hD).2
      rw [← hT]
      exact hfullR
    simpa only [add_div, mul_div_assoc] using hs

theorem fullBelowMuGeometryCheck_real_sound {leaf : SavedSymmetricLeaf}
    (h : fullBelowMuGeometryCheck leaf = true) :
    SymmetricFullBox (grid leaf.x0 : ℝ) (grid leaf.x1 : ℝ)
      (grid leaf.z0 : ℝ) (grid leaf.z1 : ℝ) ∧
      (grid leaf.x1 : ℝ) ≤ VariableEnvelope.mu := by
  have hg := fullBelowMuGeometryCheck_sound h
  exact ⟨full_geometry_of_integer_geometry hg, below_mu_of_geometry hg⟩

end ImbalancedChen.P4ASymmetricLeafGeometryCheckSourceOnly
