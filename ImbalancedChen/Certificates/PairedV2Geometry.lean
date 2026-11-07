import ImbalancedChen.Certificates.PairedV2Data

/-!
# Exact geometry of the adopted paired-v2 E0 fibres

This module uses the actual rational constants and 512 by 512 mesh from
`PairedV2Data`.  Its finite conditions concern geometry and the E0 residual
gate, independently of all stored or newly certified integral bounds.

The outer support is open.  In particular, a last mesh cell with
`uUpper j = h` or `tUpper i = d` is allowed: every interior point still
satisfies `u < h` and `t < d`.  Equality `Z = uLower j` is also allowed.
In contrast, `a = Z` and zero outer widths are excluded by the strict
nonemptiness conditions.  The E0 residual gate is specific to E0; this
predicate must not be used to relabel the adopted E1 rows as E0.

The statements describe these actual local fibres.  They do not identify
a finite sum with a union integral or supply an arithmetic parent license.
-/

namespace ImbalancedChen.Certificates.PairedV2

/-- Decidable rational conditions for an actual nonempty E0 cell.
The explicit endpoint conditions make a generated row check transparent;
the cutoff is the adopted `7/3` cutoff, not a supplied integral gain. -/
def E0Geometry (i j : ℕ) (Z : ℚ) : Prop :=
  i < 512 ∧
    j < 512 ∧
    0 < a ∧
    a < Z ∧
    Z = min (uLower j) (3 * (1 - tUpper i - uUpper j) / 13) ∧
    Z ≤ uLower j ∧
    uLower j < uUpper j ∧
    uUpper j ≤ h ∧
    h < tLower i ∧
    tLower i < tUpper i ∧
    tUpper i ≤ d ∧
    (57 / 64 : ℚ) - (5 / 2) * tLower i - uLower j ≤ 2 * a

instance (i j : ℕ) (Z : ℚ) : Decidable (E0Geometry i j Z) := by
  unfold E0Geometry
  infer_instance

/-- Executable exact geometry check. -/
def e0GeometryCheck (i j : ℕ) (Z : ℚ) : Bool :=
  decide (E0Geometry i j Z)

theorem e0GeometryCheck_sound {i j : ℕ} {Z : ℚ}
    (hcheck : e0GeometryCheck i j Z = true) : E0Geometry i j Z := by
  exact of_decide_eq_true hcheck

/-- The true interior of the decoded cell, in coordinate order `(t,u,z,w)`.
No function values or certificate endpoints occur in this definition. -/
def openFibreSupport (i j : ℕ) (Z : ℚ) (t u z w : ℝ) : Prop :=
  (tLower i : ℝ) < t ∧
    t < (tUpper i : ℝ) ∧
    (uLower j : ℝ) < u ∧
    u < (uUpper j : ℝ) ∧
    (a : ℝ) < w ∧
    w < z ∧
    z < (Z : ℝ)

/-- The exact cutoff supplies the affine inequality needed on every fibre. -/
theorem E0Geometry.cutoff_bound {i j : ℕ} {Z : ℚ}
    (hg : E0Geometry i j Z) :
    (13 / 3 : ℚ) * Z ≤ 1 - tUpper i - uUpper j := by
  rcases hg with ⟨_, _, _, _, hZ, _, _, _, _, _, _, _⟩
  have hcut : Z ≤ 3 * (1 - tUpper i - uUpper j) / 13 := by
    rw [hZ]
    exact min_le_right _ _
  linarith

/-- The E0 affine residual inequality holds on the whole outer cell,
including its boundary, rather than just at a sampled point. -/
theorem E0Geometry.residual_bound {i j : ℕ} {Z : ℚ}
    (hg : E0Geometry i j Z) {t u : ℝ}
    (ht : (tLower i : ℝ) ≤ t) (hu : (uLower j : ℝ) ≤ u) :
    (57 / 64 : ℝ) - (5 / 2) * t - u ≤ 2 * (a : ℝ) := by
  rcases hg with ⟨_, _, _, _, _, _, _, _, _, _, _, hE0⟩
  have hE0R : (57 / 64 : ℝ) - (5 / 2) * (tLower i : ℝ) -
      (uLower j : ℝ) ≤ 2 * (a : ℝ) := by
    have hc : (((57 / 64 : ℚ) - (5 / 2) * tLower i - uLower j : ℚ) : ℝ) ≤
        ((2 * a : ℚ) : ℝ) := Rat.cast_le.mpr hE0
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using hc
  linarith

/-- Every point of the actual open fibre has the required ordering and
the adopted Buchstab argument at least `7/3`. -/
theorem E0Geometry.fibre_argument {i j : ℕ} {Z : ℚ}
    (hg : E0Geometry i j Z) {t u z w : ℝ}
    (hs : openFibreSupport i j Z t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z := by
  have hcut := hg.cutoff_bound
  rcases hg with ⟨_, _, ha, _, _, hzul, _, hurh, hhtl, _, htrd, _⟩
  rcases hs with ⟨htl, htr, hul, hur, hw, hwz, hz⟩
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hzulR : (Z : ℝ) ≤ (uLower j : ℝ) := by exact_mod_cast hzul
  have hurhR : (uUpper j : ℝ) ≤ (h : ℝ) := by exact_mod_cast hurh
  have hhtlR : (h : ℝ) < (tLower i : ℝ) := by exact_mod_cast hhtl
  have htrdR : (tUpper i : ℝ) ≤ (d : ℝ) := by exact_mod_cast htrd
  have hcutR : (13 / 3 : ℝ) * (Z : ℝ) ≤
      1 - (tUpper i : ℝ) - (uUpper j : ℝ) := by
    have hc : ((((13 / 3 : ℚ) * Z) : ℚ) : ℝ) ≤
        ((1 - tUpper i - uUpper j : ℚ) : ℝ) := Rat.cast_le.mpr hcut
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hc
  have hzpos : 0 < z := haR.trans (hw.trans hwz)
  refine ⟨hw, hwz, (hz.trans_le hzulR).trans hul, hur.trans_le hurhR,
    hhtlR.trans htl, htr.trans_le htrdR, ?_⟩
  apply (le_div_iff₀ hzpos).2
  linarith

theorem e0GeometryCheck_fibre_argument {i j : ℕ} {Z : ℚ}
    (hcheck : e0GeometryCheck i j Z = true) {t u z w : ℝ}
    (hs : openFibreSupport i j Z t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z :=
  (e0GeometryCheck_sound hcheck).fibre_argument hs

/-- The strict endpoint checks supply an explicit point in the fibre.
No assumption that the claimed integral gain is positive is used. -/
theorem E0Geometry.fibre_nonempty {i j : ℕ} {Z : ℚ}
    (hg : E0Geometry i j Z) :
    ∃ t u z w : ℝ, openFibreSupport i j Z t u z w := by
  rcases hg with ⟨_, _, _, haZ, _, _, hulu, _, _, htlt, _, _⟩
  have haZR : (a : ℝ) < (Z : ℝ) := by exact_mod_cast haZ
  have huluR : (uLower j : ℝ) < (uUpper j : ℝ) := by exact_mod_cast hulu
  have htltR : (tLower i : ℝ) < (tUpper i : ℝ) := by exact_mod_cast htlt
  refine ⟨((tLower i : ℝ) + (tUpper i : ℝ)) / 2,
    ((uLower j : ℝ) + (uUpper j : ℝ)) / 2,
    ((a : ℝ) + (Z : ℝ)) / 2,
    (3 * (a : ℝ) + (Z : ℝ)) / 4, ?_⟩
  dsimp only [openFibreSupport]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end ImbalancedChen.Certificates.PairedV2
