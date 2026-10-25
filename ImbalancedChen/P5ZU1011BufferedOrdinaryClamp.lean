import ImbalancedChen.P5ZU1011H248ClampPrimeBox

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Literal upper-table H248 physical-buffer comparison on the ENTIRE clamp
R<=2*w. At knot50 the adjacent minimum is <=the right-open value; no
absolute H convergence or null-clamp assertion is made. All errors below
come from the positive residual denominator, not a table licence.
-/

namespace ImbalancedChen.P5Z.BufferedOrdinaryClamp

noncomputable section

open Set Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open U11H248 U1011H248Clamp

def physicalQuery (R w τ ξ ρ : ℝ) : ℝ := max (2 + ρ) ((R - τ) / (w - ξ))
def physicalCost (R w τ ξ ρ : ℝ) : ℝ :=
  4 * (1 - H248 (physicalQuery R w τ ξ ρ)) / (R - τ)
def originalCost (R w : ℝ) : ℝ := 4 * (1 - H248 (max 2 (R / w))) / R

/-- Explicit buffer guards keep the whole clamped half-space in knot50
or its first right-open atom. R need not be close to the clamp boundary. -/
theorem physical_query_mem (R w τ ξ ρ : ℝ) (hw : 0 < w)
    (hClamp : R ≤ 2 * w) (hτ : 0 ≤ τ)
    (hξ : 0 ≤ ξ) (hξsmall : ξ ≤ w / 202)
    (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 100) :
    0 < w - ξ ∧ physicalQuery R w τ ξ ρ ∈ Ico (2 : ℝ) (101 / 50) := by
  have hd : 0 < w - ξ := by linarith only [hw, hξsmall]
  have hRatio : (R - τ) / (w - ξ) < 101 / 50 := by
    apply (div_lt_iff₀ hd).mpr
    linarith only [hClamp, hτ, hξsmall, hw]
  have hRho : 2 + ρ < (101 / 50 : ℝ) := by linarith only [hρsmall]
  exact ⟨hd, (show 2 ≤ physicalQuery R w τ ξ ρ from
    (by linarith only [hρ] : (2 : ℝ) ≤ 2 + ρ).trans (le_max_left _ _)),
      max_lt hRho hRatio⟩

/-- The actual closed-cell adjacent minimum at 2 is at most every actual
H248 value immediately to its right, including equality at the knot. -/
theorem H248_two_le_right {q : ℝ} (hq : q ∈ Ico (2 : ℝ) (101 / 50)) :
    H248 2 ≤ H248 q := by
  by_cases hq2 : q = 2
  · subst q
    exact le_rfl
  · have hq2lt : 2 < q := lt_of_le_of_ne hq.1 (Ne.symm hq2)
    have hb : q ∈ upperAtomSet (.inl (⟨50, by norm_num⟩ : Fin 200)) := by
      change q ∈ Icc (1 : ℝ) 5 ∩ Ioo (floorGrid 50) (floorGrid 51)
      have hg0 : floorGrid 50 = 2 := floorGrid_fifty
      have hg1 : floorGrid 51 = (101 / 50 : ℝ) := by norm_num [floorGrid]
      rw [hg0, hg1]
      exact ⟨⟨by linarith only [hq.1], by linarith only [hq.2]⟩, hq2lt, hq.2⟩
    have h2 := H248_max_two_of_le (s := (2 : ℝ)) le_rfl
    simp only [max_self] at h2
    rw [h2, H248_eq_atom hb]
    exact min_le_right _ _

/-- The sole error is the true reciprocal residual-denominator increment.
The positive rational/real floor c is explicit and directly checkable. -/
theorem reciprocal_cost_upper {R τ c h : ℝ} (hc : 0 < c)
    (hRc : c ≤ R - τ) (hτ : 0 ≤ τ) (hh : 0 ≤ h ∧ h ≤ 1) :
    4 * (1 - h) / (R - τ) ≤ 4 * (1 - h) / R + (4 / c ^ 2) * τ := by
  have hd : 0 < R - τ := hc.trans_le hRc
  have hR : 0 < R := by linarith only [hd, hτ]
  have hcR : c ≤ R := by linarith only [hRc, hτ]
  have hNum0 : 0 ≤ 4 * (1 - h) := by linarith only [hh.2]
  have hNum4 : 4 * (1 - h) ≤ 4 := by linarith only [hh.1]
  have hProd : c ^ 2 ≤ R * (R - τ) := by
    simpa only [pow_two] using mul_le_mul hcR hRc hc.le hR.le
  have hEq : 4 * (1 - h) / (R - τ) =
      4 * (1 - h) / R + (4 * (1 - h)) * τ / (R * (R - τ)) := by
    field_simp [hd.ne', hR.ne']
    <;> ring
  have hErr := (div_le_div_of_nonneg_left (mul_nonneg hNum0 hτ) (pow_pos hc 2) hProd).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hNum4 hτ) (pow_nonneg hc.le 2))
  rw [hEq]
  have hErr' : (4 * (1 - h)) * τ / (R * (R - τ)) ≤ (4 / c ^ 2) * τ := by
    convert hErr using 1 <;> ring
  exact add_le_add_left hErr' _

/-- Entire-clamp safe upper approximation for the PHYSICAL buffered cost.
The literal H lookup moves in the safe direction even when its right
open value differs from the adjacent-min value at two. -/
theorem physical_cost_upper_on_clamp (R w τ ξ ρ c : ℝ) (hw : 0 < w)
    (hClamp : R ≤ 2 * w) (hτ : 0 ≤ τ)
    (hξ : 0 ≤ ξ) (hξsmall : ξ ≤ w / 202)
    (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 100)
    (hc : 0 < c) (hRc : c ≤ R - τ) :
    physicalCost R w τ ξ ρ ≤ originalCost R w + (4 / c ^ 2) * τ := by
  have hQuery := (physical_query_mem R w τ ξ ρ hw hClamp hτ hξ hξsmall hρ hρsmall).2
  have hH := H248_two_le_right hQuery
  have hd : 0 < R - τ := hc.trans_le hRc
  have hClampEq : H248 (max 2 (R / w)) = H248 2 := by
    rw [max_eq_left ((div_le_iff₀ hw).mpr hClamp)]
  have hNum : 4 * (1 - H248 (physicalQuery R w τ ξ ρ)) ≤ 4 * (1 - H248 2) := by
    linarith only [hH]
  have hCost := (div_le_div_of_nonneg_right hNum hd.le).trans
    (reciprocal_cost_upper hc hRc hτ (H248_bounds 2))
  simpa only [physicalCost, originalCost, hClampEq] using hCost

end

end ImbalancedChen.P5Z.BufferedOrdinaryClamp
