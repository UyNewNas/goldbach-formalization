import ImbalancedChen.P5ZU1011BufferedUniformLookup

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
ONE explicit physical-buffer scale before ALL compact (R,w) and buffers.
The good region retains the ENTIRE clamp R<=2w. Only its above-two part
uses separation from the 151 proper high walls, INCLUDING knot50.
-/

namespace ImbalancedChen.P5Z.BufferedUniformStrip

noncomputable section

open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open U11H248 BufferedOrdinaryClamp BufferedOrdinaryOffKnots BufferedUniformLookup

def queryConstant (a : ℝ) : ℝ := 1 + 2 / a ^ 2 + 2 / a

def eta (c a δ ε : ℝ) : ℝ :=
  min (a / 202) (min (1 / 100) (min (c / 2)
    (min (ε * c ^ 2 / 32) (δ / (2 * queryConstant a)))))

def Good (R w δ : ℝ) : Prop := R ≤ 2 * w ∨
  (2 * w < R ∧ ∀ j : Fin 151, δ ≤ |R - floorGrid (50 + j.val) * w|)

theorem eta_pos {c a δ ε : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hd : 0 < δ) (he : 0 < ε) : 0 < eta c a δ ε := by
  have hA : 0 < queryConstant a := by dsimp only [queryConstant]; positivity
  unfold eta
  positivity

theorem eta_bounds (c a δ ε : ℝ) :
    eta c a δ ε ≤ a / 202 ∧ eta c a δ ε ≤ 1 / 100 ∧
      eta c a δ ε ≤ c / 2 ∧ eta c a δ ε ≤ ε * c ^ 2 / 32 ∧
      eta c a δ ε ≤ δ / (2 * queryConstant a) := by
  have h1 : eta c a δ ε ≤ min (1 / 100) (min (c / 2)
      (min (ε * c ^ 2 / 32) (δ / (2 * queryConstant a)))) := min_le_right _ _
  have h2 := h1.trans (min_le_right _ _)
  have h3 := h2.trans (min_le_right _ _)
  exact ⟨min_le_left _ _, h1.trans (min_le_left _ _), h2.trans (min_le_left _ _),
    h3.trans (min_le_left _ _), h3.trans (min_le_right _ _)⟩

/-- Explicit uniform perturbation payment on the actual compact box. -/
theorem query_error_lt {R w c a δ ε τ ξ ρ : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hd : 0 < δ)
    (hR : c ≤ R) (hR1 : R ≤ 1) (haw : a ≤ w)
    (hτ : 0 ≤ τ) (hτsmall : τ < eta c a δ ε)
    (hξ : 0 ≤ ξ) (hξsmall : ξ < eta c a δ ε)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < eta c a δ ε) :
    |physicalQuery R w τ ξ ρ - max 2 (R / w)| < δ := by
  have hw : 0 < w := ha.trans_le haw
  have hR0 : 0 ≤ R := (hc.trans_le hR).le
  have hb := eta_bounds c a δ ε
  have hξ202 : ξ ≤ w / 202 := hξsmall.le.trans
    (hb.1.trans (div_le_div_of_nonneg_right haw (by norm_num : (0 : ℝ) ≤ 202)))
  have hξ2 : ξ ≤ w / 2 := by linarith only [hξ202, hw]
  have hError := physical_query_error R w τ ξ ρ hw hR0 hτ hξ hξ2 hρ
  have hSq : a ^ 2 ≤ w ^ 2 := by
    simpa only [pow_two] using mul_le_mul haw haw ha.le hw.le
  have hAlpha : 2 * R / w ^ 2 ≤ 2 / a ^ 2 :=
    (div_le_div_of_nonneg_right (by linarith only [hR1] : 2 * R ≤ 2) (sq_nonneg w)).trans
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (pow_pos ha 2) hSq)
  have hBeta : 2 / w ≤ 2 / a :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) ha haw
  have hα0 : (0 : ℝ) ≤ 2 / a ^ 2 := by positivity
  have hβ0 : (0 : ℝ) ≤ 2 / a := by positivity
  have hXi1 := mul_le_mul_of_nonneg_right hAlpha hξ
  have hTau1 := mul_le_mul_of_nonneg_right hBeta hτ
  have hXi2 := mul_le_mul_of_nonneg_left hξsmall.le hα0
  have hTau2 := mul_le_mul_of_nonneg_left hτsmall.le hβ0
  have hRate : ρ + (2 * R / w ^ 2) * ξ + (2 / w) * τ <
      queryConstant a * eta c a δ ε := by
    calc
      ρ + (2 * R / w ^ 2) * ξ + (2 / w) * τ ≤ ρ + (2 / a ^ 2) * ξ + (2 / a) * τ :=
        add_le_add (add_le_add_left hXi1 _) hTau1
      _ < eta c a δ ε + (2 / a ^ 2) * eta c a δ ε + (2 / a) * eta c a δ ε :=
        add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le hρsmall hXi2) hTau2
      _ = queryConstant a * eta c a δ ε := by dsimp only [queryConstant]; ring
  have hA : 0 < queryConstant a := by dsimp only [queryConstant]; positivity
  have hAdelta := mul_le_mul_of_nonneg_left hb.2.2.2.2 hA.le
  have hEq : queryConstant a * (δ / (2 * queryConstant a)) = δ / 2 := by
    field_simp [hA.ne']
    <;> ring
  rw [hEq] at hAdelta
  have hh : |physicalQuery R w τ ξ ρ - max 2 (R / w)| < δ / 2 :=
    (hError.trans_lt hRate).trans_le hAdelta
  exact hh.trans (by linarith only [hd])

/-- ONE scale chosen before ALL compact R,w,buffers. On the entire
clamp, the adjacent-min direction is used; above two, genuine wall
separation pays exact table agreement. The remaining error is 16*tau/c^2. -/
theorem physical_cost_upper_uniform {c a δ ε : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hd : 0 < δ) (he : 0 < ε)
    (R w τ ξ ρ : ℝ) (hR : c ≤ R) (hR1 : R ≤ 1) (haw : a ≤ w) (hw1 : w ≤ 1)
    (hGood : Good R w δ)
    (hτ : 0 ≤ τ) (hτsmall : τ < eta c a δ ε)
    (hξ : 0 ≤ ξ) (hξsmall : ξ < eta c a δ ε)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < eta c a δ ε) :
    physicalCost R w τ ξ ρ ≤ originalCost R w + ε := by
  have hw : 0 < w := ha.trans_le haw
  have hb := eta_bounds c a δ ε
  have hτc : τ < c / 2 := hτsmall.trans_le hb.2.2.1
  have hRc : c / 2 ≤ R - τ := by linarith only [hR, hτc]
  have hErr : (4 / (c / 2) ^ 2) * τ ≤ ε := by
    have hτE := hτsmall.trans_le hb.2.2.2.1
    have hh := mul_lt_mul_of_pos_left hτE (by positivity : (0 : ℝ) < 4 / (c / 2) ^ 2)
    have hEq : (4 / (c / 2) ^ 2) * (ε * c ^ 2 / 32) = ε / 2 := by
      field_simp [hc.ne']
      <;> ring
    rw [hEq] at hh
    exact hh.le.trans (by linarith only [he])
  have hUpper : physicalCost R w τ ξ ρ ≤ originalCost R w + (4 / (c / 2) ^ 2) * τ := by
    rcases hGood with hClamp | ⟨hAbove, hwall⟩
    · have hXi := hξsmall.le.trans (hb.1.trans
        (div_le_div_of_nonneg_right haw (by norm_num : (0 : ℝ) ≤ 202)))
      have hRho := hρsmall.le.trans hb.2.1
      exact physical_cost_upper_on_clamp R w τ ξ ρ (c / 2) hw hClamp hτ hξ hXi hρ hRho (by positivity) hRc
    · have hs : 2 < R / w := (lt_div_iff₀ hw).mpr hAbove
      have hSep := separated_of_affine_walls hw hw1 hwall
      have hError := query_error_lt hc ha hd hR hR1 haw hτ hτsmall hξ hξsmall hρ hρsmall
      have hEq := lookup_eq_of_separated hs hd hSep
        (by simpa only [max_eq_right hs.le] using hError)
      have hq2 : 2 ≤ physicalQuery R w τ ξ ρ :=
        (by linarith only [hρ] : (2 : ℝ) ≤ 2 + ρ).trans (le_max_left _ _)
      rw [max_eq_right hq2] at hEq
      have hCost := reciprocal_cost_upper (by positivity : 0 < c / 2) hRc hτ
        (H248_bounds (max 2 (R / w)))
      simpa only [physicalCost, originalCost, hEq] using hCost
  exact hUpper.trans (add_le_add_left hErr _)

/-- Explicit existential form, with eta depending ONLY on four scalar
compact/error parameters and selected before every physical tuple. -/
theorem exists_uniform_scale {c a δ ε : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hd : 0 < δ) (he : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ R w τ ξ ρ : ℝ,
      c ≤ R → R ≤ 1 → a ≤ w → w ≤ 1 → Good R w δ →
      0 ≤ τ → τ < η → 0 ≤ ξ → ξ < η → 0 ≤ ρ → ρ < η →
      physicalCost R w τ ξ ρ ≤ originalCost R w + ε := by
  exact ⟨eta c a δ ε, eta_pos hc ha hd he, physical_cost_upper_uniform hc ha hd he⟩

end

end ImbalancedChen.P5Z.BufferedUniformStrip
