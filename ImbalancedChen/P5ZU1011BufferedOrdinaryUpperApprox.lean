import ImbalancedChen.P5ZU1011BufferedOrdinaryOffKnots

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual physical upper ordinary-cost approximation, for ALL sufficiently
small nonnegative buffers. Only high knots51..200 are excluded. The entire
clamp half-space, INCLUDING raw ratio two, remains in the theorem.
-/

namespace ImbalancedChen.P5Z.BufferedOrdinaryUpperApprox

noncomputable section

open BufferedOrdinaryClamp BufferedOrdinaryOffKnots

def bufferScale (R w ε : ℝ) : ℝ :=
  min (R / 2) (min (w / 202) (min (1 / 100) (ε * R ^ 2 / 32)))

theorem bufferScale_pos {R w ε : ℝ} (hR : 0 < R) (hw : 0 < w) (hε : 0 < ε) :
    0 < bufferScale R w ε := by
  unfold bufferScale
  positivity

theorem bufferScale_le_R (R w ε : ℝ) : bufferScale R w ε ≤ R / 2 := min_le_left _ _
theorem bufferScale_le_w (R w ε : ℝ) : bufferScale R w ε ≤ w / 202 :=
  (min_le_right _ _).trans (min_le_left _ _)
theorem bufferScale_le_rho (R w ε : ℝ) : bufferScale R w ε ≤ 1 / 100 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
theorem bufferScale_le_error (R w ε : ℝ) : bufferScale R w ε ≤ ε * R ^ 2 / 32 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem small_tau_payment {R w ε τ : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hτ : 0 ≤ τ) (hτsmall : τ < bufferScale R w ε) :
    R / 2 ≤ R - τ ∧ (4 / (R / 2) ^ 2) * τ ≤ ε := by
  have hτR := hτsmall.trans_le (bufferScale_le_R R w ε)
  have hτErr := hτsmall.trans_le (bufferScale_le_error R w ε)
  have hC : 0 < (4 : ℝ) / (R / 2) ^ 2 := by positivity
  have hErr := mul_lt_mul_of_pos_left hτErr hC
  have hEq : (4 / (R / 2) ^ 2) * (ε * R ^ 2 / 32) = ε / 2 := by
    field_simp [hR.ne']
    <;> ring
  rw [hEq] at hErr
  exact ⟨by linarith only [hτR], hErr.le.trans (by linarith only [hε])⟩

/-- Genuine pointwise physical upper approximation. One eta is selected
before ALL three physical buffers. No H-correctness, density, averaging,
or target-mean assumption occurs. Clamp knot50 is explicitly retained. -/
theorem exists_physical_upper_scale (R w : ℝ) (hR : 0 < R) (hw : 0 < w)
    (hn : HighOffKnots (R / w)) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ τ ξ ρ : ℝ,
      0 ≤ τ → τ < η → 0 ≤ ξ → ξ < η → 0 ≤ ρ → ρ < η →
      physicalCost R w τ ξ ρ ≤ originalCost R w + ε := by
  by_cases hClamp : R ≤ 2 * w
  · refine ⟨bufferScale R w ε, bufferScale_pos hR hw hε, ?_⟩
    intro τ ξ ρ hτ hτsmall hξ hξsmall hρ hρsmall
    have hpay := small_tau_payment hR hε hτ hτsmall
    have hxi := hξsmall.le.trans (bufferScale_le_w R w ε)
    have hrho := hρsmall.le.trans (bufferScale_le_rho R w ε)
    have hCost := physical_cost_upper_on_clamp R w τ ξ ρ (R / 2) hw hClamp hτ hξ hxi hρ hrho
      (by positivity) hpay.1
    exact hCost.trans (add_le_add_left hpay.2 _)
  · have hs : 2 < R / w := (lt_div_iff₀ hw).mpr (lt_of_not_ge hClamp)
    obtain ⟨δ, hd, hlocal⟩ := exists_physical_upper_margin R w hw hR hs hn
    let α : ℝ := 2 * R / w ^ 2
    let β : ℝ := 2 / w
    let A : ℝ := 1 + α + β
    have hα : 0 ≤ α := by dsimp only [α]; positivity
    have hβ : 0 ≤ β := by dsimp only [β]; positivity
    have hA : 0 < A := by dsimp only [A]; linarith only [hα, hβ]
    let η : ℝ := min (bufferScale R w ε) (δ / (2 * A))
    have hη : 0 < η := lt_min (bufferScale_pos hR hw hε) (div_pos hd (by positivity))
    refine ⟨η, hη, ?_⟩
    intro τ ξ ρ hτ hτsmall hξ hξsmall hρ hρsmall
    have hηScale : η ≤ bufferScale R w ε := min_le_left _ _
    have hηDelta : η ≤ δ / (2 * A) := min_le_right _ _
    have hpay := small_tau_payment hR hε hτ (hτsmall.trans_le hηScale)
    have hxi202 := hξsmall.le.trans (hηScale.trans (bufferScale_le_w R w ε))
    have hxi2 : ξ ≤ w / 2 := by linarith only [hxi202, hw]
    have hXi := mul_le_mul_of_nonneg_left hξsmall.le hα
    have hTau := mul_le_mul_of_nonneg_left hτsmall.le hβ
    have hRate : ρ + α * ξ + β * τ < A * η := by
      calc
        ρ + α * ξ + β * τ < η + α * η + β * η :=
          add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le hρsmall hXi) hTau
        _ = A * η := by dsimp only [A]; ring
    have hAdelta := mul_le_mul_of_nonneg_left hηDelta hA.le
    have hEq : A * (δ / (2 * A)) = δ / 2 := by
      field_simp [hA.ne']
      <;> ring
    rw [hEq] at hAdelta
    have hSmall : ρ + (2 * R / w ^ 2) * ξ + (2 / w) * τ < δ := by
      change ρ + α * ξ + β * τ < δ
      exact (hRate.trans_le hAdelta).trans (by linarith only [hd])
    have hCost := hlocal τ ξ ρ (R / 2) hτ hξ hxi2 hρ hSmall (by positivity) hpay.1
    exact hCost.trans (add_le_add_left hpay.2 _)

end

end ImbalancedChen.P5Z.BufferedOrdinaryUpperApprox
