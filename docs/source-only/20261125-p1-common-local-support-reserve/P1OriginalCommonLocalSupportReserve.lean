import ImbalancedChen.RestrictedResidueScale

/-!
# Common local support reserve for the original finite coefficient families

The 2026-11-06 manuscript, Appendix on coefficient factorization,
`coef:parameter-order` and `coef:complete-scales`, uses the actual complete
product scale. The three pre-enlargement low-rank supports are respectively
19/48, 38/125 and 1527/3584; the total attached support is 599/1000.
These deterministic estimates transfer those four supports through the same
local trim and keep an explicit power margin. No signed PP, BV, or auxiliary
coefficient factorization is asserted.
-/

namespace ImbalancedChen.P1OriginalCommonLocalSupportReserve

open Filter

private theorem eventual_transfer {c α θ κ₀ : ℝ} (hc : 0 < c)
    (hα : 0 ≤ α) (hgap : θ < (1 - κ₀) * α) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - κ₀) ≤ x →
      A * (N : ℝ) ^ θ ≤ x ^ α := by
  have hcα : 0 < c ^ α := Real.rpow_pos_of_pos hc _
  filter_upwards [eventually_const_mul_rpow_le_rpow (A / c ^ α) hgap]
    with N hN
  intro x hx
  have h := mul_le_mul_of_nonneg_left hN hcα.le
  have hcancel : c ^ α * (A / c ^ α) = A := by
    rw [mul_comm, div_mul_cancel₀ _ hcα.ne']
  rw [← mul_assoc, hcancel] at h
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have htrim0 : 0 ≤ c * (N : ℝ) ^ (1 - κ₀) :=
    mul_nonneg hc.le (Real.rpow_nonneg hN0 _)
  calc
    A * (N : ℝ) ^ θ ≤ c ^ α * (N : ℝ) ^ ((1 - κ₀) * α) := h
    _ = (c * (N : ℝ) ^ (1 - κ₀)) ^ α := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hN0 _),
        ← Real.rpow_mul hN0]
    _ ≤ x ^ α := Real.rpow_le_rpow htrim0 hx hα

/-- One fixed positive trim satisfies both requirements on `κ₀`: the
moving residue range and the strict support inflation inequalities.
The low-rank reserve permits an extra fixed global exponent up to 1/100
for the small-prime attachment and other power enlargement. A constant
factor, uniform in the original chart family, is absorbed separately. -/
theorem exists_common_trim_and_local_support_reserve
    {c C κ : ℝ} (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < κ / (4 * (1 + κ)) ∧
      ∀ inflation A : ℝ, inflation ≤ 1 / 100 →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ x : ℝ,
        c * (N : ℝ) ^ (1 - κ₀) ≤ x → x ≤ C * (N : ℝ) →
        (1 < x ∧ C⁻¹ * x ≤ (N : ℝ) ∧ (N : ℝ) ≤ x ^ (1 + κ)) ∧
        A * (N : ℝ) ^ (599 / 1000 : ℝ) ≤ x ^ (3 / 5 - 1 / 4000 : ℝ) ∧
        A * (N : ℝ) ^ (19 / 48 + inflation) ≤ x ^ (1 / 2 - 1 / 4000 : ℝ) ∧
        A * (N : ℝ) ^ (38 / 125 + inflation) ≤ x ^ (1 / 2 - 1 / 4000 : ℝ) ∧
        A * (N : ℝ) ^ (1527 / 3584 + inflation) ≤ x ^ (1 / 2 - 1 / 4000 : ℝ) := by
  let trimMax : ℝ := κ / (4 * (1 + κ))
  have htrimMax : 0 < trimMax := by
    dsimp [trimMax]
    positivity
  let κ₀ : ℝ := min trimMax (1 / 1200) / 2
  have hκ₀ : 0 < κ₀ := half_pos (lt_min htrimMax (by norm_num))
  have hresTrim : κ₀ < κ / (4 * (1 + κ)) := by
    change κ₀ < trimMax
    have h := min_le_left trimMax (1 / 1200 : ℝ)
    dsimp only [κ₀]
    linarith
  have hκ₀cap : κ₀ ≤ (1 / 1200 : ℝ) := by
    have h := min_le_right trimMax (1 / 1200 : ℝ)
    dsimp only [κ₀]
    linarith
  refine ⟨κ₀, hκ₀, hresTrim, ?_⟩
  intro inflation A hi
  have hall : (599 / 1000 : ℝ) < (1 - κ₀) * (3 / 5 - 1 / 4000) := by
    linarith
  have hup : (19 / 48 : ℝ) + inflation < (1 - κ₀) * (1 / 2 - 1 / 4000) := by
    linarith
  have hordinary : (38 / 125 : ℝ) + inflation < (1 - κ₀) * (1 / 2 - 1 / 4000) := by
    linarith
  have hmarked : (1527 / 3584 : ℝ) + inflation < (1 - κ₀) * (1 / 2 - 1 / 4000) := by
    linarith
  obtain ⟨_, NR, _, hR⟩ :=
    exists_manuscript_restrictedResidueScale_threshold hc hC hκ hresTrim
  have he : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ NR ≤ N ∧
      ∀ x : ℝ, c * (N : ℝ) ^ (1 - κ₀) ≤ x →
        A * (N : ℝ) ^ (599 / 1000 : ℝ) ≤ x ^ (3 / 5 - 1 / 4000 : ℝ) ∧
        A * (N : ℝ) ^ (19 / 48 + inflation) ≤ x ^ (1 / 2 - 1 / 4000 : ℝ) ∧
        A * (N : ℝ) ^ (38 / 125 + inflation) ≤ x ^ (1 / 2 - 1 / 4000 : ℝ) ∧
        A * (N : ℝ) ^ (1527 / 3584 + inflation) ≤ x ^ (1 / 2 - 1 / 4000 : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_ge_atTop NR,
      eventual_transfer hc (by norm_num) hall A,
      eventual_transfer hc (by norm_num) hup A,
      eventual_transfer hc (by norm_num) hordinary A,
      eventual_transfer hc (by norm_num) hmarked A] with N hN hRN h1 h2 h3 h4
    exact ⟨hN, hRN, fun x hx => ⟨h1 x hx, h2 x hx, h3 x hx, h4 x hx⟩⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  refine ⟨max N₀ 2, le_max_right _ _, ?_⟩
  intro N hN x hx hX
  obtain ⟨_, hRN, hs⟩ := hN₀ N ((le_max_left _ _).trans hN)
  exact ⟨hR N hRN x hx hX, hs x hx⟩

end ImbalancedChen.P1OriginalCommonLocalSupportReserve
