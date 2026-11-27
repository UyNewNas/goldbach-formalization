import ImbalancedChen.PanProductGridRanges

/-!
# The complete-product scale in the restricted moving-residue estimate

The global residue is the target `N`, whereas the dispersion parameter `x`
is the complete local product.  A fixed lower trim
`c * N^(1 - κ₀) ≤ x` and upper bound `x ≤ C * N` imply, uniformly over
all such real `x`, the required range `C⁻¹ * x ≤ N ≤ x^(1 + κ)` once
`κ₀ < κ / (1 + κ)` and `N` is large.  Fixed multiplicative constants are
absorbed by a proved strict power gap.  The manuscript's stronger buffered
condition `κ₀ < κ / (4 * (1 + κ))` is a direct specialization.

These are scale theorems, not a prime-distribution estimate.  They do not
license a residual quotient in place of the complete local product and do
not assert the other coefficient, modulus, or spectral hypotheses of the
restricted medium theorem.
-/

namespace ImbalancedChen

open Filter

/-- The exact positive power gap needed to absorb a fixed lower-trim
constant when the residue is the global target. -/
theorem restrictedResidueScale_power_gap {κ κ₀ : ℝ} (hκ : 0 < κ)
    (hκ₀ : κ₀ < κ / (1 + κ)) :
    0 < 1 - κ₀ ∧ 1 < (1 - κ₀) * (1 + κ) := by
  have hden : 0 < 1 + κ := by linarith
  have hmul := (lt_div_iff₀ hden).mp hκ₀
  have hgap : 1 < (1 - κ₀) * (1 + κ) := by nlinarith
  constructor
  · by_contra h
    have hn : 1 - κ₀ ≤ 0 := le_of_not_gt h
    have := mul_nonpos_of_nonpos_of_nonneg hn hden.le
    linarith
  · exact hgap

/-- The threshold in this eventual statement precedes the complete local
product `x`.  In particular, all cells with the same constants use one
threshold; `x` need not be fixed as `N` varies. -/
theorem eventually_restrictedResidueScale
    {c C κ κ₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ)
    (hκ₀ : κ₀ < κ / (1 + κ)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - κ₀) ≤ x → x ≤ C * (N : ℝ) →
      1 < x ∧ C⁻¹ * x ≤ (N : ℝ) ∧ (N : ℝ) ≤ x ^ (1 + κ) := by
  obtain ⟨hbase, hgap⟩ := restrictedResidueScale_power_gap hκ hκ₀
  have hexp : 0 ≤ 1 + κ := by linarith
  have hcpow : 0 < c ^ (1 + κ) := Real.rpow_pos_of_pos hc _
  filter_upwards
    [eventually_const_mul_rpow_le_rpow (2 / c) hbase,
      eventually_const_mul_rpow_le_rpow (c ^ (1 + κ))⁻¹ hgap,
      eventually_ge_atTop (1 : ℕ)] with N hlarge hpower hN
  intro x hlow hupp
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlarge' : 2 ≤ c * (N : ℝ) ^ (1 - κ₀) := by
    simpa only [Real.rpow_zero, mul_one, mul_div_cancel₀ _ hc.ne'] using
      mul_le_mul_of_nonneg_left hlarge hc.le
  have hx : 1 < x := by linarith
  refine ⟨hx, ?_, ?_⟩
  · calc
      C⁻¹ * x ≤ C⁻¹ * (C * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hupp (inv_nonneg.mpr hC.le)
      _ = (N : ℝ) := by field_simp
  · have hpower' : (N : ℝ) ≤
        c ^ (1 + κ) * (N : ℝ) ^ ((1 - κ₀) * (1 + κ)) := by
      have hm := mul_le_mul_of_nonneg_left hpower hcpow.le
      simpa only [Real.rpow_one, ← mul_assoc, mul_inv_cancel₀ hcpow.ne',
        one_mul] using hm
    calc
      (N : ℝ) ≤ c ^ (1 + κ) *
          (N : ℝ) ^ ((1 - κ₀) * (1 + κ)) := hpower'
      _ = (c * (N : ℝ) ^ (1 - κ₀)) ^ (1 + κ) := by
        rw [Real.mul_rpow hc.le (Real.rpow_nonneg hNpos.le _),
          ← Real.rpow_mul hNpos.le]
      _ ≤ x ^ (1 + κ) :=
        Real.rpow_le_rpow (mul_nonneg hc.le (Real.rpow_nonneg hNpos.le _))
          hlow hexp

/-- An explicit common natural threshold, selected before `N` and every
complete local product at that target. -/
theorem exists_restrictedResidueScale_threshold
    {c C κ κ₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ)
    (hκ₀ : κ₀ < κ / (1 + κ)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - κ₀) ≤ x → x ≤ C * (N : ℝ) →
      1 < x ∧ C⁻¹ * x ≤ (N : ℝ) ∧ (N : ℝ) ≤ x ^ (1 + κ) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_restrictedResidueScale hc hC hκ hκ₀)
  exact ⟨max 2 N₀, le_max_left _ _, fun N hN =>
    hN₀ N ((le_max_right _ _).trans hN)⟩

/-- The actual buffered parameter choice in the manuscript is stronger
than the power gap used above.  The residue lower constant is explicitly
`C⁻¹ > 0`, not a constant depending on the local cell. -/
theorem exists_manuscript_restrictedResidueScale_threshold
    {c C κ κ₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ)
    (hκ₀ : κ₀ < κ / (4 * (1 + κ))) :
    0 < C⁻¹ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - κ₀) ≤ x → x ≤ C * (N : ℝ) →
      1 < x ∧ C⁻¹ * x ≤ (N : ℝ) ∧ (N : ℝ) ≤ x ^ (1 + κ) := by
  have hden : 0 < 1 + κ := by linarith
  have hsmall : κ / (4 * (1 + κ)) ≤ κ / (1 + κ) := by
    exact div_le_div_of_nonneg_left hκ.le hden (by linarith)
  exact ⟨inv_pos.mpr hC,
    exists_restrictedResidueScale_threshold hc hC hκ (hκ₀.trans_le hsmall)⟩

end ImbalancedChen
