import ImbalancedChen.BoundaryArbitraryLog

-- UNCOMPILED_ZERO_CREDIT. Original E5 power reserve and growing Brun support.
-- This is the new numerical payment for BOTH y=x^o(1) and the Brun gap,
-- rather than the old unrough M*D normalization theorem.

namespace ImbalancedChen
namespace OriginalOneLongSupportAbsorption

noncomputable section
open Filter
open scoped Topology

def SubpowerSupport (Y : ℕ → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∀ᶠ N : ℕ in atTop, 0 ≤ Y N ∧ Y N ≤ (N : ℝ) ^ delta

def SuperLogGap (epsilon : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, ∀ eta : ℝ, 0 < eta →
    ∀ᶠ N : ℕ in atTop, epsilon N * (Real.log (N : ℝ)) ^ r ≤ eta

theorem superLogGap_const_mul (epsilon : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hepsilon : SuperLogGap epsilon) : SuperLogGap (fun N => C * epsilon N) := by
  intro r eta heta
  by_cases hzero : C = 0
  · simp only [hzero, zero_mul]
    exact Filter.Eventually.of_forall (fun _ => heta.le)
  · have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
    filter_upwards [hepsilon r (eta / C) (div_pos heta hpos)] with N hN
    calc
      _ = C * (epsilon N * (Real.log (N : ℝ)) ^ r) := by ring
      _ ≤ C * (eta / C) := mul_le_mul_of_nonneg_left hN hC
      _ = eta := by field_simp [hzero]

theorem eventually_gap_budget (epsilon : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hepsilon : SuperLogGap epsilon) (B A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) * epsilon N * (Real.log (N : ℝ)) ^ B ≤
        eta * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  have hsmall := superLogGap_const_mul epsilon C hC hepsilon (A + B) eta heta
  filter_upwards [hsmall, eventually_one_le_nat_log] with N hN hlog
  have hl0 : Real.log (N : ℝ) ≠ 0 := ne_of_gt (by linarith)
  calc
    _ = ((C * epsilon N) * (Real.log (N : ℝ)) ^ (A + B)) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := by
      rw [pow_add]
      field_simp [hl0]
      ring
    _ ≤ eta * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by ring

-- One threshold is fixed BEFORE the actual short length M and modulus cap D.
-- theta is the manuscript's actual 20*zeta+Theta_loc, with its strict margin.
-- The growing support appears only in the power-saving term M*Y*D.
theorem eventually_one_long_E5_budget
    (Y epsilon : ℕ → ℝ) (C theta : ℝ) (B A : ℕ)
    (hC : 0 ≤ C) (htheta : theta < 1)
    (hY : SubpowerSupport Y) (hepsilon : SuperLogGap epsilon)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ M D : ℝ,
      M * D ≤ (N : ℝ) ^ theta →
      C * ((N : ℝ) * epsilon N + M * Y N * D) * (Real.log (N : ℝ)) ^ B ≤
        eta * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  let delta : ℝ := (1 - theta) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hreserve : theta + delta < 1 := by dsimp [delta]; linarith
  filter_upwards [hY delta hdelta,
    eventually_gap_budget epsilon C hC hepsilon B A (eta / 2) (half_pos heta),
    eventually_powerLog_le_logAccuracy C (theta + delta) B A hreserve
      (eta / 2) (half_pos heta),
    eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hYN hgap hpower hlog hN
  intro M D hMD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hproduct : M * Y N * D ≤ (N : ℝ) ^ (theta + delta) := by
    calc
      _ = (M * D) * Y N := by ring
      _ ≤ (N : ℝ) ^ theta * (N : ℝ) ^ delta :=
        mul_le_mul hMD hYN.2 hYN.1 (Real.rpow_nonneg hNpos.le _)
      _ = _ := (Real.rpow_add hNpos _ _).symm
  have hcost : C * (M * Y N * D) * (Real.log (N : ℝ)) ^ B ≤
      C * (N : ℝ) ^ (theta + delta) * (Real.log (N : ℝ)) ^ B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hproduct hC) (by positivity)
  have hpower' := hcost.trans hpower
  calc
    _ = C * (N : ℝ) * epsilon N * (Real.log (N : ℝ)) ^ B +
        C * (M * Y N * D) * (Real.log (N : ℝ)) ^ B := by ring
    _ ≤ (eta / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A +
        (eta / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ A := add_le_add hgap hpower'
    _ = _ := by ring

end
end OriginalOneLongSupportAbsorption
end ImbalancedChen
