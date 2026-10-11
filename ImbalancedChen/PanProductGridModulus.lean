import ImbalancedChen.PanProductGridRanges
import ImbalancedChen.PanProductLiuBridge
import ImbalancedChen.EnlargedSelbergCap

/-!
# Honest modulus gates for the dynamic Pan product grid

The smallest selected product endpoint is only of size
`N^(1 - κ₀)` (up to the recorded constant and rounding losses).  Therefore
a global square-root modulus cutoff cannot be transferred to that endpoint:
one must first choose a physical modulus exponent strictly below
`(1 - κ₀) / 2`.

This file proves exactly that power-gap statement.  For every fixed
`theta < (1 - κ₀) / 2`, the natural level `floor (N^theta)` eventually lies
below the Liu--Pan cutoff at both exact endpoints of every selected dynamic
cell.  A corollary applies it to the literal squared Selberg level already
used by the finite sieve.  No endpoint-scale cutoff is inferred from a
global-scale cutoff.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open MathlibNt.SieveTheory.LiuWeight

/-- A strict power gap below half of the smallest product exponent absorbs
every fixed logarithmic loss in the Liu--Pan conductor, uniformly over all
selected dynamic product cells.

The conclusion is stated for `floor (N^theta)`, so any smaller physical
modulus level can be inserted by transitivity. -/
theorem eventually_actualPanProductGridIndices_floor_rpow_modulus_gates
    {num den : ℕ} {κm theta : ℝ} (hκm0 : 0 < κm) (hκm1 : κm < 1)
    (htheta0 : 0 ≤ theta) (htheta : theta < (1 - κm) / 2)
    {gridκ : ℝ} (hgridκ : 1 < gridκ) (hgridκ2 : gridκ ≤ 2)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ij ∈ actualPanProductGridIndices num den N
          (manuscriptHalfProductCutoff κm N) gridκ,
        Nat.floor ((N : ℝ) ^ theta) ≤
            panModulusCutoff (multiplicativeGridIocEndpoint gridκ ij.2) B ∧
          Nat.floor ((N : ℝ) ^ theta) ≤
            panModulusCutoff
              (multiplicativeGridIocEndpoint gridκ (ij.2 + 1)) B := by
  let alpha : ℝ := (2 * theta + (1 - κm)) / 2
  let gap : ℝ := alpha / 2 - theta
  have halphaUpper : alpha < 1 - κm := by
    dsimp [alpha]
    linarith
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha]
    linarith
  have hgap : 0 < gap := by
    dsimp [gap, alpha]
    linarith
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards
    [eventually_const_mul_rpow_le_rpow 2 halphaUpper,
      eventually_log_pow_le_half_logCutoff_rpow_sub_one (Nat.ceil B) hgap,
      eventually_actualPanProductGridIndices_productEndpoints_ge
        hκm0 hκm1 hgridκ hgridκ2 2,
      hlog, eventually_ge_atTop (1 : ℕ)]
    with N hcut hlogBound hendpointTwo hlogN hN
  intro ij hij
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hNge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
  have hlogCutoffLeN : logCutoff N ≤ (N : ℝ) := by
    have hpow : 1 ≤ (Real.log (N : ℝ)) ^ 10 := one_le_pow₀ hlogN
    have hpowpos : 0 < (Real.log (N : ℝ)) ^ 10 := by linarith
    unfold logCutoff
    apply (div_le_iff₀ hpowpos).mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)
  have hlogFour : 1 ≤ Real.log (4 * (N : ℝ)) :=
    hlogN.trans (Real.log_le_log hNpos (by nlinarith))
  have hlogPower : Real.log (4 * (N : ℝ)) ^ B ≤ (N : ℝ) ^ gap := by
    calc
      Real.log (4 * (N : ℝ)) ^ B ≤
          Real.log (4 * (N : ℝ)) ^ (Nat.ceil B : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogFour (Nat.le_ceil B)
      _ = Real.log (4 * (N : ℝ)) ^ Nat.ceil B := by
        rw [Real.rpow_natCast]
      _ ≤ (logCutoff N) ^ gap / 2 - 1 := hlogBound.2
      _ ≤ (N : ℝ) ^ gap := by
        have hp := Real.rpow_le_rpow (logCutoff_nonneg N)
          hlogCutoffLeN hgap.le
        nlinarith [hp, Real.rpow_nonneg hNnonneg gap]
  have hlower := actualPanProductGridIndices_productLowerEndpoint_gt
    hgridκ hgridκ2 hij
  have hlower' :
      (N : ℝ) ^ (1 - κm) - 1 <
        (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) := by
    simpa [manuscriptHalfProductCutoff] using hlower
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ alpha :=
    Real.one_le_rpow hNge halpha0
  have hY₀base : (N : ℝ) ^ alpha ≤
      (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) := by
    linarith [hcut, hone, hlower']
  have hYmono :
      multiplicativeGridIocEndpoint gridκ ij.2 ≤
        multiplicativeGridIocEndpoint gridκ (ij.2 + 1) :=
    multiplicativeGridIocEndpoint_le_succ hgridκ ij.2
  have hY₁base : (N : ℝ) ^ alpha ≤
      (multiplicativeGridIocEndpoint gridκ (ij.2 + 1) : ℝ) := by
    exact hY₀base.trans (by exact_mod_cast hYmono)
  have hY₁cap := actualPanProductGridIndices_productUpperEndpoint_lt
    hgridκ hgridκ2 hij
  have hY₀cap :
      (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) < 2 * (N : ℝ) :=
    (by exact_mod_cast hYmono :
      (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) ≤
        (multiplicativeGridIocEndpoint gridκ (ij.2 + 1) : ℝ)).trans_lt hY₁cap
  have htwo := hendpointTwo ij hij
  have endpoint_gate : ∀ Y : ℕ,
      (N : ℝ) ^ alpha ≤ (Y : ℝ) →
      (Y : ℝ) < 2 * (N : ℝ) →
      2 ≤ Y →
      Nat.floor ((N : ℝ) ^ theta) ≤ panModulusCutoff Y B := by
    intro Y hYbase hYcap hYtwo
    have hYpos : (0 : ℝ) < (Y : ℝ) := by
      exact_mod_cast (show 0 < Y by omega)
    have hlogYpos : 0 < Real.log (Y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
    have hlogY : Real.log (Y : ℝ) ≤ Real.log (4 * (N : ℝ)) := by
      exact Real.log_le_log hYpos (by linarith)
    have hlogYrpow : Real.log (Y : ℝ) ^ B ≤
        Real.log (4 * (N : ℝ)) ^ B :=
      Real.rpow_le_rpow hlogYpos.le hlogY hB
    have hsqrtBase : (N : ℝ) ^ (alpha / 2) ≤ Real.sqrt (Y : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc
        (N : ℝ) ^ (alpha / 2) =
            ((N : ℝ) ^ alpha) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul hNnonneg]
          congr 1
          ring
        _ ≤ (Y : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hNnonneg alpha)
            hYbase (by norm_num)
    have hnumerator :
        (N : ℝ) ^ theta * Real.log (Y : ℝ) ^ B ≤ Real.sqrt (Y : ℝ) := by
      calc
        (N : ℝ) ^ theta * Real.log (Y : ℝ) ^ B ≤
            (N : ℝ) ^ theta * Real.log (4 * (N : ℝ)) ^ B :=
          mul_le_mul_of_nonneg_left hlogYrpow
            (Real.rpow_nonneg hNnonneg theta)
        _ ≤ (N : ℝ) ^ theta * (N : ℝ) ^ gap :=
          mul_le_mul_of_nonneg_left hlogPower
            (Real.rpow_nonneg hNnonneg theta)
        _ = (N : ℝ) ^ (alpha / 2) := by
          rw [← Real.rpow_add hNpos]
          dsimp [gap]
          congr 1
          ring
        _ ≤ Real.sqrt (Y : ℝ) := hsqrtBase
    unfold panModulusCutoff
    apply Nat.le_floor
    calc
      (Nat.floor ((N : ℝ) ^ theta) : ℝ) ≤ (N : ℝ) ^ theta :=
        Nat.floor_le (Real.rpow_nonneg hNnonneg theta)
      _ ≤ Real.sqrt (Y : ℝ) / Real.log (Y : ℝ) ^ B := by
        apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogYpos B)).mpr
        exact hnumerator
      _ = (Y : ℝ) ^ (1 / 2 : ℝ) / Real.log (Y : ℝ) ^ B := by
        rw [Real.sqrt_eq_rpow]
  exact ⟨endpoint_gate _ hY₀base hY₀cap htwo.1,
    endpoint_gate _ hY₁base hY₁cap htwo.2⟩

/-- The literal squared Selberg level is a valid physical modulus level at
both dynamic endpoints whenever its exponent has the required strict gap.
This connects the endpoint geometry to the already formalized finite sieve
level without replacing that level by a real-valued surrogate. -/
theorem eventually_actualPanProductGridIndices_enlargedSelberg_modulus_gates
    {num den : ℕ} {κm theta : ℝ} (hκm0 : 0 < κm) (hκm1 : κm < 1)
    (htheta0 : 0 ≤ theta) (htheta : theta < (1 - κm) / 2)
    {gridκ : ℝ} (hgridκ : 1 < gridκ) (hgridκ2 : gridκ ≤ 2)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ij ∈ actualPanProductGridIndices num den N
          (manuscriptHalfProductCutoff κm N) gridκ,
        enlargedSelbergLevel theta N * enlargedSelbergLevel theta N ≤
            panModulusCutoff (multiplicativeGridIocEndpoint gridκ ij.2) B ∧
          enlargedSelbergLevel theta N * enlargedSelbergLevel theta N ≤
            panModulusCutoff
              (multiplicativeGridIocEndpoint gridκ (ij.2 + 1)) B := by
  filter_upwards
    [eventually_actualPanProductGridIndices_floor_rpow_modulus_gates
      hκm0 hκm1 htheta0 htheta hgridκ hgridκ2 hB]
    with N hN
  intro ij hij
  have hlevel := enlargedSelbergLevel_mul_self_le_floor theta N
  exact ⟨hlevel.trans (hN ij hij).1, hlevel.trans (hN ij hij).2⟩

end

end ImbalancedChen
