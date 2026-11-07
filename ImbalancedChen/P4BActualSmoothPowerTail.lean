import ImbalancedChen.P4BActualSmoothHyperbolaCorrection
import ImbalancedChen.PowerErrorBudget

/-!
# Explicit power decay of the actual complete-product correction

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Natural floors and ceilings are paid without removing products above N.
The actual family gives the unconditional finite estimate
32(exp(width)+1) N^(1-theta) (1+log(max(1,activeCap))).
No source mass or PNT premise appears. The final corollary states exactly
where a polynomial bound for the literal active coefficient is still needed.
That original full22 support certificate is NOT produced or assumed true
for arbitrary retention policies. No currentK or genuine PP estimate occurs.
-/

namespace ImbalancedChen.P4BActualSmoothPowerTail

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open Part3 P4B P4BLabelledOuterPushforward P4BActualCompactSmoothFamily
open P4BActualSmoothHyperbolaCorrection

def actualSmoothOuterCorrection (b kappa width nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
    attachedUpperCoefficient nu r epsilon retain cap N d *
      ((finiteCoprimeMass (productCarrier N)
          (productWeight N (smoothPhysicalPairOuterRamp b N
            (manuscriptHalfProductCutoff kappa N) width)) d -
        finiteSourceMass (productCarrier N)
          (productWeight N (smoothPhysicalPairOuterRamp b N
            (manuscriptHalfProductCutoff kappa N) width))) / (Nat.totient d : ℝ))

/-- Exact rounding payment in the original continuous support scale.
The active-modulus logarithm is explicit and has not been replaced by an
unproved original-policy exponent. -/
theorem actual_compact_smooth_correction_power_bound
    {b0 b1 kappa kappaZero theta precision widthMax b : ℝ}
    (F : ActualCompactSmoothFamily b0 b1 kappa kappaZero theta precision widthMax)
    (hb0 : b0 ≤ b) (hb1 : b ≤ b1) {N : ℕ} (hN : 2 ≤ N)
    (hH : (4 : ℝ) ≤ (N : ℝ) ^ theta)
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    |actualSmoothOuterCorrection b kappa F.width nu r epsilon retain cap N| ≤
      (32 * (Real.exp F.width + 1) * (N : ℝ) ^ (1 - theta)) *
        (1 + Real.log (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ))) := by
  let H : ℝ := (N : ℝ) ^ theta
  let L : ℕ := Nat.floor H
  let K : ℕ := Nat.ceil (Real.exp F.width * (N : ℝ))
  have hHpos : 0 < H := by dsimp only [H]; linarith only [hH]
  have hL : 2 ≤ L := (Nat.le_floor_iff hHpos.le).mpr (by dsimp only [H]; linarith only [hH])
  have hLpow : (L : ℝ) ≤ (N : ℝ) ^ theta := Nat.floor_le hHpos.le
  have hK : Real.exp F.width * (N : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
  have hfinite := actual_compact_smooth_correction_le_hyperbola
    F hb0 hb1 hN hL hLpow hK nu r epsilon retain cap
  change |actualSmoothOuterCorrection b kappa F.width nu r epsilon retain cap N| ≤
    (16 * (K : ℝ) / ((L : ℝ) - 1)) *
      (1 + Real.log (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ))) at hfinite
  have hfloor : H < (L : ℝ) + 1 := Nat.lt_floor_add_one H
  have hdenom : H / 2 ≤ (L : ℝ) - 1 := by
    have hfour : (4 : ℝ) ≤ H := hH
    linarith only [hfloor, hfour]
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hKupper : (K : ℝ) ≤ (Real.exp F.width + 1) * (N : ℝ) := by
    have hceil := (Nat.ceil_lt_add_one
      (mul_nonneg (Real.exp_pos F.width).le (Nat.cast_nonneg N))).le
    change (K : ℝ) ≤ Real.exp F.width * (N : ℝ) + 1 at hceil
    nlinarith only [hceil, hNreal]
  have hratio : 16 * (K : ℝ) / ((L : ℝ) - 1) ≤
      32 * (Real.exp F.width + 1) * (N : ℝ) / H := by
    calc
      _ ≤ 16 * (K : ℝ) / (H / 2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hHpos) hdenom
      _ ≤ 16 * ((Real.exp F.width + 1) * (N : ℝ)) / (H / 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKupper (by norm_num)) (half_pos hHpos).le
      _ = _ := by field_simp [hHpos.ne']; ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpower : 32 * (Real.exp F.width + 1) * (N : ℝ) / H =
      32 * (Real.exp F.width + 1) * (N : ℝ) ^ (1 - theta) := by
    dsimp only [H]
    rw [Real.rpow_sub hNpos, Real.rpow_one]
    ring
  have hlog : 0 ≤ 1 + Real.log
      (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ)) := by
    have := Real.log_nonneg
      (le_max_left (1 : ℝ) (actualActiveUpperCap nu r epsilon retain cap N : ℝ))
    linarith
  rw [hpower] at hratio
  exact hfinite.trans (mul_le_mul_of_nonneg_right hratio hlog)

/-- The one remaining range premise is stated for the literal active rho.
Under that genuine primitive input, the new mass-free complete-product
estimate pays every tolerance uniformly in the compact real-b family.
This does not supply the original full22 range certificate itself. -/
theorem eventually_actual_compact_smooth_correction_le_of_active_power_range
    {b0 b1 kappa kappaZero theta precision widthMax : ℝ}
    (F : ActualCompactSmoothFamily b0 b1 kappa kappaZero theta precision widthMax)
    (htheta : 0 < theta) (beta : ℝ) (hbeta : 0 ≤ beta)
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (hRange : ∀ᶠ N : ℕ in atTop, Even N →
      (actualActiveUpperCap nu r epsilon retain cap N : ℝ) ≤ (N : ℝ) ^ beta)
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ b : ℝ, b0 ≤ b → b ≤ b1 →
      |actualSmoothOuterCorrection b kappa F.width nu r epsilon retain cap N| ≤
        tolerance * singularNormalization N := by
  let c : ℝ := 32 * (Real.exp F.width + 1) * (beta + 1)
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ theta :=
    ((tendsto_rpow_atTop htheta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4)
  have hlogLarge : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hRange, hlarge, hlogLarge, eventually_ge_atTop (2 : ℕ),
    eventually_powerLog_le_singularNormalization c (1 - theta) 1
      (by linarith only [htheta]) tolerance htolerance]
    with N hRangeN hH hlogN hN hbudget
  intro hEven b hb0 hb1
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hmax : max (1 : ℝ) (actualActiveUpperCap nu r epsilon retain cap N : ℝ) ≤
      (N : ℝ) ^ beta := max_le (Real.one_le_rpow hN1.le hbeta) (hRangeN hEven)
  have hlogCap : Real.log
      (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ)) ≤
        beta * Real.log (N : ℝ) := by
    have h := Real.log_le_log
      (zero_lt_one.trans_le (le_max_left (1 : ℝ) _)) hmax
    rwa [Real.log_rpow hNpos] at h
  have hL : 1 + Real.log
      (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ)) ≤
        (beta + 1) * Real.log (N : ℝ) := by
    nlinarith only [hlogCap, hlogN]
  have hfinite := actual_compact_smooth_correction_power_bound
    F hb0 hb1 hN hH nu r epsilon retain cap
  calc
    _ ≤ (32 * (Real.exp F.width + 1) * (N : ℝ) ^ (1 - theta)) *
        (1 + Real.log (max 1 (actualActiveUpperCap nu r epsilon retain cap N : ℝ))) := hfinite
    _ ≤ (32 * (Real.exp F.width + 1) * (N : ℝ) ^ (1 - theta)) *
        ((beta + 1) * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = c * (N : ℝ) ^ (1 - theta) * (Real.log (N : ℝ)) ^ (1 : ℕ) := by
      dsimp only [c]
      rw [pow_one]
      ring
    _ ≤ _ := hbudget

end
end ImbalancedChen.P4BActualSmoothPowerTail
