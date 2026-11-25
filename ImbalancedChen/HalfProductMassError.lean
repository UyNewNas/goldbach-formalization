import ImbalancedChen.HalfProductMassSplit
import ImbalancedChen.UniformPrimeTail
import ImbalancedChen.LogCutoffError

/-!
# Negligible error for the actual half-product mass approximation

The finite high/low decomposition bounds the error by a prime rectangle,
a prime square, and the natural ceiling of the actual cutoff. Under the
exact real-PNT witness used in `UniformPrimeTail`, the rectangle and square
are bounded by a fixed multiple of `N / (log N)^2`. Their ratio to the
mass scale `N / log N` therefore tends to zero.

The cutoff is literally `N / (log N)^10`. Its ratio to the mass scale is
`1 / (log N)^9`, and divergence of the mass scale absorbs the extra unit
in its ceiling. The square-root endpoint is converted by the exact identity
`floor (sqrt N) = Nat.sqrt N`; no real/natural rounding error is dropped.

The sole analytic premise is the explicit real-PNT statement. There is no
assumed estimate for a target mass, no parity restriction, and no import
from the external prime-number-theorem project.
-/

namespace ImbalancedChen

open Filter Asymptotics Topology

/-- For each fixed `0 < num < den`, the literal cutoff source differs from
the strict-window prime-prefix approximation by `o(N / log N)`, in the
explicit epsilon-eventual form. This is conditional only on the upstream
real-PNT witness, not on a mass asymptotic or a target-count bound. -/
theorem eventually_halfProductSource_massApprox_error_of_real_pnt
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {num den : ℕ} (hnum : 0 < num) (hnumden : num < den)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |((halfProductSource num den N (logCutoff N)).card : ℝ) -
          (halfProductMassApprox num den N : ℝ)| ≤
        epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  let a : ℝ := halfProductMassAlpha num den
  let b : ℝ := halfProductMassBeta num den
  have ha : 0 < a := (halfProductMass_exponents hnum hnumden).1
  have hb : 0 < b := (halfProductMass_exponents hnum hnumden).2.2.1
  have hab : a + b = 1 := (halfProductMass_exponents hnum hnumden).2.2.2
  let C : ℝ := (2 / a) * (2 / b) + 16
  have heps3 : 0 < epsilon / 3 := div_pos hepsilon (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgeomRatio : Tendsto (fun N : ℕ => C / Real.log (N : ℝ))
      atTop (𝓝 0) := hlog.const_div_atTop C
  have hcutRatio : Tendsto (fun N : ℕ => 1 / (Real.log (N : ℝ)) ^ 9)
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 9) atTop atTop :=
      (tendsto_pow_atTop (α := ℝ) (n := 9) (by norm_num)).comp hlog
    exact hpow.const_div_atTop 1
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) / Real.log (N : ℝ))
      atTop atTop := by
    have h := ((Real.tendsto_exp_div_pow_atTop 1).comp
      Real.tendsto_log_atTop).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    simp only [Function.comp_apply, Real.exp_log hNpos, pow_one]
  have hunit : ∀ᶠ N : ℕ in atTop,
      1 ≤ (epsilon / 3) * ((N : ℝ) / Real.log (N : ℝ)) :=
    (hscale.const_mul_atTop heps3).eventually (eventually_ge_atTop 1)
  filter_upwards
    [eventually_primeCounting_rpow_le_of_real_pnt hPNT ha,
      eventually_primeCounting_rpow_le_of_real_pnt hPNT hb,
      eventually_primeCounting_rpow_le_of_real_pnt hPNT
        (show (0 : ℝ) < 1 / 2 by norm_num),
      hgeomRatio.eventually (gt_mem_nhds heps3),
      hcutRatio.eventually (gt_mem_nhds heps3), hunit,
      eventually_ge_atTop (2 : ℕ)]
    with N hA hB hHalf hgeomSmall hcutSmall hunitN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hbase : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlogpos.le
  have hpower : (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) := by
    rw [← Real.rpow_add hNpos, hab, Real.rpow_one]
  have hrectangle :
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ b)) ≤
        ((2 / a) * (2 / b)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ b)) ≤
          ((2 / a) * (N : ℝ) ^ a / Real.log (N : ℝ)) *
            ((2 / b) * (N : ℝ) ^ b / Real.log (N : ℝ)) :=
        mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
      _ = ((2 / a) * (2 / b)) *
          ((N : ℝ) ^ a * (N : ℝ) ^ b) / (Real.log (N : ℝ)) ^ 2 := by ring
      _ = ((2 / a) * (2 / b)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
        rw [hpower]
  have hSqrt : (Nat.primeCounting (Nat.sqrt N) : ℝ) ≤
      4 * Real.sqrt (N : ℝ) / Real.log (N : ℝ) := by
    simpa only [← Real.sqrt_eq_rpow, Real.nat_floor_real_sqrt_eq_nat_sqrt,
      show (2 : ℝ) / (1 / 2) = 4 by norm_num] using hHalf
  have hsquare : (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
      16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
          (4 * Real.sqrt (N : ℝ) / Real.log (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hSqrt 2
      _ = 16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        norm_num
  have hgeometric :
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ b)) +
          (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      _ ≤ ((2 / a) * (2 / b)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 +
          16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := add_le_add hrectangle hsquare
      _ = C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by dsimp [C]; ring
  have hgeometricCost : C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      (epsilon / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      _ = (C / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeomSmall.le hbase
  have hcutoffCost : logCutoff N ≤
      (epsilon / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      logCutoff N = (1 / (Real.log (N : ℝ)) ^ 9) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
        unfold logCutoff
        field_simp [ne_of_gt hlogpos] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcutSmall.le hbase
  have hceil : (Nat.ceil (logCutoff N) : ℝ) ≤ logCutoff N + 1 :=
    (Nat.ceil_lt_add_one (logCutoff_nonneg N)).le
  calc
    |((halfProductSource num den N (logCutoff N)).card : ℝ) -
        (halfProductMassApprox num den N : ℝ)| ≤
        (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ b)) +
          (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 + Nat.ceil (logCutoff N) :=
      halfProductSource_mass_split_cutoff_envelope hnum hnumden N (logCutoff N)
    _ ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 + (logCutoff N + 1) :=
      add_le_add hgeometric hceil
    _ ≤ epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
      linarith [hgeometricCost, hcutoffCost, hunitN]

end ImbalancedChen
