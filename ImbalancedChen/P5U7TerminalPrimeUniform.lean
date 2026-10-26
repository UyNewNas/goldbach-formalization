import ImbalancedChen.P5U7TerminalPrimeFiniteWindow
import ImbalancedChen.PowerErrorBudget

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A single N threshold controls every physical multiplier and terminal wall.
The genuine PNT and the target-prime logarithmic bound supply all errors.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology LiLiuPrereqBuchstab

/-- Explicit relative payment for the lower wall and the upper/target atoms. -/
def p5U7TerminalPrimeLossRate (N : ℕ) (eta : ℝ) : ℝ :=
  (1 / (N : ℝ) ^ ((59 / 250 : ℝ) * eta) +
    (1 + Real.log (N : ℝ) / Real.log 2) / (N : ℝ) ^ (59 / 250 : ℝ)) *
      Real.log (N : ℝ)

theorem p5U7TerminalPrimeLossRate_tendsto_zero (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => p5U7TerminalPrimeLossRate N eta) atTop (𝓝 0) := by
  have h1 := tendsto_nat_log_pow_div_rpow 1
    (show 0 < (59 / 250 : ℝ) * eta by positivity)
  have h2 := tendsto_nat_log_pow_div_rpow 1 (by norm_num : (0 : ℝ) < 59 / 250)
  have h3 := (tendsto_nat_log_pow_div_rpow 2
    (by norm_num : (0 : ℝ) < 59 / 250)).div_const (Real.log 2)
  have hh := h1.add (h2.add h3)
  convert hh using 1
  · funext N
    dsimp only [p5U7TerminalPrimeLossRate]
    simp only [pow_one]
    ring
  · simp

/-- Uniform absolute relative error for the ACTUAL target-excluding fibre.
The threshold is chosen before a and ell; no mean/density hypothesis occurs. -/
theorem p5U7TerminalPrime_eventually_uniform_abs (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ a ell : ℕ, 0 < a →
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (N : ℝ) / (a : ℝ) →
      (ell : ℝ) ≤ ((N : ℝ) / (a : ℝ)) * (N : ℝ) ^ (-((59 / 250 : ℝ) * eta)) →
      |((p5U7MassPrimeFibre N a ell).card : ℝ) -
        ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))| ≤
          epsilon * (((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ) ^ (59 / 250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hPNT := (tendsto_primeErrorEnvelope.comp hgrowth).eventually
    (gt_mem_nhds (half_pos hepsilon))
  have hLoss := (p5U7TerminalPrimeLossRate_tendsto_zero eta heta).eventually
    (gt_mem_nhds (half_pos hepsilon))
  filter_upwards [hPNT,hLoss,hgrowth.eventually (eventually_ge_atTop primeErrorStart),
    eventually_ge_atTop (2 : ℕ)] with N hPNT hLoss hstart hN
  intro a ell ha hxbase hell
  let x : ℝ := (N : ℝ) / (a : ℝ)
  let A : ℝ := (N : ℝ) ^ (59 / 250 : ℝ)
  let B : ℝ := (N : ℝ) ^ ((59 / 250 : ℝ) * eta)
  let C : ℝ := 1 + Real.log (N : ℝ) / Real.log 2
  let K : ℝ := 1 / B + C / A
  have hN0 : 0 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNR : (0 : ℝ) < N := zero_lt_one.trans hNr
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hA : 0 < A := Real.rpow_pos_of_pos hNR _
  have hB : 0 < B := Real.rpow_pos_of_pos hNR _
  have hx : 0 < x := div_pos hNR haR
  have hx1 : 1 < x := by
    have hs : 1 < primeErrorStart := by linarith [primeErrorStart_spec.1]
    exact hs.trans_le (hstart.trans hxbase)
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hxN : x ≤ N := div_le_self hNR.le ha1
  have hlog : Real.log x ≤ Real.log (N : ℝ) := Real.log_le_log hx hxN
  have hC : 0 ≤ C := add_nonneg (by norm_num)
    (div_nonneg (Real.log_pos hNr).le (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  have hK : 0 ≤ K := add_nonneg (one_div_nonneg.mpr hB.le) (div_nonneg hC hA.le)
  have hFactors := chen_primeFactors_card_le_log hN0
  have hratio : 1 ≤ x / A := (one_le_div hA).mpr hxbase
  have hatoms : 1 + (N.primeFactors.card : ℝ) ≤ C * (x / A) := by
    have hscale := mul_le_mul_of_nonneg_left hratio hC
    dsimp only [C] at hscale ⊢
    linarith only [hscale,hFactors]
  have hell' : (ell : ℝ) ≤ x / B := by
    simpa only [Real.rpow_neg hNR.le, ← div_eq_mul_inv] using hell
  have hdeleted : (ell : ℝ) + 1 + (N.primeFactors.card : ℝ) ≤ x * K := by
    dsimp only [K]
    nlinarith only [hell',hatoms]
  have hbudget : x * K ≤ p5U7TerminalPrimeLossRate N eta * (x / Real.log x) := by
    have hm := mul_le_mul_of_nonneg_left hlog (mul_nonneg hx.le hK)
    have hid : p5U7TerminalPrimeLossRate N eta * (x / Real.log x) =
        (x * K * Real.log (N : ℝ)) / Real.log x := by
      dsimp only [p5U7TerminalPrimeLossRate,K,C,A,B]
      ring
    rw [hid]
    exact (le_div_iff₀ hlx).mpr (by nlinarith only [hm])
  have herror := p5U7TerminalPrime_abs_error N a ell ha hN0 hstart hxbase
  have hmain : 0 ≤ x / Real.log x := (div_pos hx hlx).le
  have hsmall := mul_le_mul_of_nonneg_right (add_le_add hPNT.le hLoss.le) hmain
  change |((p5U7MassPrimeFibre N a ell).card : ℝ) - x / Real.log x| ≤
    epsilon * (x / Real.log x)
  change |((p5U7MassPrimeFibre N a ell).card : ℝ) - x / Real.log x| ≤
    primeErrorEnvelope A * (x / Real.log x) +
      ((ell : ℝ) + 1 + (N.primeFactors.card : ℝ)) at herror
  dsimp only [A] at herror
  nlinarith only [herror,hdeleted,hbudget,hsmall]

/-- Leading one lower bound, with the same threshold before all fibres. -/
theorem p5U7TerminalPrime_eventually_uniform_lower (eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ a ell : ℕ, 0 < a →
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (N : ℝ) / (a : ℝ) →
      (ell : ℝ) ≤ ((N : ℝ) / (a : ℝ)) * (N : ℝ) ^ (-((59 / 250 : ℝ) * eta)) →
      (1 - epsilon) * (((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))) ≤
        ((p5U7MassPrimeFibre N a ell).card : ℝ) := by
  filter_upwards [p5U7TerminalPrime_eventually_uniform_abs eta epsilon heta hepsilon] with N hN
  intro a ell ha hx hell
  have h := (abs_le.mp (hN a ell ha hx hell)).1
  nlinarith only [h]
end
end ImbalancedChen


