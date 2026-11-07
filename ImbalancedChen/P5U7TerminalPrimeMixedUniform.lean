import ImbalancedChen.P5U7TerminalPrimeMixedEndpoints
import ImbalancedChen.PowerErrorBudget

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Uniform actual prime-window PNT with original target N, independent cutoff
M<=N, and ARBITRARY positive base/relative-wall exponents. One N threshold
precedes M,a,ell. This accepts x=M/a>=N^alpha even when x<N^(59/250).
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology LiLiuPrereqBuchstab

def p5U7TerminalPrimeMixedLossRate (N : ℕ) (alpha delta : ℝ) : ℝ :=
  (1/(N : ℝ)^delta+(1+Real.log (N : ℝ)/Real.log 2)/(N : ℝ)^alpha)*Real.log (N : ℝ)

theorem p5U7TerminalPrimeMixedLossRate_tendsto_zero (alpha delta : ℝ)
    (halpha : 0 < alpha) (hdelta : 0 < delta) :
    Tendsto (fun N : ℕ => p5U7TerminalPrimeMixedLossRate N alpha delta) atTop (𝓝 0) := by
  have h1 := tendsto_nat_log_pow_div_rpow 1 hdelta
  have h2 := tendsto_nat_log_pow_div_rpow 1 halpha
  have h3 := (tendsto_nat_log_pow_div_rpow 2 halpha).div_const (Real.log 2)
  have hh := h1.add (h2.add h3)
  convert hh using 1
  · funext N
    dsimp only [p5U7TerminalPrimeMixedLossRate]
    simp only [pow_one]
    ring
  · simp

/-- One original-target N threshold controls EVERY independent M<=N and
all actual target-excluding terminal windows with the indicated geometry. -/
theorem p5U7TerminalPrimeMixed_eventually_uniform_abs (alpha delta epsilon : ℝ)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M a ell : ℕ, M ≤ N → 0 < a →
      (N : ℝ)^alpha ≤ (M : ℝ)/(a : ℝ) →
      (ell : ℝ) ≤ ((M : ℝ)/(a : ℝ))*(N : ℝ)^(-delta) →
      |((p5U7MassPrimeWindow N M a ell).card : ℝ)-
        ((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ))| ≤
          epsilon*(((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ))) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^alpha) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp tendsto_natCast_atTop_atTop
  have hPNT := (tendsto_primeErrorEnvelope.comp hgrowth).eventually
    (gt_mem_nhds (half_pos hepsilon))
  have hLoss := (p5U7TerminalPrimeMixedLossRate_tendsto_zero alpha delta halpha hdelta).eventually
    (gt_mem_nhds (half_pos hepsilon))
  filter_upwards [hPNT,hLoss,hgrowth.eventually (eventually_ge_atTop primeErrorStart),
    eventually_ge_atTop (2 : ℕ)] with N hPNT hLoss hstart hN
  intro M a ell hMN ha hxbase hell
  let x : ℝ := (M : ℝ)/(a : ℝ)
  let A : ℝ := (N : ℝ)^alpha
  let B : ℝ := (N : ℝ)^delta
  let C : ℝ := 1+Real.log (N : ℝ)/Real.log 2
  let K : ℝ := 1/B+C/A
  have hN0 : 0 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNR : (0 : ℝ) < N := zero_lt_one.trans hNr
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hA : 0 < A := Real.rpow_pos_of_pos hNR _
  have hB : 0 < B := Real.rpow_pos_of_pos hNR _
  have hx : 0 < x := hA.trans_le hxbase
  have hx1 : 1 < x := by
    have hs : 1 < primeErrorStart := by linarith [primeErrorStart_spec.1]
    exact hs.trans_le (hstart.trans hxbase)
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hxN : x ≤ N := (div_le_self (Nat.cast_nonneg M) ha1).trans
    (show (M : ℝ) ≤ N by exact_mod_cast hMN)
  have hlog : Real.log x ≤ Real.log (N : ℝ) := Real.log_le_log hx hxN
  have hC : 0 ≤ C := add_nonneg (by norm_num)
    (div_nonneg (Real.log_pos hNr).le (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  have hK : 0 ≤ K := add_nonneg (one_div_nonneg.mpr hB.le) (div_nonneg hC hA.le)
  have hFactors := chen_primeFactors_card_le_log hN0
  have hratio : 1 ≤ x/A := (one_le_div hA).mpr hxbase
  have hatoms : 1+(N.primeFactors.card : ℝ) ≤ C*(x/A) := by
    have hscale := mul_le_mul_of_nonneg_left hratio hC
    dsimp only [C] at hscale ⊢
    linarith only [hscale,hFactors]
  have hell' : (ell : ℝ) ≤ x/B := by
    simpa only [Real.rpow_neg hNR.le,← div_eq_mul_inv] using hell
  have hdeleted : (ell : ℝ)+1+(N.primeFactors.card : ℝ) ≤ x*K := by
    dsimp only [K]
    nlinarith only [hell',hatoms]
  have hbudget : x*K ≤ p5U7TerminalPrimeMixedLossRate N alpha delta*(x/Real.log x) := by
    have hm := mul_le_mul_of_nonneg_left hlog (mul_nonneg hx.le hK)
    have hid : p5U7TerminalPrimeMixedLossRate N alpha delta*(x/Real.log x) =
        (x*K*Real.log (N : ℝ))/Real.log x := by
      dsimp only [p5U7TerminalPrimeMixedLossRate,K,C,A,B]
      ring
    rw [hid]
    exact (le_div_iff₀ hlx).mpr (by nlinarith only [hm])
  have herror := p5U7TerminalPrimeMixed_abs_error N M a ell ha hN0 hMN hstart hxbase
  have hmain : 0 ≤ x/Real.log x := (div_pos hx hlx).le
  have hsmall := mul_le_mul_of_nonneg_right (add_le_add hPNT.le hLoss.le) hmain
  change |((p5U7MassPrimeWindow N M a ell).card : ℝ)-x/Real.log x| ≤
    epsilon*(x/Real.log x)
  change |((p5U7MassPrimeWindow N M a ell).card : ℝ)-x/Real.log x| ≤
    primeErrorEnvelope A*(x/Real.log x)+((ell : ℝ)+1+(N.primeFactors.card : ℝ)) at herror
  dsimp only [A] at herror
  nlinarith only [herror,hdeleted,hbudget,hsmall]

/-- Uniform leading-one LOWER transport, with the same original target
and generic powers before choosing M or marked arithmetic coordinates. -/
theorem p5U7TerminalPrimeMixed_eventually_uniform_lower (alpha delta epsilon : ℝ)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M a ell : ℕ, M ≤ N → 0 < a →
      (N : ℝ)^alpha ≤ (M : ℝ)/(a : ℝ) →
      (ell : ℝ) ≤ ((M : ℝ)/(a : ℝ))*(N : ℝ)^(-delta) →
      (1-epsilon)*(((M : ℝ)/(a : ℝ))/Real.log ((M : ℝ)/(a : ℝ))) ≤
        ((p5U7MassPrimeWindow N M a ell).card : ℝ) := by
  filter_upwards [p5U7TerminalPrimeMixed_eventually_uniform_abs alpha delta epsilon
    halpha hdelta hepsilon] with N hN
  intro M a ell hMN ha hx hell
  have hh := (abs_le.mp (hN M a ell hMN ha hx hell)).1
  nlinarith only [hh]
end
end ImbalancedChen
