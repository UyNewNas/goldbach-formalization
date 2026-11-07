import ImbalancedChen.P2EnhancedNonunitWordMass

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact actual bad-Gamma5 scalar kernel and equality-inclusive square gate.
This finite conversion does not supply its missing prime quadrature.
-/
namespace ImbalancedChen.P2EnhancedBadGamma5ConstantCutoff
noncomputable section
open Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedTrueNormalization P2EnhancedSwitchedUnsiftedSource
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedNonunitWordMass (rawScale)
open P2SeedOmegaLiteralFibre (a0)

def coordinate (R : ℝ) (p : ℕ) : ℝ := log (p : ℝ)/log R

theorem original_cutoff (Q : ℝ) (d : ℕ) :
    cutoff Q d (227/50) = (Q/d)^a0 := by norm_num [cutoff,a0]

theorem original_cutoff_log {Q : ℝ} {d : ℕ} (hR : 1 < Q/d) :
    log (cutoff Q d (227/50)) = a0*log (Q/d) := by
  rw [original_cutoff,log_rpow (zero_lt_one.trans hR)]

/-- The inherited cutoff is CONSTANT a0. No selected-prime coordinate
is used as a denominator in this kernel. -/
theorem actual_constant_argument {N d p q : ℕ} {Q : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q) (hR : 1 < Q/d) :
    log ((N : ℝ)/(d*p*q : ℕ))/log (cutoff Q d (227/50)) =
      (trueAlpha N Q d-coordinate (Q/d) p-coordinate (Q/d) q)/a0 := by
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have he : (N : ℝ)/(d*p*q : ℕ) = ((N : ℝ)/d)/((p : ℝ)*q) := by
    push_cast
    field_simp
  rw [he,log_div (div_pos hn0 hd0).ne' (mul_pos hp0 hq0).ne',
    log_mul hp0.ne' hq0.ne',original_cutoff_log hR]
  unfold trueAlpha coordinate
  field_simp [(log_pos hR).ne',show a0 ≠ 0 by norm_num [a0]]
  ring

/-- Exact full reciprocal product and true alpha for the arithmetic
ordinary rough main term. This is a scalar identity, not an integral cap. -/
theorem actual_constant_kernel {N d p q : ℕ} {Q : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hp : 0 < p) (hq : 0 < q) (hR : 1 < Q/d) :
    buchstab (log ((N : ℝ)/(d*p*q : ℕ))/log (cutoff Q d (227/50)))*
        ((N : ℝ)/(d*p*q : ℕ))/log (cutoff Q d (227/50)) =
      rawScale N Q d*(1/((p : ℝ)*q))*
        (buchstab ((trueAlpha N Q d-coordinate (Q/d) p-coordinate (Q/d) q)/a0)/a0) := by
  rw [actual_constant_argument hN hd hp hq hR,original_cutoff_log hR]
  unfold rawScale
  push_cast
  field_simp [(Nat.cast_pos.mpr hd : (0 : ℝ) < d).ne',
    (Nat.cast_pos.mpr hp : (0 : ℝ) < p).ne',
    (Nat.cast_pos.mpr hq : (0 : ℝ) < q).ne',
    (log_pos hR).ne',show a0 ≠ 0 by norm_num [a0]]
  ring

private theorem coordinate_power {R : ℝ} (hR : 1 < R) {p : ℕ} (hp : 0 < p) :
    R^(coordinate R p) = (p : ℝ) := by
  rw [coordinate,rpow_def_of_pos (zero_lt_one.trans hR)]
  have he : log R*(log (p : ℝ)/log R) = log (p : ℝ) := by
    field_simp [(log_pos hR).ne']
  rw [he,exp_log (Nat.cast_pos.mpr hp)]

/-- The original bad square includes equality on precisely 2u+v=1. -/
theorem actual_bad_square {d p q : ℕ} {Q : ℝ}
    (hd : 0 < d) (hp : 0 < p) (hq : 0 < q) (hR : 1 < Q/d) :
    badPair Q d [p,q] ↔ 1 ≤ 2*coordinate (Q/d) p+coordinate (Q/d) q := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hR0 := zero_lt_one.trans hR
  have he : (Q/d)^(2*coordinate (Q/d) p+coordinate (Q/d) q) = (p : ℝ)^2*q := by
    rw [rpow_add hR0,show 2*coordinate (Q/d) p = coordinate (Q/d) p*2 by ring,
      rpow_mul hR0.le,rpow_natCast,coordinate_power hR hp,coordinate_power hR hq]
  have hs : badPair Q d [p,q] ↔ Q/d ≤ (p : ℝ)^2*q := by
    change Q ≤ (d : ℝ)*(p : ℝ)^2*q ↔ Q/d ≤ (p : ℝ)^2*q
    rw [div_le_iff₀ hd0]
    constructor <;> intro h <;> nlinarith only [h]
  calc
    badPair Q d [p,q] ↔ Q/d ≤ (p : ℝ)^2*q := hs
    _ ↔ (Q/d)^(1 : ℝ) ≤
        (Q/d)^(2*coordinate (Q/d) p+coordinate (Q/d) q) := by rw [rpow_one,he]
    _ ↔ 1 ≤ 2*coordinate (Q/d) p+coordinate (Q/d) q := rpow_le_rpow_left_iff hR

end
end ImbalancedChen.P2EnhancedBadGamma5ConstantCutoff
