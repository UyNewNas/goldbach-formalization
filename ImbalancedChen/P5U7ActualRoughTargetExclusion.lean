import ImbalancedChen.P5U7OriginalSourceMass
import ImbalancedChen.ChenInitialCorrectionBudget
import Mathlib.Order.Interval.Finset.Nat

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual target exclusion for rough cofactors. Every excluded cofactor is
covered by an ACTUAL prime divisor of N and a positive quotient <=x/z.
This pays all target-divisor losses without assuming a source asymptotic.
-/

namespace ImbalancedChen

noncomputable section

open LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7ActualBadRough (N : ℕ) (x z : ℝ) : Finset ℕ :=
  (roughNumbers x z).filter fun n => ¬Nat.Coprime n N

theorem p5U7ActualBadRough_card_le {N : ℕ} (hN : 0 < N) {x z : ℝ}
    (hx : 0 ≤ x) (hz : 0 < z) :
    ((p5U7ActualBadRough N x z).card : ℝ) ≤ (N.primeFactors.card : ℝ) * (x / z) := by
  let K : Finset ℕ := Finset.Icc 1 (Nat.floor (x / z))
  let fibres : ℕ → Finset ℕ := fun p => K.image (fun k => p * k)
  have hcover : p5U7ActualBadRough N x z ⊆ N.primeFactors.biUnion fibres := by
    intro n hn
    obtain ⟨hnR, hnC⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnx, hnrough⟩ := mem_roughNumbers.mp hnR
    obtain ⟨p, hp, hpn, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnC
    have hpF : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hN.ne'⟩
    have hzp : z ≤ (p : ℝ) := hnrough p hp hpn
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
    have hk0 : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp.pos
    have hkR0 : (0 : ℝ) ≤ (n / p : ℕ) := Nat.cast_nonneg _
    have hmulR : (p : ℝ) * ((n / p : ℕ) : ℝ) = n := by exact_mod_cast hmul
    have hkx : ((n / p : ℕ) : ℝ) ≤ x / z := by
      apply (le_div_iff₀ hz).mpr
      have hh := mul_le_mul_of_nonneg_right hzp hkR0
      nlinarith only [hh, hmulR, hnx]
    have hk : n / p ∈ K := Finset.mem_Icc.mpr ⟨hk0,
      (Nat.le_floor_iff (div_nonneg hx hz.le)).mpr hkx⟩
    exact Finset.mem_biUnion.mpr ⟨p, hpF, Finset.mem_image.mpr ⟨n / p, hk, hmul⟩⟩
  have hK : K.card = Nat.floor (x / z) := by simp [K]
  have hcard : (p5U7ActualBadRough N x z).card ≤ N.primeFactors.card * Nat.floor (x / z) :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul _ _ _
      (fun p _ => (Finset.card_image_le).trans_eq hK))
  have hcast : ((p5U7ActualBadRough N x z).card : ℝ) ≤
      (N.primeFactors.card : ℝ) * (Nat.floor (x / z) : ℝ) := by exact_mod_cast hcard
  exact hcast.trans (mul_le_mul_of_nonneg_left (Nat.floor_le (div_nonneg hx hz.le)) (Nat.cast_nonneg _))

/-- The existing true distinct-prime product bound gives the logarithmic
target cost; no prime-factor counting estimate is an input. -/
theorem p5U7ActualBadRough_card_le_log {N : ℕ} (hN : 0 < N) {x z : ℝ}
    (hx : 0 ≤ x) (hz : 0 < z) :
    ((p5U7ActualBadRough N x z).card : ℝ) ≤
      (Real.log (N : ℝ) / Real.log 2) * (x / z) :=
  (p5U7ActualBadRough_card_le hN hx hz).trans
    (mul_le_mul_of_nonneg_right (chen_primeFactors_card_le_log hN) (div_nonneg hx hz.le))

end

end ImbalancedChen
