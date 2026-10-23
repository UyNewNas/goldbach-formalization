import ImbalancedChen.Part3SharedFirstFactorSmallPairedSupportedReduction
import ImbalancedChen.Part3SharedFirstFactorDifferenceReciprocity

/-!
# Exact signed difference licenses for the actual first factor

The literal small paired-gcd cutoff excludes equal original row integers.
For every compatible first factor in the original carrier, the signed quotient
is therefore nonzero and recovers that first factor exactly. The original
carrier filters coprimality with the signed residue; it does not assert that
its members are prime.

The bound uses the original two row intervals and retains the original Q1,
the paired gcd, and the tail-product gcd. No additive counting term is used.
This file proves only finite arithmetic licenses. It asserts no weighted sum
identity, frequency-window separation, or spectral estimate.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical

namespace SmallCorePrimeDifferenceReindex

private theorem factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) :
    0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hceil : 1 ≤ Nat.ceil Q := by
    exact_mod_cast hQ.trans (Nat.le_ceil Q)
  have hnlo : Q ≤ (n : ℝ) :=
    (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  have hnhi : (n : ℝ) ≤ 2 * Q :=
    (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * Q))
  exact ⟨by omega, hnlo, hnhi⟩

private theorem row_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l : (ℕ × ℕ) × ℕ} (hl : l ∈ d.sharedFirstFactorRows) :
    0 < l.1.1 * l.1.2 ∧ 0 < l.2 ∧
      d.U ≤ (l.2 : ℝ) ∧ (l.2 : ℝ) ≤ 2 * d.U := by
  obtain ⟨hf, hN⟩ := Finset.mem_product.mp hl
  obtain ⟨h₂, h₃⟩ := Finset.mem_product.mp hf
  change l.2 ∈ factorCarrier d.U at hN
  have h₂bounds := factor_bounds hd.2.2.2.1 h₂
  have h₃bounds := factor_bounds hd.2.2.2.2.1 h₃
  have hNbounds := factor_bounds hd.1 hN
  exact ⟨Nat.mul_pos h₂bounds.1 h₃bounds.1, hNbounds.1, hNbounds.2⟩

private theorem gcd_mul_difference (N₁ N₂ : ℕ) :
    ((N₁.gcd N₂ : ℕ) : ℤ) *
        (((N₁ / N₁.gcd N₂ : ℕ) : ℤ) - ((N₂ / N₁.gcd N₂ : ℕ) : ℤ)) =
      (N₁ : ℤ) - N₂ := by
  have hleft : N₁.gcd N₂ * (N₁ / N₁.gcd N₂) = N₁ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left N₁ N₂)
  have hright : N₁.gcd N₂ * (N₂ / N₁.gcd N₂) = N₂ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right N₁ N₂)
  have hleftZ : ((N₁.gcd N₂ : ℕ) : ℤ) * (N₁ / N₁.gcd N₂ : ℕ) = N₁ := by
    exact_mod_cast hleft
  have hrightZ : ((N₁.gcd N₂ : ℕ) : ℤ) * (N₂ / N₁.gcd N₂ : ℕ) = N₂ := by
    exact_mod_cast hright
  rw [mul_sub, hleftZ, hrightZ]

private theorem compatible_difference_mul
    {p v w N₁ N₂ : ℕ}
    (hp : 0 < p) (hv : 0 < v) (hw : 0 < w)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hc : ComplexCRT.Compatible (p * v) (p * w) N₁ N₂) :
    ((p * v.gcd w : ℕ) : ℤ) *
        ((((N₁ / N₁.gcd N₂ : ℕ) : ℤ) - ((N₂ / N₁.gcd N₂ : ℕ) : ℤ)) /
          ((p * v.gcd w : ℕ) : ℤ)) =
      ((N₁ / N₁.gcd N₂ : ℕ) : ℤ) - ((N₂ / N₁.gcd N₂ : ℕ) : ℤ) := by
  have hdata := sharedDifferenceData_licenses hp hv hw hN₁ hN₂ hc (0 : ℤ)
  dsimp only at hdata
  rcases hdata with ⟨hg, _, _, _, _, _, _, _, _, hN₁eq, _, _, _, _, _, _, _, _, _, hf, _⟩
  have hsplit :
      CanonicalReciprocalData.supportedPart (N₁ / N₁.gcd N₂) (N₁.gcd N₂) *
          CanonicalReciprocalData.coprimePart (N₁ / N₁.gcd N₂) (N₁.gcd N₂) =
        N₁ / N₁.gcd N₂ := by
    apply Nat.mul_left_cancel hg
    calc
      _ = N₁ := by simpa only [mul_assoc] using hN₁eq.symm
      _ = N₁.gcd N₂ * (N₁ / N₁.gcd N₂) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left N₁ N₂)).symm
  have hsplitZ :
      (CanonicalReciprocalData.supportedPart (N₁ / N₁.gcd N₂) (N₁.gcd N₂) : ℤ) *
          CanonicalReciprocalData.coprimePart (N₁ / N₁.gcd N₂) (N₁.gcd N₂) =
        ((N₁ / N₁.gcd N₂ : ℕ) : ℤ) := by
    exact_mod_cast hsplit
  simpa only [hsplitZ] using hf

end SmallCorePrimeDifferenceReindex

/-- Exact arithmetic on the literal compatible first-factor carrier. -/
theorem MediumAtom.smallCore_prime_to_signed_difference_licenses
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ) × ℕ}
    (hl : l ∈ d.sharedFirstFactorRows) (hl' : l' ∈ d.sharedFirstFactorRows)
    (hsmall : (l.2.gcd l'.2 : ℝ) ≤ d.scale ^ (sigma / 4)) :
    let g := l.2.gcd l'.2
    let D := (l.1.1 * l.1.2).gcd (l'.1.1 * l'.1.2)
    let Delta : ℤ := ((l.2 / g : ℕ) : ℤ) - ((l'.2 / g : ℕ) : ℤ)
    let P := d.primitiveFirstFactorCarrier.filter (fun p =>
      ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
        (p * (l'.1.1 * l'.1.2)) l.2 l'.2)
    let f : ℕ → ℤ := fun p => Delta / ((p * D : ℕ) : ℤ)
    0 < g ∧ 0 < D ∧ Delta ≠ 0 ∧
      (∀ p ∈ P, f p ≠ 0 ∧ ((p * D : ℕ) : ℤ) * f p = Delta ∧
        Delta.natAbs = p * D * (f p).natAbs ∧
        p = Delta.natAbs / (D * (f p).natAbs) ∧
        ((f p).natAbs : ℝ) ≤ d.U / ((g : ℝ) * (D : ℝ) * d.Q1) ∧
        (0 < f p ↔ 0 < Delta) ∧ (f p < 0 ↔ Delta < 0)) ∧
      Set.InjOn f (P : Set ℕ) := by
  let g := l.2.gcd l'.2
  let D := (l.1.1 * l.1.2).gcd (l'.1.1 * l'.1.2)
  let Delta : ℤ := ((l.2 / g : ℕ) : ℤ) - ((l'.2 / g : ℕ) : ℤ)
  let P := d.primitiveFirstFactorCarrier.filter (fun p =>
    ComplexCRT.Compatible (p * (l.1.1 * l.1.2))
      (p * (l'.1.1 * l'.1.2)) l.2 l'.2)
  let f : ℕ → ℤ := fun p => Delta / ((p * D : ℕ) : ℤ)
  have hleft := SmallCorePrimeDifferenceReindex.row_bounds hd hl
  have hright := SmallCorePrimeDifferenceReindex.row_bounds hd hl'
  have hg : 0 < g := Nat.gcd_pos_of_pos_left l'.2 hleft.2.1
  have hD : 0 < D := Nat.gcd_pos_of_pos_left (l'.1.1 * l'.1.2) hleft.1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hx : 1 < d.scale :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos (1 : ℝ))).trans hd.2.2.2.2.2.1
  have hcut : d.scale ^ (sigma / 4) < d.U :=
    (Real.rpow_lt_rpow_of_exponent_lt hx (by linarith : sigma / 4 < sigma)).trans_le
      (PairedAlphaDeletion.actual_geometry_bounds hd).1
  have hne : l.2 ≠ l'.2 := by
    intro heq
    have hsmall' : (l'.2 : ℝ) ≤ d.scale ^ (sigma / 4) := by
      simpa only [heq, Nat.gcd_self] using hsmall
    linarith [hright.2.2.1]
  have hDeltaeq : (g : ℤ) * Delta = (l.2 : ℤ) - l'.2 :=
    SmallCorePrimeDifferenceReindex.gcd_mul_difference l.2 l'.2
  have hDelta : Delta ≠ 0 := by
    intro hzero
    have hN : (l.2 : ℤ) = (l'.2 : ℤ) := by
      rw [hzero, mul_zero] at hDeltaeq
      omega
    exact hne (by exact_mod_cast hN)
  have hDeltaR : (g : ℝ) * (Delta : ℝ) = (l.2 : ℝ) - l'.2 := by
    exact_mod_cast hDeltaeq
  have habsR : (Delta.natAbs : ℝ) = |(Delta : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hDeltaBound : (g : ℝ) * (Delta.natAbs : ℝ) ≤ d.U := by
    calc
      _ = |(g : ℝ) * (Delta : ℝ)| := by
        rw [habsR, abs_mul,
          (show |(g : ℝ)| = (g : ℝ) from abs_of_nonneg (Nat.cast_nonneg g))]
      _ = |(l.2 : ℝ) - l'.2| := by rw [hDeltaR]
      _ ≤ d.U := abs_le.mpr ⟨by linarith [hleft.2.2.1, hright.2.2.2],
        by linarith [hright.2.2.1, hleft.2.2.2]⟩
  have hlicenses : ∀ p ∈ P, f p ≠ 0 ∧ ((p * D : ℕ) : ℤ) * f p = Delta ∧
      Delta.natAbs = p * D * (f p).natAbs ∧
      p = Delta.natAbs / (D * (f p).natAbs) ∧
      ((f p).natAbs : ℝ) ≤ d.U / ((g : ℝ) * (D : ℝ) * d.Q1) ∧
      (0 < f p ↔ 0 < Delta) ∧ (f p < 0 ↔ Delta < 0) := by
    intro p hp
    obtain ⟨hpCarrier, hc⟩ := Finset.mem_filter.mp hp
    have hpFactor := (Finset.mem_filter.mp hpCarrier).1
    have hpBounds := SmallCorePrimeDifferenceReindex.factor_bounds hd.2.2.1 hpFactor
    have hidentity : ((p * D : ℕ) : ℤ) * f p = Delta :=
      SmallCorePrimeDifferenceReindex.compatible_difference_mul hpBounds.1
        hleft.1 hright.1 hleft.2.1 hright.2.1 hc
    have hfn : f p ≠ 0 := by
      intro hzero
      apply hDelta
      simpa only [hzero, mul_zero] using hidentity.symm
    have habs : Delta.natAbs = p * D * (f p).natAbs := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
        (congrArg Int.natAbs hidentity).symm
    have hden : 0 < D * (f p).natAbs :=
      Nat.mul_pos hD (Int.natAbs_pos.mpr hfn)
    have hinverse : p = Delta.natAbs / (D * (f p).natAbs) := by
      rw [habs, mul_assoc, Nat.mul_div_cancel _ hden]
    have habsReal : (Delta.natAbs : ℝ) = (p : ℝ) * D * (f p).natAbs := by
      exact_mod_cast habs
    have hproduct : (g : ℝ) * p * D * (f p).natAbs ≤ d.U := by
      calc
        _ = (g : ℝ) * (Delta.natAbs : ℝ) := by rw [habsReal]; ring
        _ ≤ d.U := hDeltaBound
    have hbound : ((f p).natAbs : ℝ) ≤ d.U / ((g : ℝ) * (D : ℝ) * d.Q1) := by
      apply (le_div_iff₀ (by positivity : 0 < (g : ℝ) * (D : ℝ) * d.Q1)).mpr
      calc
        _ = ((g : ℝ) * D * (f p).natAbs) * d.Q1 := by ring
        _ ≤ ((g : ℝ) * D * (f p).natAbs) * p :=
          mul_le_mul_of_nonneg_left hpBounds.2.1 (by positivity)
        _ = (g : ℝ) * p * D * (f p).natAbs := by ring
        _ ≤ d.U := hproduct
    have hpD : (0 : ℤ) < (p * D : ℕ) := by
      exact_mod_cast Nat.mul_pos hpBounds.1 hD
    have hpos : 0 < f p ↔ 0 < Delta := by
      calc
        0 < f p ↔ ((p * D : ℕ) : ℤ) * 0 < ((p * D : ℕ) : ℤ) * f p :=
          (Int.mul_lt_mul_left hpD).symm
        _ ↔ 0 < Delta := by rw [mul_zero, hidentity]
    have hneg : f p < 0 ↔ Delta < 0 := by
      calc
        f p < 0 ↔ ((p * D : ℕ) : ℤ) * f p < ((p * D : ℕ) : ℤ) * 0 :=
          (Int.mul_lt_mul_left hpD).symm
        _ ↔ Delta < 0 := by rw [mul_zero, hidentity]
    exact ⟨hfn, hidentity, habs, hinverse, hbound, hpos, hneg⟩
  refine ⟨hg, hD, hDelta, hlicenses, ?_⟩
  intro p hp q hq heq
  change f p = f q at heq
  calc
    p = Delta.natAbs / (D * (f p).natAbs) := (hlicenses p hp).2.2.2.1
    _ = Delta.natAbs / (D * (f q).natAbs) := by rw [heq]
    _ = q := (hlicenses q hq).2.2.2.1.symm

end

end ImbalancedChen.Part3
