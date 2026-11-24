import ImbalancedChen.Part3DistributionTargets
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Exact log and power margins for the fixed-d E1 estimate. -/

namespace ImbalancedChen.Part3

/-- Logarithmic coordinate at the complete local convolution scale. -/
noncomputable def MediumAtom.logScaleCoord (d : MediumAtom) (y : ℝ) : ℝ :=
  Real.log y / Real.log d.scale

private theorem logCoord_mul (d : MediumAtom) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    d.logScaleCoord (x * y) = d.logScaleCoord x + d.logScaleCoord y := by
  simp only [MediumAtom.logScaleCoord, Real.log_mul hx.ne' hy.ne', add_div]

private theorem logCoord_div (d : MediumAtom) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    d.logScaleCoord (x / y) = d.logScaleCoord x - d.logScaleCoord y := by
  simp only [MediumAtom.logScaleCoord, Real.log_div hx.ne' hy.ne', sub_div]

private theorem logCoord_pow (d : MediumAtom) (x : ℝ) (k : ℕ) :
    d.logScaleCoord (x ^ k) = (k : ℝ) * d.logScaleCoord x := by
  simp only [MediumAtom.logScaleCoord, Real.log_pow, mul_div_assoc]

private theorem logCoord_rpow (d : MediumAtom) {x : ℝ} (hx : 0 < x) (k : ℝ) :
    d.logScaleCoord (x ^ k) = k * d.logScaleCoord x := by
  simp only [MediumAtom.logScaleCoord, Real.log_rpow hx, mul_div_assoc]

private theorem logCoord_scale (d : MediumAtom) (hX : 1 < d.scale) :
    d.logScaleCoord d.scale = 1 := div_self (Real.log_pos hX).ne'

private theorem one_lt_mediumScale {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B σ κ c0 d) : 1 < d.scale :=
  (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans hd.2.2.2.2.2.1

private theorem logCoord_mono (d : MediumAtom) (hX : 1 < d.scale) {x y : ℝ}
    (hx : 0 < x) (h : x < y) : d.logScaleCoord x < d.logScaleCoord y :=
  div_lt_div_of_pos_right (Real.log_lt_log hx h) (Real.log_pos hX)

private theorem logCoord_lt_iff (d : MediumAtom) (hX : 1 < d.scale) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) : d.logScaleCoord x < d.logScaleCoord y ↔ x < y := by
  rw [MediumAtom.logScaleCoord, MediumAtom.logScaleCoord, div_lt_div_iff_of_pos_right (Real.log_pos hX),
    Real.log_lt_log_iff hx hy]

/-- Equation (19), retaining the exact logarithmic contribution of the
moving-residue constant. The middle inequality here is the Ramanujan exponent. -/
theorem medium_e1_logMargins {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hc0 : 0 < c0) (hd : MediumAdmissible B σ κ c0 d) :
    let n := d.logScaleCoord d.U
    let q := d.logScaleCoord d.Q1
    let u := d.logScaleCoord d.Q2
    let v := d.logScaleCoord d.Q3
    n + q < 1 - 9 * σ ∧
      2 * n + q + u + v < 17 / 10 - 29 / 2 * σ ∧
      n + 5 / 2 * q + 3 * u + 3 * v <
        1021 / 512 - 147 / 8 * σ - (35 / 512) * d.logScaleCoord c0 := by
  have hX := one_lt_mediumScale hd
  rcases hd with ⟨hU, _hV, hQ1, hQ2, hQ3, _hloglog, ha, _haUpper, hq, h2, h3, _⟩
  have hU0 := zero_lt_one.trans_le hU
  have hQ10 := zero_lt_one.trans_le hQ1
  have hQ20 := zero_lt_one.trans_le hQ2
  have hQ30 := zero_lt_one.trans_le hQ3
  have hX0 := zero_lt_one.trans hX
  have ha0 : (0 : ℝ) < (d.residue.natAbs : ℝ) := (mul_pos hc0 hX0).trans_le ha
  have haNat : 0 < d.residue.natAbs := Nat.cast_pos.mp ha0
  have ha1 : (1 : ℝ) ≤ (d.residue.natAbs : ℝ) := by exact_mod_cast haNat
  have hcoord_nonneg {y : ℝ} (hy : 1 ≤ y) : 0 ≤ d.logScaleCoord y :=
    div_nonneg (Real.log_nonneg hy) (Real.log_pos hX).le
  have hn0 := hcoord_nonneg hU
  have hq0 := hcoord_nonneg hQ1
  have hu0 := hcoord_nonneg hQ2
  have hv0 := hcoord_nonneg hQ3
  have haL0 := hcoord_nonneg ha1
  have haL : d.logScaleCoord c0 + 1 ≤ d.logScaleCoord (d.residue.natAbs : ℝ) := by
    have h := div_le_div_of_nonneg_right (Real.log_le_log (mul_pos hc0 hX0) ha) (Real.log_pos hX).le
    change d.logScaleCoord (c0 * d.scale) ≤ _ at h
    rwa [logCoord_mul d hc0 hX0, logCoord_scale d hX] at h
  have hL1 := logCoord_mono d hX hQ10 hq
  have hL2 := logCoord_mono d hX (by positivity) h2
  have hL3 := logCoord_mono d hX (by positivity) h3
  simp (disch := positivity) only [logCoord_mul, logCoord_pow, logCoord_rpow, logCoord_scale d hX] at hL1 hL2 hL3
  norm_num at hL1 hL2 hL3 haL haL0
  dsimp only
  have hnUpper : 2 * d.logScaleCoord d.U < 1 - 8 * σ := by linarith only [hL2, hu0, hv0]
  have huUpper : d.logScaleCoord d.Q2 < (2 - 15 * σ) / 5 := by
    linarith only [hL3, haL0, hn0, hq0, hv0]
  have hsum : d.logScaleCoord d.Q1 + d.logScaleCoord d.Q2 + d.logScaleCoord d.Q3 <
      7 / 10 - 13 / 2 * σ := by linarith only [hL1, hL2, huUpper]
  refine ⟨by linarith only [hL1, hnUpper], by linarith only [hnUpper, hsum], ?_⟩
  linarith only [hL1, hL2, hL3, haL, hv0]

/-- The three Eq. (18) powers before the fixed `d` substitution. -/
theorem medium_e1_powerMargins {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hc0 : 0 < c0) (hd : MediumAdmissible B σ κ c0 d) :
    d.U * d.Q1 / d.scale < d.scale ^ (-9 * σ) ∧
      d.U ^ 2 * d.Q1 * d.Q2 * d.Q3 / d.scale ^ 2 < d.scale ^ (-3 / 10 - 29 / 2 * σ) ∧
      d.U * d.Q1 ^ (5 / 2 : ℝ) * d.Q2 ^ 3 * d.Q3 ^ 3 / d.scale ^ 2 <
        c0 ^ (-35 / 512 : ℝ) * d.scale ^ (-3 / 512 - 147 / 8 * σ) := by
  have hX := one_lt_mediumScale hd
  obtain ⟨h1, h2, h3⟩ := medium_e1_logMargins hc0 hd
  rcases hd with ⟨hU, _hV, hQ1, hQ2, hQ3, _⟩
  have hU0 := zero_lt_one.trans_le hU
  have hQ10 := zero_lt_one.trans_le hQ1
  have hQ20 := zero_lt_one.trans_le hQ2
  have hQ30 := zero_lt_one.trans_le hQ3
  have hX0 := zero_lt_one.trans hX
  constructor
  · apply (logCoord_lt_iff d hX (by positivity) (by positivity)).mp
    simp (disch := positivity) only [logCoord_mul, logCoord_div, logCoord_rpow, logCoord_scale d hX]
    linarith only [h1]
  constructor
  · apply (logCoord_lt_iff d hX (by positivity) (by positivity)).mp
    simp (disch := positivity) only [logCoord_mul, logCoord_div, logCoord_pow, logCoord_rpow, logCoord_scale d hX]
    linarith only [h2]
  · apply (logCoord_lt_iff d hX (by positivity) (by positivity)).mp
    simp (disch := positivity) only [logCoord_mul, logCoord_div, logCoord_pow, logCoord_rpow, logCoord_scale d hX]
    linarith only [h3]

/-- Real lower and upper endpoints of the literal closed dyadic carrier. -/
theorem e1FactorCarrier_bounds {L : ℝ} (hL : 0 ≤ L) {k : ℕ}
    (hk : k ∈ factorCarrier L) : L ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * L := by
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hk
  exact ⟨(Nat.le_ceil L).trans (Nat.cast_le.mpr hl),
    (Nat.cast_le.mpr hu).trans (Nat.floor_le (by positivity))⟩

/-- A nonempty product block supplies the bound on the complete physical
product of the split divisor and the rough-pair length. -/
theorem e1RoughPairLength_le {R Q₂ Q₃ : ℝ} (hR : 0 ≤ R) (hQ₂ : 0 ≤ Q₂) (hQ₃ : 0 ≤ Q₃)
    {k w q₂ q₃ : ℕ} (hw : w ∈ factorCarrier R) (h₂ : q₂ ∈ factorCarrier Q₂)
    (h₃ : q₃ ∈ factorCarrier Q₃) (he : k * w = q₂ * q₃) :
    (k : ℝ) * R ≤ 4 * Q₂ * Q₃ := by
  calc
    _ ≤ (k : ℝ) * w := mul_le_mul_of_nonneg_left (e1FactorCarrier_bounds hR hw).1 (by positivity)
    _ = (q₂ : ℝ) * q₃ := by exact_mod_cast he
    _ ≤ (2 * Q₂) * (2 * Q₃) := by
      exact mul_le_mul (e1FactorCarrier_bounds hQ₂ h₂).2 (e1FactorCarrier_bounds hQ₃ h₃).2
        (by positivity) (by positivity)
    _ = _ := by ring

/-- The three fixed-divisor brackets of (18). The factor `k` appears only
in the diagonal bracket. -/
theorem medium_e1_fixedBrackets {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hc0 : 0 < c0) (hd : MediumAdmissible B σ κ c0 d) (k : ℕ) (hk : 0 < k)
    (R : ℝ) (hR : 1 ≤ R) (hproduct : (k : ℝ) * R ≤ 4 * d.Q2 * d.Q3) :
    let Q := (k : ℝ) * d.Q1
    d.U * Q / d.scale ≤ (k : ℝ) * d.scale ^ (-9 * σ) ∧
      d.U * Q ^ (5 / 2 : ℝ) * R ^ 3 / d.scale ^ 2 ≤
        64 * (c0 ^ (-35 / 512 : ℝ) * d.scale ^ (-3 / 512 - 147 / 8 * σ)) ∧
      d.U ^ 2 * Q * R / d.scale ^ 2 ≤ 4 * d.scale ^ (-3 / 10 - 29 / 2 * σ) := by
  have hX := one_lt_mediumScale hd
  obtain ⟨hdiag, hram, hweil⟩ := medium_e1_powerMargins hc0 hd
  rcases hd with ⟨hU, _hV, hQ1, hQ2, hQ3, _⟩
  have hX0 := zero_lt_one.trans hX
  have hU0 := zero_lt_one.trans_le hU
  have hQ10 := zero_lt_one.trans_le hQ1
  have hQ20 := zero_lt_one.trans_le hQ2
  have hQ30 := zero_lt_one.trans_le hQ3
  have hR0 := zero_lt_one.trans_le hR
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpow : (k : ℝ) ^ (5 / 2 : ℝ) ≤ (k : ℝ) ^ 3 := by
    rw [← Real.rpow_ofNat]
    exact Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hQpow : ((k : ℝ) * d.Q1) ^ (5 / 2 : ℝ) ≤ (k : ℝ) ^ 3 * d.Q1 ^ (5 / 2 : ℝ) := by
    rw [Real.mul_rpow (by positivity) hQ10.le]
    exact mul_le_mul_of_nonneg_right hkpow (by positivity)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (k : ℝ) * (d.U * d.Q1 / d.scale) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiag.le (by positivity)
  · calc
      _ ≤ d.U * ((k : ℝ) ^ 3 * d.Q1 ^ (5 / 2 : ℝ)) * R ^ 3 / d.scale ^ 2 := by gcongr
      _ = d.U * d.Q1 ^ (5 / 2 : ℝ) * ((k : ℝ) * R) ^ 3 / d.scale ^ 2 := by ring
      _ ≤ d.U * d.Q1 ^ (5 / 2 : ℝ) * (4 * d.Q2 * d.Q3) ^ 3 / d.scale ^ 2 := by gcongr
      _ = 64 * (d.U * d.Q1 ^ (5 / 2 : ℝ) * d.Q2 ^ 3 * d.Q3 ^ 3 / d.scale ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hweil.le (by norm_num)
  · calc
      _ = d.U ^ 2 * d.Q1 * ((k : ℝ) * R) / d.scale ^ 2 := by ring
      _ ≤ d.U ^ 2 * d.Q1 * (4 * d.Q2 * d.Q3) / d.scale ^ 2 := by gcongr
      _ = 4 * (d.U ^ 2 * d.Q1 * d.Q2 * d.Q3 / d.scale ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hram.le (by norm_num)

/-- The bracket of (18) at the original real scales. -/
noncomputable def e1Equation18Bracket (X N Q R : ℝ) : ℝ :=
  N * Q / X + N * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2 + N ^ 2 * Q * R / X ^ 2

/-- Absorb the selectable Eq. (18) exponent and the fixed divisor's
subpower factor while retaining at least `2σ` in the squared bound. -/
theorem medium_e1_bracketSubpower {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hσ : 0 < σ) (hc0 : 0 < c0) (hd : MediumAdmissible B σ κ c0 d)
    (k : ℕ) (hk : 0 < k) (hksub : (k : ℝ) ≤ d.scale ^ σ)
    (R : ℝ) (hR : 1 ≤ R) (hproduct : (k : ℝ) * R ≤ 4 * d.Q2 * d.Q3)
    (ε : ℝ) (hε : ε ≤ σ) :
    d.scale ^ ε * e1Equation18Bracket d.scale d.U ((k : ℝ) * d.Q1) R ≤
      (5 + 64 * c0 ^ (-35 / 512 : ℝ)) * d.scale ^ (-2 * σ) := by
  have hX := one_lt_mediumScale hd
  have hX0 := zero_lt_one.trans hX
  let X := d.scale
  let Q := (k : ℝ) * d.Q1
  let K := c0 ^ (-35 / 512 : ℝ)
  obtain ⟨hdiag, hweil, hram⟩ := medium_e1_fixedBrackets hc0 hd k hk R hR hproduct
  have hdiag' : X ^ ε * (d.U * Q / X) ≤ X ^ (-2 * σ) := by
    calc
      _ ≤ X ^ ε * ((k : ℝ) * X ^ (-9 * σ)) := mul_le_mul_of_nonneg_left hdiag (by positivity)
      _ ≤ X ^ ε * (X ^ σ * X ^ (-9 * σ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hksub (by positivity)) (by positivity)
      _ = X ^ (ε + (σ + (-9 * σ))) := by rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hweil' : X ^ ε * (d.U * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2) ≤
      (64 * K) * X ^ (-2 * σ) := by
    have hh : X ^ ε * X ^ (-3 / 512 - 147 / 8 * σ) ≤ X ^ (-2 * σ) := by
      rw [← Real.rpow_add hX0]
      exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
    calc
      _ ≤ X ^ ε * (64 * (K * X ^ (-3 / 512 - 147 / 8 * σ))) :=
        mul_le_mul_of_nonneg_left hweil (by positivity)
      _ = (64 * K) * (X ^ ε * X ^ (-3 / 512 - 147 / 8 * σ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by dsimp only [K]; positivity)
  have hram' : X ^ ε * (d.U ^ 2 * Q * R / X ^ 2) ≤ 4 * X ^ (-2 * σ) := by
    have hh : X ^ ε * X ^ (-3 / 10 - 29 / 2 * σ) ≤ X ^ (-2 * σ) := by
      rw [← Real.rpow_add hX0]
      exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
    calc
      _ ≤ X ^ ε * (4 * X ^ (-3 / 10 - 29 / 2 * σ)) := mul_le_mul_of_nonneg_left hram (by positivity)
      _ = 4 * (X ^ ε * X ^ (-3 / 10 - 29 / 2 * σ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  change X ^ ε * e1Equation18Bracket X d.U Q R ≤ (5 + 64 * K) * X ^ (-2 * σ)
  unfold e1Equation18Bracket
  rw [mul_add, mul_add]
  linarith only [hdiag', hweil', hram']

/-- The bound from (18) at fixed `d`, once its actual squared estimate
has been provided. -/
theorem medium_e1_fixedBlock_le {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hσ : 0 < σ) (hc0 : 0 < c0) (hd : MediumAdmissible B σ κ c0 d)
    (k : ℕ) (hk : 0 < k) (hksub : (k : ℝ) ≤ d.scale ^ σ)
    (R : ℝ) (hR : 1 ≤ R) (hproduct : (k : ℝ) * R ≤ 4 * d.Q2 * d.Q3)
    (ε C : ℝ) (hε : ε ≤ σ) (hC : 0 ≤ C) (Z : ℂ)
    (hZ : ‖Z‖ ^ 2 ≤ C * d.scale ^ ε * (d.U ^ 4 / ((k : ℝ) * d.Q1) ^ 2) *
      e1Equation18Bracket d.scale d.U ((k : ℝ) * d.Q1) R) :
    ‖Z‖ ≤ Real.sqrt (C * (5 + 64 * c0 ^ (-35 / 512 : ℝ))) *
      (d.U ^ 2 / ((k : ℝ) * d.Q1)) * d.scale ^ (-σ) := by
  have hX0 := zero_lt_one.trans (one_lt_mediumScale hd)
  have hU0 := zero_lt_one.trans_le hd.1
  have hQ10 := zero_lt_one.trans_le hd.2.2.1
  let Q := (k : ℝ) * d.Q1
  let K := 5 + 64 * c0 ^ (-35 / 512 : ℝ)
  have hQ0 : 0 < Q := mul_pos (Nat.cast_pos.mpr hk) hQ10
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbracket := medium_e1_bracketSubpower hσ hc0 hd k hk hksub R hR hproduct ε hε
  have hexp : d.scale ^ (-2 * σ) = (d.scale ^ (-σ)) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hX0]
    congr 1
    ring
  change ‖Z‖ ≤ Real.sqrt (C * K) * (d.U ^ 2 / Q) * d.scale ^ (-σ)
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ C * d.scale ^ ε * (d.U ^ 4 / Q ^ 2) * e1Equation18Bracket d.scale d.U Q R := hZ
    _ = (C * (d.U ^ 4 / Q ^ 2)) * (d.scale ^ ε * e1Equation18Bracket d.scale d.U Q R) := by ring
    _ ≤ (C * (d.U ^ 4 / Q ^ 2)) * (K * d.scale ^ (-2 * σ)) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by
      simp only [hexp, mul_pow, Real.sq_sqrt (mul_nonneg hC hK), div_pow]
      ring

open Finset
open scoped BigOperators

/-- A split divisor in the closed block satisfies the actual `D/k` bound
and inherits the remaining power reserve. -/
theorem e1DyadicSplitDivisor_bounds {X D σ : ℝ} (hX : 0 < X) (hD : 1 ≤ D)
    (hDsub : D ≤ X ^ (σ / 2)) (hXlarge : 2 ≤ X ^ (σ / 2))
    {k : ℕ} (hk : k ∈ factorCarrier D) :
    0 < k ∧ D / (k : ℝ) ≤ 1 ∧ (k : ℝ) ≤ X ^ σ := by
  obtain ⟨hlo, hhi⟩ := e1FactorCarrier_bounds (zero_le_one.trans hD) hk
  have hk0 : (0 : ℝ) < (k : ℝ) := (zero_lt_one.trans_le hD).trans_le hlo
  refine ⟨Nat.cast_pos.mp hk0, by simpa using (div_le_iff₀ hk0).mpr (by simpa using hlo), ?_⟩
  calc
    _ ≤ 2 * D := hhi
    _ ≤ X ^ (σ / 2) * X ^ (σ / 2) :=
      mul_le_mul hXlarge hDsub (zero_le_one.trans hD) (by positivity)
    _ = _ := by rw [← Real.rpow_add hX]; congr 1; ring

/-- The exact integer closed block has harmonic mass at most two. -/
theorem e1FactorCarrier_sum_inv_le_two {D : ℝ} (hD : 1 ≤ D) :
    (∑ k ∈ factorCarrier D, (k : ℝ)⁻¹) ≤ 2 := by
  have hD0 := zero_lt_one.trans_le hD
  have hS : factorCarrier D ⊆ Ioc 0 ⌊2 * D⌋₊ := by
    intro k hk
    have hlo := (e1FactorCarrier_bounds hD0.le hk).1
    exact mem_Ioc.mpr ⟨Nat.cast_pos.mp (hD0.trans_le hlo), (mem_Icc.mp hk).2⟩
  have hcard : ((factorCarrier D).card : ℝ) ≤ 2 * D := by
    have hc : (factorCarrier D).card ≤ ⌊2 * D⌋₊ := by
      simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hS
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by positivity))
  calc
    _ ≤ ∑ _k ∈ factorCarrier D, D⁻¹ := by
      apply sum_le_sum
      intro k hk
      simpa only [one_div] using one_div_le_one_div_of_le hD0 (e1FactorCarrier_bounds hD0.le hk).1
    _ = ((factorCarrier D).card : ℝ) * D⁻¹ := by simp
    _ ≤ (2 * D) * D⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hD0.ne', mul_one]

/-- The fixed-divisor estimates sum on their actual common dyadic block.
This is the scalar summation and the final `D` payment in (20). -/
theorem e1DyadicBlock_sum_le {X N Q D σ C : ℝ} (hX : 0 < X) (hQ : 0 < Q)
    (hD : 1 ≤ D) (hC : 0 ≤ C) (hDsub : D ≤ X ^ (σ / 2))
    (E : ℕ → ℂ)
    (hE : ∀ k ∈ factorCarrier D,
      ‖E k‖ ≤ C * (N ^ 2 / ((k : ℝ) * Q)) * X ^ (-σ)) :
    ‖∑ k ∈ factorCarrier D, E k‖ ≤ (2 * C) * (N ^ 2 / (D * Q)) * X ^ (-σ / 2) := by
  have hD0 := zero_lt_one.trans_le hD
  let L := C * (N ^ 2 / Q) * X ^ (-σ)
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hpoint (k : ℕ) (hk : k ∈ factorCarrier D) : ‖E k‖ ≤ L * (k : ℝ)⁻¹ := by
    have hk0 : (0 : ℝ) < (k : ℝ) := hD0.trans_le (e1FactorCarrier_bounds hD0.le hk).1
    refine (hE k hk).trans_eq ?_
    dsimp only [L]
    field_simp [hk0.ne', hQ.ne']
  have hpay : D * X ^ (-σ) ≤ X ^ (-σ / 2) := by
    calc
      _ ≤ X ^ (σ / 2) * X ^ (-σ) := mul_le_mul_of_nonneg_right hDsub (by positivity)
      _ = _ := by rw [← Real.rpow_add hX]; congr 1; ring
  calc
    _ ≤ ∑ k ∈ factorCarrier D, ‖E k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ factorCarrier D, L * (k : ℝ)⁻¹ := sum_le_sum hpoint
    _ = L * ∑ k ∈ factorCarrier D, (k : ℝ)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ L * 2 := mul_le_mul_of_nonneg_left (e1FactorCarrier_sum_inv_le_two hD) hL0
    _ = (2 * C) * (N ^ 2 / (D * Q)) * (D * X ^ (-σ)) := by
      dsimp only [L]
      field_simp [hD0.ne', hQ.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hpay (by positivity)

/-- Uniformly sum fixed split-divisor instances of (18) with their original
physical rough-pair lengths. The squared estimates remain explicit. -/
theorem medium_e1_dyadicBlock_le {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hσ : 0 < σ) (hc0 : 0 < c0) (hd : MediumAdmissible B σ κ c0 d)
    (D : ℝ) (hD : 1 ≤ D) (hDsub : D ≤ d.scale ^ (σ / 2)) (hXlarge : 2 ≤ d.scale ^ (σ / 2))
    (ε C : ℝ) (hε : ε ≤ σ) (hC : 0 ≤ C) (R : ℕ → ℝ) (E : ℕ → ℂ)
    (hR : ∀ k ∈ factorCarrier D, 1 ≤ R k ∧ (k : ℝ) * R k ≤ 4 * d.Q2 * d.Q3)
    (hE : ∀ k ∈ factorCarrier D,
      ‖E k‖ ^ 2 ≤ C * d.scale ^ ε * (d.U ^ 4 / ((k : ℝ) * d.Q1) ^ 2) *
        e1Equation18Bracket d.scale d.U ((k : ℝ) * d.Q1) (R k)) :
    ‖∑ k ∈ factorCarrier D, E k‖ ≤
      (2 * Real.sqrt (C * (5 + 64 * c0 ^ (-35 / 512 : ℝ)))) *
        (d.U ^ 2 / (D * d.Q1)) * d.scale ^ (-σ / 2) := by
  have hX0 := zero_lt_one.trans (one_lt_mediumScale hd)
  have hQ0 := zero_lt_one.trans_le hd.2.2.1
  apply e1DyadicBlock_sum_le hX0 hQ0 hD (Real.sqrt_nonneg _) hDsub
  intro k hk
  obtain ⟨hk0, _, hksub⟩ := e1DyadicSplitDivisor_bounds hX0 hD hDsub hXlarge hk
  obtain ⟨hRk, hprod⟩ := hR k hk
  exact medium_e1_fixedBlock_le hσ hc0 hd k hk0 hksub (R k) hRk hprod ε C hε hC (E k) (hE k hk)

open Filter in
/-- The retained smooth-part bound `y²` supplies the needed dyadic divisor
reserve uniformly once the complete scale is large. -/
theorem eventually_e1SplitScale_reserve {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ X : ℝ in atTop,
      (X ^ (1 / Real.log (Real.log X))) ^ 2 ≤ X ^ (σ / 2) ∧ 2 ≤ X ^ (σ / 2) := by
  have hhalf : 0 < σ / 2 := by positivity
  filter_upwards [((Real.tendsto_log_atTop).comp Real.tendsto_log_atTop).eventually_ge_atTop
      (max 1 (4 / σ)), (tendsto_rpow_atTop hhalf).eventually_ge_atTop 2,
      eventually_ge_atTop (1 : ℝ)] with X hlog hXlarge hX
  change max 1 (4 / σ) ≤ Real.log (Real.log X) at hlog
  have hlog0 : 0 < Real.log (Real.log X) :=
    zero_lt_one.trans_le ((le_max_left _ _).trans hlog)
  have hs := (div_le_iff₀ hσ).mp ((le_max_right 1 (4 / σ)).trans hlog)
  refine ⟨?_, hXlarge⟩
  rw [← Real.rpow_mul_natCast (zero_le_one.trans hX)]
  apply Real.rpow_le_rpow_of_exponent_le hX
  change (1 / Real.log (Real.log X)) * 2 ≤ σ / 2
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ hlog0).mpr (by nlinarith only [hs])

end ImbalancedChen.Part3
