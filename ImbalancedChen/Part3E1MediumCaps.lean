import ImbalancedChen.Part3E1MediumMargins

/-! Polynomial caps for consuming equation (18) in the shifted dyadic cells. -/

namespace ImbalancedChen.Part3

/-- An occupied dyadic cell meeting the physical smooth window has a
comparable original `q₀` scale. -/
theorem e1SmoothQCell_comparable {Q₁ q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    {q : ℕ} (hq : q ∈ factorCarrier q₀) (hlo : Q₁ / 2 ≤ (q : ℝ))
    (hhi : (q : ℝ) ≤ 5 * Q₁ / 2) : Q₁ / 4 ≤ q₀ ∧ q₀ ≤ 5 * Q₁ / 2 := by
  obtain ⟨hqlo, hqhi⟩ := e1FactorCarrier_bounds hq₀ hq
  exact ⟨by linarith only [hlo, hqhi], hqlo.trans hhi⟩

/-- The first two admissibility monomials place `Q₁` and `Q₂Q₃` below the
complete scale. -/
theorem medium_e1_factorLengths_le_scale {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hσ : 0 ≤ σ) (hX : 1 ≤ d.scale) (hd : MediumAdmissible B σ κ c0 d) :
    d.Q1 ≤ d.scale ∧ d.Q2 * d.Q3 ≤ d.scale := by
  rcases hd with ⟨hU, hV, _hQ₁, hQ₂, hQ₃, _hscale, _hlower, _hupper, hq, hp, _⟩
  have hU0 := zero_lt_one.trans_le hU
  have hQ₂0 := zero_lt_one.trans_le hQ₂
  have hQ₃0 := zero_lt_one.trans_le hQ₃
  constructor
  · have hp : d.scale ^ (-σ) ≤ 1 :=
      (Real.rpow_le_rpow_of_exponent_le hX (neg_nonpos.mpr hσ)).trans_eq (Real.rpow_zero _)
    calc
      _ ≤ d.U * d.scale ^ (-σ) := hq.le
      _ ≤ d.U := mul_le_of_le_one_right hU0.le hp
      _ ≤ d.scale := le_mul_of_one_le_right hU0.le hV
  · have hU2 : (1 : ℝ) ≤ d.U ^ 2 := one_le_pow₀ hU
    have hQ₃2 : d.Q3 ≤ d.Q3 ^ 2 := by
      rw [pow_two]
      exact le_mul_of_one_le_right hQ₃0.le hQ₃
    calc
      _ ≤ d.U ^ 2 * d.Q2 * d.Q3 ^ 2 :=
        mul_le_mul (le_mul_of_one_le_left hQ₂0.le hU2) hQ₃2 hQ₃0.le (by positivity)
      _ ≤ d.scale ^ (1 - 8 * σ) := hp.le
      _ ≤ d.scale :=
        (Real.rpow_le_rpow_of_exponent_le hX (by linarith)).trans_eq (Real.rpow_one _)

/-- For the shifted, fixed-divisor E1 cell one common polynomial exponent
licenses both of the source estimate's support bounds. -/
theorem medium_e1_realDyadic_polynomialCaps {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hσ : 0 ≤ σ) (hX : 2 ≤ d.scale) (hd : MediumAdmissible B σ κ c0 d)
    (k : ℕ) (hk : 0 < k) (q₀ R H Ccut : ℝ) (hq₀ : 1 ≤ q₀) (hq₀hi : q₀ ≤ 4 * d.Q1)
    (hR : 1 ≤ R) (hproduct : (k : ℝ) * R ≤ 4 * d.Q2 * d.Q3)
    (hlog : Ccut * Real.log d.scale ^ 5 ≤ d.scale)
    (hcut : H ≤ (Ccut * Real.log d.scale ^ 5) * (((k : ℝ) * q₀) * R / d.V)) :
    8 * ((k : ℝ) * q₀) * R ^ 2 ≤ d.scale ^ (12 : ℝ) ∧
      4 * H * R ≤ d.scale ^ (12 : ℝ) := by
  let X := d.scale
  let Q := (k : ℝ) * q₀
  have hX1 : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2).trans hX
  have hX0 := zero_lt_one.trans_le hX1
  have hQ0 : 0 < Q := mul_pos (Nat.cast_pos.mpr hk) (zero_lt_one.trans_le hq₀)
  have hR0 := zero_lt_one.trans_le hR
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨hQ₁, hQ₂₃⟩ := medium_e1_factorLengths_le_scale hσ hX1 hd
  have hD : (k : ℝ) * R ≤ 4 * X := by
    rw [mul_assoc] at hproduct
    exact hproduct.trans (mul_le_mul_of_nonneg_left hQ₂₃ (by norm_num))
  have hRX : R ≤ 4 * X := (le_mul_of_one_le_left hR0.le hk1).trans hD
  have hqX : q₀ ≤ 4 * X := hq₀hi.trans (mul_le_mul_of_nonneg_left hQ₁ (by norm_num))
  have hQR : Q * R ≤ 16 * X ^ 2 := by
    calc
      _ = q₀ * ((k : ℝ) * R) := by dsimp only [Q]; ring
      _ ≤ (4 * X) * (4 * X) := mul_le_mul hqX hD (by positivity) (by positivity)
      _ = _ := by ring
  have hQRsq : Q * R ^ 2 ≤ 64 * X ^ 3 := by
    calc
      _ = (Q * R) * R := by ring
      _ ≤ (16 * X ^ 2) * (4 * X) := mul_le_mul hQR hRX hR0.le (by positivity)
      _ = _ := by ring
  have hV0 := zero_lt_one.trans_le hd.2.1
  have hH : H ≤ X * (Q * R) := by
    calc
      _ ≤ (Ccut * Real.log X ^ 5) * (Q * R / d.V) := hcut
      _ ≤ X * (Q * R / d.V) := mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ Q * R / d.V)
      _ ≤ X * (Q * R) := mul_le_mul_of_nonneg_left (div_le_self (by positivity) hd.2.1) hX0.le
  have h512 : (512 : ℝ) ≤ X ^ 9 := by
    exact (show (512 : ℝ) = 2 ^ 9 by norm_num).le.trans (pow_le_pow_left₀ (by norm_num) hX 9)
  have h256 : (256 : ℝ) ≤ X ^ 8 := by
    exact (show (256 : ℝ) = 2 ^ 8 by norm_num).le.trans (pow_le_pow_left₀ (by norm_num) hX 8)
  change 8 * Q * R ^ 2 ≤ X ^ (12 : ℝ) ∧ 4 * H * R ≤ X ^ (12 : ℝ)
  rw [Real.rpow_ofNat]
  constructor
  · calc
      _ = 8 * (Q * R ^ 2) := by ring
      _ ≤ 8 * (64 * X ^ 3) := mul_le_mul_of_nonneg_left hQRsq (by norm_num)
      _ = 512 * X ^ 3 := by ring
      _ ≤ X ^ 9 * X ^ 3 := mul_le_mul_of_nonneg_right h512 (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ 4 * (X * (Q * R)) * R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by norm_num)) hR0.le
      _ = (4 * X) * (Q * R ^ 2) := by ring
      _ ≤ (4 * X) * (64 * X ^ 3) := mul_le_mul_of_nonneg_left hQRsq (by positivity)
      _ = 256 * X ^ 4 := by ring
      _ ≤ X ^ 8 * X ^ 4 := mul_le_mul_of_nonneg_right h256 (by positivity)
      _ = _ := by ring

/-- A fixed-cell length within a factor four preserves the original (18)
monomials with constant 512, including the inverse square in front. -/
theorem e1ShiftedQCell_monomials_le {X N Q Q' R : ℝ} (hX : 0 < X) (hN : 0 ≤ N)
    (hQ : 0 < Q) (hR : 0 ≤ R) (hlo : Q / 4 ≤ Q') (hhi : Q' ≤ 4 * Q) :
    (N ^ 4 / Q' ^ 2) * e1Equation18Bracket X N Q' R ≤
      512 * ((N ^ 4 / Q ^ 2) * e1Equation18Bracket X N Q R) := by
  have hQ' := (show 0 < Q / 4 by positivity).trans_le hlo
  have hcoef : N ^ 4 / Q' ^ 2 ≤ 16 * (N ^ 4 / Q ^ 2) := by
    calc
      _ ≤ N ^ 4 / (Q / 4) ^ 2 := by gcongr
      _ = _ := by ring
  have h4pow : (4 : ℝ) ^ (5 / 2 : ℝ) = 32 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hQpow : Q' ^ (5 / 2 : ℝ) ≤ 32 * Q ^ (5 / 2 : ℝ) := by
    calc
      _ ≤ (4 * Q) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hQ'.le hhi (by norm_num)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hQ.le, h4pow]
  have hdiag : N * Q' / X ≤ 4 * (N * Q / X) := by
    calc
      _ ≤ N * (4 * Q) / X := by gcongr
      _ = _ := by ring
  have hweil : N * Q' ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2 ≤
      32 * (N * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2) := by
    calc
      _ ≤ N * (32 * Q ^ (5 / 2 : ℝ)) * R ^ 3 / X ^ 2 := by gcongr
      _ = _ := by ring
  have hram : N ^ 2 * Q' * R / X ^ 2 ≤ 4 * (N ^ 2 * Q * R / X ^ 2) := by
    calc
      _ ≤ N ^ 2 * (4 * Q) * R / X ^ 2 := by gcongr
      _ = _ := by ring
  have hbracket : e1Equation18Bracket X N Q' R ≤ 32 * e1Equation18Bracket X N Q R := by
    unfold e1Equation18Bracket
    have hd0 : 0 ≤ N * Q / X := by positivity
    have hr0 : 0 ≤ N ^ 2 * Q * R / X ^ 2 := by positivity
    linarith only [hdiag, hweil, hram, hd0, hr0]
  calc
    _ ≤ (16 * (N ^ 4 / Q ^ 2)) * (32 * e1Equation18Bracket X N Q R) := by
      exact mul_le_mul hcoef hbracket (by unfold e1Equation18Bracket; positivity) (by positivity)
    _ = _ := by ring

end ImbalancedChen.Part3
