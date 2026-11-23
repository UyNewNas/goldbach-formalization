import ImbalancedChen.Part3E1Equation18
import ImbalancedChen.Part3E1SourceMask

/-!
# E1 with real dyadic scales

Ceiling enlargement is confined to the proof. The emitted source uses the
original dyadic sets, original Fourier argument, and exact floor cutoff.
-/

namespace ImbalancedChen.Part3

/-- Dyadic upper rounding preserves all three terms of (18) at an explicit constant. -/
theorem e1RoundedMonomials_le
    (Q R N X Q' R' N' X' ε : ℝ)
    (hQ : 1 ≤ Q) (hR : 1 ≤ R) (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hQlo : Q ≤ Q') (hQhi : Q' ≤ 2 * Q)
    (hRlo : R ≤ R') (hRhi : R' ≤ 2 * R)
    (hNlo : N ≤ N') (hNhi : N' ≤ 2 * N)
    (hXlo : X ≤ X') (hXhi : X' ≤ 2 * X) (hε : 0 ≤ ε) :
    X' ^ ε * (N' ^ 4 / Q' ^ 2) *
        (N' * Q' / X' + N' * Q' ^ (5 / 2 : ℝ) * R' ^ 3 / X' ^ 2 +
          N' ^ 2 * Q' * R' / X' ^ 2) ≤
      (2048 * (2 : ℝ) ^ ε) *
        (X ^ ε * (N ^ 4 / Q ^ 2) *
          (N * Q / X + N * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2 + N ^ 2 * Q * R / X ^ 2)) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hQ'0 := hQ0.trans_le hQlo
  have hR'0 := hR0.trans_le hRlo
  have hN'0 := hN0.trans_le hNlo
  have hX'0 := hX0.trans_le hXlo
  have hscale : X' ^ ε ≤ (2 : ℝ) ^ ε * X ^ ε :=
    (Real.rpow_le_rpow hX'0.le hXhi hε).trans_eq (Real.mul_rpow (by norm_num) hX0.le)
  have hcoef : N' ^ 4 / Q' ^ 2 ≤ 16 * (N ^ 4 / Q ^ 2) := by
    calc
      _ ≤ (2 * N) ^ 4 / Q ^ 2 := by gcongr
      _ = _ := by ring
  have hpower : Q' ^ (5 / 2 : ℝ) ≤ 8 * Q ^ (5 / 2 : ℝ) := by
    have ht : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 8 := by
      calc
        _ ≤ (2 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = _ := by norm_num
    calc
      _ ≤ (2 * Q) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hQ'0.le hQhi (by norm_num)
      _ = (2 : ℝ) ^ (5 / 2 : ℝ) * Q ^ (5 / 2 : ℝ) := Real.mul_rpow (by norm_num) hQ0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (by positivity)
  have hdiag : N' * Q' / X' ≤ 4 * (N * Q / X) := by
    calc
      _ ≤ (2 * N) * (2 * Q) / X := by gcongr
      _ = _ := by ring
  have hweil : N' * Q' ^ (5 / 2 : ℝ) * R' ^ 3 / X' ^ 2 ≤ 128 * (N * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2) := by
    calc
      _ ≤ (2 * N) * (8 * Q ^ (5 / 2 : ℝ)) * (2 * R) ^ 3 / X ^ 2 := by gcongr
      _ = _ := by ring
  have hram : N' ^ 2 * Q' * R' / X' ^ 2 ≤ 16 * (N ^ 2 * Q * R / X ^ 2) := by
    calc
      _ ≤ (2 * N) ^ 2 * (2 * Q) * (2 * R) / X ^ 2 := by gcongr
      _ = _ := by ring
  have hsum : N' * Q' / X' + N' * Q' ^ (5 / 2 : ℝ) * R' ^ 3 / X' ^ 2 +
        N' ^ 2 * Q' * R' / X' ^ 2 ≤
      128 * (N * Q / X + N * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2 + N ^ 2 * Q * R / X ^ 2) := by
    have hA : 0 ≤ N * Q / X := by positivity
    have hB : 0 ≤ N ^ 2 * Q * R / X ^ 2 := by positivity
    calc
      _ ≤ 4 * (N * Q / X) + 128 * (N * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2) +
          16 * (N ^ 2 * Q * R / X ^ 2) := add_le_add (add_le_add hdiag hweil) hram
      _ ≤ _ := by linarith only [hA, hB]
  calc
    _ ≤ ((2 : ℝ) ^ ε * X ^ ε) * (16 * (N ^ 4 / Q ^ 2)) *
        (128 * (N * Q / X + N * Q ^ (5 / 2 : ℝ) * R ^ 3 / X ^ 2 + N ^ 2 * Q * R / X ^ 2)) := by
      exact mul_le_mul (mul_le_mul hscale hcoef (by positivity) (by positivity)) hsum
        (by positivity) (by positivity)
    _ = _ := by ring

end ImbalancedChen.Part3

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Finset
open scoped BigOperators SchwartzMap FourierTransform

/-- The natural points of the exact half-open real dyadic interval. -/
def realDyadicCarrier (L : ℝ) : Finset ℕ := Ico ⌈L⌉₊ ⌈2 * L⌉₊

theorem mem_realDyadicCarrier {L : ℝ} {n : ℕ} :
    n ∈ realDyadicCarrier L ↔ L ≤ (n : ℝ) ∧ (n : ℝ) < 2 * L := by
  simp only [realDyadicCarrier, mem_Ico, Nat.ceil_le, Nat.lt_ceil]

private theorem realDyadicCarrier_subset (L : ℝ) :
    realDyadicCarrier L ⊆ Ico ⌈L⌉₊ (2 * ⌈L⌉₊) := by
  intro n hn
  obtain ⟨hlo, hup⟩ := mem_Ico.mp hn
  have hc : ⌈2 * L⌉₊ ≤ 2 * ⌈L⌉₊ := by
    apply Nat.ceil_le.mpr
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil L) (by norm_num)
  exact mem_Ico.mpr ⟨hlo, hup.trans_le hc⟩

private theorem ceil_realScale_upper {L : ℝ} (hL : 1 ≤ L) : (⌈L⌉₊ : ℝ) ≤ 2 * L :=
  (Nat.ceil_lt_add_one (zero_le_one.trans hL)).le.trans (by linarith)

private theorem ceil_realScale_pos {L : ℝ} (hL : 1 ≤ L) : 0 < ⌈L⌉₊ :=
  Nat.cast_pos.mp ((zero_lt_one.trans_le hL).trans_le (Nat.le_ceil L))

/-- Uniform E1 at real positive dyadic scales and the exact integer
truncation of the real frequency limit. -/
theorem exists_source_realDyadic_equation18 {κ ε Ccut : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hCcut : 0 ≤ Ccut) (ψ : 𝓢(ℝ, ℂ)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (X M Q R N H : ℝ), 2 ≤ X → 0 < M → 1 ≤ Q → 1 ≤ R → 1 ≤ N → 0 ≤ H →
        X = M * N → 8 * Q * R^2 ≤ X ^ κ → 4 * H * R ≤ X ^ κ →
        H ≤ (Ccut * (Real.log X)^5) * (Q * R / M) →
        ∀ (a : ℤ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ),
          (∀ q ∈ realDyadicCarrier Q, ∀ r ∈ realDyadicCarrier R, ‖lambda q r‖ ≤ 1) →
          (∀ n ∈ realDyadicCarrier N, ‖alpha n‖ ≤ 1) →
          ‖source (realDyadicCarrier Q) (realDyadicCarrier R) (realDyadicCarrier N)
            (e1NonzeroFrequencies ⌊H⌋₊) a M (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) lambda alpha‖ ^ 2 ≤
            A * X ^ ε * (N^4 / Q^2) * (N * Q / X + N * Q ^ (5/2 : ℝ) * R^3 / X^2 + N^2 * Q * R / X^2) := by
  obtain ⟨A, hA, hAall⟩ := exists_source_dyadic_equation18 (κ := κ + 3)
    (by positivity) hε hCcut ψ
  refine ⟨A * (2048 * 2 ^ ε), by positivity, ?_⟩
  intro X M Q R N H hX hM hQ hR hN hH hXeq hQR hHR hcut a lambda alpha hlambda halpha
  let q := ⌈Q⌉₊
  let r := ⌈R⌉₊
  let n := ⌈N⌉₊
  let f := ⌊H⌋₊
  let Y := M * (n : ℝ)
  let lambdaExt (u v : ℕ) := if u ∈ realDyadicCarrier Q ∧ v ∈ realDyadicCarrier R then lambda u v else 0
  let alphaExt (u : ℕ) := if u ∈ realDyadicCarrier N then alpha u else 0
  have hq : Q ≤ (q : ℝ) := Nat.le_ceil Q
  have hq' : (q : ℝ) ≤ 2 * Q := ceil_realScale_upper hQ
  have hr : R ≤ (r : ℝ) := Nat.le_ceil R
  have hr' : (r : ℝ) ≤ 2 * R := ceil_realScale_upper hR
  have hn : N ≤ (n : ℝ) := Nat.le_ceil N
  have hn' : (n : ℝ) ≤ 2 * N := ceil_realScale_upper hN
  have hf : (f : ℝ) ≤ H := Nat.floor_le hH
  have hXY : X ≤ Y := by
    rw [hXeq]
    exact mul_le_mul_of_nonneg_left hn hM.le
  have hYX : Y ≤ 2 * X := by
    rw [hXeq, ← mul_left_comm]
    exact mul_le_mul_of_nonneg_left hn' hM.le
  have hX1 : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2).trans hX
  have hY : 1 ≤ Y := hX1.trans hXY
  have hY8 : 8 * X ^ κ ≤ Y ^ (κ + 3) := by
    have hcube : (8 : ℝ) ≤ Y ^ (3 : ℝ) := by
      rw [Real.rpow_ofNat]
      exact (show (8 : ℝ) = 2^3 by norm_num).le.trans
        (pow_le_pow_left₀ (by norm_num) (hX.trans hXY) 3)
    rw [Real.rpow_add (zero_lt_one.trans_le hY), mul_comm (8 : ℝ)]
    exact mul_le_mul (Real.rpow_le_rpow (zero_le_one.trans hX1) hXY hκ.le) hcube
      (by norm_num) (by positivity)
  have hqrCap : 8 * (q : ℝ) * (r : ℝ)^2 ≤ Y ^ (κ + 3) := by
    calc
      _ ≤ 8 * (2 * Q) * (2 * R)^2 := by gcongr
      _ = 8 * (8 * Q * R^2) := by ring
      _ ≤ 8 * X ^ κ := mul_le_mul_of_nonneg_left hQR (by norm_num)
      _ ≤ _ := hY8
  have hfrCap : 4 * (f : ℝ) * (r : ℝ) ≤ Y ^ (κ + 3) := by
    calc
      _ ≤ 4 * H * (2 * R) := by gcongr
      _ = 2 * (4 * H * R) := by ring
      _ ≤ 2 * X ^ κ := mul_le_mul_of_nonneg_left hHR (by norm_num)
      _ ≤ 8 * X ^ κ := by gcongr; norm_num
      _ ≤ _ := hY8
  have hcut' : (f : ℝ) ≤ (Ccut * (Real.log Y)^5) * ((q : ℝ) * r / M) := by
    refine (hf.trans hcut).trans ?_
    have hlog := Real.log_le_log (zero_lt_one.trans_le hX1) hXY
    have hpow := pow_le_pow_left₀ (Real.log_nonneg hX1) hlog 5
    have hprod : Q * R ≤ (q : ℝ) * r :=
      mul_le_mul hq hr (zero_le_one.trans hR) (Nat.cast_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hCcut)
      (div_le_div_of_nonneg_right hprod hM.le) (by positivity)
      (mul_nonneg hCcut (pow_nonneg (Real.log_nonneg hY) _))
  have hlambda' : ∀ u ∈ Ico q (2 * q), ∀ v ∈ Ico r (2 * r), ‖lambdaExt u v‖ ≤ 1 := by
    intro u _ v _
    dsimp only [lambdaExt]
    split_ifs with h
    · exact hlambda u h.1 v h.2
    · simp only [norm_zero, zero_le_one]
  have halpha' : ∀ u ∈ Ico n (2 * n), ‖alphaExt u‖ ≤ 1 := by
    intro u _
    dsimp only [alphaExt]
    split_ifs with h
    · exact halpha u h
    · simp only [norm_zero, zero_le_one]
  have hs := hAall Y M q r n f hY hM (ceil_realScale_pos hQ) (ceil_realScale_pos hR)
    (ceil_realScale_pos hN) rfl hqrCap hfrCap hcut' a lambdaExt alphaExt hlambda' halpha'
  rw [source_subsets_eq_zero_extend _ _ _ _ _ _ (realDyadicCarrier_subset Q)
    (realDyadicCarrier_subset R) (realDyadicCarrier_subset N)]
  have hb := e1RoundedMonomials_le Q R N X q r n Y ε hQ hR hN hX1
    hq hq' hr hr' hn hn' hXY hYX hε.le
  refine hs.trans ?_
  convert mul_le_mul_of_nonneg_left hb hA.le using 1 <;> ring

end

end ImbalancedChen.Part3.E1Finite
