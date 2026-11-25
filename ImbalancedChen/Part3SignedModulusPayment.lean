import ImbalancedChen.Part3OffDiagonalModuli
import Mathlib

/-!
# Divisor payment after the complete modulus sum

This is the finite arithmetic step in the proper-prime-power removal in
the 1106 manuscript, Appendix D.  The modulus coefficient is bounded only
on the original finite set of moduli.  The complete-product diagonal and
the primitive-coprime mean remain separate throughout the estimate.

The count/mean norm calculation is the lightweight form of the existing
`Part3PrimeProductChartTransfer` calculation.  The new step uses
`Part3OffDiagonalModuli` to pay the whole off-diagonal modulus row by
divisors of the actual product distance.  No estimate for the residual or
for prime-product distribution is an input to this calculation.
-/

namespace ImbalancedChen.Part3.SignedModulusPayment

noncomputable section

open Classical Finset
open scoped BigOperators

def modulusMass (Q : Finset ℕ) (ρ : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖ρ q‖

def meanMass (Q : Finset ℕ) (ρ : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖ρ q‖ / (q.totient : ℝ)

def coprimeMeanMass (Q : Finset ℕ) (ρ : ℕ → ℂ) (b : ℕ) : ℝ :=
  ∑ q ∈ Q, if b.Coprime q then ‖ρ q‖ / (q.totient : ℝ) else 0

theorem modulusMass_nonneg (Q : Finset ℕ) (ρ : ℕ → ℂ) : 0 ≤ modulusMass Q ρ :=
  sum_nonneg fun _ _ => norm_nonneg _

theorem meanMass_nonneg (Q : Finset ℕ) (ρ : ℕ → ℂ) : 0 ≤ meanMass Q ρ :=
  sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

theorem coprimeMeanMass_nonneg (Q : Finset ℕ) (ρ : ℕ → ℂ) (b : ℕ) :
    0 ≤ coprimeMeanMass Q ρ b := by
  apply sum_nonneg
  intro q _
  split_ifs
  · exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem coprimeMeanMass_le (Q : Finset ℕ) (ρ : ℕ → ℂ) (b : ℕ) :
    coprimeMeanMass Q ρ b ≤ meanMass Q ρ := by
  apply sum_le_sum
  intro q _
  split_ifs
  · exact le_rfl
  · exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

/-- Divisor monotonicity is used only when the complete distance is nonzero. -/
theorem card_divisors_le_of_dvd {q n : ℕ} (hn : n ≠ 0) (hq : q ∣ n) :
    q.divisors.card ≤ n.divisors.card := by
  apply card_le_card
  intro d hd
  exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.mem_divisors.mp hd).1 hq, hn⟩

/-- On a non-diagonal row, the original moduli form a subset of the
divisors of the complete-product distance.  No bound outside `Q` is used. -/
theorem offDiagonal_count_le (Q : Finset ℕ) (ρ : ℕ → ℂ) (J : ℕ)
    {Cρ : ℝ} (hCρ : 0 ≤ Cρ)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    {b N : ℕ} (hb : b ≠ N) :
    (∑ q ∈ Q, if b ≡ N [MOD q] then ‖ρ q‖ else 0) ≤
      Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1) := by
  have hn : Nat.dist b N ≠ 0 := (Nat.dist_pos_of_ne hb).ne'
  calc
    _ = ∑ q ∈ Q ∩ (Nat.dist b N).divisors, ‖ρ q‖ := by
      rw [sum_modEq_eq_sum_inter_divisors_dist, if_neg hb]
    _ ≤ ∑ q ∈ Q ∩ (Nat.dist b N).divisors,
        Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ J := by
      apply sum_le_sum
      intro q hq
      have hqQ := (mem_inter.mp hq).1
      have hqd := (Nat.mem_divisors.mp (mem_inter.mp hq).2).1
      have hcard : (q.divisors.card : ℝ) ≤ ((Nat.dist b N).divisors.card : ℝ) := by
        exact_mod_cast card_divisors_le_of_dvd hn hqd
      exact (hρ q hqQ).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard J) hCρ)
    _ ≤ ∑ q ∈ (Nat.dist b N).divisors,
        Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ J :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right
        (fun _ _ _ => mul_nonneg hCρ (pow_nonneg (Nat.cast_nonneg _) _))
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, pow_succ]
      ring

/-- The diagonal is paid by the original modulus mass, including `q = 0`. -/
theorem count_le_diagonal_or_divisors (Q : Finset ℕ) (ρ : ℕ → ℂ) (J : ℕ)
    {Cρ : ℝ} (hCρ : 0 ≤ Cρ)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    (b N : ℕ) :
    (∑ q ∈ Q, if b ≡ N [MOD q] then ‖ρ q‖ else 0) ≤
      if b = N then modulusMass Q ρ
      else Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1) := by
  by_cases hb : b = N
  · subst b
    simp [modulusMass, Nat.ModEq.refl]
  · rw [if_neg hb]
    exact offDiagonal_count_le Q ρ J hCρ hρ hb

private theorem kernel_norm_le (q N b : ℕ) :
    ‖(if b ≡ N [MOD q] then (1 : ℂ) else 0) -
        (if b.Coprime q then (1 : ℂ) else 0) / (q.totient : ℂ)‖ ≤
      (if b ≡ N [MOD q] then (1 : ℝ) else 0) +
        (if b.Coprime q then (1 : ℝ) / q.totient else 0) := by
  refine (norm_sub_le _ _).trans_eq ?_
  simp only [norm_div, Complex.norm_natCast]
  split_ifs <;> simp

/-- The exact primitive-coprime mean is retained in the row estimate. -/
theorem signedRow_norm_le (Q : Finset ℕ) (ρ : ℕ → ℂ) (J : ℕ)
    {Cρ : ℝ} (hCρ : 0 ≤ Cρ)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    (b N : ℕ) :
    ‖∑ q ∈ Q, ρ q * ((if b ≡ N [MOD q] then (1 : ℂ) else 0) -
      (if b.Coprime q then (1 : ℂ) else 0) / (q.totient : ℂ))‖ ≤
      (if b = N then modulusMass Q ρ
       else Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1)) +
        coprimeMeanMass Q ρ b := by
  calc
    _ ≤ ∑ q ∈ Q, ‖ρ q‖ *
        ((if b ≡ N [MOD q] then (1 : ℝ) else 0) +
          (if b.Coprime q then (1 : ℝ) / q.totient else 0)) := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun q _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (kernel_norm_le q N b) (norm_nonneg _)
    _ = (∑ q ∈ Q, if b ≡ N [MOD q] then ‖ρ q‖ else 0) +
        coprimeMeanMass Q ρ b := by
      simp only [mul_add, sum_add_distrib, coprimeMeanMass]
      congr 1 <;> apply sum_congr rfl <;> intro q _ <;> split_ifs <;> simp_all [div_eq_mul_inv]
    _ ≤ _ := add_le_add (count_le_diagonal_or_divisors Q ρ J hCρ hρ b N) le_rfl

private theorem signedError_norm_le_rows (B Q : Finset ℕ) (N J : ℕ)
    (ρ c : ℕ → ℂ) {Cρ : ℝ} (hCρ : 0 ≤ Cρ)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) :
    ‖∑ q ∈ Q, ρ q * ∑ b ∈ B, c b *
      ((if b ≡ N [MOD q] then (1 : ℂ) else 0) -
        (if b.Coprime q then (1 : ℂ) else 0) / (q.totient : ℂ))‖ ≤
      ∑ b ∈ B, ‖c b‖ *
        ((if b = N then modulusMass Q ρ
          else Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1)) +
            coprimeMeanMass Q ρ b) := by
  have hswap :
      (∑ q ∈ Q, ρ q * ∑ b ∈ B, c b *
        ((if b ≡ N [MOD q] then (1 : ℂ) else 0) -
          (if b.Coprime q then (1 : ℂ) else 0) / (q.totient : ℂ))) =
      ∑ b ∈ B, c b * ∑ q ∈ Q, ρ q *
        ((if b ≡ N [MOD q] then (1 : ℂ) else 0) -
          (if b.Coprime q then (1 : ℂ) else 0) / (q.totient : ℂ)) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro q _
    ring
  rw [hswap]
  refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (signedRow_norm_le Q ρ J hCρ hρ b N) (norm_nonneg _)

private theorem sum_count_cost (B Q : Finset ℕ) (N J : ℕ)
    (ρ c : ℕ → ℂ) (Cρ : ℝ) :
    (∑ b ∈ B, ‖c b‖ * (if b = N then modulusMass Q ρ
      else Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1))) =
    Cρ * (∑ b ∈ B.erase N, ‖c b‖ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1)) +
      (if N ∈ B then ‖c N‖ * modulusMass Q ρ else 0) := by
  by_cases hN : N ∈ B
  · calc
      _ = (∑ b ∈ B.erase N, ‖c b‖ * (if b = N then modulusMass Q ρ
          else Cρ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1))) +
          ‖c N‖ * (if N = N then modulusMass Q ρ
          else Cρ * ((Nat.dist N N).divisors.card : ℝ) ^ (J + 1)) :=
        (sum_erase_add B _ hN).symm
      _ = _ := by
        simp only [if_pos hN, mul_sum]
        congr 1
        apply sum_congr rfl
        intro b hb
        rw [if_neg (mem_erase.mp hb).1]
        ring
  · have he : B.erase N = B := by
      ext b
      simp only [mem_erase]
      exact ⟨And.right, fun hb => ⟨fun h => hN (h ▸ hb), hb⟩⟩
    rw [if_neg hN, add_zero, he, mul_sum]
    apply sum_congr rfl
    intro b hb
    have hbN : b ≠ N := fun h => hN (h ▸ hb)
    rw [if_neg hbN]
    ring

/-- The whole signed error splits into the off-diagonal divisor payment,
the exact coprime mean and the true complete-product diagonal. -/
theorem signedError_norm_le_exact (B Q : Finset ℕ) (N J : ℕ)
    (ρ c : ℕ → ℂ) {Cρ : ℝ} (hCρ : 0 ≤ Cρ)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) :
    ‖∑ q ∈ Q, ρ q * ∑ b ∈ B, c b *
      ((if b ≡ N [MOD q] then (1 : ℂ) else 0) -
        (if b.Coprime q then (1 : ℂ) else 0) / (q.totient : ℂ))‖ ≤
      Cρ * (∑ b ∈ B.erase N, ‖c b‖ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1)) +
      (∑ b ∈ B, ‖c b‖ * coprimeMeanMass Q ρ b) +
      (if N ∈ B then ‖c N‖ * modulusMass Q ρ else 0) := by
  refine (signedError_norm_le_rows B Q N J ρ c hCρ hρ).trans_eq ?_
  simp only [mul_add, sum_add_distrib]
  rw [sum_count_cost]
  ring

/-- A finite divisor budget and independently proved coefficient mass
budgets pay the same signed sum.  Neither positivity of `N` nor of the
moduli is needed. -/
theorem signedError_norm_le_budget (B Q : Finset ℕ) (N J D : ℕ)
    (ρ c : ℕ → ℂ) {Cρ R Rdiag : ℝ} (hCρ : 0 ≤ Cρ)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    (hD : ∀ b ∈ B, b ≠ N → (Nat.dist b N).divisors.card ≤ D)
    (hMass : (∑ b ∈ B, ‖c b‖) ≤ R) (hDiag : ‖c N‖ ≤ Rdiag) :
    ‖∑ q ∈ Q, ρ q * ∑ b ∈ B, c b *
      ((if b ≡ N [MOD q] then (1 : ℂ) else 0) -
        (if b.Coprime q then (1 : ℂ) else 0) / (q.totient : ℂ))‖ ≤
      R * (Cρ * (D : ℝ) ^ (J + 1) + meanMass Q ρ) +
        Rdiag * modulusMass Q ρ := by
  have hOff :
      (∑ b ∈ B.erase N, ‖c b‖ * ((Nat.dist b N).divisors.card : ℝ) ^ (J + 1)) ≤
        R * (D : ℝ) ^ (J + 1) := by
    calc
      _ ≤ ∑ b ∈ B.erase N, ‖c b‖ * (D : ℝ) ^ (J + 1) := by
        apply sum_le_sum
        intro b hb
        have hcard : ((Nat.dist b N).divisors.card : ℝ) ≤ (D : ℝ) := by
          exact_mod_cast hD b (mem_erase.mp hb).2 (mem_erase.mp hb).1
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _) (norm_nonneg _)
      _ ≤ (∑ b ∈ B, ‖c b‖) * (D : ℝ) ^ (J + 1) := by
        rw [sum_mul]
        exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          (fun b _ _ => mul_nonneg (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      _ ≤ _ := mul_le_mul_of_nonneg_right hMass (pow_nonneg (Nat.cast_nonneg _) _)
  have hMean : (∑ b ∈ B, ‖c b‖ * coprimeMeanMass Q ρ b) ≤ R * meanMass Q ρ := by
    calc
      _ ≤ ∑ b ∈ B, ‖c b‖ * meanMass Q ρ :=
        sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
          (coprimeMeanMass_le Q ρ b) (norm_nonneg _)
      _ = (∑ b ∈ B, ‖c b‖) * meanMass Q ρ := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hMass (meanMass_nonneg Q ρ)
  have hDiagonal :
      (if N ∈ B then ‖c N‖ * modulusMass Q ρ else 0) ≤ Rdiag * modulusMass Q ρ := by
    split_ifs
    · exact mul_le_mul_of_nonneg_right hDiag (modulusMass_nonneg Q ρ)
    · exact mul_nonneg ((norm_nonneg _).trans hDiag) (modulusMass_nonneg Q ρ)
  calc
    _ ≤ _ := signedError_norm_le_exact B Q N J ρ c hCρ hρ
    _ ≤ Cρ * (R * (D : ℝ) ^ (J + 1)) + R * meanMass Q ρ + Rdiag * modulusMass Q ρ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hOff hCρ) hMean) hDiagonal
    _ = _ := by ring

/-- The divisor budget can always be chosen from the finite off-diagonal
carrier itself; it is not an additional distribution assumption. -/
theorem dist_divisors_card_le_sup (B : Finset ℕ) (N : ℕ)
    {b : ℕ} (hb : b ∈ B) (hbN : b ≠ N) :
    (Nat.dist b N).divisors.card ≤
      (B.erase N).sup (fun m => (Nat.dist m N).divisors.card) :=
  Finset.le_sup (f := fun m : ℕ => (Nat.dist m N).divisors.card)
    (mem_erase.mpr ⟨hbN, hb⟩)

end

end ImbalancedChen.Part3.SignedModulusPayment
