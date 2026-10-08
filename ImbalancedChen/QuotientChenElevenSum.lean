import ImbalancedChen.QuotientChenSummedBridge

/-!
# The eleven actual Upsilon terms and their summed Chen inequality

Each `chenUpsilon` below is an actual finite sum over original additive
primes `P < N`, with `Coprime P N`, of its literal quotient tuple count at
`N - P`. In particular the eleventh term uses the full fourth-prime range
`[N^h, N^d)`. These are not scalar placeholders for analytic estimates.
-/

namespace ImbalancedChen

open scoped BigOperators

noncomputable section

/-- The manuscript writes `P ≤ N`. Its endpoint is impossible for a prime
coprime to `N`, so the positive-receiver carrier is exactly the same set. -/
theorem mem_chenAdditivePrimeCarrier_iff_le {N P : ℕ} :
    P ∈ chenAdditivePrimeCarrier N ↔ P ≤ N ∧ Nat.Prime P ∧ Nat.Coprime P N := by
  rw [mem_chenAdditivePrimeCarrier]
  constructor
  · rintro ⟨hPN, hp, hcop⟩
    exact ⟨hPN.le, hp, hcop⟩
  · rintro ⟨hPN, hp, hcop⟩
    have hlt : P < N := by
      rcases lt_or_eq_of_le hPN with hlt | heq
      · exact hlt
      · subst P
        have hN₁ : N = 1 := by simpa [Nat.Coprime] using hcop
        exact (hp.ne_one hN₁).elim
    exact ⟨hlt, hp, hcop⟩

def chenUpsilon1 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY1 (N - P) ((N : ℝ) ^ (100 / 1149 : ℝ)) : ℝ)

def chenUpsilon2 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY2 (N - P) ((N : ℝ) ^ (50 / 309 : ℝ)) : ℝ)

def chenUpsilon3 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY3 (N - P) ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ)

def chenUpsilon4 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY4 (N - P) ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) : ℝ)

def chenUpsilon5 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY5 (N - P) ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (50 / 309 : ℝ)) : ℝ)

def chenUpsilon6 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY6 (N - P) ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (50 / 309 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) : ℝ)

def chenUpsilon7 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY7 (N - P) (N : ℝ)
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) : ℝ)

def chenUpsilon8 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY8 (N - P) (N : ℝ) ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ)

def chenUpsilon9 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY9 (N - P) (N : ℝ) ((N : ℝ) ^ (50 / 309 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) : ℝ)

def chenUpsilon10 (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY10 (N - P) ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (50 / 309 : ℝ)) : ℝ)

/-- Full fourth-prime range: the endpoint is exactly `N^d`. -/
def chenUpsilon11Full (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N,
    (chenY11Full (N - P) ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (50 / 309 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) : ℝ)

/-- Exact linearity of the actual eleven quotient sums. -/
theorem chenElevenPrimeSum_eq_upsilon (N : ℕ) :
    chenElevenPrimeSum N =
      3 * chenUpsilon1 N + chenUpsilon2 N - chenUpsilon3 N - chenUpsilon4 N +
        chenUpsilon5 N + chenUpsilon6 N - 2 * chenUpsilon7 N - chenUpsilon8 N -
        chenUpsilon9 N - chenUpsilon10 N - chenUpsilon11Full N := by
  simp only [chenElevenPrimeSum, chenFixedElevenWeight, chenElevenWeight,
    chenUpsilon1, chenUpsilon2, chenUpsilon3, chenUpsilon4, chenUpsilon5,
    chenUpsilon6, chenUpsilon7, chenUpsilon8, chenUpsilon9, chenUpsilon10,
    chenUpsilon11Full, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- The literal eleven-term lower bound with a finite, explicit error. -/
theorem chen_eleven_upsilon_sub_explicit_error_le_four_D12Omega (N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hA : 1 < (N : ℝ) ^ (100 / 1149 : ℝ)) :
    3 * chenUpsilon1 N + chenUpsilon2 N - chenUpsilon3 N - chenUpsilon4 N +
      chenUpsilon5 N + chenUpsilon6 N - 2 * chenUpsilon7 N - chenUpsilon8 N -
      chenUpsilon9 N - chenUpsilon10 N - chenUpsilon11Full N -
      246 * ((Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))) : ℝ) +
        (N : ℝ) / ((N : ℝ) ^ (100 / 1149 : ℝ) - 1)) ≤
      4 * (D12Omega N : ℝ) := by
  rw [← chenElevenPrimeSum_eq_upsilon]
  have h := chenElevenPrimeSum_le_count_add_explicit_error N hN hA
  linarith

/-- The repaired manuscript inequality with an explicit `984 N^(1-a)`
loss. Its only size condition beyond `N ≥ 1` is `N^a ≥ 2`. -/
theorem chen_eleven_upsilon_sub_error_le_four_D12Omega (N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hA : 2 ≤ (N : ℝ) ^ (100 / 1149 : ℝ)) :
    3 * chenUpsilon1 N + chenUpsilon2 N - chenUpsilon3 N - chenUpsilon4 N +
      chenUpsilon5 N + chenUpsilon6 N - 2 * chenUpsilon7 N - chenUpsilon8 N -
      chenUpsilon9 N - chenUpsilon10 N - chenUpsilon11Full N -
      984 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) ≤ 4 * (D12Omega N : ℝ) := by
  rw [← chenElevenPrimeSum_eq_upsilon]
  exact chenElevenPrimeSum_sub_error_le_four_D12Omega N hN hA

/-- Passing to the convention excluding receiver one costs at most four
in the four-times count. The possible unit representation remains explicit. -/
theorem chen_eleven_upsilon_sub_error_sub_four_le_four_D12 (N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hA : 2 ≤ (N : ℝ) ^ (100 / 1149 : ℝ)) :
    3 * chenUpsilon1 N + chenUpsilon2 N - chenUpsilon3 N - chenUpsilon4 N +
      chenUpsilon5 N + chenUpsilon6 N - 2 * chenUpsilon7 N - chenUpsilon8 N -
      chenUpsilon9 N - chenUpsilon10 N - chenUpsilon11Full N -
      984 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) - 4 ≤ 4 * (D12 N : ℝ) := by
  have h := chen_eleven_upsilon_sub_error_le_four_D12Omega N hN hA
  have hunit : (D12Omega N : ℝ) ≤ (D12 N : ℝ) + 1 := by
    exact_mod_cast D12Omega_le_D12_add_one N
  linarith

end

end ImbalancedChen
