import ImbalancedChen.QuotientChenPositiveBound
import ImbalancedChen.RoughSquareException

/-!
# The actual prime-indexed eleven-term inequality

The carrier consists of the original additive primes `P < N`, with
`Coprime P N`. Its summand is the literal quotient weight at `N - P`.
The exception set is a union of small receivers and nonsquarefree rough
receivers. Complementation is injective, so each additive prime and each
exceptional receiver is counted once. Only an upper bound on the signed
weight is used when a receiver is discarded.

All errors are explicit finite bounds. There are no analytic counting
hypotheses and no assumed tuple-count identities. The count `D12Omega`
retains receiver one; the existing multiplicity module supplies its exact
correction when passing to `D12`.
-/

namespace ImbalancedChen

open scoped BigOperators ArithmeticFunction.Omega

noncomputable section

/-- Original additive primes, with the manuscript's coprimality restriction. -/
def chenAdditivePrimeCarrier (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun P => Nat.Prime P ∧ Nat.Coprime P N

@[simp] theorem mem_chenAdditivePrimeCarrier {N P : ℕ} :
    P ∈ chenAdditivePrimeCarrier N ↔ P < N ∧ Nat.Prime P ∧ Nat.Coprime P N := by
  classical
  simp [chenAdditivePrimeCarrier]

/-- The actual sum of the fixed eleven-term quotient weight. -/
def chenElevenPrimeSum (N : ℕ) : ℝ :=
  ∑ P ∈ chenAdditivePrimeCarrier N, chenFixedElevenWeight (N - P) (N : ℝ)

/-- A union of the two exceptional receiver conditions. Nonrough receivers
need not be discarded: their signed weight is already nonpositive. -/
def chenExceptionalAdditivePrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (chenAdditivePrimeCarrier N).filter fun P =>
    ((N - P : ℕ) : ℝ) < (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) ∨
      (ChenPrimeRough ((N : ℝ) ^ (100 / 1149 : ℝ)) (N - P) ∧
        ¬ Squarefree (N - P))

@[simp] theorem mem_chenExceptionalAdditivePrimes {N P : ℕ} :
    P ∈ chenExceptionalAdditivePrimes N ↔
      P ∈ chenAdditivePrimeCarrier N ∧
        (((N - P : ℕ) : ℝ) < (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) ∨
          (ChenPrimeRough ((N : ℝ) ^ (100 / 1149 : ℝ)) (N - P) ∧
            ¬ Squarefree (N - P))) := by
  classical
  simp only [chenExceptionalAdditivePrimes, Finset.mem_filter]

/-- An actual nonsquarefree rough receiver contains an actual large prime
square. This uses the prime-square characterization of squarefreeness. -/
theorem chen_mem_roughSquareExceptions_of_not_squarefree {N n : ℕ} {A : ℝ}
    (hn : 0 < n) (hnN : n ≤ N) (hrough : ChenPrimeRough A n)
    (hnsf : ¬ Squarefree n) : n ∈ roughSquareExceptions N A := by
  classical
  have hex : ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ n := by
    by_contra hnot
    apply hnsf
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hd
    exact hnot ⟨p, hp, hd⟩
  obtain ⟨p, hp, hd⟩ := hex
  have hpn : p ∣ n := (dvd_mul_right p p).trans hd
  exact mem_roughSquareExceptions.mpr
    ⟨by omega, hnN, p, hp, hrough p hp hpn, by simpa only [pow_two] using hd⟩

/-- The exceptional prime carrier injects into a union of actual integers.
The cardinality bound therefore does not count different prime-square
witnesses or overlapping exception conditions multiple times. -/
theorem chenExceptionalAdditivePrimes_card_le_union (N : ℕ) :
    (chenExceptionalAdditivePrimes N).card ≤
      ((Finset.range (Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))))) ∪
        roughSquareExceptions N ((N : ℝ) ^ (100 / 1149 : ℝ))).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun P : ℕ => N - P)
  · intro P hP
    obtain ⟨hPc, hbad⟩ := mem_chenExceptionalAdditivePrimes.mp hP
    have hPN := (mem_chenAdditivePrimeCarrier.mp hPc).1
    apply Finset.mem_union.mpr
    rcases hbad with hsmall | ⟨hrough, hnsf⟩
    · exact Or.inl (Finset.mem_range.mpr (Nat.lt_ceil.mpr hsmall))
    · exact Or.inr (chen_mem_roughSquareExceptions_of_not_squarefree
        (by omega : 0 < N - P) (Nat.sub_le N P) hrough hnsf)
  · intro P hP Q hQ hPQ
    have hPN := (mem_chenAdditivePrimeCarrier.mp
      (mem_chenExceptionalAdditivePrimes.mp hP).1).1
    have hQN := (mem_chenAdditivePrimeCarrier.mp
      (mem_chenExceptionalAdditivePrimes.mp hQ).1).1
    change N - P = N - Q at hPQ
    omega

/-- The literal finite error budget before simplifying the powers. -/
theorem chenExceptionalAdditivePrimes_card_cast_le (N : ℕ)
    (hA : 1 < (N : ℝ) ^ (100 / 1149 : ℝ)) :
    ((chenExceptionalAdditivePrimes N).card : ℝ) ≤
      (Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))) : ℝ) +
        (N : ℝ) / ((N : ℝ) ^ (100 / 1149 : ℝ) - 1) := by
  classical
  have hcard : (chenExceptionalAdditivePrimes N).card ≤
      Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))) +
        (roughSquareExceptions N ((N : ℝ) ^ (100 / 1149 : ℝ))).card := by
    calc
      (chenExceptionalAdditivePrimes N).card ≤
          ((Finset.range (Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))))) ∪
            roughSquareExceptions N ((N : ℝ) ^ (100 / 1149 : ℝ))).card :=
        chenExceptionalAdditivePrimes_card_le_union N
      _ ≤ (Finset.range (Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))))).card +
          (roughSquareExceptions N ((N : ℝ) ^ (100 / 1149 : ℝ))).card :=
        Finset.card_union_le _ _
      _ = _ := by rw [Finset.card_range]
  have hcardR : ((chenExceptionalAdditivePrimes N).card : ℝ) ≤
      (Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))) : ℝ) +
        ((roughSquareExceptions N ((N : ℝ) ^ (100 / 1149 : ℝ))).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (add_le_add le_rfl (roughSquareExceptions_card_le N hA))

/-- Finite summation of a constant indicator, with real cardinality. -/
theorem chen_sum_indicator_card (S : Finset ℕ) (q : ℕ → Prop) (c : ℝ)
    [DecidablePred q] :
    (∑ P ∈ S, if q P then c else 0) = ((S.filter q).card : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp

/-- Receiver-wise majorization: good receivers use the actual pointwise
source theorem; nonrough receivers have nonpositive weight; the remaining
union costs at most 246 per original additive prime. -/
theorem chenFixedElevenWeight_le_indicator_add_exception {N P : ℕ}
    (hN : 1 ≤ (N : ℝ)) (hP : P ∈ chenAdditivePrimeCarrier N) :
    chenFixedElevenWeight (N - P) (N : ℝ) ≤
      (if Ω (N - P) ≤ 2 then (4 : ℝ) else 0) +
        (if P ∈ chenExceptionalAdditivePrimes N then (246 : ℝ) else 0) := by
  classical
  have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
  have hn : N - P ≠ 0 := by omega
  have hnN : ((N - P : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N P
  have hindicator : 0 ≤ (if Ω (N - P) ≤ 2 then (4 : ℝ) else 0) := by
    split_ifs <;> norm_num
  by_cases hbad : P ∈ chenExceptionalAdditivePrimes N
  · rw [if_pos hbad]
    have hbound := chenFixedElevenWeight_le_246 hN hn hnN
    linarith
  · rw [if_neg hbad, add_zero]
    by_cases hrough : ChenPrimeRough ((N : ℝ) ^ (100 / 1149 : ℝ)) (N - P)
    · have hsf : Squarefree (N - P) := by
        by_contra hnsf
        exact hbad (mem_chenExceptionalAdditivePrimes.mpr ⟨hP, Or.inr ⟨hrough, hnsf⟩⟩)
      have hband : (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) ≤ ((N - P : ℕ) : ℝ) := by
        by_contra hnot
        exact hbad (mem_chenExceptionalAdditivePrimes.mpr ⟨hP, Or.inl (lt_of_not_ge hnot)⟩)
      exact chenFixedElevenWeight_le_four_indicator hN hsf hnN hband
    · have hAH : (N : ℝ) ^ (100 / 1149 : ℝ) ≤ (N : ℝ) ^ (50 / 309 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
      exact (chenElevenWeight_nonpos_of_not_rough hn hAH hrough).trans hindicator

/-- Summation over the original additive primes. The good count is bounded
by `D12Omega`, which counts prime summands rather than factorization witnesses. -/
theorem chenElevenPrimeSum_le_count_add_exceptions (N : ℕ) (hN : 1 ≤ (N : ℝ)) :
    chenElevenPrimeSum N ≤ 4 * (D12Omega N : ℝ) +
      246 * ((chenExceptionalAdditivePrimes N).card : ℝ) := by
  classical
  let S := chenAdditivePrimeCarrier N
  let E := chenExceptionalAdditivePrimes N
  have hsub : S.filter (fun P => Ω (N - P) ≤ 2) ⊆ omegaChenPrimes N := by
    intro P hP
    obtain ⟨hPS, hΩ⟩ := Finset.mem_filter.mp hP
    obtain ⟨hPN, hp, _⟩ := mem_chenAdditivePrimeCarrier.mp hPS
    exact mem_omegaChenPrimes.mpr ⟨hPN, hp, hΩ⟩
  have hcount : (((S.filter (fun P => Ω (N - P) ≤ 2)).card) : ℝ) ≤
      (D12Omega N : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hfilterE : S.filter (fun P => P ∈ E) = E := by
    ext P
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hPE
      exact ⟨(mem_chenExceptionalAdditivePrimes.mp hPE).1, hPE⟩
  calc
    chenElevenPrimeSum N ≤ ∑ P ∈ S,
        ((if Ω (N - P) ≤ 2 then (4 : ℝ) else 0) +
          (if P ∈ E then (246 : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro P hP
      exact chenFixedElevenWeight_le_indicator_add_exception hN hP
    _ = (((S.filter (fun P => Ω (N - P) ≤ 2)).card) : ℝ) * 4 +
        ((E.card : ℕ) : ℝ) * 246 := by
      rw [Finset.sum_add_distrib, chen_sum_indicator_card, chen_sum_indicator_card, hfilterE]
    _ ≤ 4 * (D12Omega N : ℝ) + 246 * (E.card : ℝ) := by linarith

/-- Actual finite eleven-term bound with a literal ceiling and the exact
large-prime-square denominator. No asymptotic input is a hypothesis. -/
theorem chenElevenPrimeSum_le_count_add_explicit_error (N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hA : 1 < (N : ℝ) ^ (100 / 1149 : ℝ)) :
    chenElevenPrimeSum N ≤ 4 * (D12Omega N : ℝ) +
      246 * ((Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))) : ℝ) +
        (N : ℝ) / ((N : ℝ) ^ (100 / 1149 : ℝ) - 1)) := by
  have hsum := chenElevenPrimeSum_le_count_add_exceptions N hN
  have herr := chenExceptionalAdditivePrimes_card_cast_le N hA
  linarith

/-- A fixed power bounds the whole exceptional union as soon as `N^a ≥ 2`.
The ceiling contributes at most `2 N^(1-a)` and the prime-square union
contributes at most `2 N^(1-a)`. -/
theorem chenExceptionalAdditivePrimes_card_cast_le_four_rpow (N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hA : 2 ≤ (N : ℝ) ^ (100 / 1149 : ℝ)) :
    ((chenExceptionalAdditivePrimes N).card : ℝ) ≤
      4 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN
  have hX : 1 ≤ (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (0 : ℝ) ≤ 1 - 100 / 1149))
  have hceil : (Nat.ceil ((N : ℝ) ^ (1 - (100 / 1149 : ℝ))) : ℝ) ≤
      2 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) := by
    have hc := Nat.ceil_lt_add_one (le_trans zero_le_one hX)
    linarith
  have hdiv : (N : ℝ) / (N : ℝ) ^ (100 / 1149 : ℝ) =
      (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) := by
    rw [Real.rpow_sub hNpos, Real.rpow_one]
  have hrecip : 1 / ((N : ℝ) ^ (100 / 1149 : ℝ) - 1) ≤
      2 / (N : ℝ) ^ (100 / 1149 : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : 0 < (N : ℝ) ^ (100 / 1149 : ℝ) - 1)
      (by linarith : 0 < (N : ℝ) ^ (100 / 1149 : ℝ))).mpr
    linarith
  have hsq : (N : ℝ) / ((N : ℝ) ^ (100 / 1149 : ℝ) - 1) ≤
      2 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) := by
    calc
      (N : ℝ) / ((N : ℝ) ^ (100 / 1149 : ℝ) - 1) =
          (N : ℝ) * (1 / ((N : ℝ) ^ (100 / 1149 : ℝ) - 1)) := by ring
      _ ≤ (N : ℝ) * (2 / (N : ℝ) ^ (100 / 1149 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg N)
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ (100 / 1149 : ℝ)) := by ring
      _ = 2 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) := by rw [hdiv]
  have herror := chenExceptionalAdditivePrimes_card_cast_le N (by linarith)
  linarith

/-- The manuscript's prime-indexed eleven-term inequality, with a literal
constant in place of `O(N^(1-a))`. This still includes receiver one. -/
theorem chenElevenPrimeSum_sub_error_le_four_D12Omega (N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hA : 2 ≤ (N : ℝ) ^ (100 / 1149 : ℝ)) :
    chenElevenPrimeSum N - 984 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) ≤
      4 * (D12Omega N : ℝ) := by
  have hsum := chenElevenPrimeSum_le_count_add_exceptions N hN
  have herror := chenExceptionalAdditivePrimes_card_cast_le_four_rpow N hN hA
  linarith

end

end ImbalancedChen
