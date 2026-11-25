import ImbalancedChen.P5ZU1011OriginalSixteenInteriorArithmetic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Exact reflection of the TRUE original sixteen-policy logarithmic gate into
natural prime-prefix and selected-subproduct square tests. Every inequality
is strict on both sides, including the separate W gate and largest-prime
threshold. This supplies an actual arithmetic eligibility predicate for a
later adaptive winner; no analytic coefficient/count upper bound is used.
W critical-interval/factorization and all AP/density licenses remain separate.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenArithmeticEligibility

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenInteriorArithmetic P5U1011JointOverlap

theorem slot_rpow {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (j : Fin 4) :
    (N : ℝ) ^ coordinates N t j = (slots t j : ℝ) :=
  actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) j

/-- Equality, not merely a one-sided estimate, on every strict original
full-prefix square, retaining the exact natural primes and their order. -/
theorem fullSquare_rpow {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (j : Fin 4) :
    (N : ℝ) ^ fullSquare j (coordinates N t) =
      (prefixProduct j t : ℝ) * (slots t j : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hsum : (∑ i : Fin 4, if i.val < j.val then coordinates N t i else 0) =
      ∑ i ∈ prefixIndices j, coordinates N t i := by
    simp [prefixIndices,Finset.sum_filter]
  unfold prefixProduct
  rw [fullSquare,hsum,Real.rpow_add hpos,subproduct_rpow hN ht (prefixIndices j),
    show 2 * coordinates N t j = coordinates N t j * (2 : ℕ) by ring,
    Real.rpow_mul_natCast hpos.le,slot_rpow hN ht j]

/-- The selected-square exponent evaluates to precisely the original
selected natural product times the EARLIER UNSELECTED prefix times pj². -/
theorem selectedSquare_rpow {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (p : Policy) (j : Fin 4) :
    (N : ℝ) ^ selectedSquare p j (coordinates N t) =
      (selectedProduct p t : ℝ) * (earlierRemainderProduct p j t : ℝ) * (slots t j : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hsum : (∑ i : Fin 4,
      if i.val < j.val ∧ ¬Selected p i then coordinates N t i else 0) =
        ∑ i ∈ earlierRemainderIndices p j, coordinates N t i := by
    simp [earlierRemainderIndices,Finset.sum_filter]
  unfold earlierRemainderProduct
  rw [selectedSquare,hsum,Real.rpow_add hpos,Real.rpow_add hpos,
    selectedProduct_rpow hN ht p,subproduct_rpow hN ht (earlierRemainderIndices p j),
    show 2 * coordinates N t j = coordinates N t j * (2 : ℕ) by ring,
    Real.rpow_mul_natCast hpos.le,slot_rpow hN ht j]

def ArithmeticEligible (p : Policy) (N : ℕ) (t : Four) : Prop :=
  (N : ℝ) < (N : ℝ) ^ (2 * cap p (coordinates N t)) ∧
    (∀ j : Fin 4, (prefixProduct j t : ℝ) * (slots t j : ℝ) ^ 2 <
      (N : ℝ) ^ cap p (coordinates N t)) ∧
    (if p.val < 15 then ∀ j : Fin 4, ¬Selected p j →
      (selectedProduct p t : ℝ) * (earlierRemainderProduct p j t : ℝ) * (slots t j : ℝ) ^ 2 <
        (N : ℝ) ^ cap p (coordinates N t)
     else (N : ℝ) * (slots t 0 : ℝ) < (N : ℝ) ^ (2 * cap p (coordinates N t)) ∧
       (slots t 0 : ℝ) < (N : ℝ) ^ (25 / 128 : ℝ))

/-- Exact arithmetic/logarithmic dictionary on the original actual joint
prime carrier. It covers all fifteen true mask branches AND the distinct W
branch, without requiring any wall to have zero arithmetic mass. -/
theorem arithmeticEligible_iff {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E) (p : Policy) :
    ArithmeticEligible p N t ↔ TypedEligible p (coordinates N t) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hhalf : ((N : ℝ) < (N : ℝ) ^ (2 * cap p (coordinates N t))) ↔
      (1 / 2 : ℝ) < cap p (coordinates N t) := by
    have hh : ((N : ℝ) ^ (1 : ℝ) < (N : ℝ) ^ (2 * cap p (coordinates N t))) ↔
        (1 / 2 : ℝ) < cap p (coordinates N t) := by
      rw [Real.rpow_lt_rpow_left_iff hNr]
      constructor <;> intro h <;> linarith
    simpa only [Real.rpow_one] using hh
  have hfull (j : Fin 4) :
      ((prefixProduct j t : ℝ) * (slots t j : ℝ) ^ 2 < (N : ℝ) ^ cap p (coordinates N t)) ↔
        fullSquare j (coordinates N t) < cap p (coordinates N t) := by
    rw [← fullSquare_rpow hN ht j,Real.rpow_lt_rpow_left_iff hNr]
  have hselected (j : Fin 4) :
      ((selectedProduct p t : ℝ) * (earlierRemainderProduct p j t : ℝ) * (slots t j : ℝ) ^ 2 <
        (N : ℝ) ^ cap p (coordinates N t)) ↔
        selectedSquare p j (coordinates N t) < cap p (coordinates N t) := by
    rw [← selectedSquare_rpow hN ht p j,Real.rpow_lt_rpow_left_iff hNr]
  have hwgate : ((N : ℝ) * (slots t 0 : ℝ) < (N : ℝ) ^ (2 * cap p (coordinates N t))) ↔
      (1 + coordinates N t 0) / 2 < cap p (coordinates N t) := by
    have hp : (N : ℝ) ^ (1 + coordinates N t 0) = (N : ℝ) * (slots t 0 : ℝ) := by
      rw [Real.rpow_add hpos,Real.rpow_one,slot_rpow hN ht 0]
    rw [← hp,Real.rpow_lt_rpow_left_iff hNr]
    constructor <;> intro h <;> linarith
  have hwlargest : ((slots t 0 : ℝ) < (N : ℝ) ^ (25 / 128 : ℝ)) ↔
      coordinates N t 0 < (25 / 128 : ℝ) := by
    rw [← slot_rpow hN ht 0,Real.rpow_lt_rpow_left_iff hNr]
  unfold ArithmeticEligible TypedEligible
  simp only [hhalf,hfull,hselected,hwgate,hwlargest]

/-- The natural-number bank reader is total: no out-of-bank integer can
create an ordinary action. These exact tests may select a different action
at every labelled tuple, while preserving the original16 bank. -/
def arithmeticEligible (j N : ℕ) (t : Four) : Prop :=
  if hj : j < 16 then ArithmeticEligible ⟨j,hj⟩ N t else False

theorem arithmetic_bank_eligible_iff {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E) (j : ℕ) :
    arithmeticEligible j N t ↔ U1011OriginalSixteenPolicyBank.eligible j (coordinates N t) := by
  by_cases hj : j < 16
  · simp only [arithmeticEligible,U1011OriginalSixteenPolicyBank.eligible,dif_pos hj]
    exact arithmeticEligible_iff hN ht ⟨j,hj⟩
  · simp only [arithmeticEligible,U1011OriginalSixteenPolicyBank.eligible,dif_neg hj]

end
end ImbalancedChen.P5Z.U1011OriginalSixteenArithmeticEligibility
