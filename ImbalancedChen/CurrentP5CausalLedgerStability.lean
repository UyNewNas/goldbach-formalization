import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.CurrentChenLowerScale

/-!
# Quantitative stability of the literal current causal ledger

Source-only candidate, uncompiled. Indices zero through ten are the actual
eleven occurrences in `CurrentChenMeanLedger`, in their original order.
`E` is one literal prime-pair predicate: the same complement is retained in
occurrences six and eleven. No replacement selection is defined here.

Unlike the existing uniform `14 * delta` lemma, these results retain each
individual residual, permit an arbitrary finite partial ledger, and charge
its complement as an explicit tail. The final finite consumer uses the
original `currentC`, `singularNormalization`, and division by four.
The analytic suppliers of the causal occurrence estimates remain open.
-/

namespace ImbalancedChen

open scoped BigOperators

noncomputable section

/-- Signed root coefficients before the unique Chen-quarter normalization. -/
def p5CausalOccurrenceWeight : Fin 11 → ℝ :=
  ![3, 1, -1, -1, 1, 1, -2, -1, -1, -1, -1]

/-- The concrete occurrences; in particular neither switched tuple
multiplicities nor the full eleventh last-prime interval is changed. -/
def p5CausalActualOccurrence (N : ℕ) (E : ℕ × ℕ → Prop) : Fin 11 → ℝ :=
  ![currentChenUpsilon1 N, currentChenUpsilon2 N,
    currentChenUpsilon3 N, currentChenUpsilon4 N,
    currentChenUpsilon5 N, currentChenUpsilon6 N E,
    currentChenUpsilon7 N, currentChenUpsilon8 N,
    currentChenUpsilon9 N, currentChenUpsilon10 N,
    currentChenUpsilon11 N E]

def p5CausalSignedLedger (v : Fin 11 → ℝ) : ℝ :=
  ∑ i, p5CausalOccurrenceWeight i * v i

/-- A residual is in the same units as an actual Upsilon count. -/
def p5CausalOccurrenceResidual (N : ℕ) (E : ℕ × ℕ → Prop)
    (model : Fin 11 → ℝ) (i : Fin 11) : ℝ :=
  p5CausalActualOccurrence N E i - model i

/-- Positive error budget with all eleven absolute coefficient weights. -/
def p5CausalL1Error (N : ℕ) (E : ℕ × ℕ → Prop)
    (model : Fin 11 → ℝ) : ℝ :=
  ∑ i, |p5CausalOccurrenceWeight i| *
    |p5CausalOccurrenceResidual N E model i|

/-- A separately supplied error for each occurrence, before normalization. -/
def p5CausalWeightedBudget (e : Fin 11 → ℝ) : ℝ :=
  ∑ i, |p5CausalOccurrenceWeight i| * e i

theorem p5CausalSignedLedger_actual (N : ℕ) (E : ℕ × ℕ → Prop) :
    p5CausalSignedLedger (p5CausalActualOccurrence N E) =
      currentChenPairedPrimeSum N E := by
  rw [currentChenPairedPrimeSum_eq_upsilon]
  simp [p5CausalSignedLedger, p5CausalActualOccurrence,
    p5CausalOccurrenceWeight, Fin.sum_univ_succ] <;> ring

/-- This is the unequal-error aggregate, with both exceptional
coefficients displayed explicitly. -/
theorem p5CausalWeightedBudget_eq (e : Fin 11 → ℝ) :
    p5CausalWeightedBudget e =
      3 * e 0 + e 1 + e 2 + e 3 + e 4 + e 5 +
        2 * e 6 + e 7 + e 8 + e 9 + e 10 := by
  norm_num [p5CausalWeightedBudget, p5CausalOccurrenceWeight,
    Fin.sum_univ_succ]

/-- Exact signed error, retaining cancellation before taking one absolute
value outside the signed sum. -/
theorem p5CausalSignedResidual_eq (N : ℕ) (E : ℕ × ℕ → Prop)
    (model : Fin 11 → ℝ) :
    p5CausalSignedLedger (p5CausalOccurrenceResidual N E model) =
      currentChenPairedPrimeSum N E - p5CausalSignedLedger model := by
  rw [← p5CausalSignedLedger_actual N E]
  simp only [p5CausalSignedLedger, p5CausalOccurrenceResidual,
    mul_sub, Finset.sum_sub_distrib]

/-- Concrete L1 stability: unequal local approximation errors are charged
against the actual paired prime sum, on its original mask. -/
theorem p5Causal_abs_error_le (N : ℕ) (E : ℕ × ℕ → Prop)
    (model : Fin 11 → ℝ) :
    |currentChenPairedPrimeSum N E - p5CausalSignedLedger model| ≤
      p5CausalL1Error N E model := by
  rw [← p5CausalSignedResidual_eq N E model]
  simpa only [p5CausalSignedLedger, p5CausalL1Error, abs_mul] using
    (Finset.abs_sum_le_sum_abs
      (fun i => p5CausalOccurrenceWeight i *
        p5CausalOccurrenceResidual N E model i) Finset.univ)

/-- A partial causal ledger is usable without silently discarding the
unwritten occurrences. Their residuals appear as the complement tail. -/
theorem p5Causal_abs_error_le_partial_add_tail
    (N : ℕ) (E : ℕ × ℕ → Prop) (model : Fin 11 → ℝ)
    (s : Finset (Fin 11)) :
    |currentChenPairedPrimeSum N E - p5CausalSignedLedger model| ≤
      (∑ i ∈ s, |p5CausalOccurrenceWeight i| *
        |p5CausalOccurrenceResidual N E model i|) +
      ∑ i ∈ Finset.univ \ s, |p5CausalOccurrenceWeight i| *
        |p5CausalOccurrenceResidual N E model i| := by
  have hsplit :
      (∑ i ∈ Finset.univ \ s, |p5CausalOccurrenceWeight i| *
        |p5CausalOccurrenceResidual N E model i|) +
      (∑ i ∈ s, |p5CausalOccurrenceWeight i| *
        |p5CausalOccurrenceResidual N E model i|) =
      p5CausalL1Error N E model := by
    exact Finset.sum_sdiff (Finset.subset_univ s)
  have h := p5Causal_abs_error_le N E model
  rw [← hsplit] at h
  simpa only [add_comm] using h

/-- Separate partial and tail budgets can be supplied by different
completed analytic subchains; all omitted terms are still paid for. -/
theorem p5Causal_abs_error_le_of_partial_tail_budgets
    (N : ℕ) (E : ℕ × ℕ → Prop) (model : Fin 11 → ℝ)
    (s : Finset (Fin 11)) {localBudget tailBudget : ℝ}
    (hlocal : (∑ i ∈ s, |p5CausalOccurrenceWeight i| *
      |p5CausalOccurrenceResidual N E model i|) ≤ localBudget)
    (htail : (∑ i ∈ Finset.univ \ s, |p5CausalOccurrenceWeight i| *
      |p5CausalOccurrenceResidual N E model i|) ≤ tailBudget) :
    |currentChenPairedPrimeSum N E - p5CausalSignedLedger model| ≤
      localBudget + tailBudget := by
  exact (p5Causal_abs_error_le_partial_add_tail N E model s).trans
    (add_le_add hlocal htail)

/-- Coefficient models use the exact existing singular normalization. -/
theorem p5CausalSignedLedger_normalized (N : ℕ) (b : Fin 11 → ℝ) :
    p5CausalSignedLedger (fun i => b i * singularNormalization N) =
      p5CausalSignedLedger b * singularNormalization N := by
  simp only [p5CausalSignedLedger, Finset.sum_mul, mul_assoc]

/-- Propagation from eleven independently sized normalized residuals.
No common error size and no whole-weight mean premise are required. -/
theorem p5CausalL1Error_le_weighted_normalized_budget
    (N : ℕ) (E : ℕ × ℕ → Prop) (b e : Fin 11 → ℝ)
    (hterm : ∀ i,
      |p5CausalActualOccurrence N E i - b i * singularNormalization N| ≤
        e i * singularNormalization N) :
    p5CausalL1Error N E (fun i => b i * singularNormalization N) ≤
      p5CausalWeightedBudget e * singularNormalization N := by
  calc
    p5CausalL1Error N E (fun i => b i * singularNormalization N) ≤
        ∑ i, |p5CausalOccurrenceWeight i| *
          (e i * singularNormalization N) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg _)
    _ = p5CausalWeightedBudget e * singularNormalization N := by
      simp only [p5CausalWeightedBudget, Finset.sum_mul, mul_assoc]

theorem p5Causal_abs_normalized_error_le
    (N : ℕ) (E : ℕ × ℕ → Prop) (b e : Fin 11 → ℝ)
    (hterm : ∀ i,
      |p5CausalActualOccurrence N E i - b i * singularNormalization N| ≤
        e i * singularNormalization N) :
    |currentChenPairedPrimeSum N E -
        p5CausalSignedLedger b * singularNormalization N| ≤
      p5CausalWeightedBudget e * singularNormalization N := by
  have h := (p5Causal_abs_error_le N E
    (fun i => b i * singularNormalization N)).trans
      (p5CausalL1Error_le_weighted_normalized_budget N E b e hterm)
  simpa only [p5CausalSignedLedger_normalized] using h

/-- Only the adverse direction of each occurrence is needed for a lower
bound: positive coefficients charge `model - actual`, and negative
coefficients charge `actual - model`. This accepts the manuscript's
lower/upper estimates without demanding two-sided occurrence asymptotics. -/
theorem p5Causal_weight_lower_of_oriented_errors
    (N : ℕ) (E : ℕ × ℕ → Prop) (b e : Fin 11 → ℝ)
    (hterm : ∀ i,
      p5CausalOccurrenceWeight i *
        (b i * singularNormalization N - p5CausalActualOccurrence N E i) ≤
      |p5CausalOccurrenceWeight i| * e i * singularNormalization N) :
    (p5CausalSignedLedger b - p5CausalWeightedBudget e) *
        singularNormalization N ≤ currentChenPairedPrimeSum N E := by
  have hsum :
      (∑ i, p5CausalOccurrenceWeight i *
        (b i * singularNormalization N - p5CausalActualOccurrence N E i)) ≤
      ∑ i, |p5CausalOccurrenceWeight i| * e i * singularNormalization N := by
    exact Finset.sum_le_sum (fun i hi => hterm i)
  have hleft :
      (∑ i, p5CausalOccurrenceWeight i *
        (b i * singularNormalization N - p5CausalActualOccurrence N E i)) =
      p5CausalSignedLedger b * singularNormalization N -
        currentChenPairedPrimeSum N E := by
    rw [← p5CausalSignedLedger_actual N E]
    simp only [p5CausalSignedLedger, mul_sub, Finset.sum_sub_distrib,
      Finset.sum_mul, mul_assoc]
  have hright :
      (∑ i, |p5CausalOccurrenceWeight i| * e i * singularNormalization N) =
      p5CausalWeightedBudget e * singularNormalization N := by
    simp only [p5CausalWeightedBudget, Finset.sum_mul]
  rw [hleft, hright] at hsum
  nlinarith only [hsum]

/-- The coefficient minus the full unequal-error budget is a finite
lower bound for the actual weight. -/
theorem p5Causal_weight_lower_of_normalized_errors
    (N : ℕ) (E : ℕ × ℕ → Prop) (b e : Fin 11 → ℝ)
    (hterm : ∀ i,
      |p5CausalActualOccurrence N E i - b i * singularNormalization N| ≤
        e i * singularNormalization N) :
    (p5CausalSignedLedger b - p5CausalWeightedBudget e) *
        singularNormalization N ≤ currentChenPairedPrimeSum N E := by
  have h := (abs_le.mp (p5Causal_abs_normalized_error_le N E b e hterm)).1
  nlinarith only [h]

/-- Finite connection to the original count constant. Its analytic inputs
are eleven concrete residual bounds, a coefficient calculation and the
existing count-exception budget. It does not assume `hLower` or a full
paired-weight mean estimate. -/
theorem p5Causal_lower_scale_of_unequal_errors
    {N : ℕ} (E : ℕ × ℕ → Prop) (b e : Fin 11 → ℝ)
    {epsilon etaCount : ℝ}
    (hterm : ∀ i,
      p5CausalOccurrenceWeight i *
        (b i * singularNormalization N - p5CausalActualOccurrence N E i) ≤
      |p5CausalOccurrenceWeight i| * e i * singularNormalization N)
    (hcoefficient : 4 * currentC ≤ p5CausalSignedLedger b)
    (hbudget : p5CausalWeightedBudget e + etaCount ≤ 4 * epsilon)
    (hcount : currentChenPairedPrimeSum N E -
      etaCount * singularNormalization N ≤ 4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  have hH : 0 ≤ singularNormalization N := by
    exact div_nonneg
      (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hcoeffH := mul_le_mul_of_nonneg_right hcoefficient hH
  have hlocal := p5Causal_weight_lower_of_oriented_errors N E b e hterm
  have hweight :
      (4 * currentC - p5CausalWeightedBudget e) * singularNormalization N ≤
        currentChenPairedPrimeSum N E := by
    nlinarith only [hcoeffH, hlocal]
  exact currentChen_lower_scale_of_finite_budgets E hbudget hweight hcount

end

end ImbalancedChen
