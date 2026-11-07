import ImbalancedChen.CurrentP5CausalCommonReceiverPartition
import ImbalancedChen.CurrentChenLowerScale

/-!
# Eventual assembly from actual common-policy cell contributions

Source-only candidate, uncompiled. The first import is the preceding
source-only candidate, intended for the corresponding ImbalancedChen path.
The index type is fixed and finite; its actual receiver cells may depend
on N. Every supplier bounds one concrete local signed eleven-term source.
No supplier of the completed paired-weight mean is an input.

Unequal positive local accuracies are charged by the finite absolute
amplification budget. A budget-plus-one allocation also works for zero
total amplification and empty finite types. The classifier specialization
uses the original shared-cell source equality. The direct partition API
is retained because a total map from Nat to an empty index type cannot
serve as a meaningful empty-partition interface.
-/

namespace ImbalancedChen

open scoped BigOperators Classical
open Filter

noncomputable section

/-- The actual eleven-term contribution of one receiver cell. All source
definitions and the original E come from the preceding concrete module. -/
def p5CausalPartitionCellContribution (N : ℕ) (E : ℕ × ℕ → Prop)
    (cell : Finset ℕ) : ℝ :=
  ∑ i, p5CausalReceiverLedgerWeight i *
    (∑ P ∈ cell, p5CausalReceiverOccurrence N E P i)

theorem p5CausalPartitionCellContribution_classified {ι : Type*} [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (label : ℕ → ι) (a : ι) :
    p5CausalPartitionCellContribution N E (p5CausalReceiverCell N label a) =
      p5CausalCellSignedLedger N E label a := rfl

theorem p5CausalPartitionCellContribution_sum {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (cells : ι → Finset ℕ)
    (hdisjoint : Set.PairwiseDisjoint (Finset.univ : Set ι) cells)
    (hcover : Finset.univ.biUnion cells = chenAdditivePrimeCarrier N) :
    (∑ a, p5CausalPartitionCellContribution N E (cells a)) =
      currentChenPairedPrimeSum N E := by
  exact p5Causal_disjoint_partition_signed_ledger N E Finset.univ cells hdisjoint hcover

theorem p5CausalCellAssembly_normalization_nonneg (N : ℕ) :
    0 ≤ singularNormalization N := by
  exact div_nonneg
    (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)

def p5CausalCellErrorBudget {ι : Type*} [Fintype ι]
    (amplification accuracy : ι → ℝ) : ℝ :=
  ∑ a, |amplification a| * accuracy a

/-- Finite common-partition assembly with independent one-sided cell
errors. No whole-weight lower bound appears among the inputs. -/
theorem p5CausalCellAssembly_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (cells : ι → Finset ℕ)
    (hdisjoint : Set.PairwiseDisjoint (Finset.univ : Set ι) cells)
    (hcover : Finset.univ.biUnion cells = chenAdditivePrimeCarrier N)
    (mass amplification accuracy : ι → ℝ)
    (hlocal : ∀ a, (mass a - |amplification a| * accuracy a) *
      singularNormalization N ≤ p5CausalPartitionCellContribution N E (cells a)) :
    ((∑ a, mass a) - p5CausalCellErrorBudget amplification accuracy) *
      singularNormalization N ≤ currentChenPairedPrimeSum N E := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a ha => hlocal a)
  rw [p5CausalPartitionCellContribution_sum N E cells hdisjoint hcover] at hsum
  simpa only [p5CausalCellErrorBudget, Finset.sum_sub_distrib,
    Finset.sum_mul, sub_mul] using hsum

/-- The fixed finite family of local thresholds is intersected once.
Classifiers/cells may vary with N; the index type does not. -/
theorem p5CausalCellAssembly_eventually_of_accuracies {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (E : ℕ → ℕ × ℕ → Prop) (cells : ℕ → ι → Finset ℕ)
    (hdisjoint : ∀ N, Set.PairwiseDisjoint (Finset.univ : Set ι) (cells N))
    (hcover : ∀ N, Finset.univ.biUnion (cells N) = chenAdditivePrimeCarrier N)
    (mass amplification accuracy : ι → ℝ)
    (hlocal : ∀ a, ∀ᶠ N : ℕ in atTop, Even N →
      (mass a - |amplification a| * accuracy a) * singularNormalization N ≤
        p5CausalPartitionCellContribution N (E N) (cells N a)) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((∑ a, mass a) - p5CausalCellErrorBudget amplification accuracy) *
        singularNormalization N ≤ currentChenPairedPrimeSum N (E N) := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ a, Even N →
      (mass a - |amplification a| * accuracy a) * singularNormalization N ≤
        p5CausalPartitionCellContribution N (E N) (cells N a) :=
    eventually_all.mpr hlocal
  filter_upwards [hall] with N hN
  intro hEven
  exact p5CausalCellAssembly_finite N (E N) (cells N) (hdisjoint N) (hcover N)
    mass amplification accuracy (fun a => hN a hEven)

/-- Priority weights can allocate genuinely unequal local accuracies. -/
def p5CausalCellAllocatedAccuracy {ι : Type*} [Fintype ι]
    (epsilon : ℝ) (amplification priority : ι → ℝ) (a : ι) : ℝ :=
  epsilon * priority a / (1 + p5CausalCellErrorBudget amplification priority)

theorem p5CausalCellErrorBudget_nonneg {ι : Type*} [Fintype ι]
    (amplification priority : ι → ℝ) (hpriority : ∀ a, 0 ≤ priority a) :
    0 ≤ p5CausalCellErrorBudget amplification priority := by
  exact Finset.sum_nonneg (fun a ha => mul_nonneg (abs_nonneg _) (hpriority a))

theorem p5CausalCellAllocatedAccuracy_pos {ι : Type*} [Fintype ι]
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (amplification priority : ι → ℝ) (hpriority : ∀ a, 0 < priority a) (a : ι) :
    0 < p5CausalCellAllocatedAccuracy epsilon amplification priority a := by
  have hB := p5CausalCellErrorBudget_nonneg amplification priority
    (fun a => (hpriority a).le)
  exact div_pos (mul_pos hepsilon (hpriority a)) (by linarith)

/-- The allocation never divides by the number of cells or by the total
absolute budget. Empty families and zero amplifications are included. -/
theorem p5CausalCellAllocatedAccuracy_budget {ι : Type*} [Fintype ι]
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (amplification priority : ι → ℝ) (hpriority : ∀ a, 0 ≤ priority a) :
    p5CausalCellErrorBudget amplification
      (p5CausalCellAllocatedAccuracy epsilon amplification priority) ≤ epsilon := by
  have hB := p5CausalCellErrorBudget_nonneg amplification priority hpriority
  have hden : 0 < 1 + p5CausalCellErrorBudget amplification priority := by linarith
  have hfrac : p5CausalCellErrorBudget amplification priority /
      (1 + p5CausalCellErrorBudget amplification priority) ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith
  calc
    p5CausalCellErrorBudget amplification
        (p5CausalCellAllocatedAccuracy epsilon amplification priority) =
        (epsilon / (1 + p5CausalCellErrorBudget amplification priority)) *
          p5CausalCellErrorBudget amplification priority := by
      simp only [p5CausalCellErrorBudget, p5CausalCellAllocatedAccuracy]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = epsilon * (p5CausalCellErrorBudget amplification priority /
        (1 + p5CausalCellErrorBudget amplification priority)) := by ring
    _ ≤ epsilon * 1 := mul_le_mul_of_nonneg_left hfrac hepsilon
    _ = epsilon := mul_one _

/-- Actual cell suppliers, with the requested accuracy chosen before N,
assemble into the actual paired-prime-sum mean at their finite mass sum. -/
theorem p5CausalCellAssembly_eventual_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ℕ → ℕ × ℕ → Prop) (cells : ℕ → ι → Finset ℕ)
    (hdisjoint : ∀ N, Set.PairwiseDisjoint (Finset.univ : Set ι) (cells N))
    (hcover : ∀ N, Finset.univ.biUnion (cells N) = chenAdditivePrimeCarrier N)
    (mass amplification priority : ι → ℝ) (hpriority : ∀ a, 0 < priority a)
    (hlocal : ∀ a, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N →
        (mass a - |amplification a| * delta) * singularNormalization N ≤
          p5CausalPartitionCellContribution N (E N) (cells N a))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((∑ a, mass a) - epsilon) * singularNormalization N ≤
        currentChenPairedPrimeSum N (E N) := by
  let accuracy := p5CausalCellAllocatedAccuracy epsilon amplification priority
  have hacc : ∀ a, 0 < accuracy a :=
    p5CausalCellAllocatedAccuracy_pos hepsilon amplification priority hpriority
  have hbudget : p5CausalCellErrorBudget amplification accuracy ≤ epsilon :=
    p5CausalCellAllocatedAccuracy_budget hepsilon.le amplification priority
      (fun a => (hpriority a).le)
  have hmean := p5CausalCellAssembly_eventually_of_accuracies E cells hdisjoint hcover
    mass amplification accuracy (fun a => hlocal a (accuracy a) (hacc a))
  filter_upwards [hmean] with N hN
  intro hEven
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hbudget _)
    (p5CausalCellAssembly_normalization_nonneg N)).trans (hN hEven)

/-- The numerical certificate is only a finite comparison at the original
4*currentC scale; the actual mean is produced from the local suppliers. -/
theorem p5CausalCellAssembly_eventual_current_mean {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (E : ℕ → ℕ × ℕ → Prop) (cells : ℕ → ι → Finset ℕ)
    (hdisjoint : ∀ N, Set.PairwiseDisjoint (Finset.univ : Set ι) (cells N))
    (hcover : ∀ N, Finset.univ.biUnion (cells N) = chenAdditivePrimeCarrier N)
    (mass amplification priority : ι → ℝ) (hpriority : ∀ a, 0 < priority a)
    (hlocal : ∀ a, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N →
        (mass a - |amplification a| * delta) * singularNormalization N ≤
          p5CausalPartitionCellContribution N (E N) (cells N a))
    (hnumeric : 4 * currentC ≤ ∑ a, mass a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (4 * currentC - epsilon) * singularNormalization N ≤
        currentChenPairedPrimeSum N (E N) := by
  filter_upwards [p5CausalCellAssembly_eventual_mean E cells hdisjoint hcover
    mass amplification priority hpriority hlocal epsilon hepsilon] with N hN
  intro hEven
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hnumeric epsilon)
    (p5CausalCellAssembly_normalization_nonneg N)).trans (hN hEven)

/-- Full eventual D12 consumer of the local causal-contribution route.
The negligible count loss is the already proved uniform-selector loss. -/
theorem p5CausalCellAssembly_eventual_D12 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ℕ → ℕ × ℕ → Prop) (cells : ℕ → ι → Finset ℕ)
    (hdisjoint : ∀ N, Set.PairwiseDisjoint (Finset.univ : Set ι) (cells N))
    (hcover : ∀ N, Finset.univ.biUnion (cells N) = chenAdditivePrimeCarrier N)
    (mass amplification priority : ι → ℝ) (hpriority : ∀ a, 0 < priority a)
    (hlocal : ∀ a, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N →
        (mass a - |amplification a| * delta) * singularNormalization N ≤
          p5CausalPartitionCellContribution N (E N) (cells N a))
    (hnumeric : 4 * currentC ≤ ∑ a, mass a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  have htwo : 0 < 2 * epsilon := by linarith
  filter_upwards [p5CausalCellAssembly_eventual_current_mean E cells hdisjoint hcover
    mass amplification priority hpriority hlocal hnumeric (2 * epsilon) htwo,
    eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12
      (2 * epsilon) htwo] with N hmean hcount
  intro hEven
  exact currentChen_lower_scale_of_equal_finite_budgets (E N)
    (hmean hEven) (hcount (E N))

/-- Varying classifiers still have one fixed finite index family. This
is the direct local-cell mean interface for a finite numerical mass sum. -/
theorem p5CausalClassifiedCellAssembly_eventual_mean {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (E : ℕ → ℕ × ℕ → Prop) (label : ℕ → ℕ → ι)
    (mass amplification priority : ι → ℝ) (hpriority : ∀ a, 0 < priority a)
    (hlocal : ∀ a, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N →
        (mass a - |amplification a| * delta) * singularNormalization N ≤
          p5CausalCellSignedLedger N (E N) (label N) a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((∑ a, mass a) - epsilon) * singularNormalization N ≤
        currentChenPairedPrimeSum N (E N) := by
  apply p5CausalCellAssembly_eventual_mean E
    (fun N a => p5CausalReceiverCell N (label N) a)
    (fun N a ha b hb hab => p5CausalReceiverCell_disjoint N (label N) hab)
    (fun N => p5CausalReceiverCell_cover N (label N))
    mass amplification priority hpriority
    ?_ epsilon hepsilon
  intro a delta hdelta
  simpa only [p5CausalPartitionCellContribution_classified] using hlocal a delta hdelta

/-- The requested varying-classifier D12 specialization, on precisely
the shared actual cells of the preceding common-partition module. -/
theorem p5CausalClassifiedCellAssembly_eventual_D12 {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (E : ℕ → ℕ × ℕ → Prop) (label : ℕ → ℕ → ι)
    (mass amplification priority : ι → ℝ) (hpriority : ∀ a, 0 < priority a)
    (hlocal : ∀ a, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N →
        (mass a - |amplification a| * delta) * singularNormalization N ≤
          p5CausalCellSignedLedger N (E N) (label N) a)
    (hnumeric : 4 * currentC ≤ ∑ a, mass a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  apply p5CausalCellAssembly_eventual_D12 E
    (fun N a => p5CausalReceiverCell N (label N) a)
    (fun N a ha b hb hab => p5CausalReceiverCell_disjoint N (label N) hab)
    (fun N => p5CausalReceiverCell_cover N (label N))
    mass amplification priority hpriority
    ?_ hnumeric epsilon hepsilon
  intro a delta hdelta
  simpa only [p5CausalPartitionCellContribution_classified] using hlocal a delta hdelta

/-- For a genuinely empty finite partition the original actual source
is zero. No impossible Nat-to-empty classifier is introduced. -/
theorem p5CausalEmptyPartition_source_eq_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (N : ℕ) (E : ℕ × ℕ → Prop) (cells : ι → Finset ℕ)
    (hcover : Finset.univ.biUnion cells = chenAdditivePrimeCarrier N) :
    currentChenPairedPrimeSum N E = 0 := by
  have hcarrier : chenAdditivePrimeCarrier N = ∅ := by simpa using hcover.symm
  simp [currentChenPairedPrimeSum, hcarrier]

/-- The original positive numerical target cannot be certified by an
empty mass sum; the empty boundary cannot manufacture a lower constant. -/
theorem p5CausalEmptyPartition_no_current_certificate {ι : Type*}
    [Fintype ι] [IsEmpty ι] (mass : ι → ℝ)
    (hnumeric : 4 * currentC ≤ ∑ a, mass a) : False := by
  have hzero : 4 * currentC ≤ 0 := by simpa using hnumeric
  norm_num [currentC] at hzero

end

end ImbalancedChen
