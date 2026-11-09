import ImbalancedChen.Part5OriginalH430ActualMarkedRootConsumer
import ImbalancedChen.CurrentChenUpsilon34OrdinaryUpperMean

/-!
P5.6 / h34: an unconditional *ordinary* envelope for the actual unpaid
original U3/U4 q-to-resolved-marked source discrepancy.

This packet does not identify a quotient q with a historical parent product.
It uses the genuinely resolved, occurrence-weighted positive Phi source
and the already-existing ordinary upper mean of the ORIGINAL sifted
U3/U4 receiver counts. Both overlapping U4 labels are paid separately
in the arithmetic total, with no deduplication of original q receipts.

The bound is useful as an explicit worst-case debt ledger, but is too
weak by itself to prove the sharp upper H430 saving. No H430 count owner,
root sigma identification, signed Euler payment, or closed-cell licence
is inferred from this result.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualUnpaidOrdinaryEnvelope

noncomputable section

open scoped Classical BigOperators
open Filter
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430AllActionOccurrenceSource
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualResolvedMarkedPushforward
open Part5OriginalH430TrueCountMarkedGap
open P2EnhancedTwentyOneSameQWeighted
open Part5UpperTables.OriginalU34

/-- The actual level's unpaid difference, with its own physical Q, the
original q receiver, and multiplicity-preserving resolved-product marks.
No arbitrary D/sigma or q=d hypothesis is introduced. -/
def actualUnpaidAt
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  unpaidOriginalMarkedGap N n p k tau
    (activeProductSupport N n k tau p g)
    (activeProductSigma N n k tau p g)

/-- True generated marked Phi is nonnegative for EVERY resolved level,
including an empty one. This uses actual strictly positive path marks
and the nonnegative original natural source-sieve count. No roughness,
cutoff, or Theta-division hypothesis is needed. -/
theorem actual_resolved_Phi_nonneg
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    0 ≤ Phi N (rootQ N n k tau p)
      (activeProductSupport N n k tau p g)
      (activeProductSigma N n k tau p g) (11/5) := by
  rw [activeProduct_Phi_exact]
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (mark_pos (levelOccurrence l)).le
    (Nat.cast_nonneg _)

/-- For a genuine original receiver, no nonnegative marked source can
make the *unpaid positive part* larger than the original q cardinality.
The inequality is not a claim that this debt is small relative to Theta. -/
theorem actual_unpaid_nonneg_le_original_card
    (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    0 ≤ actualUnpaidAt N n k tau p g ∧
      actualUnpaidAt N n k tau p g ≤
        ((originalReceiver N p).card : ℝ) := by
  have hPhi := actual_resolved_Phi_nonneg N n k tau p g
  have hcard : (0 : ℝ) ≤ ((originalReceiver N p).card : ℝ) :=
    Nat.cast_nonneg _
  dsimp [actualUnpaidAt, unpaidOriginalMarkedGap, originalMarkedDiscrepancy]
  constructor
  · exact le_max_right _ _
  · apply max_le
    · linarith
    · exact hcard

/-- Every original U3/U4 (p,q) receipt is kept under its own tag.
In particular p in the U4 overlap is still present in BOTH sums. -/
def actualU34Unpaid
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) : ℝ :=
  (∑ p ∈ originalBand N .U3,
    actualUnpaidAt N n .U3 tau p (depth .U3 p)) +
  (∑ p ∈ originalBand N .U4,
    actualUnpaidAt N n .U4 tau p (depth .U4 p))

/-- No original receiver is silently lost when bounding the unresolved
marked-source difference. This holds for ANY true generated depths,
without claiming those depths are the final selected-count owners. -/
theorem actual_U34_unpaid_nonneg_le_original_count
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    0 ≤ actualU34Unpaid N n tau depth ∧
    actualU34Unpaid N n tau depth ≤
      currentChenUpsilon3 N + currentChenUpsilon4 N := by
  have h3nonneg :
      0 ≤ ∑ p ∈ originalBand N .U3,
        actualUnpaidAt N n .U3 tau p (depth .U3 p) := by
    apply Finset.sum_nonneg
    intro p hp
    exact (actual_unpaid_nonneg_le_original_card N n .U3 tau p (depth .U3 p)).1
  have h4nonneg :
      0 ≤ ∑ p ∈ originalBand N .U4,
        actualUnpaidAt N n .U4 tau p (depth .U4 p) := by
    apply Finset.sum_nonneg
    intro p hp
    exact (actual_unpaid_nonneg_le_original_card N n .U4 tau p (depth .U4 p)).1
  have h3 :
      (∑ p ∈ originalBand N .U3,
        actualUnpaidAt N n .U3 tau p (depth .U3 p)) ≤
      (∑ p ∈ originalBand N .U3, ((originalReceiver N p).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact (actual_unpaid_nonneg_le_original_card N n .U3 tau p (depth .U3 p)).2
  have h4 :
      (∑ p ∈ originalBand N .U4,
        actualUnpaidAt N n .U4 tau p (depth .U4 p)) ≤
      (∑ p ∈ originalBand N .U4, ((originalReceiver N p).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact (actual_unpaid_nonneg_le_original_card N n .U4 tau p (depth .U4 p)).2
  constructor
  · exact add_nonneg h3nonneg h4nonneg
  · unfold actualU34Unpaid
    calc
      _ ≤ (∑ p ∈ originalBand N .U3, ((originalReceiver N p).card : ℝ)) +
            (∑ p ∈ originalBand N .U4, ((originalReceiver N p).card : ℝ)) :=
          add_le_add h3 h4
      _ = currentChenUpsilon3 N + currentChenUpsilon4 N := by
        rw [original_U34_eq_tagged_card, original_tagged_card]
        simp only [Nat.cast_add, Nat.cast_sum]

/-- A genuine unconditional (eventual, even-N) envelope for the TOTAL
unpaid arithmetic q-minus-marked deficit. It reuses the installed
ordinary U3/U4 upper means with epsilon split in half, retaining
the same singular normalization and the two original labelled bands.

Crucially, this is an ORDINARY upper coefficient, not an H430
coefficient and not an o(Theta) payment. It cannot close h34. -/
theorem eventually_actual_U34_unpaid_le_ordinary_upper
    (n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      actualU34Unpaid N n tau depth ≤
        (currentChenSinglePrimeOrdinaryUpperIntegral (1/3) +
          currentChenSinglePrimeOrdinaryUpperIntegral (59/250) +
          epsilon) * singularNormalization N := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards
    [ImbalancedChen.eventually_currentChenUpsilon3_Upsilon4_le_ordinary_upper_mean
      (epsilon / 2) hhalf] with N hN
  intro hEven
  obtain ⟨h3, h4⟩ := hN hEven
  calc
    actualU34Unpaid N n tau depth ≤
        currentChenUpsilon3 N + currentChenUpsilon4 N :=
      (actual_U34_unpaid_nonneg_le_original_count N n tau depth).2
    _ ≤ (currentChenSinglePrimeOrdinaryUpperIntegral (1/3) +
        epsilon / 2) * singularNormalization N +
        (currentChenSinglePrimeOrdinaryUpperIntegral (59/250) +
        epsilon / 2) * singularNormalization N :=
      add_le_add h3 h4
    _ = (currentChenSinglePrimeOrdinaryUpperIntegral (1/3) +
        currentChenSinglePrimeOrdinaryUpperIntegral (59/250) +
        epsilon) * singularNormalization N := by ring

end
end ImbalancedChen.Part5OriginalH430ActualUnpaidOrdinaryEnvelope
