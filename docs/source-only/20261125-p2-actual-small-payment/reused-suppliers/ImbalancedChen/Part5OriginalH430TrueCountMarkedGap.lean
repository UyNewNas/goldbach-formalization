import ImbalancedChen.Part5OriginalH430PositiveFibreThetaDirection
import ImbalancedChen.P2EnhancedTwentyOneSourceComparison

/-!
P5.6 / h34: a REAL original U3/U4 q-count to positive marked-family
finite source estimate, preserving the exact UNPAID arithmetic/product
matching gap instead of postulating q=B or count=Phi.

The finite 21-term source estimate comes from the already installed
P2EnhancedTwentyOneSourceComparison. Its threshold is chosen BEFORE
the even target N and every root, physical Q, and positive marked family.
This packet applies that estimate at the actual rootQ for each original
U3/U4 selected prime p, then sums the literal original quotient-prime
counts with both overlapping root labels. Mark indices d are NOT q.

The nonnegative source gap is the positive part of
  card(originalReceiver N p) - 5 * Phi N rootQ D sigma (11/5).
It is recorded and NOT bounded or identified with zero. No H430
selected owner, integral, signed Euler payment, or full/selected/inherited
filter is inferred. This is not the final upper H430 count theorem.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430TrueCountMarkedGap

noncomputable section

open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5UpperTables.OriginalU34
open Part5OriginalH430TaggedArithmeticReceivers
open P2EnhancedTwentyOneSameQWeighted
open P2EnhancedTwentyOneSourceComparison

/-- The literal original q COUNT minus the genuine marked Phi source.
The arithmetic receiver q and the positive marked product d remain
different types of occurrence and are never identified here. -/
def originalMarkedDiscrepancy
    (N precision p : ℕ) (k : Root) (tau : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ((originalReceiver N p).card : ℝ) -
    5 * Phi N (rootQ N precision k tau p) D sigma (11/5)

/-- Only the POSITIVE part of the unpaired original-versus-marked
source discrepancy may increase a genuine upper estimate.
This is unpaid, not a sieve correction with a proved small bound. -/
def unpaidOriginalMarkedGap
    (N precision p : ℕ) (k : Root) (tau : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  max (originalMarkedDiscrepancy N precision p k tau D sigma) 0

/-- Root-specific, genuinely positive-family upper expression.
The original physical Q is kept, and sigma is the positive weight on d,
not a fictitious weight on the quotient prime q. -/
def markedFiniteUpperWithGap
    (N precision p : ℕ) (k : Root) (tau epsilon : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  weightedQuotient N (rootQ N precision k tau p) D sigma +
    epsilon * Theta N (rootQ N precision k tau p) D sigma +
    unpaidOriginalMarkedGap N precision p k tau D sigma

private theorem count_le_budget_of_real_marked_source
    (N precision p : ℕ) (k : Root) (tau epsilon : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hsource : 5 * Phi N (rootQ N precision k tau p) D sigma (11/5) ≤
      weightedQuotient N (rootQ N precision k tau p) D sigma +
        epsilon * Theta N (rootQ N precision k tau p) D sigma) :
    ((originalReceiver N p).card : ℝ) ≤
      markedFiniteUpperWithGap N precision p k tau epsilon D sigma := by
  have hgap :
      ((originalReceiver N p).card : ℝ) -
        5 * Phi N (rootQ N precision k tau p) D sigma (11/5) ≤
      unpaidOriginalMarkedGap N precision p k tau D sigma := by
    dsimp only [unpaidOriginalMarkedGap, originalMarkedDiscrepancy]
    exact le_max_left _ _
  dsimp only [markedFiniteUpperWithGap]
  linarith only [hsource, hgap]

/-- REAL, uniform-before-N source-count inequality. The primitive marked
support requirements belong to the existing twentyOne theorem, including
all three negative windows and selected-square collisions. The positive
unpaired arithmetic/product discrepancy is visible on the RIGHT and
is not asserted to be o(Theta), zero, or paid by the H430 table. -/
theorem original_q_count_le_positive_marked_with_unpaid_gap
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (precision p : ℕ) (k : Root) (tau : ℝ)
        (D : Finset ℕ) (sigma : ℕ → ℝ),
        rootQ N precision k tau p ≤ (N : ℝ) →
        (∀ d ∈ D, 0 < d) →
        (∀ d ∈ D, 0 ≤ sigma d) →
        (∀ d ∈ D, 1 < rootQ N precision k tau p / (d : ℝ)) →
        (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
        (∀ d ∈ D, (N : ℝ) ^ eta ≤
          cutoff (rootQ N precision k tau p) d (227/50)) →
        ((originalReceiver N p).card : ℝ) ≤
          markedFiniteUpperWithGap N precision p k tau epsilon D sigma := by
  obtain ⟨T, hT, hsource⟩ :=
    twentyOne_source_comparison heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he precision p k tau D sigma hQN hd hsigma hR hold hcut
  exact count_le_budget_of_real_marked_source
    N precision p k tau epsilon D sigma
    (hsource N hNT he (rootQ N precision k tau p)
      D sigma hQN hd hsigma hR hold hcut)

/-- Genuine original U3+U4 selected q count, with both tags on the
overlap, is upper-bounded by the sum of SAME physical-Q marked budgets
and their explicitly UNPAID q-versus-product gaps.
All hypotheses are primitive gates on the marked families, NOT a
selected-count estimate, owner-injection, or target-equivalent licence.
Every root p may have its OWN actual Q, D and sigma. -/
theorem original_U34_le_positive_marked_budgets_with_unpaid_gap
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (precision : ℕ) (tau : ℝ)
        (D : Root → ℕ → Finset ℕ)
        (sigma : Root → ℕ → ℕ → ℝ),
        (∀ k p, p ∈ originalBand N k →
          rootQ N precision k tau p ≤ (N : ℝ) ∧
          (∀ d ∈ D k p, 0 < d) ∧
          (∀ d ∈ D k p, 0 ≤ sigma k p d) ∧
          (∀ d ∈ D k p,
            1 < rootQ N precision k tau p / (d : ℝ)) ∧
          (∀ d ∈ D k p, ∀ q ∈ d.primeFactors,
            (N : ℝ) ^ eta ≤ (q : ℝ)) ∧
          (∀ d ∈ D k p, (N : ℝ) ^ eta ≤
            cutoff (rootQ N precision k tau p) d (227/50))) →
        currentChenUpsilon3 N + currentChenUpsilon4 N ≤
          (∑ p ∈ originalBand N .U3,
            markedFiniteUpperWithGap N precision p .U3 tau epsilon
              (D .U3 p) (sigma .U3 p)) +
          (∑ p ∈ originalBand N .U4,
            markedFiniteUpperWithGap N precision p .U4 tau epsilon
              (D .U4 p) (sigma .U4 p)) := by
  obtain ⟨T, hT, hlocal⟩ :=
    original_q_count_le_positive_marked_with_unpaid_gap heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he precision tau D sigma hgates
  have h3 :
      (∑ p ∈ originalBand N .U3, ((originalReceiver N p).card : ℝ)) ≤
      (∑ p ∈ originalBand N .U3,
        markedFiniteUpperWithGap N precision p .U3 tau epsilon
          (D .U3 p) (sigma .U3 p)) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hQ, hd, hs, hr, hold, hc⟩ := hgates .U3 p hp
    exact hlocal N hNT he precision p .U3 tau
      (D .U3 p) (sigma .U3 p) hQ hd hs hr hold hc
  have h4 :
      (∑ p ∈ originalBand N .U4, ((originalReceiver N p).card : ℝ)) ≤
      (∑ p ∈ originalBand N .U4,
        markedFiniteUpperWithGap N precision p .U4 tau epsilon
          (D .U4 p) (sigma .U4 p)) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hQ, hd, hs, hr, hold, hc⟩ := hgates .U4 p hp
    exact hlocal N hNT he precision p .U4 tau
      (D .U4 p) (sigma .U4 p) hQ hd hs hr hold hc
  have hcount :
      currentChenUpsilon3 N + currentChenUpsilon4 N =
        (∑ p ∈ originalBand N .U3, ((originalReceiver N p).card : ℝ)) +
        (∑ p ∈ originalBand N .U4, ((originalReceiver N p).card : ℝ)) := by
    rw [original_U34_eq_tagged_card, original_tagged_card]
    simp only [Nat.cast_add, Nat.cast_sum]
  rw [hcount]
  exact add_le_add h3 h4

end
end ImbalancedChen.Part5OriginalH430TrueCountMarkedGap
