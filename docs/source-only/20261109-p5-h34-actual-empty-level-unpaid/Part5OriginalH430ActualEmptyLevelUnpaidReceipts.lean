import ImbalancedChen.Part5OriginalH430ActualResolvedPhysicalGates
import ImbalancedChen.Part5OriginalH430TrueCountMarkedGap

/-!
P5.6 / h34: the exact empty-generation boundary for the genuine
resolved request positions and the original arithmetic q receivers.

This is NOT the arbitrary zero-sigma example: the finite support and
sigma are defined by the actual resolver and positive marks at an
actual generated level. The source-count discrepancy is evaluated at
that same root's physical Q, retaining the original quotient-prime
cardinality. No quotient prime q is identified with a parent product d.

The result is a necessary boundary condition for any future
selected-count-to-Theta payment. It does not supply the missing
q/tag to historical-owner map or the H430 inequality.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualEmptyLevelUnpaidReceipts

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualResolvedMarkedPushforward
open Part5OriginalH430ActualResolvedPhysicalGates
open Part5OriginalH430TrueCountMarkedGap
open P2EnhancedTwentyOneSameQWeighted

/-- A level where the REAL resolver selects no list occurrence has
no parent-product support. No fictitious marked index is introduced. -/
theorem empty_resolved_product_support
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅) :
    activeProductSupport N n root tau p g = ∅ := by
  simp [activeProductSupport, hempty]

/-- The actual aggregated positive-path coefficient is identically
zero at an empty resolved level; multiplicity is not changed. -/
theorem empty_resolved_product_sigma
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅) (d : ℕ) :
    activeProductSigma N n root tau p g d = 0 := by
  simp [activeProductSigma, hempty]

/-- The genuine same-Q positive marked Phi vanishes on an empty
actual level, by the exact occurrence-preserving pushforward. -/
theorem empty_resolved_Phi
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅) :
    Phi N (rootQ N n root tau p)
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) (11/5) = 0 := by
  rw [activeProduct_Phi_exact]
  simp [hempty]

/-- The genuine same-Q Theta vanishes on an empty actual level.
This is a zero-mass case, not a positive normalizer to divide by. -/
theorem empty_resolved_Theta
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅) :
    Theta N (rootQ N n root tau p)
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) = 0 := by
  rw [activeProduct_Theta_exact]
  simp [hempty]

/-- At a genuinely empty resolved level the original-minus-5Phi
unpaid positive part is EXACTLY the original arithmetic q count.
No empty history is allowed to pay a positive original receiver. -/
theorem empty_resolved_unpaid_eq_original_count
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅) :
    unpaidOriginalMarkedGap N n p root tau
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) =
        ((originalReceiver N p).card : ℝ) := by
  unfold unpaidOriginalMarkedGap originalMarkedDiscrepancy
  have hc : (0 : ℝ) ≤ ((originalReceiver N p).card : ℝ) :=
    Nat.cast_nonneg _
  simpa [empty_resolved_Phi N n root tau p g hempty]
    using (max_eq_left hc)

/-- Even the proposed finite source upper budget has no marked
contribution at such a level. All of it is the still-unpaid q count;
this is an equality of finite expressions, not a bound on that debt. -/
theorem empty_resolved_finite_upper_eq_original_count
    (N n : ℕ) (root : Root) (tau epsilon : ℝ) (p : ℕ)
    (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅) :
    markedFiniteUpperWithGap N n p root tau epsilon
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) =
        ((originalReceiver N p).card : ℝ) := by
  have hsupport := empty_resolved_product_support N n root tau p g hempty
  have hgap := empty_resolved_unpaid_eq_original_count
    N n root tau p g hempty
  have htheta := empty_resolved_Theta N n root tau p g hempty
  unfold markedFiniteUpperWithGap
  rw [hgap, htheta, hsupport]
  simp [weightedQuotient]

/-- Conversely, under the original physical root geometry, the exact
Theta normalizer is zero precisely for a level with no real resolved
position. The nonempty direction uses the already supplied actual
product-positivity and Q/d > 1 gates. -/
theorem actual_Theta_zero_iff_no_resolved
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    Theta N (rootQ N n root tau p)
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) = 0 ↔
        activePositions N n root tau p g = ∅ := by
  constructor
  · intro hz
    by_cases he : activePositions N n root tau p g = ∅
    · exact he
    · have hnonempty : (activePositions N n root tau p g).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr he
      have hpos := activeProduct_Theta_pos_from_root_geometry
        N n root tau p g hN ht ht' hn hp hband hnonempty
      linarith
  · exact empty_resolved_Theta N n root tau p g

/-- A genuinely nonempty original q fibre cannot have its marked
deficit fully paid if the actual resolver has no selected occurrence.
This is a necessary condition only, never a coverage theorem. -/
theorem positive_q_count_no_payment_at_empty_level
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅)
    (hcard : 0 < (originalReceiver N p).card) :
    0 < unpaidOriginalMarkedGap N n p root tau
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) := by
  rw [empty_resolved_unpaid_eq_original_count N n root tau p g hempty]
  exact_mod_cast hcard

end
end ImbalancedChen.Part5OriginalH430ActualEmptyLevelUnpaidReceipts
