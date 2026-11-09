import ImbalancedChen.Part5OriginalH430ActualEmptyLevelUnpaidReceipts

/-!
P5.6 / h34: instantiate the existing positive marked-source comparison at
the ACTUAL resolved request-history products, keeping the complete original
U3/U4 arithmetic q counts and the explicit UNPAID difference.

Unlike the earlier arbitrary-D/sigma source theorem, D here is the image
of actual selected level LIST POSITIONS under their original integer parent
product, and sigma is the sum of actual positive marks over every position
with that product. It is not identified with an arithmetic quotient prime q.

Parent-product positivity and Q/d > 1 are supplied by the actual generated
root geometry. Prime-factor roughness, cutoff and Q <= N are still separate
primitive source gates, NOT asserted proved for every history. The displayed
upper bound retains the original-minus-5Phi positive-part gap, without
bounding it. It is NOT a completed H430 selected-count estimate or owner
identification. No arbitrary count/payment hypothesis is introduced.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualMarkedRootConsumer

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualResolvedMarkedPushforward
open Part5OriginalH430ActualResolvedPhysicalGates
open Part5OriginalH430ActualEmptyLevelUnpaidReceipts
open Part5OriginalH430TrueCountMarkedGap
open P2EnhancedTwentyOneSourceComparison

/-- Every product in the ACTUAL resolved support comes from a real
level-list position. The witness is not unique: product collisions
retain all distinct positions and their separate path weights. -/
theorem actual_product_support_has_position
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) {d : ℕ}
    (hd : d ∈ activeProductSupport N n root tau p g) :
    ∃ l : Index N n root tau p g,
      l ∈ activePositions N n root tau p g ∧
      parentProduct (levelOccurrence l).current.old = d := by
  classical
  change d ∈ (activePositions N n root tau p g).image
    (fun l : Index N n root tau p g =>
      parentProduct (levelOccurrence l).current.old) at hd
  exact Finset.mem_image.mp hd

/-- The literal finite budget at a true root/generation. The unpaid
original q-to-marked discrepancy is part of its definition, not an
assumed small error. -/
def actualMarkedRootBudget
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (epsilon : ℝ) : ℝ :=
  markedFiniteUpperWithGap N n p root tau epsilon
    (activeProductSupport N n root tau p g)
    (activeProductSigma N n root tau p g)

/-- The existing uniform-before-N 21-term source comparison applies
to the REAL resolved history marked family. The support positivity
and physical Q/d gates are discharged at original U3/U4 roots.

Remaining assumptions are precisely the primitive Q<=N, rough-prime
and cutoff gates on each actual history occurrence; they are not a
selected-count theorem. In particular the original q count minus
5*Phi is still UNPAID. Empty levels are allowed; no zero Theta is
divided by. -/
theorem original_q_le_actual_resolved_marked_budget
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
        (g : Fin 430),
        0 ≤ tau → tau ≤ 1/12 →
        1 / ((n : ℝ) + 1) ≤ 11/384 →
        p ∈ originalBand N root →
        rootQ N n root tau p ≤ (N : ℝ) →
        (∀ l : Index N n root tau p g,
          l ∈ activePositions N n root tau p g →
          ∀ q ∈ (parentProduct (levelOccurrence l).current.old).primeFactors,
            (N : ℝ)^eta ≤ (q : ℝ)) →
        (∀ l : Index N n root tau p g,
          l ∈ activePositions N n root tau p g →
          (N : ℝ)^eta ≤ cutoff (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) (227/50)) →
        ((originalReceiver N p).card : ℝ) ≤
          actualMarkedRootBudget N n root tau p g epsilon := by
  obtain ⟨T, hT, hsource⟩ :=
    original_q_count_le_positive_marked_with_unpaid_gap heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he n root tau p g ht ht' hn hp hQN hrough hcut
  have hN : 4 ≤ N := le_trans hT hNT
  have hprime : p.Prime ∧ p.Coprime N := original_band_prime hp
  have hband : physicalPrime N p ∈ rootBand root :=
    original_band_geometry (by omega : 2 ≤ N) hp
  have hdpos :
      ∀ d ∈ activeProductSupport N n root tau p g, 0 < d := by
    intro d hd
    obtain ⟨l, hl, hld⟩ :=
      actual_product_support_has_position N n root tau p g hd
    subst d
    exact actual_level_parent_product_pos N n root tau p g l
      hN ht ht' hn hprime hband
  have hsigma :
      ∀ d ∈ activeProductSupport N n root tau p g,
        0 ≤ activeProductSigma N n root tau p g d := by
    intro d hd
    exact activeProductSigma_nonneg N n root tau p g d
  have hlevel :
      ∀ d ∈ activeProductSupport N n root tau p g,
        1 < rootQ N n root tau p / (d : ℝ) := by
    intro d hd
    obtain ⟨l, hl, hld⟩ :=
      actual_product_support_has_position N n root tau p g hd
    subst d
    exact actual_level_quotient_gt_one N n root tau p g l
      hN ht ht' hn hprime hband
  have hroughD :
      ∀ d ∈ activeProductSupport N n root tau p g,
        ∀ q ∈ d.primeFactors, (N : ℝ)^eta ≤ (q : ℝ) := by
    intro d hd q hq
    obtain ⟨l, hl, hld⟩ :=
      actual_product_support_has_position N n root tau p g hd
    subst d
    exact hrough l hl q hq
  have hcutD :
      ∀ d ∈ activeProductSupport N n root tau p g,
        (N : ℝ)^eta ≤
          cutoff (rootQ N n root tau p) d (227/50) := by
    intro d hd
    obtain ⟨l, hl, hld⟩ :=
      actual_product_support_has_position N n root tau p g hd
    subst d
    exact hcut l hl
  change ((originalReceiver N p).card : ℝ) ≤
    markedFiniteUpperWithGap N n p root tau epsilon
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g)
  exact hsource N hNT he n p root tau
    (activeProductSupport N n root tau p g)
    (activeProductSigma N n root tau p g)
    hQN hdpos hsigma hlevel hroughD hcutD

/-- At the actual EMPTY generation, even this instantiated finite
budget equals the entire original q cardinality. The empty-root debt
cannot be dismissed from a global upper count. -/
theorem actual_empty_budget_eq_original_count
    (N n : ℕ) (root : Root) (tau epsilon : ℝ) (p : ℕ)
    (g : Fin 430)
    (hempty : activePositions N n root tau p g = ∅) :
    actualMarkedRootBudget N n root tau p g epsilon =
      ((originalReceiver N p).card : ℝ) := by
  exact empty_resolved_finite_upper_eq_original_count
    N n root tau epsilon p g hempty

/-- Original U3 and U4 q counts, with BOTH actual root tags on the
overlap, are bounded by rootwise actual-resolved finite budgets.
Each original prime may be inspected at its own generation; the
choice of generation is NOT a proof of its true selected-count owner.

The original q-versus-product payment remains explicit in each
budget. No arbitrary D/sigma family or target-equivalent count
assumption is used. Q<=N/roughness/cutoff still need to be proved
at the real selected owner before H430 can close. -/
theorem original_U34_le_actual_resolved_budgets
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430),
        0 ≤ tau → tau ≤ 1/12 →
        1 / ((n : ℝ) + 1) ≤ 11/384 →
        (∀ (k : Root) (p : ℕ), p ∈ originalBand N k →
          rootQ N n k tau p ≤ (N : ℝ) ∧
          (∀ l : Index N n k tau p (depth k p),
            l ∈ activePositions N n k tau p (depth k p) →
            ∀ q ∈ (parentProduct (levelOccurrence l).current.old).primeFactors,
              (N : ℝ)^eta ≤ (q : ℝ)) ∧
          (∀ l : Index N n k tau p (depth k p),
            l ∈ activePositions N n k tau p (depth k p) →
            (N : ℝ)^eta ≤ cutoff (rootQ N n k tau p)
              (parentProduct (levelOccurrence l).current.old) (227/50))) →
        currentChenUpsilon3 N + currentChenUpsilon4 N ≤
          (∑ p ∈ originalBand N .U3,
            actualMarkedRootBudget N n .U3 tau p (depth .U3 p) epsilon) +
          (∑ p ∈ originalBand N .U4,
            actualMarkedRootBudget N n .U4 tau p (depth .U4 p) epsilon) := by
  obtain ⟨T, hT, hlocal⟩ :=
    original_q_le_actual_resolved_marked_budget heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT he n tau depth ht ht' hn hgates
  have h3 :
      (∑ p ∈ originalBand N .U3, ((originalReceiver N p).card : ℝ)) ≤
      (∑ p ∈ originalBand N .U3,
        actualMarkedRootBudget N n .U3 tau p (depth .U3 p) epsilon) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hQ, hrough, hcut⟩ := hgates .U3 p hp
    exact hlocal N hNT he n .U3 tau p (depth .U3 p)
      ht ht' hn hp hQ hrough hcut
  have h4 :
      (∑ p ∈ originalBand N .U4, ((originalReceiver N p).card : ℝ)) ≤
      (∑ p ∈ originalBand N .U4,
        actualMarkedRootBudget N n .U4 tau p (depth .U4 p) epsilon) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hQ, hrough, hcut⟩ := hgates .U4 p hp
    exact hlocal N hNT he n .U4 tau p (depth .U4 p)
      ht ht' hn hp hQ hrough hcut
  have hcount :
      currentChenUpsilon3 N + currentChenUpsilon4 N =
        (∑ p ∈ originalBand N .U3, ((originalReceiver N p).card : ℝ)) +
        (∑ p ∈ originalBand N .U4, ((originalReceiver N p).card : ℝ)) := by
    rw [original_U34_eq_tagged_card, original_tagged_card]
    simp only [Nat.cast_add, Nat.cast_sum]
  rw [hcount]
  exact add_le_add h3 h4

end
end ImbalancedChen.Part5OriginalH430ActualMarkedRootConsumer
