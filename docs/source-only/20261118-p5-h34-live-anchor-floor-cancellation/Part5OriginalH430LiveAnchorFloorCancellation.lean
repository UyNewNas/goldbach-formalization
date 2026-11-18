import ImbalancedChen.Part5OriginalH430LiteralZeroFixedSeed

/-!
P5.6 / h34: genuine cancellation of the gross analytic fixed-anchor
seed debit against ACTUAL Q80 anchor recovery, with COMPLETE original
per-product and outer-quotient floor credit retained.

The original 106-bank W1/W2 endpoints, W2 4:1 weights, true selected
Fin positions, occurrenceScale and same-Q history are unchanged.
An initial reference charge is a GROSS ledger entry: the exact clipped
Q80 recovery is already present on the LEFT of the root inequality.
One must not pay the full gross reference AND separately ignore recovery.
The net remaining fixed deficit is the CURRENT selected positive anchor
allowance, not automatically zero.

No count-owner identification, quantitative smallness, h34 conclusion or
new analytic premise is supplied here. This is manuscript-internal source
only, uncompiled, with the original CLOSED-CELL assumption still open.
-/

namespace ImbalancedChen.Part5OriginalH430LiveAnchorFloorCancellation

noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430SelectedPositiveAnchorPayment
open Part5OriginalH430ClippedAnchorRecovery
open Part5OriginalH430ExactOuterQ80FloorCredit
open Part5OriginalH430MonotoneQ80AnchorZeroRise
open Part5OriginalH430LiteralZeroFixedSeed

/-- No CLOSED-CELL or analytic sign premise is required: the gross
positive analytic seed charge consists exactly of the current literal
Q80 endpoint deficit plus the ACTUAL clipped recovery. This identity
holds at every genuine selected bank Fin list occurrence. -/
theorem selected_analytic_seed_exact_net
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) :
    bankSelectedAnalyticSeedPayment N n root tau p g F =
      bankSelectedPositiveAnchorPayment N n root tau p g F +
      bankSelectedAnchorRecovery N n root tau p g F := by
  calc
    bankSelectedAnalyticSeedPayment N n root tau p g F =
        bankSelectedSeedAnchorPayment N n root tau p g F :=
          (bank_seed_eq_analytic N n root tau p g F).symm
    _ = bankSelectedPositiveAnchorPayment N n root tau p g F +
          bankSelectedAnchorRecovery N n root tau p g F :=
          (bank_selected_anchor_eq_seed_plus_recovery
            N n root tau p g F).symm

/-- The same identity with the literal fixedReference rather than
positive parts, under exactly the zero-generation CLOSED-CELL premise.
The sign premise is not inferred from the Q80 maximum operation. -/
theorem selected_reference_seed_exact_net
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hzero : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 0 true) i ≤ F s) :
    bankSelectedFixedReferenceSeedPayment N n root tau p g F =
      bankSelectedPositiveAnchorPayment N n root tau p g F +
      bankSelectedAnchorRecovery N n root tau p g F := by
  calc
    bankSelectedFixedReferenceSeedPayment N n root tau p g F =
        bankSelectedSeedAnchorPayment N n root tau p g F :=
          (bank_seed_eq_reference N n root tau p g F hzero).symm
    _ = bankSelectedPositiveAnchorPayment N n root tau p g F +
          bankSelectedAnchorRecovery N n root tau p g F :=
          (bank_selected_anchor_eq_seed_plus_recovery
            N n root tau p g F).symm

/-- Unconditional 430-generation exact netting of the analytic
positive fixed-anchor charge. The sum is over genuine generation slots
and retains all selected request-list occurrences. -/
theorem all_generations_analytic_seed_exact_net
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ) :
    (∑ g : Fin 430,
       bankSelectedAnalyticSeedPayment N n root tau p g F) =
      (∑ g : Fin 430,
         bankSelectedPositiveAnchorPayment N n root tau p g F) +
      (∑ g : Fin 430,
         bankSelectedAnchorRecovery N n root tau p g F) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  exact selected_analytic_seed_exact_net N n root tau p g F

/-- The full original root source ledger is exactly the CURRENT
selected bank-anchor deficit plus the already-computed recovery.
Buchstab, base/ideal and the physical applied absolute error remain
unchanged, without changing any existing 430-generation weights. -/
theorem all_generations_reference_source_exact_net
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hzero : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 0 true) i ≤ F s) :
    (∑ g : Fin 430,
       (buchstabPhysicalSource N n root tau p g +
         (bankBaseIdealPositive N n root tau p g +
           bankSelectedFixedReferenceSeedPayment N n root tau p g F) +
         bankPhysicalAppliedAbs N n root tau p g)) =
      (∑ g : Fin 430,
         (buchstabPhysicalSource N n root tau p g +
           (bankBaseIdealPositive N n root tau p g +
             bankSelectedPositiveAnchorPayment N n root tau p g F) +
           bankPhysicalAppliedAbs N n root tau p g)) +
      (∑ g : Fin 430,
         bankSelectedAnchorRecovery N n root tau p g F) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  rw [selected_reference_seed_exact_net N n root tau p g F hzero]
  ring

/-- Net fixed-anchor consumer retaining BOTH literal integer rounding
channels, after cancelling only the ACTUAL recovery appearing on both
sides of the gross-reference bound. This is a change of ledger form,
not a quantitative payment of the remaining current positive deficit.
In particular the true predecessor CLOSED-CELL hypothesis is retained. -/
theorem frozen_root_le_live_anchors_with_complete_floor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430,
         bankCompleteFloorCredit N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
         levelMark l *
           max 0 (weightedRequest N (rootQ N n root tau p) 0
             (levelOccurrence l).current)) +
      (∑ g : Fin 430,
         (buchstabPhysicalSource N n root tau p g +
           (bankBaseIdealPositive N n root tau p g +
             bankSelectedPositiveAnchorPayment N n root tau p g F) +
           bankPhysicalAppliedAbs N n root tau p g)) := by
  have hroot := frozen_root_le_reference_seed_with_floor_and_recovery
    N n root tau p F hN ht ht' hn hp hband hclosed
  have hsource := all_generations_reference_source_exact_net
    N n root tau p F (hclosed firstOriginalGeneration)
  rw [hsource] at hroot
  linarith only [hroot]

end
end ImbalancedChen.Part5OriginalH430LiveAnchorFloorCancellation
