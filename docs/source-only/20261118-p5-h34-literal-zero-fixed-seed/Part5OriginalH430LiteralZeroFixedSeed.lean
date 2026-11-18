import ImbalancedChen.Part5OriginalH430MonotoneQ80AnchorZeroRise

/-!
P5.6 / h34: exact literal seed at ALL original 106-bank FIXED reads.
The Q80 seed only occupies upper cells with index < 60. In contrast,
the literal 70 W1 rows read 109+10*j, and the 36 W2 rows read pairs
of original row indices between 110 and 192 (verified against rows).
Thus EVERY fixed anchor reads ZERO at iteration zero.

The remaining seed-anchor payment is therefore the full positive
part of the analytic F at the actual W1/W2 fixed endpoints. Under the
EXISTING predecessor CLOSED-CELL hypothesis, these fixed F values are
nonnegative, so the positive parts can be removed exactly. This is
NOT a smallness estimate: it exposes a real manuscript-internal debt.
The true generation-zero terminal weightedRequest seed is distinct.

No weakening of the 4:1 W2 mixture, actual selected Fin occurrence
multiplicity, same Q, floor credit, retention, or 430+11 target.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralZeroFixedSeed

noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SelectedPositiveAnchorPayment
open Part5OriginalH430SelectedAnchorBackwardVariation
open Part5OriginalH430ClippedAnchorRecovery
open Part5OriginalH430ExactOuterQ80FloorCredit
open Part5OriginalH430MonotoneQ80AnchorZeroRise

/-- The original seed has no positive upper numerator outside its
literal first 60 cells. No assumption on the row base is used. -/
theorem initial_upper_numerator_zero (i : Fin 200)
    (hi : 60 ≤ i.val) :
    iterate 0 true i = 0 := by
  change seed true i = 0
  simp [seed, Nat.not_lt.mpr hi]

theorem initial_upper_floor_zero (i : Fin 200)
    (hi : 60 ≤ i.val) :
    floorValue (iterate 0 true) i = 0 := by
  have h := initial_upper_numerator_zero i hi
  simp [floorValue, h]

/-- All ten W1 fixed anchor cells have index at least 109. The
seven distinct W1 target labels do not alter that fixed read. -/
theorem w1_fixed_cell_outside_seed (j : Fin 10) :
    60 ≤ (w1Cell j).val := by
  dsimp [w1Cell]
  omega

/-- All 72 W2 fixed endpoint appearances have index at least 60.
This checks the ORIGINAL finite row table and its point ordering,
not a new analytic or arbitrary endpoint classification. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem w2_fixed_cell_outside_seed
    (j : Fin 36) (anchor : Bool) :
    60 ≤ (w2Cell j anchor).val := by
  fin_cases j <;> cases anchor <;> decide

theorem w1_initial_fixed_floor_zero (j : Fin 10) :
    floorValue (iterate 0 true) (w1Cell j) = 0 :=
  initial_upper_floor_zero _ (w1_fixed_cell_outside_seed j)

theorem w2_initial_fixed_floor_zero (j : Fin 36) (anchor : Bool) :
    floorValue (iterate 0 true) (w2Cell j anchor) = 0 :=
  initial_upper_floor_zero _ (w2_fixed_cell_outside_seed j anchor)

/-- Exact analytic positive endpoint debit at the REAL fixed reads.
W2 uses precisely the original 4/5 and 1/5 weights. -/
def actionAnalyticSeedAllowance (F : ℝ → ℝ) :
    Original106Action → ℝ
  | .inl (_,j) => max 0 (F (W1Anchor j))
  | .inr j =>
      (4 * max 0 (F (originalW2At j).s0) +
        max 0 (F (originalW2At j).phi1)) / 5

/-- The earlier zero-iterate fixed-anchor allowance is not a small
Q80 rounding residual: the exact old fixed numerators are all zero. -/
theorem action_seed_allowance_exact (F : ℝ → ℝ)
    (a : Original106Action) :
    actionPositiveAnchorAllowance firstOriginalGeneration F a =
      actionAnalyticSeedAllowance F a := by
  rcases a with ⟨i,j⟩ | j
  · change max 0 (F (W1Anchor j) -
        floorValue (iterate 0 true) (w1Cell j)) =
        max 0 (F (W1Anchor j))
    rw [w1_initial_fixed_floor_zero]
    ring
  · change (4 * max 0 (F (originalW2At j).s0 -
          floorValue (iterate 0 true) (w2Cell j true)) +
        max 0 (F (originalW2At j).phi1 -
          floorValue (iterate 0 true) (w2Cell j false))) / 5 =
        (4 * max 0 (F (originalW2At j).s0) +
          max 0 (F (originalW2At j).phi1)) / 5
    rw [w2_initial_fixed_floor_zero j true,
      w2_initial_fixed_floor_zero j false]
    ring

/-- The initial CLOSED-CELL inequality forces F to be nonnegative
at the original fixed endpoints, since their exact seed read is 0.
This condition is still a manuscript-internal induction debt. -/
theorem action_seed_eq_fixed_reference (F : ℝ → ℝ)
    (hzero : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 0 true) i ≤ F s)
    (a : Original106Action) :
    actionAnalyticSeedAllowance F a = fixedReference F a := by
  rcases a with ⟨i,j⟩ | j
  · have hF : 0 ≤ F (W1Anchor j) := by
      have h := hzero (w1Cell j) (W1Anchor j) (w1Cell_contains j)
      simpa only [w1_initial_fixed_floor_zero] using h
    change max 0 (F (W1Anchor j)) = F (W1Anchor j)
    exact max_eq_right hF
  · have h0 : 0 ≤ F (originalW2At j).s0 := by
      have h := hzero (w2Cell j true) (originalW2At j).s0
        (w2Cell_contains j true)
      simpa only [w2_initial_fixed_floor_zero] using h
    have h1 : 0 ≤ F (originalW2At j).phi1 := by
      have h := hzero (w2Cell j false) (originalW2At j).phi1
        (w2Cell_contains j false)
      simpa only [w2_initial_fixed_floor_zero] using h
    change (4 * max 0 (F (originalW2At j).s0) +
        max 0 (F (originalW2At j).phi1)) / 5 =
      (4 * F (originalW2At j).s0 + F (originalW2At j).phi1) / 5
    rw [max_eq_right h0, max_eq_right h1]

/-- The exact selected-bank seed charge has all original action and
Fin list-position weights. No count-owner or distinct-product
identification is used. -/
def bankSelectedAnalyticSeedPayment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        actionAnalyticSeedAllowance F a

def bankSelectedFixedReferenceSeedPayment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        fixedReference F a

theorem bank_seed_eq_analytic
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) :
    bankSelectedSeedAnchorPayment N n root tau p g F =
      bankSelectedAnalyticSeedPayment N n root tau p g F := by
  unfold bankSelectedSeedAnchorPayment bankSelectedAnalyticSeedPayment
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l _
  rw [action_seed_allowance_exact F a]

theorem bank_seed_eq_reference
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hzero : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate 0 true) i ≤ F s) :
    bankSelectedSeedAnchorPayment N n root tau p g F =
      bankSelectedFixedReferenceSeedPayment N n root tau p g F := by
  rw [bank_seed_eq_analytic]
  unfold bankSelectedAnalyticSeedPayment
    bankSelectedFixedReferenceSeedPayment
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l _
  rw [action_seed_eq_fixed_reference F hzero a]

/-- The original root consumer, now with the exact FULL positive
analytic fixed-reference seed cost exposed. The total terminal
generation-zero seed and the physical Buchstab source are unchanged.
The original CLOSED-CELL hypothesis is NOT discharged. -/
theorem frozen_root_le_reference_seed_with_floor_and_recovery
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430, bankCompleteFloorCredit N n root tau p g) +
      (∑ g : Fin 430, bankSelectedAnchorRecovery N n root tau p g F) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedFixedReferenceSeedPayment N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_seed_with_full_floor_and_recovery
    N n root tau p F hN ht ht' hn hp hband hclosed
  have hseed : ∀ g : Fin 430,
      bankSelectedSeedAnchorPayment N n root tau p g F =
      bankSelectedFixedReferenceSeedPayment N n root tau p g F := by
    intro g
    exact bank_seed_eq_reference N n root tau p g F
      (hclosed firstOriginalGeneration)
  simpa only [hseed] using hroot

end
end ImbalancedChen.Part5OriginalH430LiteralZeroFixedSeed
