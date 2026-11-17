import ImbalancedChen.Part5OriginalH430TrueRootFinWaveBridge
import ImbalancedChen.Part5OriginalH430ActualSelectedRowBudget

/-!
P5.6 h34: pay the genuine selected-bank PHYSICAL row error directly.
The prior raw-request candidate comparison carried an absolute child-Theta
drift. The physical telescope instead requires the *Theta-weighted* new
read minus the same-Q physical edgeValue. Comparing that with the original
same-Q ideal profile needs no separate child-Theta payment.

This source does NOT bound the positive excess of the true Q80 bank read
above its original ideal, the Buchstab positive source, or the seed.
No source/count identification, ownership or 430+11 closure is asserted.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430DirectPhysicalBankPayment
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430PhysicalRequestDefectBridge
open Part5OriginalH430WeightedPhysicalTelescope
open Part5OriginalH430PositivePhysicalSourcePartition
open Part5OriginalH430TrueRootFinWaveBridge

/-- Unpaid, genuinely physical one-sided excess of the TRUE selected
Q80 request read over the old same-Q selected-bank ideal.
Unlike the older raw candidate surplus, the theta factor is applied to
the actual new request read, not silently discarded. -/
def bankReadIdealPositiveExcess (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        max 0
          (thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) *
              iteratedRequest (g.val+1) (levelOccurrence l).current -
            thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) *
              idealCellProfile (precedingH g) (precedingh g) a)

/-- The existing absolute selected-bank applied-row error, counted
ONCE, at genuine selected Fin positions and with original marks. -/
def bankPhysicalAppliedAbs (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, levelAppliedError N n root tau p g a

/-- The original selected root-specific theta mass. This is not the
separate outer count-source normalization 7/2. -/
def bankPhysicalTheta (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, levelTheta N n root tau p g a

/-- A positive part must be taken before summing over history positions.
This bound uses exactly one absolute applied-row error; there is no
absolute child-theta drift on the physical side. -/
private theorem positive_gap_le_ideal_plus_abs (x y z : ℝ) :
    max 0 (x-z) ≤ max 0 (x-y) + |z-y| := by
  have htri : x-z ≤ (x-y) + |z-y| := by
    have h : y-z ≤ |z-y| := by
      calc
        y-z ≤ |y-z| := le_abs_self _
        _ = |z-y| := abs_sub_comm _ _
    linarith only [h]
  apply max_le
  · exact add_nonneg (le_max_left _ _) (abs_nonneg _)
  · have hpos : x-y ≤ max 0 (x-y) := le_max_right _ _
    linarith only [htri, hpos]

/-- Local one-sided physical source estimate. It uses the literal
selected-iterate new read, original theta, real same-Q physical row,
and the same ideal profile as the existing coefficient-error supplier.
No sign assumption on the request read is needed. -/
theorem actual_physical_source_le_read_ideal_plus_applied
    (N : ℕ) (Q : ℝ) (g : Fin 430) (r : Request)
    (a : Original106Action) :
    positivePhysicalSource N Q (g.val+1) r ≤
      max 0
        (thetaAtom N Q (parentProduct r.old) *
            iteratedRequest (g.val+1) r -
          thetaAtom N Q (parentProduct r.old) *
            idealCellProfile (precedingH g) (precedingh g) a) +
      |edgeValue Q (iterate g.val) r (children N Q g.val r) -
        thetaAtom N Q (parentProduct r.old) *
          idealCellProfile (precedingH g) (precedingh g) a| := by
  simpa only [positivePhysicalSource, physicalDefectAt,
    physicalStepDefect, actualStep] using
      (positive_gap_le_ideal_plus_abs
        (thetaAtom N Q (parentProduct r.old) *
          iteratedRequest (g.val+1) r)
        (thetaAtom N Q (parentProduct r.old) *
          idealCellProfile (precedingH g) (precedingh g) a)
        (edgeValue Q (iterate g.val) r (children N Q g.val r)))

/-- The chosen ORIGINAL 106-bank's true physical positive source is
bounded by its still-unpaid true-read-versus-ideal excess plus the OLD
applied-row absolute error. There is NO independent childThetaDriftAbs.
The positive-part inequality is applied at each selected Fin occurrence
before any sum, preserving duplicate paths and the selected action. -/
theorem selected_bank_physical_source_le_ideal_plus_applied
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    bankPhysicalSource N n root tau p g ≤
      bankReadIdealPositiveExcess N n root tau p g +
        bankPhysicalAppliedAbs N n root tau p g := by
  let Q := rootQ N n root tau p
  let X : Original106Action → Index N n root tau p g → ℝ :=
    fun a l =>
      max 0
        (thetaAtom N Q (parentProduct (levelOccurrence l).current.old) *
            iteratedRequest (g.val+1) (levelOccurrence l).current -
          thetaAtom N Q (parentProduct (levelOccurrence l).current.old) *
            idealCellProfile (precedingH g) (precedingh g) a)
  let Y : Original106Action → Index N n root tau p g → ℝ :=
    fun a l =>
      |edgeValue Q (iterate g.val) (levelOccurrence l).current
          (children N Q g.val (levelOccurrence l).current) -
        thetaAtom N Q (parentProduct (levelOccurrence l).current.old) *
          idealCellProfile (precedingH g) (precedingh g) a|
  have hpoint (a : Original106Action) (l : Index N n root tau p g) :
      positivePhysicalSource N Q (g.val+1) (levelOccurrence l).current ≤
        X a l + Y a l := by
    exact actual_physical_source_le_read_ideal_plus_applied N Q g
      (levelOccurrence l).current a
  have hsum :
      bankPhysicalSource N n root tau p g ≤
        ∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a,
            levelMark l * (X a l + Y a l) := by
    unfold bankPhysicalSource
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_left (hpoint a l) (mark_pos _).le
  calc
    bankPhysicalSource N n root tau p g ≤
        ∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a,
            levelMark l * (X a l + Y a l) := hsum
    _ = bankReadIdealPositiveExcess N n root tau p g +
        bankPhysicalAppliedAbs N n root tau p g := by
      simp only [X, Y, Q, bankReadIdealPositiveExcess,
        bankPhysicalAppliedAbs, levelAppliedError,
        mul_add, Finset.sum_add_distrib]

/-- Uniform genuine selected-bank physical source payment: the already
pinned coefficientwise absolute bank error pays the applied physical
term ONCE. The true Q80 read-versus-ideal positive excess stays OPEN.
The threshold precedes every N, root, precision, prime and generation. -/
theorem uniform_selected_bank_physical_source_open_excess
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        bankPhysicalSource N n root tau p g ≤
          bankReadIdealPositiveExcess N n root tau p g +
            epsilon * bankPhysicalTheta N n root tau p g := by
  obtain ⟨T, hT4, hT⟩ := uniform_level_bank_supply he
  refine ⟨T, hT4, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hpaid :
      bankPhysicalAppliedAbs N n root tau p g ≤
        epsilon * bankPhysicalTheta N n root tau p g := by
    unfold bankPhysicalAppliedAbs bankPhysicalTheta
    calc
      (∑ a : Original106Action, levelAppliedError N n root tau p g a) ≤
        ∑ a : Original106Action,
          epsilon * levelTheta N n root tau p g a := by
            apply Finset.sum_le_sum
            intro a _
            exact (hT N hN n root tau ht ht' hn p hp hband g a).2.1
      _ = epsilon * (∑ a : Original106Action,
            levelTheta N n root tau p g a) := by
              rw [Finset.mul_sum]
  have hsplit := selected_bank_physical_source_le_ideal_plus_applied
    N n root tau p g
  linarith only [hpaid, hsplit]

/-- Concrete frozen 430-root reduction in the REAL Fin owners.
The terminal seed and strict-prime Buchstab positive source are not
estimated; the selected physical bank row error is not silently lost. -/
theorem frozen_root_le_seed_buchstab_ideal_excess_applied
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    weightedRequest N (rootQ N n root tau p) 430
      (rootRequest N n root tau p) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankReadIdealPositiveExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_430_le_actual_fin_payments N n root tau p
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPhysicalSource N n root tau p g)) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankReadIdealPositiveExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g) := by
    apply Finset.sum_le_sum
    intro g _
    have hb := selected_bank_physical_source_le_ideal_plus_applied
      N n root tau p g
    linarith only [hb]
  linarith only [hroot, hlevels]

/-- Same REAL 430 root with uniform epsilon*theta payment.
This is only a partial physical-source bound; it does NOT assert the
remaining terms vanish or that the physical request root equals U3/U4
selected-count with the original 7/2 outer coefficient. -/
theorem uniform_frozen_root_le_partly_paid_physical_source
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) ≤
        (∑ l : LevelIndex N n root tau p 0,
          levelMark l *
            max 0 (weightedRequest N (rootQ N n root tau p) 0
              (levelOccurrence l).current)) +
        ∑ g : Fin 430,
          (buchstabPhysicalSource N n root tau p g +
            bankReadIdealPositiveExcess N n root tau p g +
              epsilon * bankPhysicalTheta N n root tau p g) := by
  obtain ⟨T, hT4, hT⟩ :=
    uniform_selected_bank_physical_source_open_excess he
  refine ⟨T, hT4, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband
  have hroot := frozen_root_430_le_actual_fin_payments N n root tau p
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPhysicalSource N n root tau p g)) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankReadIdealPositiveExcess N n root tau p g +
            epsilon * bankPhysicalTheta N n root tau p g) := by
    apply Finset.sum_le_sum
    intro g _
    have hb := hT N hN n root tau ht ht' hn p hp hband g
    linarith only [hb]
  linarith only [hroot, hlevels]

end
end ImbalancedChen.Part5OriginalH430DirectPhysicalBankPayment
