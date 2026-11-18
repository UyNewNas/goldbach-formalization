import ImbalancedChen.Part5OriginalH430FirstCompatibleFrontierFactor
import ImbalancedChen.Part5OriginalH430ActualQUniqueExitLedger

/-!
P5.6 / h34: distinguish the genuine ORIGINAL q/tag receivers that
survive the root and second Rosser gates from the original receivers
in the two first-excluded frozen-cutoff FAILURE lanes.

The two sets are disjoint as literal (U3/U4,p,q) RECEIPTS under
the manuscript's actual original-to-frozen cutoff inclusion. The
retained prefix fibres and the actual-Q signed first-exit fibres
therefore cannot be matched by assuming they are the same receipt.

Both disjoint arithmetic sources are preserved in one exact signed
ledger. Each distinct actual (Q,p,ell) first-excluded EVENT is
charged only once, and the difference between its signed history
and all original q/tag receipts remains explicitly UNPAID.

This does not exclude historical first-forbidden states on retained
paths at deeper ranks, prove any q-to-Fin owner, remove collision
multiplicities, or provide a quantitative h34 bound.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430RetainedVsFirstExitSeparation

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ActualRetainedPrefixFibres
open Part5OriginalH430FirstCompatibleFrontierFactor
open Part5OriginalH430ActualQFirstExitReceipts
open Part5OriginalH430ActualQUniqueExitLedger
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430RealSignedExitPayment

/-- A retained arithmetic receipt is in the TRUE strict original
q/tag source. It is not a merely frozen-admitted candidate. -/
theorem retained_receipt_in_original
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver}
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    z ∈ originalTagged N :=
  ((mem_stage_retained_original N cap precision tau z0 lower z).mp hz).1

/-- No strict-original retained receipt can also be in the
frozen-only first-excluded lane: its literal carrier explicitly
requires failure of the strict original roughness gate. -/
theorem retained_not_frozen_first_exit
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver}
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    z ∉ frozenFailAtActualQ N n precision tau z0 lower := by
  intro hf
  have hfo : z ∈ frozenOnly N n tau :=
    (Finset.mem_filter.mp hf).1
  exact (Finset.mem_sdiff.mp hfo).2
    (retained_receipt_in_original N cap precision tau z0 lower hz)

/-- Under the ACTUAL manuscript frozen-cutoff dominance hypotheses,
an original-strict receipt is admitted by the frozen sieve, hence
cannot simultaneously be in the still-rejected frozen first-exit
lane. The explicit threshold assumptions are not discarded. -/
theorem retained_not_rejected_first_exit
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    {z : TaggedReceiver}
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    z ∉ rejectedFailAtActualQ N n precision tau z0 lower := by
  intro hr
  have hrejected : z ∈ rejectedFrozen N n tau :=
    (Finset.mem_filter.mp hr).1
  have hfrozen : z ∈ frozenTagged N n tau :=
    original_tagged_subset_frozen N n tau hN htau htauhi hn
      (retained_receipt_in_original N cap precision tau z0 lower hz)
  exact (Finset.mem_sdiff.mp hrejected).2 hfrozen

/-- Thus a retained q/tag RECEIPT is not itself any of the original
actual-Q first-excluded FAILURE receipts. This must not be
misinterpreted as absence of a historical first-exit on another
path, or disjointness of projected physical event keys. -/
theorem retained_not_actual_Q_fail
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    {z : TaggedReceiver}
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    z ∉ actualQFailSource N n precision tau z0 lower := by
  intro hf
  change z ∈ frozenFailAtActualQ N n precision tau z0 lower ∪
    rejectedFailAtActualQ N n precision tau z0 lower at hf
  rcases Finset.mem_union.mp hf with hfrozen | hreject
  · exact (retained_not_frozen_first_exit
      N n cap precision tau z0 lower hz) hfrozen
  · exact (retained_not_rejected_first_exit
      N n cap precision tau z0 lower hN htau htauhi hn hz) hreject

/-- The genuine original-retained source and both actual-Q signed
first-excluded failure sources are disjoint at the tagged q level. -/
theorem retained_and_actual_Q_fail_disjoint
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    Disjoint
      (stageRetainedOriginal N cap precision tau z0 lower)
      (actualQFailSource N n precision tau z0 lower) := by
  apply Finset.disjoint_left.mpr
  intro z hz hfail
  exact (retained_not_actual_Q_fail
    N n cap precision tau z0 lower hN htau htauhi hn hz) hfail

/-- In particular, an arithmetic canonical (tag,p,ell) retained
prefix fibre and an actual first-excluded (Q,p,bad-factor) fibre
have NO COMMON original receipt, even if their projected prefix
labels happen to agree. No claim of disjoint history states. -/
theorem canonical_retained_fibre_disjoint_exit_fibre
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (retKey : Option SecondPrefixKey) (exitKey : ℝ × EventKey) :
    Disjoint
      (actualRetainedPrefixFibre N cap precision tau z0 lower retKey)
      (actualQExitFibre N n precision tau z0 lower exitKey) := by
  apply Finset.disjoint_left.mpr
  intro z hz hexit
  have hret : z ∈ stageRetainedOriginal N cap precision tau z0 lower :=
    (Finset.mem_filter.mp hz).1
  have hfail : z ∈ actualQFailSource N n precision tau z0 lower :=
    (Finset.mem_filter.mp hexit).1
  exact (retained_not_actual_Q_fail
    N n cap precision tau z0 lower hN htau htauhi hn hret) hfail

/-- The exact joint signed ARITHMETIC source has two disjoint
components: canonical first-compatible frontier q/tag fibres and
the true actual-Q first-excluded q/tag fibres. No signed receipts
are quotiented out by event-key equality. -/
theorem joint_signed_source_by_separate_fibres
    {M : Type*} [AddCommMonoid M]
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (w : TaggedReceiver → M) :
    (∑ z ∈ (stageRetainedOriginal N cap precision tau z0 lower ∪
        actualQFailSource N n precision tau z0 lower), w z) =
      (∑ key ∈ stagePrefixKeys N cap precision tau z0 lower,
        ∑ z ∈ actualRetainedPrefixFibre
          N cap precision tau z0 lower key, w z) +
      (∑ key ∈ actualQExitKeys N n precision tau z0 lower,
        ∑ z ∈ actualQExitFibre
          N n precision tau z0 lower key, w z) := by
  rw [Finset.sum_union
    (retained_and_actual_Q_fail_disjoint
      N n cap precision tau z0 lower hN htau htauhi hn)]
  rw [exact_retained_source_by_prefix,
    actual_Q_signed_fibre_partition]

/-- Historical signed exits are available ONLY once per distinct
actual (Q,p,bad-factor) first-excluded key. The exact residual
between all failure receipts and that one history event remains a
separate, unpaid real quantity, alongside all retained receipts.
No selected-count owner, root 7/2 budget, or h34 lower bound follows. -/
theorem joint_signed_source_history_and_unpaid
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ (stageRetainedOriginal N cap precision tau z0 lower ∪
        actualQFailSource N n precision tau z0 lower), w z) =
      (∑ key ∈ stagePrefixKeys N cap precision tau z0 lower,
        ∑ z ∈ actualRetainedPrefixFibre
          N cap precision tau z0 lower key, w z) +
      (∑ key ∈ actualQExitKeys N n precision tau z0 lower,
        actualRankTwoSignedExit N cap lower key.1 key.2) +
      (∑ key ∈ actualQExitKeys N n precision tau z0 lower,
        (∑ z ∈ actualQExitFibre
          N n precision tau z0 lower key, w z) -
          actualRankTwoSignedExit N cap lower key.1 key.2) := by
  have hsplit :
      (∑ key ∈ actualQExitKeys N n precision tau z0 lower,
        ∑ z ∈ actualQExitFibre
          N n precision tau z0 lower key, w z) =
      (∑ key ∈ actualQExitKeys N n precision tau z0 lower,
        actualRankTwoSignedExit N cap lower key.1 key.2) +
      (∑ key ∈ actualQExitKeys N n precision tau z0 lower,
        (∑ z ∈ actualQExitFibre
          N n precision tau z0 lower key, w z) -
          actualRankTwoSignedExit N cap lower key.1 key.2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro key _
    ring
  calc
    _ = (∑ key ∈ stagePrefixKeys N cap precision tau z0 lower,
          ∑ z ∈ actualRetainedPrefixFibre
            N cap precision tau z0 lower key, w z) +
        (∑ key ∈ actualQExitKeys N n precision tau z0 lower,
          ∑ z ∈ actualQExitFibre
            N n precision tau z0 lower key, w z) :=
      joint_signed_source_by_separate_fibres
        N n cap precision tau z0 lower hN htau htauhi hn w
    _ = _ := by rw [hsplit]; ring

end
end ImbalancedChen.Part5OriginalH430RetainedVsFirstExitSeparation
