import ImbalancedChen.Part5OriginalH430WeightedPhysicalTelescope
import ImbalancedChen.Part5OriginalH430RetainedZeroNetDefect
import ImbalancedChen.Part5OriginalH430ActualRequestAllActionPartition

/-!
P5.6/h34: ONE-SIDED physical-source ledger on the actual selected
request history. Unlike the earlier unweighted request-local deficit,
this charges the exact Theta-weighted same-Q physical source.

A genuinely chosen retention has ZERO physical source defect, not merely
zero parent+source+child net request defect. Exterior requests are also
zero. The genuine Fin-level physical positive source therefore splits
into only Buchstab and the winning 106-bank actions. The full 430-step
weighted root is bounded by terminal weighted seed and the physical
source's positive part. No signed total is mistaken for a sum of
positive parts, and no magnitude estimate is asserted.

All statements are SOURCE ONLY, UNCOMPILED, UNEVALUATED.
The original U3/U4 count-owner, selected/inherited filters, root 7/2,
row 12, c/K, same-Q, genuine alpha and 430+11 remain unchanged.
-/

namespace ImbalancedChen.Part5OriginalH430PositivePhysicalSourcePartition
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualNetDefect
open Part5OriginalH430RetainedZeroNetDefect
open Part5OriginalH430ActualRequestAllActionWave
open Part5OriginalH430RequestWaveTelescoping
open Part5OriginalH430PhysicalRequestDefectBridge
open Part5OriginalH430WeightedPhysicalTelescope
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets

/-- The actual nonnegative one-sided physical source, after forming
the full signed same-Q physical defect at each real request. -/
def positivePhysicalSource (N : ℕ) (Q : ℝ)
    (j : ℕ) (r : Request) : ℝ :=
  max 0 (physicalDefectAt N Q j r)

theorem physical_source_le_positive
    (N : ℕ) (Q : ℝ) (j : ℕ) (r : Request) :
    physicalDefectAt N Q j r ≤ positivePhysicalSource N Q j r :=
  le_max_right (0 : ℝ) _

/-- At the ACTUAL retained winner the literal previous Q80 cell
equals the new request read. Its physical source is exactly zero;
this does not require Theta=1, nor a scalar owner for a cell request. -/
theorem selected_retention_physical_source_zero
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (i : Fin 200) (hs : Selected g r i .retained) :
    physicalDefectAt N Q (g+1) r = 0 := by
  change physicalStepDefect N Q g r = 0
  rw [selected_retention_physical_gap N Q g r i hs,
    selected_retention_request_fixed N g r i hs]
  have hread :
      iteratedRequest g (nextRequest r (Edge.retained (N := N) i)) =
        floorValue (iterate g r.node.upper) i :=
    retained_successor_reads_old_cell N (iterate g) r i
  rw [hread]
  ring

theorem selected_retention_positive_physical_zero
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (i : Fin 200) (hs : Selected g r i .retained) :
    positivePhysicalSource N Q (g+1) r = 0 := by
  change max 0 (physicalStepDefect N Q g r) = 0
  rw [selected_retention_physical_source_zero N Q g r i hs]
  simp

/-- Genuine retained Fin positions, including repetitions, carry NO
physical source expense even before taking positive parts. -/
theorem actual_retained_level_physical_source_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l *
        positivePhysicalSource N (rootQ N n root tau p)
          (g.val+1) (levelOccurrence l).current) = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  have hs := retained_level_actual_cell_selected N n root tau p g l hl
  rw [selected_retention_positive_physical_zero N
    (rootQ N n root tau p) g.val (levelOccurrence l).current
    (actualRetainedCell N n root tau p g l) hs]
  ring

/-- The genuine exterior read and its selected child list are absent;
the old physical-source zero statement is sufficient here. -/
theorem unresolved_positive_physical_source_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∉ resolvedLevel N n root tau p g) :
    positivePhysicalSource N (rootQ N n root tau p)
      (g.val+1) (levelOccurrence l).current = 0 := by
  let r := (levelOccurrence l).current
  cases hr : resolve (g.val+1) r with
  | none =>
      change max 0 (physicalStepDefect N (rootQ N n root tau p) g.val r) = 0
      rw [exterior_physical_gap_zero N (rootQ N n root tau p) g.val r hr]
      simp
  | some i =>
      have hm : l ∈ resolvedLevel N n root tau p g := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp [actualChoice, hr, r]
      exact (hl hm).elim

/-- Original list-position physical source (all true requests). -/
def fullPhysicalSource (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    levelMark l *
      positivePhysicalSource N (rootQ N n root tau p)
        (g.val+1) (levelOccurrence l).current

/-- Only the actually selected strict-prime Buchstab positions. -/
def buchstabPhysicalSource (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l *
      positivePhysicalSource N (rootQ N n root tau p)
        (g.val+1) (levelOccurrence l).current

/-- Only the winning original 106-bank action for each true Fin slot. -/
def bankPhysicalSource (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        positivePhysicalSource N (rootQ N n root tau p)
          (g.val+1) (levelOccurrence l).current

/-- The actual same-Q PHYSICAL positive source, not the unweighted
request-local net deficit, is partitioned without an extra retention
or unresolved charge. No selected alternative is double-counted. -/
theorem full_physical_source_eq_buchstab_plus_bank
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    fullPhysicalSource N n root tau p g =
      buchstabPhysicalSource N n root tau p g +
        bankPhysicalSource N n root tau p g := by
  let Q := rootQ N n root tau p
  let F : Index N n root tau p g → ℝ := fun l =>
    levelMark l * positivePhysicalSource N Q (g.val+1)
      (levelOccurrence l).current
  have hresolved :
      (∑ l : Index N n root tau p g, F l) =
        ∑ l ∈ resolvedLevel N n root tau p g, F l := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l ∈ resolvedLevel N n root tau p g
    · simp [hl]
    · have hz := unresolved_positive_physical_source_zero
        N n root tau p g l hl
      simp [F, Q, hl, hz]
  change (∑ l : Index N n root tau p g, F l) =
    (∑ l ∈ buchstabLevel N n root tau p g, F l) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a, F l)
  calc
    _ = ∑ l ∈ resolvedLevel N n root tau p g, F l := hresolved
    _ = (∑ l ∈ retainedLevel N n root tau p g, F l) +
        (∑ l ∈ buchstabLevel N n root tau p g, F l) +
          (∑ a : Original106Action,
            ∑ l ∈ selectedLevel N n root tau p g a, F l) :=
        resolved_level_sum_all_actions N n root tau p g F
    _ = _ := by
      have hzero :=
        actual_retained_level_physical_source_zero N n root tau p g
      change (∑ l ∈ retainedLevel N n root tau p g, F l) = 0 at hzero
      rw [hzero]
      ring

/-- The signed full-history telescope yields an actually ONE-SIDED
root bound without separately paying absolute child-Theta drift.
This is NOT a quantitative smallness bound for the new right side. -/
theorem weighted_root_le_seed_plus_positive_physical
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    weightedRequest N Q g r ≤
      waveAccount N Q g r (weightedSeed N Q) +
        waveAccount N Q g r (positivePhysicalSource N Q) := by
  have he := weighted_request_root_exact N Q g r
  have hm := waveAccount_mono N Q g r
    (physicalDefectAt N Q) (positivePhysicalSource N Q)
    (fun j s => physical_source_le_positive N Q j s)
  linarith only [he, hm]

/-- Both terminal and genuine physical debts may be signed; taking
positive parts at every actual list occurrence is a safe, more
conservative upper bound, not an analytic payment. -/
theorem weighted_root_le_positive_seed_and_physical
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    weightedRequest N Q g r ≤
      waveAccount N Q g r
        (fun j s => max 0 (weightedSeed N Q j s)) +
      waveAccount N Q g r (positivePhysicalSource N Q) := by
  have hroot := weighted_root_le_seed_plus_positive_physical N Q g r
  have hseed := waveAccount_mono N Q g r
    (weightedSeed N Q)
    (fun j s => max 0 (weightedSeed N Q j s))
    (fun j s => le_max_right (0 : ℝ) _)
  linarith only [hroot, hseed]

/-- Actual frozen root and EXACT 430 generations; no invented root
owner, change of manuscript, or assumed U3/U4 selected-count equality. -/
theorem frozen_root_430_le_positive_physical_source
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    weightedRequest N (rootQ N n root tau p) 430
      (rootRequest N n root tau p) ≤
    waveAccount N (rootQ N n root tau p) 430
      (rootRequest N n root tau p)
      (fun j s => max 0
        (weightedSeed N (rootQ N n root tau p) j s)) +
    waveAccount N (rootQ N n root tau p) 430
      (rootRequest N n root tau p)
      (positivePhysicalSource N (rootQ N n root tau p)) := by
  exact weighted_root_le_positive_seed_and_physical N
    (rootQ N n root tau p) 430 (rootRequest N n root tau p)

end
end ImbalancedChen.Part5OriginalH430PositivePhysicalSourcePartition
