import ImbalancedChen.P5All16MarkedFineScalarBudget
import ImbalancedChen.P5OriginalWWholeRealAssignment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original selected-mask and W programs, run on the SAME full marked
and residual upper-endpoint word.  No prime tuple, beta value or test is
an argument of the assignment.  The W partition is derived directly
from its recursion, including the first-overflow completion, without
assuming any endpoint capacity theorem or final partition.

This is only the structural assignment.  Its analytic capacity licences
still require the original endpoint inequalities.  In particular no
such licence follows merely from the unconditional partition below.
-/

namespace ImbalancedChen.P5Z.All16ComputedWholeWordAssignment
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U11Integral U1011OriginalSixteenPolicyBank
open PresievedRoughGateMeshReserve PresievedRoughSlotAffineGates
open SelectedRealEndpointSupport SelectedRealWholeAtomGroups
open All16MarkedCommonFineSource All16MarkedFineScalarBudget
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion

/-- The original residual completion consumes every unread occurrence,
independently of whether its numeric capacity licence has been proved. -/
theorem finish_trace {α : Type*} (w : α → ℝ) (A : ℝ)
    (input : List α) (initial : Bins α) :
    Trace initial input (finish w A initial input) := by
  induction input generalizing initial with
  | nil => exact Trace.nil initial
  | cons p xs ih =>
      unfold finish
      split_ifs with hfit
      · exact Trace.left initial p (ih (putLeft initial p))
      · exact Trace.right initial p (ih (putRight initial p))

/-- Every branch of the actual original W program has an occurrence
trace.  The overflowing slot enters the middle exactly once, and the
original unread suffix is consumed by `finish`. -/
theorem complete_trace {α : Type*} (w : α → ℝ) (A B C : ℝ)
    (input : List α) (initial : Bins α) :
    Trace initial input (complete w A B C initial input) := by
  induction input generalizing initial with
  | nil => exact Trace.nil initial
  | cons p xs ih =>
      unfold complete
      rw [run]
      split_ifs with hleft hmiddle hright
      · exact Trace.left initial p (ih (putLeft initial p))
      · exact Trace.middle initial p (ih (putMiddle initial p))
      · exact Trace.right initial p (ih (putRight initial p))
      · exact Trace.middle initial p (finish_trace w A xs (putMiddle initial p))

/-- The actual G W assignment partitions all four marked positions and
every residual position.  There is no `hpart` or successful-run input. -/
theorem W_groups_partition {r : ℕ} (N : ℕ) (u : Fin 4 → ℝ)
    (v : Fin r → ℝ) (B : Box) (eta : ℚ) (A : ℝ) :
    let g := OriginalWWholeRealAssignment.groups N u v B eta A
    (g.1 ++ g.2.1 ++ g.2.2).Perm (wholeLabels r) := by
  have ht := complete_trace (weight N u v) A
    (OriginalWRealEndpointCapacities.middleCapacity B eta N)
    (OriginalWRealEndpointCapacities.rightCapacity B eta N A)
    (OriginalWWholeRealAssignment.suffix r)
    (OriginalWWholeRealAssignment.initial N u v A)
  have hp := Part3.ActualWFineWordAdapter.trace_perm ht
  have hs := (OriginalWWholeRealAssignment.initial_partition N u v A).append_right
    (OriginalWWholeRealAssignment.suffix r)
  have hword : [Sum.inl (0 : Fin 4), Sum.inl 1] ++
      OriginalWWholeRealAssignment.suffix r = wholeLabels r := by
    simp [OriginalWWholeRealAssignment.suffix, wholeLabels, front]
  simpa only [OriginalWWholeRealAssignment.groups, OriginalWWholeRealAssignment.out,
    Part3.ActualWFineWordAdapter.flatten, hword] using hp.trans hs

def ownerBox {n m r : ℕ} (k : Key n m r) : Box :=
  U1011OriginalFifteenNativeGridCells.gridBox n k.1

def ownerPolicy {n m r : ℕ} (k : Key n m r) : Policy :=
  U1011OriginalSixteenStaticNativeCompiler.boxPolicy (ownerBox k)

/-- The literal original run level nu-2*delta, distinct from both the
physical residual exponent and the coefficient's common beta level. -/
def runLevel {n m r : ℕ} (eta : ℚ) (k : Key n m r) : ℝ :=
  (U1011OriginalSixteenNearCapBoxProfiles.nu (ownerPolicy k) (ownerBox k) eta : ℝ) -
    2 * (U1011OriginalSixteenNearCapBoxProfiles.delta (ownerPolicy k) (ownerBox k) eta : ℝ)

/-- Computed ONCE from a whole atom's real upper endpoints.  The W
branch uses the original first-two-slot initialization and overflow
completion; the other fifteen policies use their original selected
mask and full-word low-capacity repair. -/
def occurrenceGroups (n N m r : ℕ) (eta : ℚ) (A : ℝ) (k : Key n m r) :
    List (Fin 4 ⊕ Fin r) × List (Fin 4 ⊕ Fin r) × List (Fin 4 ⊕ Fin r) :=
  if ownerPolicy k = wPolicy then
    OriginalWWholeRealAssignment.groups N
      (logPrimeMeshHi 0 1 m k.2.1) (logPrimeMeshHi 0 1 m k.2.2) (ownerBox k) eta A
  else
    SelectedRealWholeAtomGroups.groups N (ownerPolicy k)
      (logPrimeMeshHi 0 1 m k.2.1) (logPrimeMeshHi 0 1 m k.2.2) (runLevel eta k) A

def labelGroups (n N m r : ℕ) (eta : ℚ) (A : ℝ) (k : Key n m r) :
    List (Fin (m + 1)) × List (Fin (m + 1)) × List (Fin (m + 1)) :=
  let g := occurrenceGroups n N m r eta A k
  let labels := occurrenceLabels k.2.1 k.2.2
  (g.1.map labels, g.2.1.map labels, g.2.2.map labels)

theorem occurrenceGroups_of_W {n N m r : ℕ} (eta : ℚ) (A : ℝ) (k : Key n m r)
    (hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) = wPolicy) :
    occurrenceGroups n N m r eta A k = OriginalWWholeRealAssignment.groups N
      (logPrimeMeshHi 0 1 m k.2.1) (logPrimeMeshHi 0 1 m k.2.2)
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta A := by
  simp only [occurrenceGroups, ownerPolicy, ownerBox, hW, if_true]

theorem labelGroups_of_W {n N m r : ℕ} (eta : ℚ) (A : ℝ) (k : Key n m r)
    (hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) = wPolicy) :
    labelGroups n N m r eta A k =
      let g := OriginalWWholeRealAssignment.groups N
        (logPrimeMeshHi 0 1 m k.2.1) (logPrimeMeshHi 0 1 m k.2.2)
        (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta A
      (g.1.map (occurrenceLabels k.2.1 k.2.2),
        g.2.1.map (occurrenceLabels k.2.1 k.2.2),
        g.2.2.map (occurrenceLabels k.2.1 k.2.2)) := by
  simp only [labelGroups, occurrenceGroups_of_W eta A k hW]

theorem occurrenceGroups_partition (n N m r : ℕ) (eta : ℚ) (A : ℝ) (k : Key n m r) :
    let g := occurrenceGroups n N m r eta A k
    (g.1 ++ g.2.1 ++ g.2.2).Perm (wholeLabels r) := by
  unfold occurrenceGroups
  split_ifs with hW
  · exact W_groups_partition N _ _ _ eta A
  · exact SelectedRealWholeAtomGroups.groups_partition N _ _ _ _ A

/-- The finite original occurrence convention [p4,p3,p2,p1] agrees
with G's independently defined common marked word, also at rank zero. -/
theorem wholeLabels_eq_wholeOccurrences (r : ℕ) : wholeLabels r = wholeOccurrences r := by
  have hf : front = List.ofFn (fun i : Fin 4 => i) := by rfl
  simp only [wholeLabels, wholeOccurrences, hf, List.finRange, List.map_ofFn,
    Function.comp_def]

/-- The precise lists used in every gamma below form the full marked
and residual common word.  No partition premise remains at the source
or restoring-scalar consumer. -/
theorem labelGroups_partition (n N m r : ℕ) (eta : ℚ) (A : ℝ) (k : Key n m r) :
    let g := labelGroups n N m r eta A k
    (g.1 ++ g.2.1 ++ g.2.2).Perm (fullWord k.2.1 k.2.2) := by
  have hp := (occurrenceGroups_partition n N m r eta A k).map
    (occurrenceLabels k.2.1 k.2.2)
  simpa only [labelGroups, List.map_append, wholeLabels_eq_wholeOccurrences,
    whole_occurrences_labels] using hp

end
end ImbalancedChen.P5Z.All16ComputedWholeWordAssignment
