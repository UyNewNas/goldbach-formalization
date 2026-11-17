import ImbalancedChen.Part5OriginalH430ActualRequestAllActionWave

/-!
P5.6/h34: exact finite residual telescoping on the ACTUAL selected request tree.

The ledger uses only the existing selected children, their literal edge
weights, full request identity (scalar versus specified cell), and every
list occurrence. This is a discrete transport identity, not an assumption
of a CLOSED-CELL bound, a Buchstab estimate, or original U3/U4 ownership.

For an arbitrary diagnostic F, the root diagnostic is exactly the terminal
seed sum plus the marked sum of its actual local one-step defects. Thus an
unpaid local discrepancy cannot be erased by an abstract closure claim.
SOURCE ONLY / UNCOMPILED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430RequestWaveTelescoping

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430ActualRequestAllActionWave

/-- Only real generation-zero leaves contribute seed values.
This is deliberately not a predecessor-429 reinterpretation. -/
def terminalSeed (F : ℕ → Request → ℝ) (remaining : ℕ) (r : Request) : ℝ :=
  if remaining = 0 then F 0 r else 0

/-- The literal one-step signed discrepancy at an ACTUAL request.
There are no imported arithmetic licences and no user-supplied owner. -/
def localDefect (N : ℕ) (Q : ℝ) (F : ℕ → Request → ℝ)
    (remaining : ℕ) (r : Request) : ℝ :=
  match remaining with
  | 0 => 0
  | g+1 =>
      F (g+1) r -
        ((children N Q g r).map
          (fun e => edgeWeight e * F g (nextRequest r e))).sum

/-- An explicit nonnegative unpaid residual; not an upper bound proved by
the manuscript or an assumption replacing the desired count estimate. -/
def positiveDefect (N : ℕ) (Q : ℝ) (F : ℕ → Request → ℝ)
    (remaining : ℕ) (r : Request) : ℝ :=
  max 0 (localDefect N Q F remaining r)

@[simp] theorem terminalSeed_zero (F : ℕ → Request → ℝ) (r : Request) :
    terminalSeed F 0 r = F 0 r := by simp [terminalSeed]

@[simp] theorem terminalSeed_succ (F : ℕ → Request → ℝ) (g : ℕ) (r : Request) :
    terminalSeed F (g+1) r = 0 := by simp [terminalSeed]

@[simp] theorem localDefect_zero (N : ℕ) (Q : ℝ)
    (F : ℕ → Request → ℝ) (r : Request) :
    localDefect N Q F 0 r = 0 := rfl

@[simp] theorem positiveDefect_zero (N : ℕ) (Q : ℝ)
    (F : ℕ → Request → ℝ) (r : Request) :
    positiveDefect N Q F 0 r = 0 := by
  simp [positiveDefect]

private theorem weighted_map_sum_add {α : Type*} (es : List α)
    (w f h : α → ℝ) :
    (es.map (fun e => w e * f e)).sum +
      (es.map (fun e => w e * h e)).sum =
    (es.map (fun e => w e * (f e + h e))).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      rw [← ih]
      ring

/-- Discrete telescoping along the ACTUAL chosen tree, with every old
path occurrence and its literal positive edge-product mark retained.
This identity has NO analytic, count-owner, or local-defect premise. -/
theorem root_eq_terminal_plus_defects
    (N : ℕ) (Q : ℝ) (F : ℕ → Request → ℝ) :
    ∀ g : ℕ, ∀ r : Request,
      waveAccount N Q g r (terminalSeed F) +
        waveAccount N Q g r (localDefect N Q F) = F g r := by
  intro g
  induction g with
  | zero =>
      intro r
      simp [wave_zero]
  | succ g ih =>
      intro r
      let es := children N Q g r
      have hsum :
          (es.map (fun e => edgeWeight e *
            waveAccount N Q g (nextRequest r e) (terminalSeed F))).sum +
          (es.map (fun e => edgeWeight e *
            waveAccount N Q g (nextRequest r e) (localDefect N Q F))).sum =
          (es.map (fun e => edgeWeight e * F g (nextRequest r e))).sum := by
        calc
          _ = (es.map (fun e => edgeWeight e *
                 (waveAccount N Q g (nextRequest r e) (terminalSeed F) +
                  waveAccount N Q g (nextRequest r e) (localDefect N Q F)))).sum :=
                weighted_map_sum_add es edgeWeight
                  (fun e => waveAccount N Q g (nextRequest r e) (terminalSeed F))
                  (fun e => waveAccount N Q g (nextRequest r e) (localDefect N Q F))
          _ = _ := by simp_rw [ih]
      calc
        waveAccount N Q (g+1) r (terminalSeed F) +
            waveAccount N Q (g+1) r (localDefect N Q F) =
          (es.map (fun e => edgeWeight e *
            waveAccount N Q g (nextRequest r e) (terminalSeed F))).sum +
          (F (g+1) r -
            (es.map (fun e => edgeWeight e * F g (nextRequest r e))).sum +
            (es.map (fun e => edgeWeight e *
              waveAccount N Q g (nextRequest r e) (localDefect N Q F))).sum) := by
                simp only [wave_successor, terminalSeed_succ, zero_add]
                change _ + _ = _
                rfl
        _ = F (g+1) r := by
          linarith only [hsum]

/-- All-action transport respects pointwise bounds precisely because
the REAL original path products are positive. -/
theorem waveAccount_mono (N : ℕ) (Q : ℝ) (g : ℕ)
    (r : Request) (V W : ℕ → Request → ℝ)
    (h : ∀ j s, V j s ≤ W j s) :
    waveAccount N Q g r V ≤ waveAccount N Q g r W := by
  unfold waveAccount
  have aux : ∀ xs : List (Occurrence N),
      (xs.map (fun o => mark o * V o.remaining o.current)).sum ≤
      (xs.map (fun o => mark o * W o.remaining o.current)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons o xs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (h o.remaining o.current) (mark_pos o).le) ih
  exact aux _

theorem localDefect_le_positive (N : ℕ) (Q : ℝ)
    (F : ℕ → Request → ℝ) (g : ℕ) (r : Request) :
    localDefect N Q F g r ≤ positiveDefect N Q F g r :=
  le_max_right (0 : ℝ) _

/-- The precise remaining CLOSED-CELL debt is the nonnegative sum of
LOCAL ACTUAL selected-action defects, rather than an assumed global
U3/U4 count bound. No payment or smallness is claimed for that debt. -/
theorem root_le_terminal_plus_unpaid_defects
    (N : ℕ) (Q : ℝ) (F : ℕ → Request → ℝ)
    (g : ℕ) (r : Request) :
    F g r ≤
      waveAccount N Q g r (terminalSeed F) +
      waveAccount N Q g r (positiveDefect N Q F) := by
  have ht := root_eq_terminal_plus_defects N Q F g r
  have hm := waveAccount_mono N Q g r
    (localDefect N Q F) (positiveDefect N Q F)
    (fun j s => localDefect_le_positive N Q F j s)
  linarith only [ht, hm]

/-- Selected retention uses the specified cell and ONE retained edge;
no scalar substitution or extra owner is introduced. -/
theorem selected_retention_defect
    (N : ℕ) (Q : ℝ) (F : ℕ → Request → ℝ)
    (g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .retained) :
    localDefect N Q F (g+1) r =
      F (g+1) r - F g (nextRequest r (.retained i)) := by
  simp [localDefect, children, hs.1, hs.2, branchEdges, edgeWeight]

/-- Selected Buchstab uses the original strict prime carrier, including
both polarities and the actual scalar successor for each prime. -/
theorem selected_buchstab_defect
    (N : ℕ) (Q : ℝ) (F : ℕ → Request → ℝ)
    (g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .buchstab) :
    localDefect N Q F (g+1) r =
      F (g+1) r -
        ((singleChildren
          (.buchstab r.node.upper r.node.physical.argument)
          N Q r.old r.node.physical.ceiling).toList.map
          (fun p => F g (nextRequest r (.buchstab r.node.upper p)))).sum := by
  simp [localDefect, children, hs.1, hs.2, branchEdges,
    List.map_map, edgeWeight]

/-- Exactly the original selected 106-bank row is charged in the defect. -/
theorem selected_bank_defect
    (N : ℕ) (Q : ℝ) (F : ℕ → Request → ℝ)
    (g : ℕ) (r : Request) (i : Fin 200) (k : Fin 106)
    (hs : Selected g r i (.bank k)) :
    localDefect N Q F (g+1) r =
      F (g+1) r -
        ((bankEdges N Q r (actionOfSlot k)).map
          (fun e => edgeWeight e * F g (nextRequest r e))).sum := by
  simp [localDefect, children, hs.1, hs.2, branchEdges]

end
end ImbalancedChen.Part5OriginalH430RequestWaveTelescoping
