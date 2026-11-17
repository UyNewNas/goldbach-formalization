import ImbalancedChen.Part5OriginalH430RequestWaveTelescoping

/-!
P5.6/h34: connect the ACTUAL request-value wave to the physical same-Q
edge consumer, retaining both parent-Theta and child-Theta corrections.

The preceding telescope accepted an arbitrary F and therefore did not
identify its local defects with the genuine iterate(g+1) request read.
Here F is the *literal* chosen scalar/specified-cell requestValue of the
frozen feedback iterate. The two Theta corrections are explicit signed
debts, not assumed small or paid. Every child is from the original
selected resolver, not a second choice. No U3/U4 owner is asserted.

SOURCE ONLY / UNCOMPILED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalRequestDefectBridge

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P2OriginalChildPhysicalNormalization
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430ActualRequestAllActionWave
open Part5OriginalH430RequestWaveTelescoping

/-- The genuine scalar OR specified-cell request read at the exact iterate. -/
def iteratedRequest (g : ℕ) (r : Request) : ℝ :=
  requestValue (iterate g) r

/-- Signed parent-Theta-adjusted source defect, using precisely the
original physical same-Q edgeValue on the selected preceding iterate. -/
def physicalStepDefect (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) : ℝ :=
  thetaAtom N Q (parentProduct r.old) * iteratedRequest (g+1) r -
    actualStep N Q g r (iterate g)

/-- The complete child-side normalization debt, evaluated at the actual
next request. No Theta=1 assumption or positivity of the table is used. -/
def childThetaDrift (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) : ℝ :=
  ((children N Q g r).map (fun e =>
    edgeWeight e *
      (thetaAtom N Q (parentProduct (nextRequest r e).old) - 1) *
        iteratedRequest g (nextRequest r e))).sum

/-- Literal physical edgeValue equals the unweighted request wave plus
its child-Theta correction. This retains every selected original edge occurrence. -/
theorem edgeValue_eq_raw_plus_theta (N : ℕ) (Q : ℝ) (r : Request)
    (es : List (Edge N)) (t : Table) :
    edgeValue Q t r es =
      ((es.map (fun e =>
        edgeWeight e * requestValue t (nextRequest r e))).sum) +
      ((es.map (fun e =>
        edgeWeight e *
          (thetaAtom N Q (parentProduct (nextRequest r e).old) - 1) *
            requestValue t (nextRequest r e))).sum) := by
  unfold edgeValue
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem physical_step_eq_raw_plus_drift (N : ℕ) (Q : ℝ)
    (g : ℕ) (r : Request) :
    actualStep N Q g r (iterate g) =
      ((children N Q g r).map
        (fun e => edgeWeight e * iteratedRequest g (nextRequest r e))).sum +
      childThetaDrift N Q g r := by
  simpa only [actualStep, childThetaDrift, iteratedRequest] using
    edgeValue_eq_raw_plus_theta N Q r (children N Q g r) (iterate g)

/-- A nonabstract local defect identity for the TRUE g+1 iterate.
Two signed normalization corrections must be paid separately from the
physical same-Q source defect; neither has a presumed favorable sign. -/
theorem actual_request_local_defect_exact (N : ℕ) (Q : ℝ)
    (g : ℕ) (r : Request) :
    localDefect N Q iteratedRequest (g+1) r =
      (1 - thetaAtom N Q (parentProduct r.old)) *
          iteratedRequest (g+1) r +
        (physicalStepDefect N Q g r + childThetaDrift N Q g r) := by
  have h := physical_step_eq_raw_plus_drift N Q g r
  change iteratedRequest (g+1) r -
      ((children N Q g r).map
        (fun e => edgeWeight e * iteratedRequest g (nextRequest r e))).sum =
      (1 - thetaAtom N Q (parentProduct r.old)) *
          iteratedRequest (g+1) r +
        (physicalStepDefect N Q g r + childThetaDrift N Q g r)
  unfold physicalStepDefect
  rw [h]
  ring

/-- The exterior scalar request has neither a read nor a physical gap.
Specified-cell requests cannot be exterior by definition. -/
theorem exterior_physical_gap_zero (N : ℕ) (Q : ℝ)
    (g : ℕ) (r : Request) (h : resolve (g+1) r = none) :
    physicalStepDefect N Q g r = 0 := by
  have hread := (exterior_children_empty h).2
  have hstep := step_exterior_zero N Q g r (iterate g) h
  simp [physicalStepDefect, iteratedRequest, hread, hstep]

/-- The exact selected retention source deficit still reads its own
specified predecessor cell; parent Theta has NOT been normalized away. -/
theorem selected_retention_physical_gap (N : ℕ) (Q : ℝ)
    (g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .retained) :
    physicalStepDefect N Q g r =
      thetaAtom N Q (parentProduct r.old) *
        (iteratedRequest (g+1) r - floorValue (iterate g r.node.upper) i) := by
  unfold physicalStepDefect
  rw [step_retained N Q g r (iterate g) i hs]
  ring


/-- On the selected genuine retention edge, the parent-normalization
and child-normalization terms cancel in the TOTAL request residual.
It is incorrect to charge them independently as two retained debts. -/
theorem selected_retention_total_gap (N : ℕ) (Q : ℝ)
    (g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .retained) :
    (1 - thetaAtom N Q (parentProduct r.old)) *
        iteratedRequest (g+1) r +
      (physicalStepDefect N Q g r + childThetaDrift N Q g r) =
    iteratedRequest (g+1) r -
      iteratedRequest g (nextRequest r (.retained i)) := by
  have h := actual_request_local_defect_exact N Q g r
  rw [selected_retention_defect N Q iteratedRequest g r i hs] at h
  exact h.symm

/-- Zero generation is the seed, not a wrapped predecessor-429. -/
def parentThetaAt (N : ℕ) (Q : ℝ) : ℕ → Request → ℝ
  | 0, _ => 0
  | g+1, r => (1 - thetaAtom N Q (parentProduct r.old)) *
      iteratedRequest (g+1) r

def physicalDefectAt (N : ℕ) (Q : ℝ) : ℕ → Request → ℝ
  | 0, _ => 0
  | g+1, r => physicalStepDefect N Q g r

def childThetaAt (N : ℕ) (Q : ℝ) : ℕ → Request → ℝ
  | 0, _ => 0
  | g+1, r => childThetaDrift N Q g r

theorem every_generation_physical_split (N : ℕ) (Q : ℝ)
    (j : ℕ) (r : Request) :
    localDefect N Q iteratedRequest j r =
      parentThetaAt N Q j r +
        (physicalDefectAt N Q j r + childThetaAt N Q j r) := by
  cases j with
  | zero =>
      simp [localDefect, parentThetaAt, physicalDefectAt, childThetaAt]
  | succ g =>
      simpa only [parentThetaAt, physicalDefectAt, childThetaAt] using
        actual_request_local_defect_exact N Q g r

private theorem waveAccount_add (N : ℕ) (Q : ℝ) (g : ℕ)
    (r : Request) (V W : ℕ → Request → ℝ) :
    waveAccount N Q g r (fun j s => V j s + W j s) =
      waveAccount N Q g r V + waveAccount N Q g r W := by
  unfold waveAccount
  have aux (xs : List (Occurrence N)) :
      (xs.map (fun o => mark o * (V o.remaining o.current +
        W o.remaining o.current))).sum =
      (xs.map (fun o => mark o * V o.remaining o.current)).sum +
      (xs.map (fun o => mark o * W o.remaining o.current)).sum := by
    induction xs with
    | nil => simp
    | cons o xs ih =>
        simp only [List.map_cons, List.sum_cons, mul_add]
        rw [ih]
        ring
  exact aux (history N Q g r)

/-- Full genuine request-value telescope: seed plus physical same-Q
source defect plus BOTH normalization corrections, at every actual
history occurrence and with original edge-product weights. This
reduces the remaining quantitative CLOSED-CELL work to three explicit
manuscript-local payments; it does not claim any payment is small. -/
theorem root_iterated_request_exact_physical_wave
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    iteratedRequest g r =
      waveAccount N Q g r (terminalSeed iteratedRequest) +
      waveAccount N Q g r (parentThetaAt N Q) +
      waveAccount N Q g r (physicalDefectAt N Q) +
      waveAccount N Q g r (childThetaAt N Q) := by
  have hloc :
      waveAccount N Q g r (localDefect N Q iteratedRequest) =
      waveAccount N Q g r
        (fun j s => parentThetaAt N Q j s +
          (physicalDefectAt N Q j s + childThetaAt N Q j s)) := by
    simp only [waveAccount, every_generation_physical_split]
  have hsplit :
      waveAccount N Q g r
        (fun j s => parentThetaAt N Q j s +
          (physicalDefectAt N Q j s + childThetaAt N Q j s)) =
      waveAccount N Q g r (parentThetaAt N Q) +
        (waveAccount N Q g r (physicalDefectAt N Q) +
          waveAccount N Q g r (childThetaAt N Q)) := by
    calc
      _ = waveAccount N Q g r (parentThetaAt N Q) +
          waveAccount N Q g r
            (fun j s => physicalDefectAt N Q j s + childThetaAt N Q j s) :=
              waveAccount_add N Q g r (parentThetaAt N Q)
                (fun j s => physicalDefectAt N Q j s + childThetaAt N Q j s)
      _ = _ := by rw [waveAccount_add]
  calc
    iteratedRequest g r =
        waveAccount N Q g r (terminalSeed iteratedRequest) +
          waveAccount N Q g r (localDefect N Q iteratedRequest) :=
            (root_eq_terminal_plus_defects N Q iteratedRequest g r).symm
    _ = _ := by
      rw [hloc, hsplit]
      ring

end
end ImbalancedChen.Part5OriginalH430PhysicalRequestDefectBridge
