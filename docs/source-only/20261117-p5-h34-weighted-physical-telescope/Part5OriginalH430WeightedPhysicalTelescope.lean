import ImbalancedChen.Part5OriginalH430BankSurplusPhysicalSplit

/-!
P5.6 / h34: exact transport of PHYSICAL Theta across the genuine
selected-action request history.

The unweighted root-request telescope has separate parent and child
Theta terms. At each true selected edge, however, the child's physical
Theta is precisely the normalization of the child's own request read.
Keeping the original edge weights therefore makes the two normalizations
cancel internally in the full history, leaving only the Theta-weighted
generation-zero SEED and the genuine same-Q physical source defects.

No error term is assumed small. The result does not identify generated
request values with the original U3/U4 selected counts or prove the
CLOSED-CELL induction, base inequalities, PP/same-rho or 430+11 closure.
The original scalar/specified-cell mode, Q, selected edge list, and path
multiplicities are unchanged.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430WeightedPhysicalTelescope
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430ActualRequestAllActionWave
open Part5OriginalH430RequestWaveTelescoping
open Part5OriginalH430PhysicalRequestDefectBridge

/-- The actual old physical Theta times the literal iterate-g request read.
This uses the same fixed Q for both parent and every true successor. -/
def weightedRequest (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) : ℝ :=
  thetaAtom N Q (parentProduct r.old) * iteratedRequest g r

/-- Only genuine generation-zero leaves carry a weighted seed.
In particular generation 430 is not identified with a seed. -/
def weightedSeed (N : ℕ) (Q : ℝ) (j : ℕ) (r : Request) : ℝ :=
  if j = 0 then weightedRequest N Q 0 r else 0

/-- Exact local identification: the defect of the Theta-weighted
request wave is the PREVIOUSLY DEFINED physical same-Q source defect.
Each child contributes edgeWeight * Theta(child) * requestValue(child),
not the raw unweighted predecessor and not all alternative bank rows. -/
theorem weighted_local_defect_eq_physical
    (N : ℕ) (Q : ℝ) (j : ℕ) (r : Request) :
    localDefect N Q (weightedRequest N Q) j r =
      physicalDefectAt N Q j r := by
  cases j with
  | zero => rfl
  | succ g =>
      simp only [localDefect, physicalDefectAt, physicalStepDefect,
        actualStep, edgeValue, weightedRequest, iteratedRequest, mul_assoc]

/-- Full physical source telescope on the literal selected request tree.
Every path occurrence and coefficient is inherited from history; its
unweighted internal parent/child Theta drift does not need TWO extra
separate payments. The physical source defect itself stays unpaid. -/
theorem weighted_request_root_exact
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    weightedRequest N Q g r =
      waveAccount N Q g r (weightedSeed N Q) +
        waveAccount N Q g r (physicalDefectAt N Q) := by
  have hs : terminalSeed (weightedRequest N Q) = weightedSeed N Q := rfl
  have hd : localDefect N Q (weightedRequest N Q) =
      physicalDefectAt N Q := by
    funext j r
    exact weighted_local_defect_eq_physical N Q j r
  have h := (root_eq_terminal_plus_defects
    N Q (weightedRequest N Q) g r).symm
  rw [hs, hd] at h
  exact h

/-- The original four-term unweighted physical wave and the new
weighted wave give an EXACT cross-generation parent/child Theta
cancellation. The only uncancelled normalization is the true
root-versus-generation-zero boundary, never an assumed zero. -/
theorem parent_child_theta_wave_boundary_exact
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    waveAccount N Q g r (parentThetaAt N Q) +
      waveAccount N Q g r (childThetaAt N Q) =
    (1 - thetaAtom N Q (parentProduct r.old)) *
        iteratedRequest g r +
      waveAccount N Q g r (weightedSeed N Q) -
      waveAccount N Q g r (terminalSeed iteratedRequest) := by
  have hu := root_iterated_request_exact_physical_wave N Q g r
  have hw := weighted_request_root_exact N Q g r
  unfold weightedRequest at hw
  have hroot :
      (1 - thetaAtom N Q (parentProduct r.old)) *
          iteratedRequest g r =
        iteratedRequest g r -
          thetaAtom N Q (parentProduct r.old) *
            iteratedRequest g r := by ring
  rw [hroot]
  linarith only [hu, hw]

/-- Pin the exact 430-generation identity to the REAL frozen U3/U4
request root and its original root-specific Q, not an arbitrary owner.
This is a source equality, NOT the manuscript count-source equality. -/
theorem frozen_root_430_weighted_physical_source
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    thetaAtom N (rootQ N n root tau p)
        (parentProduct (rootRequest N n root tau p).old) *
        iteratedRequest 430 (rootRequest N n root tau p) =
      waveAccount N (rootQ N n root tau p) 430
        (rootRequest N n root tau p)
        (weightedSeed N (rootQ N n root tau p)) +
      waveAccount N (rootQ N n root tau p) 430
        (rootRequest N n root tau p)
        (physicalDefectAt N (rootQ N n root tau p)) := by
  exact weighted_request_root_exact N (rootQ N n root tau p)
    430 (rootRequest N n root tau p)

end
end ImbalancedChen.Part5OriginalH430WeightedPhysicalTelescope
