import ImbalancedChen.ActualPrimeBoxOwnCubeResidual
import ImbalancedChen.ActualFrozenOwnCubeDensity
import ImbalancedChen.PrimeHistoryLogCoordinates

/-!
# Exact own-cube density dictionary for reverse-stored histories

The processing-order tuple retains the actual history product and last
selected prime. Thus its gated, normalized lower residual is the same
physical density used by the actual frontier identities. Reciprocal-prime
mass is preserved even with repeated entries; the separate totient
corollary explicitly requires a duplicate-free history.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory

/-- The two logarithmic coordinate systems agree at the same target. -/
theorem primeHistoryLogCoordinates_eq_actualPrimeTupleLog
    (N k : ℕ) (history : List ℕ) :
    primeHistoryLogCoordinates (N : ℝ) k history =
      actualPrimeTupleLog N (primeHistoryTuple k history) := rfl

/-- Neither side changes its strict own-cube gate or its quotient level. -/
theorem actualPrimeTupleOwnCubeMinus_primeHistoryTuple
    (N cap : ℕ) (lambda : ℝ) {k : ℕ} {history : List ℕ}
    (hlen : history.length = k + 1) :
    actualPrimeTupleOwnCubeMinus N cap lambda (primeHistoryTuple (k + 1) history) =
      actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambda) history *
        Real.log (N : ℝ) / singularSeries N := by
  simp only [actualPrimeTupleOwnCubeMinus, actualOwnCubeGatedMinusDensity,
    primeHistoryTuple_prod hlen, primeHistoryTuple_last hlen]
  split_ifs <;> ring

/-- The original history's own-cube condition is exactly the strict
affine condition on its processing-order logarithmic coordinates. -/
theorem primeHistoryOwnCube_iff_log
    {N k : ℕ} (hN : 1 < N) {history : List ℕ}
    (hlen : history.length = k + 1) (hpos : ∀ p ∈ history, 0 < p) (lambda : ℝ) :
    (history.prod : ℝ) * (history.headD 0 : ℝ) ^ 2 < (N : ℝ) ^ lambda ↔
      primeTupleOwnCubeForm (primeHistoryLogCoordinates (N : ℝ) (k + 1) history) <
        lambda := by
  simpa only [primeHistoryTuple_prod hlen, primeHistoryTuple_last hlen,
    primeHistoryLogCoordinates_eq_actualPrimeTupleLog] using
    actualPrimeTupleOwnCube_iff hN (primeHistoryTuple (k + 1) history)
      (primeHistoryTuple_pos hlen hpos) lambda

/-- This weighted identity needs no ordering, primality or distinctness
assumption. The same list mass is used on both sides. -/
theorem primeHistory_weightedOwnCubeMinus
    (N cap : ℕ) (lambda : ℝ) {k : ℕ} {history : List ℕ}
    (hlen : history.length = k + 1) :
    (∏ i, 1 / ((primeHistoryTuple (k + 1) history i : ℝ) - 1)) *
        actualPrimeTupleOwnCubeMinus N cap lambda (primeHistoryTuple (k + 1) history) =
      (history.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
        actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambda) history *
        Real.log (N : ℝ) / singularSeries N := by
  rw [primeHistoryTuple_reciprocal_mass hlen,
    actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap lambda hlen]
  ring

/-- Both own-cube indicators remain present when comparing two levels. -/
theorem primeHistory_weightedOwnCubeMinus_sub
    (N cap : ℕ) (lambdaOld lambdaNew : ℝ) {k : ℕ} {history : List ℕ}
    (hlen : history.length = k + 1) :
    (∏ i, 1 / ((primeHistoryTuple (k + 1) history i : ℝ) - 1)) *
        (actualPrimeTupleOwnCubeMinus N cap lambdaNew (primeHistoryTuple (k + 1) history) -
          actualPrimeTupleOwnCubeMinus N cap lambdaOld (primeHistoryTuple (k + 1) history)) =
      (history.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
        (actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambdaNew) history -
          actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambdaOld) history) *
        Real.log (N : ℝ) / singularSeries N := by
  rw [primeHistoryTuple_reciprocal_mass hlen,
    actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap lambdaNew hlen,
    actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap lambdaOld hlen]
  ring

/-- Only the reciprocal-totient rewriting needs distinct prime labels. -/
theorem primeHistoryTuple_reciprocalTotient
    {N k : ℕ} {a b : Fin k → ℝ} {history : List ℕ}
    (hlen : history.length = k) (hnodup : history.Nodup)
    (hp : primeHistoryTuple k history ∈ actualPrimeBoxTuples N a b) :
    1 / (Nat.totient history.prod : ℝ) =
      (history.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod := by
  have hinj : Function.Injective (primeHistoryTuple k history) := by
    apply List.nodup_ofFn.mp
    rw [primeHistoryTuple_ofFn hlen]
    exact List.nodup_reverse.mpr hnodup
  simpa only [primeHistoryTuple_prod hlen, primeHistoryTuple_reciprocal_mass hlen] using
    actualPrimeBoxTuple_reciprocalTotient hp hinj

/-- For every real next candidate the state mass, rather than an assumed
substitute, gives the exact tuple expression. Rejected candidates remain. -/
theorem actualPrimeCandidate_weightedOwnCubeMinus_sub
    (k : ℕ) (parent : Bool → List ℕ → Bool) (N cap : ℕ) (z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining)
    (lambdaOld lambdaNew : ℝ) :
    (∏ i, 1 / ((primeHistoryTuple (k + 1) candidate.selectedPrefix i : ℝ) - 1)) *
        (actualPrimeTupleOwnCubeMinus N cap lambdaNew
            (primeHistoryTuple (k + 1) candidate.selectedPrefix) -
          actualPrimeTupleOwnCubeMinus N cap lambdaOld
            (primeHistoryTuple (k + 1) candidate.selectedPrefix)) =
      candidate.mass *
        (actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambdaNew)
            candidate.selectedPrefix -
          actualOwnCubeGatedMinusDensity N cap (fun _ => (N : ℝ) ^ lambdaOld)
            candidate.selectedPrefix) * Real.log (N : ℝ) / singularSeries N := by
  obtain ⟨hlen, _hsort, _hP, _hcut, _hremaining, _hsign, hmass, _hprime⟩ :=
    actualPrimeNextSelection_geometry k parent N cap z frontier hfrontier candidate hcandidate
  rw [primeHistory_weightedOwnCubeMinus_sub N cap lambdaOld lambdaNew hlen, hmass]

end

end ImbalancedChen
