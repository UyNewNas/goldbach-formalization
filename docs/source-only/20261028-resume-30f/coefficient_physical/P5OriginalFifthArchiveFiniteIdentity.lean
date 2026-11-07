import ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual gated finite Rosser residual, original prime weights and the
two different causal third-frontier carriers are retained. Below mu those
carriers agree; outside the licensed fifth source both local residual
differences are zero. Therefore the complete normalized literal FIFTH
tuple charge is unchanged for this independently indexed archive.

This identifies an actual finite charge with the ORIGINAL actual saving;
it does not silently identify that charge with the common physical-rho
difference. That caller still needs the common admissibility/refreezing
and signed small-beta correction. No finite signed-density monotonicity,
desired error estimate or common compact approximation is a premise.
-/
namespace ImbalancedChen.P5OriginalFifthArchiveFiniteIdentity
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P5OriginalFifthArchiveFallbackSeparation
open P5OriginalCommonRefinedPreservation
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P1CorrectedFifthCausalTupleDictionary
open P1HistoricalFifthCommonPolicyInputs

private theorem ownCubeDensity_congr_at (N cap : ℕ) (Q R : List ℕ → ℝ)
    (pre : List ℕ) (h : Q pre = R pre) :
    actualOwnCubeGatedMinusDensity N cap Q pre = actualOwnCubeGatedMinusDensity N cap R pre := by
  simp only [actualOwnCubeGatedMinusDensity, h]

def oldQ4 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ := N ^ oldFourth d N pre
def oldQ5 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ := N ^ oldFifth d N pre

private theorem literal_eq_zero_of_same_level (Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (h : Q5 (tupleHistory p) = Q4 (rosserAncestor 4 (tupleHistory p))) :
    literalTupleDifference Q4 Q5 N cap p = 0 := by
  have he := ownCubeDensity_congr_at N cap Q5
    (fun pre => Q4 (rosserAncestor 4 pre)) (tupleHistory p) h
  simp only [literalTupleDifference, he, sub_self, zero_mul, zero_div]

variable (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (e : ℚ) (q : ℕ) (chi omega : ℝ)

theorem actual_literal_same_increment (N cap : ℕ) (p : Fin 5 → ℕ) :
    literalTupleDifference
      (level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (level5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ)) N cap p =
    literalTupleDifference
      (oldQ4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (oldQ5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ)) N cap p := by
  let d := sourceData rows4 licensed4 e q chi omega
  have hl : (tupleHistory p).length = 5 := by simp [tupleHistory]
  by_cases hx : primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) 0 < VariableEnvelope.mu
  · have h4 := inherited_eq_old_below_mu d (N : ℝ) (tupleHistory p) hl hx.le
    have h5 := fifth_eq_old_below_mu d (N : ℝ) (tupleHistory p) hl hx.le
    have ho4 := ownCubeDensity_congr_at N cap
      (fun pre => level4 d (N : ℝ) (rosserAncestor 4 pre))
      (fun pre => oldQ4 d (N : ℝ) (rosserAncestor 4 pre)) (tupleHistory p)
      (congrArg (fun x : ℝ => (N : ℝ) ^ x) h4)
    have ho5 := ownCubeDensity_congr_at N cap (level5 d (N : ℝ)) (oldQ5 d (N : ℝ))
      (tupleHistory p) (congrArg (fun x : ℝ => (N : ℝ) ^ x) h5)
    simp only [literalTupleDifference, ho4, ho5]
  · have he := actual_archive_fifth_outside_below_mu rows4 licensed4 e q chi omega
      (N : ℝ) (tupleHistory p) hl (le_of_not_gt hx)
    have hcommon := literal_eq_zero_of_same_level (level4 d (N : ℝ)) (level5 d (N : ℝ))
      N cap p (congrArg (fun x : ℝ => (N : ℝ) ^ x) he.2)
    have hold := literal_eq_zero_of_same_level (oldQ4 d (N : ℝ)) (oldQ5 d (N : ℝ))
      N cap p (congrArg (fun x : ℝ => (N : ℝ) ^ x) he.1)
    exact hcommon.trans hold.symm

theorem actual_literal_zero_above_mu (N cap : ℕ) (p : Fin 5 → ℕ)
    (hx : VariableEnvelope.mu ≤ actualPrimeTupleLog N p 0) :
    literalTupleDifference
      (oldQ4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (oldQ5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ)) N cap p = 0 := by
  have hl : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have he := (actual_archive_fifth_outside_below_mu rows4 licensed4 e q chi omega
    (N : ℝ) (tupleHistory p) hl (by simpa only [tupleHistory_log] using hx)).1
  exact literal_eq_zero_of_same_level _ _ N cap p
    (congrArg (fun x : ℝ => (N : ℝ) ^ x) he)

private theorem common3_third_eq_old (d : OriginalData) (N : ℝ) (p0 p1 p2 : ℕ)
    (hx : Real.log (p0 : ℝ) / Real.log N ≤ VariableEnvelope.mu) :
    common3 d N false [p2, p1, p0] = old3 d N false [p2, p1, p0] := by
  have hs : ¬secondGuard N [p2, p1, p0] := by
    intro hg
    have hh : VariableEnvelope.mu < Real.log (p0 : ℝ) / Real.log N := by
      simpa [primeHistoryLogCoordinates, primeHistoryTuple, rosserAncestor] using hg.1
    exact not_lt_of_ge hx hh
  simp [common3, fallback23, finalPolicy, secondPolicy, firstExitDepthSplicePolicy,
    secondReplacement, hs, oldPolicy, old3]

/-- Only the proper parent is tested: the fifth candidate is not required
to pass either its old or its new own-cube/admission gate. -/
theorem actual_fifth_carrier_iff_below_mu (d : OriginalData) (N : ℝ)
    (carrier : List ℕ) (p : Fin 5 → ℕ)
    (hx : Real.log (p 0 : ℝ) / Real.log N ≤ VariableEnvelope.mu) :
    p ∈ firstExitFrontierTuples 4 (common3 d N) carrier ↔
      p ∈ firstExitFrontierTuples 4 (old3 d N) carrier := by
  have hd : (List.ofFn p).dropLast = [p 0, p 1, p 2, p 3] := by simp [List.ofFn_succ]
  have h1 := common3_through_two d N false [p 0] (by simp)
  have h3 := common3_third_eq_old d N (p 0) (p 1) (p 2) hx
  have ho (pre : List ℕ) : old3 d N true pre = true := by
    simp [old3, HistoricalThirdCoarse.policy_even]
  rw [mem_firstExitFrontierTuples_iff, mem_firstExitFrontierTuples_iff, hd]
  simp only [FirstExitValidSelection, Bool.not_true, Bool.not_false, common3_even, ho,
    h1, h3, and_true]

def commonLiteralCharge (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4
      (common3 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (roughPrimeUniverse N cap 0 z),
    (∏ i, 1 / ((p i : ℝ) - 1)) * literalTupleDifference
      (level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (level5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ)) N cap p

/-- The different carrier domains are paid by exact zero extension, not
assumed equal. This equality is valid at every finite target and cap. -/
theorem commonLiteralCharge_eq_original (N cap : ℕ) (z : ℝ) :
    commonLiteralCharge rows4 licensed4 e q chi omega N cap z =
      P4AOriginalVariableFifthPhysicalLedger.fifthTupleCharge e chi
        (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) omega rows4 licensed4
        (P1HistoricalFifthIndexedOwnerArchive.globalOwners e q chi omega)
        (P1HistoricalFifthIndexedOwnerArchive.licensedRows e q chi omega) N cap z := by
  let d := sourceData rows4 licensed4 e q chi omega
  let A := firstExitFrontierTuples 4 (common3 d (N : ℝ)) (roughPrimeUniverse N cap 0 z)
  let B := firstExitFrontierTuples 4 (old3 d (N : ℝ)) (roughPrimeUniverse N cap 0 z)
  let F := fun p : Fin 5 → ℕ => (∏ i, 1 / ((p i : ℝ) - 1)) *
    literalTupleDifference (oldQ4 d (N : ℝ)) (oldQ5 d (N : ℝ)) N cap p
  have hz (p : Fin 5 → ℕ) (hx : ¬Real.log (p 0 : ℝ) / Real.log (N : ℝ) < VariableEnvelope.mu) :
      F p = 0 := by
    have hh := actual_literal_zero_above_mu rows4 licensed4 e q chi omega N cap p (le_of_not_gt hx)
    simp only [F, hh, mul_zero]
  have hA : (∑ p ∈ A, F p) = ∑ p ∈ A ∪ B, F p := by
    apply Finset.sum_subset Finset.subset_union_left
    intro p hp hn
    by_cases hx : Real.log (p 0 : ℝ) / Real.log (N : ℝ) < VariableEnvelope.mu
    · have hb : p ∈ B := (Finset.mem_union.mp hp).resolve_left hn
      exact False.elim (hn ((actual_fifth_carrier_iff_below_mu d (N : ℝ) _ p hx.le).mpr hb))
    · exact hz p hx
  have hB : (∑ p ∈ B, F p) = ∑ p ∈ A ∪ B, F p := by
    apply Finset.sum_subset Finset.subset_union_right
    intro p hp hn
    by_cases hx : Real.log (p 0 : ℝ) / Real.log (N : ℝ) < VariableEnvelope.mu
    · have ha : p ∈ A := (Finset.mem_union.mp hp).resolve_right hn
      exact False.elim (hn ((actual_fifth_carrier_iff_below_mu d (N : ℝ) _ p hx.le).mp ha))
    · exact hz p hx
  unfold commonLiteralCharge
  simp_rw [actual_literal_same_increment rows4 licensed4 e q chi omega]
  exact hA.trans hB.symm

/-- Connection to the independent ORIGINAL finite actual saving. The
common-rho density caller and its signed beta term remain separate. -/
theorem commonLiteralCharge_eq_normalized_original_saving (N cap : ℕ) (z : ℝ) :
    commonLiteralCharge rows4 licensed4 e q chi omega N cap z =
      P1OriginalVariableFifthContinuation.actualFifthSaving e chi
        (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) omega rows4 licensed4
        (P1HistoricalFifthIndexedOwnerArchive.globalOwners e q chi omega)
        (P1HistoricalFifthIndexedOwnerArchive.licensedRows e q chi omega) N cap z *
          Real.log (N : ℝ) / singularSeries N := by
  rw [commonLiteralCharge_eq_original]
  exact (P4AOriginalVariableFifthPhysicalLedger.fifthSaving_normalized_eq_tupleCharge
    _ _ _ _ _ _ _ _ N cap z).symm

end
end ImbalancedChen.P5OriginalFifthArchiveFiniteIdentity
