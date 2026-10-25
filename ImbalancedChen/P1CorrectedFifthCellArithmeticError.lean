import ImbalancedChen.P1CorrectedFifthVariableResidualApproximation
import ImbalancedChen.P1OriginalCoarseFifthCellLimit

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual selected-cell charge begins at the original firstStop/raw-Q3
T3 carrier. Its exact finite tuple dictionary gives the constant stored
new cap and the ACTUAL pointwise old variable-fourth profile. Uniform
arithmetic residual control replaces these two own-cube terms by their
separately gated continuous profiles, with error tending to zero.

No equality of an actual prime sum with a test sum is assumed. The exact
finite carrier identity is proved first. The prime TEST integral limit and
the small-last-prime tail remain OPEN here. No generic-D base is used.
-/

namespace ImbalancedChen.P1CorrectedFifthCellArithmeticError

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P1CorrectedFifthDensityDictionary P1CorrectedFifthCausalTupleDictionary
  P1VariableOwnCubeResidualUniformity P1CorrectedFifthVariableResidualApproximation

def originalCellRegion (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Label5 m) : Set (Fin 5 → ℝ) :=
  logPrimeMeshCell 0 (19 / 96) m j ∩
    HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion (e : ℝ) chi m omega j

def gatedProfileDifference
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega : ℝ) (j : Label5 D.m)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (t : Fin 5 → ℝ) : ℝ :=
  primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
    primeOwnCubeGatedProfile
      (originalVariableFourthProfile e chi omega D.m j rows4 licensed4 t) t

/-- Exact positive-box reindexing from the ACTUAL original T3 carrier.
No old or new fifth admission is imposed on its tuple enumeration. -/
theorem correctedCellPrimeCorrection_eq_residualSums
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega a : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    correctedCellPrimeCorrection D J e chi omega rows4 licensed4 a N cap j =
      actualPrimeBoxOwnCubeMinusSum 4 N cap a (19 / 96) (D.cap5 j : ℝ)
          (originalCellRegion e chi D.m omega j) -
        actualPrimeBoxVariableOwnCubeMinusSum 4 N cap a (19 / 96)
          (originalVariableFourthProfile e chi omega D.m j rows4 licensed4)
          (originalCellRegion e chi D.m omega j) := by
  have hfilter :
      (HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
        (e : ℝ) chi D.m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
            logPrimeMeshCell 0 (19 / 96) D.m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ originalCellRegion e chi D.m omega j) := by
    simpa only [Set.mem_inter_iff, and_comm, originalCellRegion] using
      P1OriginalHistoricalFifthOwnCubeAffineGates.truncated_candidates_filter
        (e : ℝ) chi D.m omega N cap hN hcap j a
  unfold correctedCellPrimeCorrection
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, hfilter, Finset.sum_filter]
  unfold actualPrimeBoxOwnCubeMinusSum actualPrimeBoxVariableOwnCubeMinusSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ originalCellRegion e chi D.m omega j
  · simp only [if_pos ht]
    have hpos : ∀ i, 0 < p i := fun i =>
      (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    rw [correctedTupleDifference_on_selected_cell D J e chi omega rows4 licensed4
      N cap hN p hpos j hj ht.1]
    ring
  · simp only [if_neg ht, mul_zero, sub_self]

/-- The prime test functional is exactly linear on the two separately
gated residuals; this is a finite identity, independent of regularity. -/
theorem actualPrimeBoxTestSum_region_sub {k : ℕ}
    (N : ℕ) (a b : Fin k → ℝ) (R : Set (Fin k → ℝ))
    (f g : (Fin k → ℝ) → ℝ) :
    actualPrimeBoxTestSum N a b (fun t => if t ∈ R then f t - g t else 0) =
      actualPrimeBoxTestSum N a b (fun t => if t ∈ R then f t else 0) -
        actualPrimeBoxTestSum N a b (fun t => if t ∈ R then g t else 0) := by
  unfold actualPrimeBoxTestSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> ring

/-- Genuine arithmetic approximation for one selected original cell.
The only eventual premise covers enumeration of the unchanged carrier.
Both own-cube indicators remain literal, at their own respective levels. -/
theorem tendsto_correctedCellPrimeCorrection_sub_gatedTest
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega a : ℝ) (ha : 0 < a) (hab : a < (19 / 96 : ℝ))
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      correctedCellPrimeCorrection D J e chi omega rows4 licensed4 a N (cap N) j -
        actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
          (fun t => if t ∈ originalCellRegion e chi D.m omega j then
            gatedProfileDifference D e chi omega j rows4 licensed4 t else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  let R := originalCellRegion e chi D.m omega j
  let old := originalVariableFourthProfile e chi omega D.m j rows4 licensed4
  let newSum (N : ℕ) := actualPrimeBoxOwnCubeMinusSum 4 N (cap N) a (19 / 96)
    (D.cap5 j : ℝ) R
  let oldSum (N : ℕ) := actualPrimeBoxVariableOwnCubeMinusSum 4 N (cap N) a (19 / 96) old R
  let newTest (N : ℕ) := actualPrimeBoxTestSum N (fun _ : Fin 5 => a)
    (fun _ => (19 / 96 : ℝ))
      (fun t => if t ∈ R then primeOwnCubeGatedProfile (D.cap5 j : ℝ) t else 0)
  let oldTest (N : ℕ) := actualPrimeBoxTestSum N (fun _ : Fin 5 => a)
    (fun _ => (19 / 96 : ℝ))
      (fun t => if t ∈ R then primeOwnCubeGatedProfile (old t) t else 0)
  have hnew : Tendsto (fun N : ℕ => newSum N - newTest N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) :=
    tendsto_actualPrimeBoxOwnCubeMinus_error 4 a (19 / 96) (D.cap5 j : ℝ)
      ha hab R cap hcap
  have hold : Tendsto (fun N : ℕ => oldSum N - oldTest N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) :=
    tendsto_originalVariableFourth_ownCube_error D e chi omega a ha hab j
      rows4 licensed4 R cap hcap
  have hdiff : Tendsto (fun N : ℕ =>
      (newSum N - newTest N) - (oldSum N - oldTest N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
    simpa only [sub_self] using hnew.sub hold
  apply hdiff.congr'
  have hlarge : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge, hcap] with N hN hc
  rw [correctedCellPrimeCorrection_eq_residualSums D J e chi omega a
    rows4 licensed4 N (cap N) hN hc j hj]
  have htest : actualPrimeBoxTestSum N (fun _ : Fin 5 => a)
      (fun _ => (19 / 96 : ℝ))
        (fun t => if t ∈ originalCellRegion e chi D.m omega j then
          gatedProfileDifference D e chi omega j rows4 licensed4 t else 0) =
      newTest N - oldTest N := by
    exact actualPrimeBoxTestSum_region_sub N (fun _ : Fin 5 => a)
      (fun _ => (19 / 96 : ℝ)) R
        (primeOwnCubeGatedProfile (D.cap5 j : ℝ))
        (fun t => primeOwnCubeGatedProfile (old t) t)
  rw [htest]
  change (newSum N - newTest N) - (oldSum N - oldTest N) =
    (newSum N - oldSum N) - (newTest N - oldTest N)
  ring

/-- Unselected owners contribute exactly zero on the finite original
carrier, including their half-open mesh boundaries. -/
theorem correctedCellPrimeCorrection_eq_zero_of_unselected
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega a : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (N cap : ℕ) (j : Label5 D.m) (hj : j ∉ D.cells5 ∩ J) :
    correctedCellPrimeCorrection D J e chi omega rows4 licensed4 a N cap j = 0 := by
  unfold correctedCellPrimeCorrection
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
        logPrimeMeshCell 0 (19 / 96) D.m j
  · have hout : ∀ q ∈ D.cells5 ∩ J,
        actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) D.m q := by
      intro q hq hmem
      have heq : q = j := logPrimeMeshCell_unique
        (by norm_num : (0 : ℝ) ≤ 19 / 96) hmem ht.2
      exact hj (heq ▸ hq)
    rw [if_pos ht, correctedTupleDifference_outside D J e chi omega
      rows4 licensed4 N cap p hout, mul_zero]
  · rw [if_neg ht, mul_zero]

end
end ImbalancedChen.P1CorrectedFifthCellArithmeticError
