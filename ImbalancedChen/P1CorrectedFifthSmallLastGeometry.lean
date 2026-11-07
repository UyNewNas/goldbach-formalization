import ImbalancedChen.P1CorrectedFifthStoredH45Check
import ImbalancedChen.P1CorrectedFifthGlobalSourceAssembly
import ImbalancedChen.P1OriginalFifthMovingHarmonicEnvelope

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual corrected OLD4 producer inherits the unchanged original raw Q3.
A finite stored h45 check raises the stored NEW cap above that actual OLD4.
The original selected third cube and rough activation therefore force a
common omega/2 residual gap when the last fifth coordinate is small.
Both strict own-cube gates and arbitrary moving auxiliary source budgets
are proved from that geometry, before invoking any arithmetic tail bound.

No old coarse cap4 dictionary, all15 surrogate, desired remainder bound,
or target mean is used. The finite checker is primitive source data; no
claim is made that a concrete numerical table has passed it. Summing or
removing the actual corrected small remainder is still OPEN.
-/

namespace ImbalancedChen.P1CorrectedFifthSmallLastGeometry

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1CorrectedFifthCausalTupleDictionary
open P1CorrectedFifthStoredH45Check P1OriginalSmallCutoffActualLowerTail

abbrev FifthLabel (m : ℕ) := P1OriginalCoarseFifthContinuation.Label5 m

/-- A pointwise geometric conclusion on the TRUE original selected source.
The producer max and stored cap have their own distinct strict gates. -/
theorem actual_corrected_source_gaps_and_gates
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega a : ℝ) (homega : 0 < omega) (ha : 0 < a)
    (haomega : a ≤ omega / 3)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true)
    (j : FifthLabel D.m) (hj : j ∈ D.cells5 ∩ J) (t : Fin 5 → ℝ)
    (ht : t ∈ P1CorrectedFifthCellArithmeticError.originalCellRegion e chi D.m omega j)
    (hlast : 0 < t 4) (hsmall : t 4 ≤ a) :
    omega / 2 < originalVariableFourthProfile e chi omega D.m j rows licensed t - ∑ i, t i ∧
      omega / 2 < (D.cap5 j : ℝ) - ∑ i, t i ∧
      omega / (2 * a) <
        (originalVariableFourthProfile e chi omega D.m j rows licensed t - ∑ i, t i) / t 4 ∧
      omega / (2 * a) < ((D.cap5 j : ℝ) - ∑ i, t i) / t 4 ∧
      primeTupleOwnCubeForm t < originalVariableFourthProfile e chi omega D.m j rows licensed t ∧
      primeTupleOwnCubeForm t < (D.cap5 j : ℝ) := by
  have hselected : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) :=
    (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) j).mpr
        ⟨hj, (howned.2.2 j hj).1, (howned.2.2 j hj).2⟩
  have hactive := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
    e chi D.m omega (D.cells5 ∩ J) j hselected ht.1
  have hg := (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_jointRegion
    (e : ℝ) chi D.m omega j t).mp ht.2
  have h34 := originalVariableFourthProfile_inherits_rawQ3
    e chi omega D.m j rows licensed t
  have h45 := originalVariableFourthProfile_le_storedCap
    D J e chi omega rows licensed howned hcheck j hj t ht.1
  obtain ⟨_, _, hgapOld, hgapNew, hratioOld, hratioNew, hgateOld, hgateNew⟩ :=
    HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_small_last_gates
      omega (HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
        (e : ℝ) chi D.m omega j t)
      (originalVariableFourthProfile e chi omega D.m j rows licensed t) (D.cap5 j : ℝ)
      a t homega ha haomega hlast hsmall hactive hg.2.2.2.2
        (hg.2.1 (by decide : (2 : Fin 5) < 3)) h34 h45
  exact ⟨hgapOld, hgapNew, hratioOld, hratioNew, hgateOld, hgateNew⟩

/-- The actual original candidate dictionary supplies primality, the
strict outer cutoff, and the true original jointRegion, without an own cube. -/
theorem corrected_candidate_physical_gaps
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega a : ℝ) (homega : 0 < omega) (ha : 0 < a)
    (haomega : a ≤ omega / 3)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ)
    (hp : p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (e : ℝ) chi D.m omega N cap)
    (j : FifthLabel D.m) (hj : j ∈ D.cells5 ∩ J)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j)
    (hsmall : actualPrimeTupleLog N p 4 ≤ a) :
    (∀ i, 0 < p i) ∧ 1 < (p 4 : ℝ) ∧ (p 4 : ℝ) ≤ (cap : ℝ) ∧
      omega / 2 < originalVariableFourthProfile e chi omega D.m j rows licensed
        (actualPrimeTupleLog N p) - ∑ i, actualPrimeTupleLog N p i ∧
      omega / 2 < (D.cap5 j : ℝ) - ∑ i, actualPrimeTupleLog N p i ∧
      (N : ℝ) ^ (omega / 2) < residualLevel N
        (originalVariableFourthProfile e chi omega D.m j rows licensed (actualPrimeTupleLog N p)) p ∧
      (N : ℝ) ^ (omega / 2) < residualLevel N (D.cap5 j : ℝ) p ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^
        originalVariableFourthProfile e chi omega D.m j rows licensed (actualPrimeTupleLog N p) ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < (N : ℝ) ^ (D.cap5 j : ℝ) := by
  have hd := (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_candidates_iff_log_on_cell
    (e : ℝ) chi D.m omega N cap hN hcap p j ht).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.1 i).1.pos
  have hy : (1 : ℝ) < p 4 := by exact_mod_cast (hd.1 4).1.one_lt
  have hlast : 0 < actualPrimeTupleLog N p 4 :=
    div_pos (Real.log_pos hy) (Real.log_pos (by exact_mod_cast hN))
  have hg := actual_corrected_source_gaps_and_gates D J e chi omega a homega ha haomega
    rows licensed howned hcheck j hj (actualPrimeTupleLog N p) ⟨ht, hd.2⟩ hlast hsmall
  refine ⟨hpos, hy, (hd.1 4).2.2.2.le.trans hcap, hg.1, hg.2.1, ?_, ?_, ?_, ?_⟩
  · exact HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
      hN p hpos _ _ hg.1
  · exact HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
      hN p hpos _ _ hg.2.1
  · exact (actualPrimeTupleOwnCube_iff hN p hpos _).mpr hg.2.2.2.2.1
  · exact (actualPrimeTupleOwnCube_iff hN p hpos _).mpr hg.2.2.2.2.2

/-- The only remaining restrictions are primitive scalar source budgets.
Their legality at BOTH unchanged physical quotient levels is derived from
the actual original source gap, not assumed as a tail estimate. -/
theorem corrected_selected_source_budgets
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega a T : ℝ) (homega : 0 < omega) (ha : 0 < a)
    (haomega : a ≤ omega / 3) (hT : 2 ≤ T) (haT : a * T ≤ omega / 2)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (hbudget : T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ))
    (hlog : Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ))
    (p : Fin 5 → ℕ)
    (hp : p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (e : ℝ) chi D.m omega N cap)
    (j : FifthLabel D.m) (hj : j ∈ D.cells5 ∩ J)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j)
    (hsmall : actualPrimeTupleLog N p 4 ≤ a) :
    sourceBudget (p 4 : ℝ) (residualLevel N
      (originalVariableFourthProfile e chi omega D.m j rows licensed (actualPrimeTupleLog N p)) p) T ∧
      sourceBudget (p 4 : ℝ) (residualLevel N (D.cap5 j : ℝ) p) T := by
  have hg := corrected_candidate_physical_gaps D J e chi omega a homega ha haomega
    rows licensed howned hcheck N cap hN hcap p hp j hj ht hsmall
  constructor
  · exact P1OriginalFifthMovingHarmonicEnvelope.sourceBudget_of_log_cutoff_and_gap
      N hN p hg.1 _ (omega / 2) a T hsmall hg.2.2.2.1 hT haT hbudget hlog
  · exact P1OriginalFifthMovingHarmonicEnvelope.sourceBudget_of_log_cutoff_and_gap
      N hN p hg.1 _ (omega / 2) a T hsmall hg.2.2.2.2.1 hT haT hbudget hlog

/-- Genuine pointwise normalized arithmetic source estimate on the actual
corrected carrier. A,B,K are supplied by the proved same-cutoff lower-deficit
source, and the displayed primitive scalar budgets suffice for both legs. -/
theorem exists_correctedTupleDifference_exp_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
        (e : ℚ) (chi omega a T : ℝ), 0 < omega → 0 < a → a ≤ omega / 3 →
        2 ≤ T → a * T ≤ omega / 2 →
        ∀ (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
        P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega →
        storedH45Check D J e rows = true →
        ∀ N cap : ℕ, 1 < N → Even N →
        (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ) →
        Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ) →
        ∀ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
          (e : ℝ) chi D.m omega N cap,
        ∀ j ∈ D.cells5 ∩ J,
        actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j →
        actualPrimeTupleLog N p 4 ≤ a →
        |correctedTupleDifference D J e chi omega rows licensed N cap p| ≤
          (actualSmallEulerProduct N cap (p 4 : ℝ) *
            (tailEnvelope A B K (residualLevel N
                (originalVariableFourthProfile e chi omega D.m j rows licensed
                  (actualPrimeTupleLog N p)) p) T +
              tailEnvelope A B K (residualLevel N (D.cap5 j : ℝ) p) T)) *
            |Real.log (N : ℝ) / singularSeries N| := by
  obtain ⟨A, B, K, hA, hB, hK, hsource⟩ := exists_tuple_gated_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro D J e chi omega a T homega ha haomega hT haT rows licensed howned hcheck
    N cap hN hEven hcap hbudget hlog p hp j hj ht hsmall
  obtain ⟨hpos, hy, hcover, _hgapOld, _hgapNew, _hROld, _hRNew, hgateOld, hgateNew⟩ :=
    corrected_candidate_physical_gaps D J e chi omega a homega ha haomega rows licensed
      howned hcheck N cap hN hcap p hp j hj ht hsmall
  have hbudgets := corrected_selected_source_budgets D J e chi omega a T homega ha haomega
    hT haT rows licensed howned hcheck N cap hN hcap hbudget hlog p hp j hj ht hsmall
  let old := originalVariableFourthProfile e chi omega D.m j rows licensed (actualPrimeTupleLog N p)
  let new := (D.cap5 j : ℝ)
  have hpair := hsource N cap hEven old new p hpos hy hcover hgateOld hgateNew T T
    hbudgets.1 hbudgets.2
  have hdiff : correctedTupleDifference D J e chi omega rows licensed N cap p =
      (tupleGatedMinus N cap new p - tupleGatedMinus N cap old p) *
        (Real.log (N : ℝ) / singularSeries N) := by
    rw [correctedTupleDifference_on_selected_cell D J e chi omega rows licensed
      N cap hN p hpos j hj ht,
      tupleGatedMinus_of_gate N cap new p hgateNew,
      tupleGatedMinus_of_gate N cap old p hgateOld]
    simp only [actualPrimeTupleOwnCubeMinus, if_pos hgateNew, if_pos hgateOld]
    change actualSmallRosserMinusDensity N cap (p 4 : ℝ) (residualLevel N new p) *
        Real.log (N : ℝ) / singularSeries N -
      actualSmallRosserMinusDensity N cap (p 4 : ℝ) (residualLevel N old p) *
        Real.log (N : ℝ) / singularSeries N = _
    ring
  rw [hdiff, abs_mul]
  exact mul_le_mul_of_nonneg_right hpair (abs_nonneg _)

end
end ImbalancedChen.P1CorrectedFifthSmallLastGeometry
