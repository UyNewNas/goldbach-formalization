import ImbalancedChen.P1CorrectedFifthSmallLastGeometry
import ImbalancedChen.P1FifthMiddleNormalizedPointwise

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The generic arbitrary-physical-residual normalized quadratic source is
bound to the ACTUAL corrected original-T3 tuple difference. The old level
is the original variable producer; the new level is the stored cap licensed
above it by the finite h45 checker. Both physical residual gaps are derived
from the unchanged original third gate before the generic source is used.

The tuple difference already includes logN/singularSeriesN. No second
normalization is introduced. The resulting C*t5^2 bound is uniform over all
fixed-cutoff middle shells a(N)<=t5<a<=omega/6 after one target threshold.
No target remainder bound, desired mean, or coarse-old5 dictionary is used.
-/

namespace ImbalancedChen.P1CorrectedFifthMiddlePointwise

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1CorrectedFifthCausalTupleDictionary
open P1CorrectedFifthStoredH45Check P1CorrectedFifthSmallLastGeometry
open P1OriginalSmallCutoffActualLowerTail
open P1OriginalFifthMovingScaleLimit P1FifthMiddleNormalizedPointwise

/-- Absolute source constant, chosen before every target, stored table,
producer family and moving middle shell. The only finite certificate input
is the actual stored h45 check, whose concrete passing instance stays OPEN. -/
theorem exists_eventually_correctedTupleDifference_middle_quadratic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ omega : ℝ, 0 < omega →
      ∀ᶠ N : ℕ in atTop,
      ∀ (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
        (e : ℚ) (chi a : ℝ)
        (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
      P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega →
      storedH45Check D J e rows = true →
      ∀ cap : ℕ, Even N → (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
      a ≤ omega / 6 →
      ∀ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
        (e : ℝ) chi D.m omega N cap,
      ∀ j ∈ D.cells5 ∩ J,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j →
      movingCutoff omega N ≤ actualPrimeTupleLog N p 4 → actualPrimeTupleLog N p 4 < a →
      |correctedTupleDifference D J e chi omega rows licensed N cap p| ≤
        (C / omega ^ 3) * (actualPrimeTupleLog N p 4) ^ 2 := by
  obtain ⟨C, hC, hgeneric⟩ := exists_eventually_actualMinus_middle_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro omega homega
  filter_upwards [hgeneric omega homega, eventually_gt_atTop (1 : ℕ)] with N hbound hN
  intro D J e chi a rows licensed howned hcheck cap hEven hcap haomega p hp j hj ht hmiddle hsmall
  have hd := (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_candidates_iff_log_on_cell
    (e : ℝ) chi D.m omega N cap hN hcap p j ht).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.1 i).1.pos
  have hy : (1 : ℝ) < p 4 := by exact_mod_cast (hd.1 4).1.one_lt
  have hx : 0 < actualPrimeTupleLog N p 4 :=
    div_pos (Real.log_pos hy) (Real.log_pos (by exact_mod_cast hN))
  have ha : 0 < a := hx.trans hsmall
  have haomega3 : a ≤ omega / 3 := by linarith
  obtain ⟨_, _, hcover, _hgapOld, _hgapNew, hROld, hRNew, hgateOld, hgateNew⟩ :=
    corrected_candidate_physical_gaps D J e chi omega a homega ha haomega3 rows licensed
      howned hcheck N cap hN hcap p hp j hj ht hsmall.le
  let old := originalVariableFourthProfile e chi omega D.m j rows licensed (actualPrimeTupleLog N p)
  let new := (D.cap5 j : ℝ)
  have hpoint := hbound cap hEven (p 4 : ℝ)
    (residualLevel N old p) (residualLevel N new p) a (by linarith) hcover haomega
    hmiddle hsmall hROld.le hRNew.le
  have hdiff : correctedTupleDifference D J e chi omega rows licensed N cap p =
      (actualSmallRosserMinusDensity N cap (p 4 : ℝ) (residualLevel N new p) -
        actualSmallRosserMinusDensity N cap (p 4 : ℝ) (residualLevel N old p)) *
          Real.log (N : ℝ) / singularSeries N := by
    rw [correctedTupleDifference_on_selected_cell D J e chi omega rows licensed
      N cap hN p hpos j hj ht]
    simp only [actualPrimeTupleOwnCubeMinus, if_pos hgateNew, if_pos hgateOld]
    change actualSmallRosserMinusDensity N cap (p 4 : ℝ) (residualLevel N new p) *
        Real.log (N : ℝ) / singularSeries N -
      actualSmallRosserMinusDensity N cap (p 4 : ℝ) (residualLevel N old p) *
        Real.log (N : ℝ) / singularSeries N = _
    ring
  rw [hdiff]
  exact hpoint

end
end ImbalancedChen.P1CorrectedFifthMiddlePointwise
