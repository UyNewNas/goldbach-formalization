import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import ImbalancedChen.P1FifthMiddleNormalizedPointwise

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL finite-max variable fifth level inherits the ACTUAL variable
fourth producer, which inherits the original raw Q3. Consequently original
small-last candidates have a common physical residual gap and BOTH strict
own-cube gates. No stored-cap checker, old5 constant lookup, all15 profile,
or desired density/tail assumption occurs here.
-/

namespace ImbalancedChen.P1ActualVariableFifthSmallLastGeometry
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthCausalTupleDictionary
open P1OriginalFifthWeightedSourceReduction
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalCoarseFifthContinuation
open P1OriginalVariableFourthContinuation
open P1OriginalSmallCutoffActualLowerTail
open P1OriginalFifthMovingHarmonicEnvelope
open P1FifthMiddleNormalizedPointwise

def variableOldLevel (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (N : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4
    (rosserAncestor 4 (tupleHistory p))

def variableNewLevel (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (N : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  P1OriginalVariableFifthContinuation.level5 e chi m omega (N : ℝ)
    rows4 licensed4 J5 rows5 (tupleHistory p)

/-- This is structural finite-max inheritance, including losing rows. -/
theorem variableOldLevel_le_newLevel
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (N : ℕ) (hN : 1 ≤ N) (p : Fin 5 → ℕ) :
    variableOldLevel e chi m omega rows4 licensed4 N p ≤
      variableNewLevel e chi m omega rows4 licensed4 J5 rows5 N p :=
  P1OriginalVariableFifthContinuation.fourthLevel_le_fifthLevel
    e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 (by exact_mod_cast hN) (tupleHistory p)

/-- The actual old variable-fourth level retains the original raw-Q3
level on the same actual third ancestor of this fifth tuple. -/
theorem rawQ3_le_variableOldLevel
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i)
    (j : Label5 m)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (N : ℝ) ^ currentExponent (e : ℝ) chi m omega j (actualPrimeTupleLog N p) ≤
      variableOldLevel e chi m omega rows4 licensed4 N p := by
  have hancestor : rosserAncestor 3 (tupleHistory p) = thirdHistory p := by
    simp [tupleHistory, List.ofFn_succ, rosserAncestor, thirdHistory]
  have hh := producer_frozenThird_le_level4 (e : ℝ) chi m omega (N : ℝ)
    (by exact_mod_cast hN.le) rows4 licensed4 (rosserAncestor 4 (tupleHistory p))
  have hfrozen : HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega (N : ℝ)
      (rosserAncestor 4 (tupleHistory p)) =
      HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ) (thirdHistory p) := by
    unfold HistoricalThirdCoarse.frozenLevel
    rw [rosserAncestor_nested 3 4 (by omega), hancestor]
  rw [hfrozen, rawLevel_on_fifth_cell (e : ℝ) chi m omega N hN p hpos j ht] at hh
  exact hh

/-- Genuine physical gap and two strict gates on actual original T3
candidates. Neither fourth nor fifth own cube filters the enumeration. -/
theorem actual_variable5_physical_gaps
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (homega : 0 < omega) (ha : a ≤ omega / 3)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (hp : p ∈ sourceCarrier e chi m omega N cap)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hsmall : actualPrimeTupleLog N p 4 ≤ a) :
    (∀ i, 0 < p i) ∧ 1 < (p 4 : ℝ) ∧ (p 4 : ℝ) ≤ (cap : ℝ) ∧
      (N : ℝ) ^ (omega / 2) < variableOldLevel e chi m omega rows4 licensed4 N p / (∏ i, p i : ℕ) ∧
      (N : ℝ) ^ (omega / 2) < variableNewLevel e chi m omega rows4 licensed4 J5 rows5 N p / (∏ i, p i : ℕ) ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < variableOldLevel e chi m omega rows4 licensed4 N p ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < variableNewLevel e chi m omega rows4 licensed4 J5 rows5 N p := by
  have hc : p ∈ candidates (e : ℝ) chi m omega N cap := by
    simpa only [sourceCarrier, candidates] using hp
  have hd := (mem_candidates_iff_log_on_cell (e : ℝ) chi m omega N cap hN hcap p j ht).mp hc
  have hpos : ∀ i, 0 < p i := fun i => (hd.1 i).1.pos
  have hg := (mem_jointRegion (e : ℝ) chi m omega j _).mp hd.2
  have hactive := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_cell_rough
    e chi m omega J5 j hj ht
  have hgo := (HistoricalThirdCoarse.P1OriginalSmallCoordinate.fifth_numerator_gap
    omega (currentExponent (e : ℝ) chi m omega j (actualPrimeTupleLog N p))
    (currentExponent (e : ℝ) chi m omega j (actualPrimeTupleLog N p))
    (actualPrimeTupleLog N p) hactive hg.2.2.2.2
    (hg.2.1 (by decide : (2 : Fin 5) < 3)) le_rfl).2
  have hgap : omega / 2 < currentExponent (e : ℝ) chi m omega j (actualPrimeTupleLog N p) -
      ∑ i, actualPrimeTupleLog N p i := by linarith
  have hQ34 := rawQ3_le_variableOldLevel e chi m omega rows4 licensed4 N hN p hpos j ht
  have hQ45 := variableOldLevel_le_newLevel e chi m omega rows4 licensed4 J5 rows5 N hN.le p
  have hquot := HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
    hN p hpos _ (omega / 2) hgap
  have hRold := hquot.trans_le (div_le_div_of_nonneg_right hQ34 (Nat.cast_nonneg _))
  have hRnew := hRold.trans_le (div_le_div_of_nonneg_right hQ45 (Nat.cast_nonneg _))
  have hgate : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 <
      (N : ℝ) ^ currentExponent (e : ℝ) chi m omega j (actualPrimeTupleLog N p) := by
    apply (actualPrimeTupleOwnCube_iff hN p hpos _).mpr
    unfold primeTupleOwnCubeForm
    change (∑ i, actualPrimeTupleLog N p i) + 2 * actualPrimeTupleLog N p 4 < _
    linarith
  exact ⟨hpos, by exact_mod_cast (hd.1 4).1.one_lt,
    (hd.1 4).2.2.2.le.trans hcap, hRold, hRnew, hgate.trans_le hQ34,
      (hgate.trans_le hQ34).trans_le hQ45⟩

/-- Removing the two actual gates is legal only after both primitive
physical cube inequalities have been established. -/
theorem literalTupleDifference_of_gates (Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (hold : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < Q4 (rosserAncestor 4 (tupleHistory p)))
    (hnew : (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 < Q5 (tupleHistory p)) :
    literalTupleDifference Q4 Q5 N cap p =
      (actualSmallRosserMinusDensity N cap (p 4 : ℝ) (Q5 (tupleHistory p) / (∏ i, p i : ℕ)) -
        actualSmallRosserMinusDensity N cap (p 4 : ℝ)
          (Q4 (rosserAncestor 4 (tupleHistory p)) / (∏ i, p i : ℕ))) *
        Real.log (N : ℝ) / singularSeries N := by
  have hprod : (tupleHistory p).prod = ∏ i, p i := by simp [tupleHistory, List.prod_ofFn]
  have hhead : (tupleHistory p).headD 0 = p 4 := by simp [tupleHistory, List.ofFn_succ]
  simp only [literalTupleDifference, actualOwnCubeGatedMinusDensity, hprod, hhead,
    if_pos hold, if_pos hnew]

end
end ImbalancedChen.P1ActualVariableFifthSmallLastGeometry
