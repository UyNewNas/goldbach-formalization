import ImbalancedChen.P1ActualVariableFifthSmallLastGeometry
import ImbalancedChen.P1ActualVariableFifthGlobalSourceDefinitions

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual finite-max VARIABLE5 arithmetic pointwise tail suppliers, with the
canonical actual variable tupleDifference. The fourth raw-Q3 floor and
fifth finite-max inheritance supply every geometric comparison. No stored
checker, coarse cap lookup, all15 surrogate, or desired tail is assumed.
-/

namespace ImbalancedChen.P1ActualVariableFifthTailPointwise
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseFifthContinuation
open P1OriginalVariableFourthContinuation
open P1CorrectedFifthCausalTupleDictionary
open P1OriginalFifthWeightedSourceReduction
open P1OriginalSmallCutoffActualLowerTail
open P1OriginalFifthMovingHarmonicEnvelope
open P1OriginalFifthMovingScaleLimit
open P1FifthMiddleNormalizedPointwise
open P1ActualVariableFifthSmallLastGeometry
open P1ActualVariableFifthGlobalSourceAssembly

theorem sourceBudget_of_power_cutoff
    (N : ℕ) (hN : 1 < N) (omega a T y R : ℝ)
    (hy : 0 ≤ y) (hcut : y ≤ (N : ℝ) ^ a)
    (hR : (N : ℝ) ^ (omega / 2) ≤ R)
    (hT : 2 ≤ T) (haT : a * T ≤ omega / 2)
    (hbudget : T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ))
    (hlog : Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ)) :
    sourceBudget y R T := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hpower : y ^ T ≤ (N : ℝ) ^ (omega / 2) := by
    calc
      _ ≤ ((N : ℝ) ^ a) ^ T := Real.rpow_le_rpow hy hcut (by linarith)
      _ = (N : ℝ) ^ (a * T) := (Real.rpow_mul hn0.le a T).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le haT
  have hlogR : (omega / 2) * Real.log (N : ℝ) ≤ Real.log (Nat.ceil R : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hn0 (omega / 2)) (hR.trans (Nat.le_ceil R))
    simpa only [Real.log_rpow hn0] using hh
  exact ⟨hT, hpower.trans hR, hbudget.trans hlogR, hlog.trans hlogR⟩

theorem variable5_selected_sourceBudgets
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a T : ℝ)
    (homega : 0 < omega) (ha : a ≤ omega / 3) (hT : 2 ≤ T) (haT : a * T ≤ omega / 2)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (hbudget : T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ))
    (hlog : Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ))
    (p : Fin 5 → ℕ) (hp : p ∈ sourceCarrier e chi m omega N cap)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hsmall : actualPrimeTupleLog N p 4 ≤ a) :
    sourceBudget (p 4 : ℝ) (variableOldLevel e chi m omega rows4 licensed4 N p / (∏ i, p i : ℕ)) T ∧
    sourceBudget (p 4 : ℝ) (variableNewLevel e chi m omega rows4 licensed4 J5 rows5 N p / (∏ i, p i : ℕ)) T := by
  obtain ⟨hpos, _hy, _hcover, hold, hnew, _hgo, _hgn⟩ := actual_variable5_physical_gaps
    e chi m omega a homega ha rows4 licensed4 J5 rows5 N cap hN hcap p hp j hj ht hsmall
  have hcut : (p 4 : ℝ) ≤ (N : ℝ) ^ a :=
    (HistoricalThirdCoarse.P1OriginalSmallCoordinate.last_log_le_iff_prime_le_rpow hN p hpos a).mp hsmall
  exact ⟨sourceBudget_of_power_cutoff N hN omega a T _ _ (Nat.cast_nonneg _) hcut hold.le hT haT hbudget hlog,
    sourceBudget_of_power_cutoff N hN omega a T _ _ (Nat.cast_nonneg _) hcut hnew.le hT haT hbudget hlog⟩

/-- Absolute constants precede every actual variable row family and cutoff.
This controls the FULL lower-deficit source, not merely its explicit error. -/
theorem exists_variable5_tupleDifference_exp_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a T : ℝ),
      0 < omega → a ≤ omega / 3 → 2 ≤ T → a * T ≤ omega / 2 →
      ∀ (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
        (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)),
      ∀ N cap : ℕ, 1 < N → Even N → (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
      T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ) → Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ) →
      ∀ p ∈ sourceCarrier e chi m omega N cap,
      ∀ j ∈ selectedFifthCells e chi m omega J5,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j → actualPrimeTupleLog N p 4 ≤ a →
      |tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p| ≤
        (C * Real.exp (-T)) * |Real.log (N : ℝ) / singularSeries N| := by
  obtain ⟨A, B, K, hA, hB, _hK, hsource⟩ := exists_actualMinus_pair_exp_bound
  let C : ℝ := 2 * (A + B * Real.exp (Real.sqrt K))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro e chi m omega a T homega ha hT haT rows4 licensed4 J5 rows5
    N cap hN hEven hcap hbudget hlog p hp j hj ht hsmall
  obtain ⟨_hpos, hy, hcover, _hold, _hnew, hgo, hgn⟩ := actual_variable5_physical_gaps
    e chi m omega a homega ha rows4 licensed4 J5 rows5 N cap hN hcap p hp j hj ht hsmall
  obtain ⟨ho, hn⟩ := variable5_selected_sourceBudgets e chi m omega a T homega ha hT haT
    rows4 licensed4 J5 rows5 N cap hN hcap hbudget hlog p hp j hj ht hsmall
  let Ro := variableOldLevel e chi m omega rows4 licensed4 N p / (∏ i, p i : ℕ)
  let Rn := variableNewLevel e chi m omega rows4 licensed4 J5 rows5 N p / (∏ i, p i : ℕ)
  have hyPower : (p 4 : ℝ) ≤ (p 4 : ℝ) ^ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy.le (by linarith : 1 ≤ T)
  have hb := hsource N cap hEven (p 4 : ℝ) Ro Rn T T hcover hy
    (hyPower.trans ho.2.1) (hyPower.trans hn.2.1)
    ho.1 hn.1 ho.2.1 hn.2.1 ho.2.2.1 hn.2.2.1 ho.2.2.2 hn.2.2.2
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1))
  have hto := tailEnvelope_le_uniform_exp A B K Ro T T hA.le hB.le le_rfl (he.trans ho.2.2.2)
  have htn := tailEnvelope_le_uniform_exp A B K Rn T T hA.le hB.le le_rfl (he.trans hn.2.2.2)
  have hraw : |actualSmallRosserMinusDensity N cap (p 4 : ℝ) Rn -
      actualSmallRosserMinusDensity N cap (p 4 : ℝ) Ro| ≤ C * Real.exp (-T) := by
    calc
      _ ≤ actualSmallEulerProduct N cap (p 4 : ℝ) *
          (tailEnvelope A B K Ro T + tailEnvelope A B K Rn T) := hb
      _ ≤ actualSmallEulerProduct N cap (p 4 : ℝ) * (C * Real.exp (-T)) := by
        apply mul_le_mul_of_nonneg_left _ (actualSmallEulerProduct_pos N cap _ hEven).le
        dsimp [C]
        linarith [hto, htn]
      _ ≤ 1 * (C * Real.exp (-T)) := mul_le_mul_of_nonneg_right
        (actualSmallEulerProduct_le_one N cap _) (by dsimp [C]; positivity)
      _ = _ := one_mul _
  rw [tupleDifference, literalTupleDifference_of_gates _ _ N cap p hgo hgn, mul_div_assoc, abs_mul]
  exact mul_le_mul_of_nonneg_right hraw (abs_nonneg _)

/-- Actual normalized VARIABLE5 middle-shell summands have a genuine
quadratic bound. The constant precedes all rows, policies and targets. -/
theorem exists_eventually_variable5_tupleDifference_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ omega : ℝ, 0 < omega →
      ∀ᶠ N : ℕ in atTop, ∀ (e : ℚ) (chi : ℝ) (m cap : ℕ), Even N →
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
      ∀ (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
        (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)),
      ∀ a : ℝ, a ≤ omega / 6 → ∀ p ∈ sourceCarrier e chi m omega N cap,
      ∀ j ∈ selectedFifthCells e chi m omega J5,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      movingCutoff omega N ≤ actualPrimeTupleLog N p 4 → actualPrimeTupleLog N p 4 < a →
      |tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p| ≤
        (C / omega ^ 3) * (actualPrimeTupleLog N p 4) ^ 2 := by
  obtain ⟨C, hC, hsource⟩ := exists_eventually_actualMinus_middle_quadratic_bound
  refine ⟨C, hC, ?_⟩
  intro omega homega
  filter_upwards [hsource omega homega, eventually_ge_atTop (2 : ℕ)] with N hs hN
  intro e chi m cap hEven hcap rows4 licensed4 J5 rows5 a ha p hp j hj ht hmiddle hsmall
  have hN' : 1 < N := by omega
  obtain ⟨hpos, _hy, hcover, hold, hnew, hgo, hgn⟩ := actual_variable5_physical_gaps
    e chi m omega a homega (by linarith) rows4 licensed4 J5 rows5 N cap hN' hcap p hp j hj ht hsmall.le
  have hb := hs cap hEven (p 4 : ℝ)
    (variableOldLevel e chi m omega rows4 licensed4 N p / (∏ i, p i : ℕ))
    (variableNewLevel e chi m omega rows4 licensed4 J5 rows5 N p / (∏ i, p i : ℕ)) a
    (by exact_mod_cast hpos 4) hcover ha hmiddle hsmall hold.le hnew.le
  rw [tupleDifference, literalTupleDifference_of_gates _ _ N cap p hgo hgn]
  simpa only [logCoordinate, actualPrimeTupleLog] using hb

end
end ImbalancedChen.P1ActualVariableFifthTailPointwise
