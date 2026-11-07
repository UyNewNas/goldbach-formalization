import ImbalancedChen.P1LiteralVariableFifthCompactSupplier
import ImbalancedChen.P1OriginalCoarseFifthCellLimit

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The literal max15+W / buffered fifth M_I profile has a true positive-cell
prime TEST limit on the ORIGINAL firstStop/raw-Q3 jointRegion. The existing
original source-region transport proves its mixed affine wall payments;
no desired mean, density limit, or boundary-null assumption is an input.

The finite prime test retains target-divisor deletion. It is not yet the
actual old/new arithmetic Rosser residual sum: that still requires the
variable-parameter approximation and original producer identification.
In particular the actual producer OLD4 bridge supplied separately does not
identify a generic producer row family with this literal all15 raw profile.

The continuous test below EXCLUDES the reciprocal product, which the prime
integration theorem inserts exactly once. Its limit integrand is precisely
P1LiteralVariableFifthCompactSupplier.kernel, not kernel times another copy.
-/

namespace ImbalancedChen.P1LiteralVariableFifthPositiveCellTestLimit

noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical BigOperators
open P1LiteralVariableFifthCompactSupplier

/-- Both moving levels lie in one explicit interval on the positive cube.
This is suitable for the independent compact uniform arithmetic residual
supplier; no arithmetic mean or assumed profile bound is needed. -/
theorem profiles_mem_fixed_interval (e a b : ℝ) (ha : 0 ≤ a)
    (rows : Finset (Finset (Fin 5))) (t : Point)
    (ht : t ∈ positiveCube a b) :
    P1LiteralVariableFifthCompactSupplier.old5 e t ∈
        Icc (VariableEnvelope.cap - (3 / 8 : ℝ) * b - 2 * e)
          (VariableEnvelope.cap - 2 * e) ∧
      next5 e rows t ∈
        Icc (VariableEnvelope.cap - (3 / 8 : ℝ) * b - 2 * e)
          (VariableEnvelope.cap - 2 * e) := by
  have ht2 := ht (2 : Fin 5) (mem_univ _)
  have hnonneg : 0 ≤ t 2 := ha.trans ht2.1
  have hlo : VariableEnvelope.B (t 2) ≤ rawFourth t :=
    P1OriginalVariableFourthContinuation.finiteMax_seed_le _ _ _ _
  have hraw : rawFourth t ≤ VariableEnvelope.cap := by
    apply P1OriginalVariableFourthContinuation.finiteMax_le
    · dsimp [VariableEnvelope.B]
      linarith
    · intro I _ _
      exact VariableEnvelope.v_le_cap _
  have hold : P1LiteralVariableFifthCompactSupplier.old5 e t ≤
      VariableEnvelope.cap - 2 * e := sub_le_sub_right hraw _
  have hlow : VariableEnvelope.cap - (3 / 8 : ℝ) * b - 2 * e ≤
      P1LiteralVariableFifthCompactSupplier.old5 e t := by
    dsimp [VariableEnvelope.B] at hlo
    unfold P1LiteralVariableFifthCompactSupplier.old5
    linarith [ht2.2]
  have hnew : next5 e rows t ≤ VariableEnvelope.cap - 2 * e := by
    apply P1OriginalVariableFourthContinuation.finiteMax_le
    · exact hold
    · intro I _ _
      rw [M_eq_v]
      exact sub_le_sub_right (VariableEnvelope.v_le_cap _) _
  exact ⟨⟨hlow, hold⟩, ⟨hlow.trans (old5_le_next5 e rows t), hnew⟩⟩

def test (e : ℝ) (rows : Finset (Finset (Fin 5))) (t : Point) : ℝ :=
  primeOwnCubeGatedProfile (next5 e rows t) t -
    primeOwnCubeGatedProfile (P1LiteralVariableFifthCompactSupplier.old5 e t) t

theorem test_mul_reciprocal_eq_kernel (e : ℝ)
    (rows : Finset (Finset (Fin 5))) (t : Point) :
    test e rows t * (∏ i, 1 / t i) = kernel e rows t := rfl

theorem continuousOn_test (e a b : ℝ) (ha : 0 < a)
    (rows : Finset (Finset (Fin 5))) :
    ContinuousOn (test e rows) (univ.pi (fun _ : Fin 5 => Icc a b)) := by
  exact (continuousOn_movingOwnCubeProfile a b ha _ (continuous_next5 e rows)).sub
    (continuousOn_movingOwnCubeProfile a b ha _ (continuous_old5 e))

/-- This is a proved prime-test limit on the original selected fifth
owner, including its actual firstStop false branch and all seven strict
parent affine rows. The fifth own-cube gates remain inside the test. -/
theorem tendsto_literalFifth_positiveCell_test
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (j : P1OriginalCoarseFifthContinuation.Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (rows : Finset (Finset (Fin 5))) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
        (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
        ((P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
          (test (e : ℝ) rows))) atTop
      (𝓝 (∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
        kernel (e : ℝ) rows t)) := by
  have h := P1OriginalFifthLimit.tendsto_test_original_sourceRegion
    e chi m omega a ha haRho J5 j hj (test (e : ℝ) rows)
    (continuousOn_test (e : ℝ) a (19 / 96) ha rows)
  simpa only [test_mul_reciprocal_eq_kernel] using h

/-- The entire fixed selected owner table has the true sum of its genuine
integrals as its prime-test limit. Different owners retain their own row
sets; no desired total saving or common midpoint appears as an input. -/
theorem tendsto_literalFifth_selected_positive_tests
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (ha : 0 < a) (haRho : a < (19 / 96 : ℝ))
    (J5 : Finset (P1OriginalCoarseFifthContinuation.Label5 m))
    (rows : P1OriginalCoarseFifthContinuation.Label5 m → Finset (Finset (Fin 5))) :
    Tendsto (fun N : ℕ =>
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
          ((P1OriginalFifthLimit.sourceRegion e chi m omega j).indicator
            (test (e : ℝ) (rows j)))) atTop
      (𝓝 (∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        ∫ t in P1OriginalFifthIntegral.truncatedCell e chi m omega a j,
          kernel (e : ℝ) (rows j) t)) := by
  exact tendsto_finsetSum _ (fun j hj =>
    tendsto_literalFifth_positiveCell_test e chi m omega a ha haRho J5 j hj (rows j))

end
end ImbalancedChen.P1LiteralVariableFifthPositiveCellTestLimit
