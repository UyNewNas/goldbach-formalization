import ImbalancedChen.Part3OriginalRawChartSieve
import ImbalancedChen.Part3OriginalAllChartLossyPair

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Price the two actual m-side J sums in the raw positive exceptional chart
with the existing initial-region estimate and explicit 3/4 transport.
The raw n-row and actual test-profile costs remain visible. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRawChartTransport20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102
open OriginalExceptionalPostRemovalPair20261113 (levels Slots rowMass rowLength)
open OriginalPositiveRawCauchy20261120 (rawSlot)
open OriginalPositiveProfileBudget20261120 (profileBudget)
open OriginalExceptionalCosinePair20261120 (cosineCost)
open OriginalRawChartSieve20261120 (positive_chart_with_raw_sieve)
open OriginalAllChartLossyPair20261119 (transportedPrice full_J_with_transport)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)

/-- Quantitative but lossy bound on one original positive exceptional
chart. The two transport prices are separately evaluated at Z/2 and Z;
the same phase is used before applying their uniform estimates. -/
theorem positive_raw_chart_with_transport {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (k : BlockKey) (upper : Bool) (J j : ℕ) (ell : D4 → ℤ),
    D.block.atom.residue ≠ 0 →
    ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool) {Y : ℝ} (hY : 0 < Y),
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
    let M := classicalMScale j
    let W := threshold V Z
    (∑ a : Slots D k upper, ‖rawSlot D r k upper negativeM J j ell Y a‖)^2 ≤
      (cosineCost*profileBudget ell hY)^2 *
        (((2+Real.log (4*V+1))^2 *
          ((transportedPrice C ε (Z/2) M W + transportedPrice C ε Z M W)/4)) *
          ((2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/Z)) *
            ∑ z : ↥(levels D k upper), rowMass D r k z.val)) := by
  obtain ⟨C, cp, hJ⟩ := full_J_with_transport hε
  refine ⟨C, cp, ?_⟩
  intro D k upper J j ell ha r negativeM Y hY
  dsimp only
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  have hz : 0 < Z := fixedZ_pos D upper
  have hv : 0 < V := by dsimp [V]; positivity
  have hw : 0 < W := threshold_pos hv
  obtain ⟨ω, hchart⟩ := positive_chart_with_raw_sieve D k upper J j ell ha
  have h1 := hJ j (Z/2) W ω (by linarith only [hz]) hw
  have h2 := hJ j Z W ω hz hw
  have hmass : 0 ≤ ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    apply Finset.sum_nonneg
    intro z _
    unfold rowMass
    exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hL : 0 ≤ rowLength k := div_nonneg (dyadicScale_pos _).le (Nat.cast_nonneg _)
  have hG : 0 ≤ (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k) :=
    mul_nonneg (Nat.cast_nonneg _) hL
  have hcost : 0 ≤ (2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/Z))*
      ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) sieveConstant_pos.le)
      (add_nonneg zero_le_one (div_nonneg hG hz.le))) hmass
  have hbound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (add_le_add h1 h2) (by norm_num : (0:ℝ) ≤ 4))
        (sq_nonneg (2+Real.log (4*V+1)))) hcost)
    (sq_nonneg (cosineCost*profileBudget ell hY))
  exact (hchart r negativeM hY).trans hbound

end ImbalancedChen.Part3.OriginalRawChartTransport20261120
end
