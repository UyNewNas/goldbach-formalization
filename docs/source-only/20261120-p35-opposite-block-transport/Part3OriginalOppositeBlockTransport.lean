import ImbalancedChen.Part3OriginalOppositeBlockExceptionalBound
import ImbalancedChen.Part3OriginalAllChartLossyPair

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Explicitly price both original opposite-block exceptional J energies
using the existing initial-region estimate and 3/4 transport. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalOppositeBlockTransport20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalExceptionalPostRemovalPair20261113 (levels rowMass rowLength)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open OriginalAllChartLossyPair20261119 (transportedPrice full_J_with_transport)
open OriginalOppositeBlockSplit20261120 (blockCuspComplement blockContinuous)
open OriginalOppositeBlockExceptionalBound20261120
  (rawChartJ rawChartN rawChartCost opposite_block_with_exceptional_raw_bound)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)

/-- The two explicit, distinct 3/4-transport prices of one physical chart. -/
def transportedChartJ (C ε : ℝ) (D : OriginalData) (k : BlockKey)
    (upper : Bool) (j : ℕ) : ℝ :=
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  (2+Real.log (4*V+1))^2 *
    ((transportedPrice C ε (Z/2) (classicalMScale j) W +
      transportedPrice C ε Z (classicalMScale j) W)/4)

def transportedChartCost (C ε : ℝ) (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (j : ℕ) (M B : ℝ) : ℝ :=
  (M^2*fixedZ D upper) * (B^2 * (transportedChartJ C ε D k upper j *
    rawChartN D r k upper))

/-- The raw n cost is nonnegative with its actual level-dependent rows. -/
theorem raw_chart_n_nonneg (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) : 0 ≤ rawChartN D r k upper := by
  have hz : 0 < fixedZ D upper := fixedZ_pos D upper
  have hl : 0 ≤ rowLength k := div_nonneg (dyadicScale_pos _).le (Nat.cast_nonneg _)
  have hm : 0 ≤ ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    apply Finset.sum_nonneg
    intro z _
    unfold rowMass
    exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
  unfold rawChartN
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) sieveConstant_pos.le)
    (add_nonneg zero_le_one (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hl) hz.le))) hm

/-- One constant, chosen before all physical parameters, replaces both
literal J values by the existing explicit 3/4 transport price. -/
theorem all_raw_chart_costs_with_transport {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
        (upper : Bool) (j : ℕ) (M B ω : ℝ),
        rawChartCost D r k upper j M B ω ≤ transportedChartCost C ε D r k upper j M B := by
  obtain ⟨C,hC,hJ⟩ := full_J_with_transport hε
  refine ⟨C,hC,?_⟩
  intro D r k upper j M B ω
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  have hz : 0 < Z := fixedZ_pos D upper
  have hv : 0 < V := by dsimp [V]; positivity
  have hw : 0 < W := threshold_pos hv
  have h1 := hJ j (Z/2) W ω (by linarith only [hz]) hw
  have h2 := hJ j Z W ω hz hw
  have hj : rawChartJ D k upper j ω ≤ transportedChartJ C ε D k upper j := by
    dsimp only [rawChartJ,transportedChartJ]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (add_le_add h1 h2) (by norm_num : (0:ℝ) ≤ 4))
      (sq_nonneg (2+Real.log (4*V+1)))
  have hm : 0 ≤ M^2 * fixedZ D upper := mul_nonneg (sq_nonneg _) hz.le
  have hn := raw_chart_n_nonneg D r k upper
  unfold rawChartCost transportedChartCost
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hj hn) (sq_nonneg B)) hm

/-- For the actual opposite block, both exceptional energies are now
priced. Regular cuspidal and continuous parts remain explicit. -/
theorem opposite_block_with_transported_exceptional {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (k : BlockKey) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ),
      0 < N → D.block.atom.residue ≠ 0 →
      ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∃ B₁ : ℝ, 0 ≤ B₁ ∧
      ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
        traceNegative D k negativeM = true →
        ‖fullBlockMode D r k J j negativeM M N ell‖^2 ≤
          3 * (2 * ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
            (transportedChartCost C ε D r k false j M B₀ +
              transportedChartCost C ε D r k true j M B₁) +
            ‖blockCuspComplement D r k negativeM J j M N ell‖^2 +
            ‖blockContinuous D r k negativeM J j M N ell‖^2) := by
  obtain ⟨C,hC,hcost⟩ := all_raw_chart_costs_with_transport hε
  refine ⟨C,hC,?_⟩
  intro D k J j M N ell hN ha
  obtain ⟨B₀,hB₀,ω₀,B₁,hB₁,ω₁,hblock⟩ :=
    opposite_block_with_exceptional_raw_bound D k J j M hN ell ha
  refine ⟨B₀,hB₀,B₁,hB₁,?_⟩
  intro r negativeM hs
  have hprices := add_le_add (hcost D r k false j M B₀ ω₀)
    (hcost D r k true j M B₁ ω₁)
  have hE := mul_le_mul_of_nonneg_left hprices
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg _))
  exact (hblock r negativeM hs).trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_right hE _) _) (by norm_num))

end ImbalancedChen.Part3.OriginalOppositeBlockTransport20261120
end
