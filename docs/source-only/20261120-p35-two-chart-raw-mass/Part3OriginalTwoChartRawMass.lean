import ImbalancedChen.Part3OriginalExceptionalChartIndex
import ImbalancedChen.Part3OriginalOppositeBlockExceptionalBound
import ImbalancedChen.Part3OriginalOppositeBlockHighV

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Exact two-chart assembly of the original level-dependent raw n mass,
followed by one common explicit raw-sieve price. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwoChartRawMass20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open OriginalMaskedOuterEnergy20261102
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalExceptionalPostRemovalPair20261113 (levels rowMass rowLength)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels pascadiJ)
open OriginalExceptionalChartIndex20261120 (chartLevelEquiv)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open OriginalOppositeBlockExceptionalBound20261120
  (rawChartJ rawChartN rawChartCost opposite_block_with_exceptional_raw_bound)
open OriginalOppositeBlockSplit20261120 (blockCuspComplement blockContinuous)
open OriginalOppositeBlockTransport20261120 (raw_chart_n_nonneg)
open OriginalOppositeBlockHighV20261120 (fixedZ_lower_le_upper)
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)

/-- The same original row mass, indexed by its actual natural level. -/
def rowMassAt (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : ℕ) : ℝ :=
  ∑ n ∈ nCarrier D k z, ‖blockBeta D r k (decode k z n)‖^2

def actualOutputMass (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) : ℝ :=
  ∑ zy ∈ outputCarrier D k, ‖blockBeta D r k zy‖^2

/-- An occupied printed-level union and its literal physical chart
carry exactly the same row mass, including the lower boundary. -/
theorem chart_row_mass_eq (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) :
    (∑ z : ↥(levels D k upper), rowMass D r k z.val) =
      ∑ z ∈ chartLevels D k upper, rowMassAt D r k z := by
  classical
  calc
    _ = ∑ z : ↥(chartLevels D k upper), rowMassAt D r k z.val := by
      refine Fintype.sum_equiv (chartLevelEquiv D k upper) _ _ ?_
      intro z
      rfl
    _ = _ := by simp only [Finset.univ_eq_attach,Finset.sum_attach]

/-- The two physical charts reassemble the original arithmetic output
mass exactly. No boundary level or joint-output multiplicity is repeated. -/
theorem two_chart_row_mass_eq_actual (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) :
    (∑ z : ↥(levels D k false), rowMass D r k z.val) +
      (∑ z : ↥(levels D k true), rowMass D r k z.val) = actualOutputMass D r k := by
  classical
  rw [chart_row_mass_eq D r k false,chart_row_mass_eq D r k true]
  have hcharts : (∑ z ∈ chartLevels D k false, rowMassAt D r k z) +
      (∑ z ∈ chartLevels D k true, rowMassAt D r k z) =
        ∑ z ∈ levelCarrier D k, rowMassAt D r k z := by
    simpa only [chartLevels,Bool.false_eq_true,if_false,if_true,not_lt] using
      (Finset.sum_filter_add_sum_filter_not (levelCarrier D k)
        (fun z => (z:ℝ) < 2*(scaleS D.key)^2) (rowMassAt D r k))
  rw [hcharts]
  have houtput := sum_output_eq_rows D k
    (fun zy => ((‖blockBeta D r k zy‖^2 : ℝ) : ℂ))
  unfold actualOutputMass rowMassAt
  exact_mod_cast houtput.symm

/-- The sum of the two raw fixed-level sieve costs is paid by one
original output mass and the lower-chart cost, without a factor two
from counting the chart partition. The raw |a|*nu price is retained. -/
theorem two_chart_rawN_le_original_mass (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) :
    rawChartN D r k false + rawChartN D r k true ≤
      (2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/
        fixedZ D false)) * actualOutputMass D r k := by
  classical
  let G : ℝ := (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)
  let Z₀ := fixedZ D false
  let Z₁ := fixedZ D true
  let E₀ := ∑ z : ↥(levels D k false), rowMass D r k z.val
  let E₁ := ∑ z : ↥(levels D k true), rowMass D r k z.val
  let A₀ := 2*sieveConstant*(1+G/Z₀)
  let A₁ := 2*sieveConstant*(1+G/Z₁)
  have hz₀ : 0 < Z₀ := fixedZ_pos D false
  have hzz : Z₀ ≤ Z₁ := fixedZ_lower_le_upper D
  have hl : 0 ≤ rowLength k := div_nonneg (dyadicScale_pos _).le (Nat.cast_nonneg _)
  have hg : 0 ≤ G := mul_nonneg (Nat.cast_nonneg _) hl
  have he₁ : 0 ≤ E₁ := by
    apply Finset.sum_nonneg
    intro z _
    unfold rowMass
    exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hA : A₁ ≤ A₀ := by
    dsimp only [A₀,A₁]
    exact mul_le_mul_of_nonneg_left
      (add_le_add_left (div_le_div_of_nonneg_left hg hz₀ hzz) 1)
      (mul_nonneg (by norm_num) sieveConstant_pos.le)
  have hm : E₀+E₁ = actualOutputMass D r k := two_chart_row_mass_eq_actual D r k
  change A₀*E₀+A₁*E₁ ≤ A₀*actualOutputMass D r k
  calc
    _ ≤ A₀*E₀+A₀*E₁ := add_le_add_left (mul_le_mul_of_nonneg_right hA he₁) _
    _ = A₀*(E₀+E₁) := by ring
    _ = _ := by rw [hm]

/-- Two distinct nonnegative chart prices may be retained until after
the exact mass assembly; the maximum is taken only over the two prices. -/
theorem weighted_two_chart_rawN_le_original_mass (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (w₀ w₁ : ℝ)
    (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) :
    w₀*rawChartN D r k false + w₁*rawChartN D r k true ≤
      max w₀ w₁ * ((2*sieveConstant*(1+
        (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D false)) *
          actualOutputMass D r k) := by
  have hn₀ := raw_chart_n_nonneg D r k false
  have hn₁ := raw_chart_n_nonneg D r k true
  have hmax : 0 ≤ max w₀ w₁ := hw₀.trans (le_max_left _ _)
  calc
    _ ≤ max w₀ w₁ * rawChartN D r k false +
        max w₀ w₁ * rawChartN D r k true :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hn₀)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hn₁)
    _ = max w₀ w₁ * (rawChartN D r k false + rawChartN D r k true) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (two_chart_rawN_le_original_mass D r k) hmax

/-- Nonnegativity is proved on the full native m-side energy, not
assumed for the level-dependent n rows. -/
theorem raw_chart_J_nonneg (D : OriginalData) (k : BlockKey)
    (upper : Bool) (j : ℕ) (ω : ℝ) : 0 ≤ rawChartJ D k upper j ω := by
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  have hv : 0 < V := by dsimp [V]; positivity
  have hw : 0 ≤ W := (threshold_pos hv).le
  have hj (Q : ℝ) : 0 ≤ pascadiJ (classicalLevels Q) W j ω := by
    unfold pascadiJ
    apply Finset.sum_nonneg
    intro z _
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (Real.rpow_nonneg hw _) (sq_nonneg _)
  change 0 ≤ (2+Real.log (4*V+1))^2 *
    ((pascadiJ (classicalLevels (Z/2)) W j ω +
      pascadiJ (classicalLevels Z) W j ω)/4)
  exact mul_nonneg (sq_nonneg _) (div_nonneg (add_nonneg (hj (Z/2)) (hj Z)) (by norm_num))

def rawChartOuterWeight (D : OriginalData) (k : BlockKey) (upper : Bool)
    (j : ℕ) (M B ω : ℝ) : ℝ :=
  (M^2*fixedZ D upper) * (B^2*rawChartJ D k upper j ω)

theorem raw_chart_outer_weight_nonneg (D : OriginalData) (k : BlockKey)
    (upper : Bool) (j : ℕ) (M B ω : ℝ) : 0 ≤ rawChartOuterWeight D k upper j M B ω := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (fixedZ_pos D upper).le)
    (mul_nonneg (sq_nonneg _) (raw_chart_J_nonneg D k upper j ω))

/-- Direct input for the two-chart exceptional bound: both actual
J(W)-weighted raw costs use one original arithmetic output mass. -/
theorem two_chart_raw_cost_le_original_mass (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (j : ℕ)
    (M B₀ ω₀ B₁ ω₁ : ℝ) :
    rawChartCost D r k false j M B₀ ω₀ + rawChartCost D r k true j M B₁ ω₁ ≤
      max (rawChartOuterWeight D k false j M B₀ ω₀)
          (rawChartOuterWeight D k true j M B₁ ω₁) *
        ((2*sieveConstant*(1+
          (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D false)) *
            actualOutputMass D r k) := by
  have h := weighted_two_chart_rawN_le_original_mass D r k
    (rawChartOuterWeight D k false j M B₀ ω₀)
    (rawChartOuterWeight D k true j M B₁ ω₁)
    (raw_chart_outer_weight_nonneg D k false j M B₀ ω₀)
    (raw_chart_outer_weight_nonneg D k true j M B₁ ω₁)
  simpa only [rawChartCost,rawChartOuterWeight,mul_assoc] using h

/-- The original opposite block now has one exact arithmetic output
mass on the exceptional side; regular and continuous terms remain. -/
theorem opposite_block_with_original_raw_mass (D : OriginalData) (k : BlockKey)
    (J j : ℕ) (M : ℝ) {N : ℝ} (hN : 0 < N)
    (ell : D4 → ℤ) (ha : D.block.atom.residue ≠ 0) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∃ ω₀ : ℝ, ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∃ ω₁ : ℝ,
      ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
        traceNegative D k negativeM = true →
        ‖fullBlockMode D r k J j negativeM M N ell‖^2 ≤
          3 * (2 * ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
              (max (rawChartOuterWeight D k false j M B₀ ω₀)
                   (rawChartOuterWeight D k true j M B₁ ω₁) *
                ((2*sieveConstant*(1+
                  (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D false)) *
                    actualOutputMass D r k)) +
            ‖blockCuspComplement D r k negativeM J j M N ell‖^2 +
            ‖blockContinuous D r k negativeM J j M N ell‖^2) := by
  obtain ⟨B₀,hB₀,ω₀,B₁,hB₁,ω₁,hblock⟩ :=
    opposite_block_with_exceptional_raw_bound D k J j M hN ell ha
  refine ⟨B₀,hB₀,ω₀,B₁,hB₁,ω₁,?_⟩
  intro r negativeM hs
  have hm := two_chart_raw_cost_le_original_mass D r k j M B₀ ω₀ B₁ ω₁
  have he := mul_le_mul_of_nonneg_left hm
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg _))
  exact (hblock r negativeM hs).trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_right he _) _) (by norm_num))

end ImbalancedChen.Part3.OriginalTwoChartRawMass20261120
end
