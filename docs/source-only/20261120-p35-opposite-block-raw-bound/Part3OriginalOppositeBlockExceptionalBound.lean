import ImbalancedChen.Part3OriginalOppositeBlockSplit

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Connect the actual two-chart exceptional block to the existing common
phase, original raw-n Cauchy estimate, with each chart's actual weights. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalOppositeBlockExceptionalBound20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels pascadiJ)
open OriginalExceptionalPostRemovalPair20261113 (levels Slots rowMass rowLength)
open OriginalSignedExceptionalChart20261120 (signedRawSlot signed_chart_with_raw_sieve)
open OriginalSignedExceptionalMode20261120 (signedExceptionalMode)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant)
open OriginalOppositeBlockSplit20261120
  (blockExceptional blockCuspComplement blockContinuous opposite_block_sq_le_parts)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)

/-- The original full m-side spectral energy on the two endpoint-corrected
classical level intervals of one physical chart. -/
def rawChartJ (D : OriginalData) (k : BlockKey) (upper : Bool) (j : ℕ) (ω : ℝ) : ℝ :=
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  (2+Real.log (4*V+1))^2 *
    ((pascadiJ (classicalLevels (Z/2)) W j ω +
      pascadiJ (classicalLevels Z) W j ω)/4)

/-- The original, level-dependent n rows, paid with the available raw
fixed-level sieve. The large |a|*nu cost is explicitly retained. -/
def rawChartN (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) : ℝ :=
  (2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/
    fixedZ D upper)) * ∑ z : ↥(levels D k upper), rowMass D r k z.val

def rawChartCost (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (j : ℕ) (M B ω : ℝ) : ℝ :=
  (M^2*fixedZ D upper) * (B^2 * (rawChartJ D k upper j ω * rawChartN D r k upper))

/-- One phase for every level and native multiplicity of this chart,
chosen before the original mark r and before the Poisson sign. -/
theorem one_chart_mode_raw_bound (D : OriginalData) (k : BlockKey)
    (upper : Bool) (J j : ℕ) (M : ℝ) {N : ℝ} (hN : 0 < N)
    (ell : D4 → ℤ) (ha : D.block.atom.residue ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ ω : ℝ, ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
      ‖signedExceptionalMode D r k upper negativeM J j M N ell‖^2 ≤
        ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
          rawChartCost D r k upper j M B ω := by
  classical
  let Z := fixedZ D upper
  let Y := chartY0 D k upper j N
  have hZ : 0 < Z := fixedZ_pos D upper
  have hY : 0 < Y := original_spectral_scale_pos D k upper j hN ha
  obtain ⟨B,hB,hchart⟩ := signed_chart_with_raw_sieve ell hY
  obtain ⟨ω,hω⟩ := hchart D k upper J j ha
  refine ⟨B,hB,ω,?_⟩
  intro r negativeM
  let S : ℂ := ∑ a : Slots D k upper, signedRawSlot D r k upper negativeM J j ell Y a
  have hn : ‖S‖ ≤ ∑ a : Slots D k upper,
      ‖signedRawSlot D r k upper negativeM J j ell Y a‖ := norm_sum_le _ _
  have hspec : ‖S‖^2 ≤ B^2 *
      (rawChartJ D k upper j ω * rawChartN D r k upper) := by
    have hp := (pow_le_pow_left₀ (norm_nonneg S) hn 2).trans (hω r negativeM)
    simpa only [rawChartJ,rawChartN] using hp
  have hscale : ‖((M*Real.sqrt Z:ℝ):ℂ)‖^2 = M^2*Z := by
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt hZ.le]
  have hfactor : 0 ≤ ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
      (M^2*Z) := mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hZ.le)
  calc
    _ = (‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
        (M^2*Z)) * ‖S‖^2 := by
      dsimp only [signedExceptionalMode,S,Y,Z]
      rw [norm_mul,norm_mul,mul_pow,mul_pow,hscale]
      ring
    _ ≤ (‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
        (M^2*Z)) * (B^2 * (rawChartJ D k upper j ω * rawChartN D r k upper)) :=
      mul_le_mul_of_nonneg_left hspec hfactor
    _ = _ := by dsimp [rawChartCost,Z]; ring

/-- The two chart phases may differ; each is fixed before r and before
the sign, and each retains its own real level interval and original cost. -/
theorem two_chart_exceptional_raw_bound (D : OriginalData) (k : BlockKey)
    (J j : ℕ) (M : ℝ) {N : ℝ} (hN : 0 < N)
    (ell : D4 → ℤ) (ha : D.block.atom.residue ≠ 0) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∃ ω₀ : ℝ, ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∃ ω₁ : ℝ,
      ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
        ‖blockExceptional D r k negativeM J j M N ell‖^2 ≤
          2 * ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
            (rawChartCost D r k false j M B₀ ω₀ + rawChartCost D r k true j M B₁ ω₁) := by
  obtain ⟨B₀,hB₀,ω₀,h₀⟩ := one_chart_mode_raw_bound D k false J j M hN ell ha
  obtain ⟨B₁,hB₁,ω₁,h₁⟩ := one_chart_mode_raw_bound D k true J j M hN ell ha
  refine ⟨B₀,hB₀,ω₀,B₁,hB₁,ω₁,?_⟩
  intro r negativeM
  let E₀ := signedExceptionalMode D r k false negativeM J j M N ell
  let E₁ := signedExceptionalMode D r k true negativeM J j M N ell
  let A := ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2
  let P₀ := rawChartCost D r k false j M B₀ ω₀
  let P₁ := rawChartCost D r k true j M B₁ ω₁
  have ht : ‖E₀+E₁‖ ≤ ‖E₀‖+‖E₁‖ := norm_add_le _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg (E₀+E₁)) ht 2
  have htwo : (‖E₀‖+‖E₁‖)^2 ≤ 2*(‖E₀‖^2+‖E₁‖^2) := by
    nlinarith only [sq_nonneg (‖E₀‖-‖E₁‖)]
  have hparts : ‖E₀‖^2+‖E₁‖^2 ≤ A*P₀+A*P₁ :=
    add_le_add (h₀ r negativeM) (h₁ r negativeM)
  change ‖E₀+E₁‖^2 ≤ 2*A*(P₀+P₁)
  calc
    _ ≤ (‖E₀‖+‖E₁‖)^2 := hsq
    _ ≤ 2*(‖E₀‖^2+‖E₁‖^2) := htwo
    _ ≤ 2*(A*P₀+A*P₁) := mul_le_mul_of_nonneg_left hparts (by norm_num)
    _ = _ := by ring

/-- Partial original-block inequality: only the exceptional term has
been supplied; the actual complement and continuous terms remain. -/
theorem opposite_block_with_exceptional_raw_bound (D : OriginalData) (k : BlockKey)
    (J j : ℕ) (M : ℝ) {N : ℝ} (hN : 0 < N)
    (ell : D4 → ℤ) (ha : D.block.atom.residue ≠ 0) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∃ ω₀ : ℝ, ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∃ ω₁ : ℝ,
      ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
        traceNegative D k negativeM = true →
        ‖fullBlockMode D r k J j negativeM M N ell‖^2 ≤
          3 * (2 * ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
              (rawChartCost D r k false j M B₀ ω₀ + rawChartCost D r k true j M B₁ ω₁) +
            ‖blockCuspComplement D r k negativeM J j M N ell‖^2 +
            ‖blockContinuous D r k negativeM J j M N ell‖^2) := by
  obtain ⟨B₀,hB₀,ω₀,B₁,hB₁,ω₁,h⟩ :=
    two_chart_exceptional_raw_bound D k J j M hN ell ha
  refine ⟨B₀,hB₀,ω₀,B₁,hB₁,ω₁,?_⟩
  intro r negativeM hs
  have hb := opposite_block_sq_le_parts D r k negativeM J j M ell hN ha hs
  have he := h r negativeM
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_right he _) _) (by norm_num))

end ImbalancedChen.Part3.OriginalOppositeBlockExceptionalBound20261120
end
