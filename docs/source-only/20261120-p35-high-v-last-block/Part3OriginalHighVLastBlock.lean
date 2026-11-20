import ImbalancedChen.Part3OriginalHighVActualCutoff

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Sufficient and excluding scale conditions for the original ceiling
cutoff, and a consumer at its actual last retained frequency block. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHighVLastBlock20261120
open Finset
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalCommonPoissonLanes20261102 (blockIndices commonMBlock globalCutoff globalCutoff_covers)
open OriginalHighVActualCutoff20261120 (common_block_nonempty_iff no_highV_if_real_cutoff_small)
open OriginalOppositeBlockHighV20261120 (initialChartCost opposite_block_highV_initial_price)
open OriginalOppositeBlockSplit20261120 (blockCuspComplement blockContinuous)
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

/-- A sufficient original-scale condition. Its witness is the last
actual clipped block, not an arbitrary continuous dyadic scale. -/
theorem last_block_highV_of_large_cutoff (D : OriginalData) {x η : ℝ}
    (hx : 0 < x) (hlarge : 4*scaleS D.key ≤ x^η) :
    let J := globalCutoff D x η
    let j := Nat.log 2 J
    j ∈ blockIndices J ∧ (commonMBlock J j).Nonempty ∧
      fixedZ D true ≤ (((2:ℕ)^j : ℕ):ℝ) := by
  let S := scaleS D.key
  let J := globalCutoff D x η
  let j := Nat.log 2 J
  have hS : 0 < S := scaleS_pos D.key
  have hSone : 1 ≤ S := scaleS_one_le D.key
  have hSsq : 1 ≤ S^2 := by nlinarith only [hSone]
  have hratio : D.cScale/D.bScale = S := by
    dsimp only [S]
    unfold OriginalData.cScale
    field_simp [D.bScale_pos.ne'] <;> ring
  have hcover : S*x^η ≤ (J:ℝ) := by
    have h := globalCutoff_covers D x η
    simpa only [J,hratio] using h
  have hmult := mul_le_mul_of_nonneg_left hlarge hS.le
  have hfour : 4*S^2 ≤ (J:ℝ) := by nlinarith only [hmult,hcover]
  have hJ : 0 < J := by
    have hJR : (0:ℝ) < (J:ℝ) := by nlinarith only [hfour,hSsq]
    exact_mod_cast hJR
  have hnext : J < (2:ℕ)^(j+1) := by
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) J
  have hnextR : (J:ℝ) < (((2:ℕ)^(j+1):ℕ):ℝ) := by exact_mod_cast hnext
  have hnextEq : (((2:ℕ)^(j+1):ℕ):ℝ) = 2*((((2:ℕ)^j:ℕ):ℝ)) := by
    push_cast
    rw [pow_succ]
    ring
  have hupper : fixedZ D true ≤ (((2:ℕ)^j:ℕ):ℝ) := by
    simp only [fixedZ,if_true]
    nlinarith only [hfour,hnextR,hnextEq]
  refine ⟨?_,?_,hupper⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
  · exact (common_block_nonempty_iff J j).mpr (Nat.pow_log_le_self 2 hJ.ne')

/-- If the cutoff exponent is no larger than the actual S scale, the
high-V branch contains no retained frequency block. -/
theorem no_highV_of_small_cutoff (D : OriginalData) {x η : ℝ}
    (hx : 0 < x) (hsmall : x^η ≤ scaleS D.key) :
    ¬ ∃ j ∈ blockIndices (globalCutoff D x η),
      (commonMBlock (globalCutoff D x η) j).Nonempty ∧
        fixedZ D true ≤ (((2:ℕ)^j:ℕ):ℝ) := by
  let S := scaleS D.key
  have hS : 0 < S := scaleS_pos D.key
  have hSone : 1 ≤ S := scaleS_one_le D.key
  have hSsq : 1 ≤ S^2 := by nlinarith only [hSone]
  have hm := mul_le_mul_of_nonneg_left hsmall hS.le
  have hreal : S*x^η+1 ≤ 2*S^2 := by nlinarith only [hm,hSsq]
  exact no_highV_if_real_cutoff_small D hx hreal

/-- The actual last block inherits the original two-chart high-V
opposite estimate. No nonzero coefficient or spectral row is asserted. -/
theorem last_block_opposite_initial_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (k : BlockKey) (x η M N : ℝ) (ell : D4 → ℤ),
      0 < x → 4*scaleS D.key ≤ x^η → 0 < N → D.block.atom.residue ≠ 0 →
      let J := globalCutoff D x η
      let j := Nat.log 2 J
      j ∈ blockIndices J ∧ (commonMBlock J j).Nonempty ∧
      ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∃ B₁ : ℝ, 0 ≤ B₁ ∧
      ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool),
        traceNegative D k negativeM = true →
        ‖fullBlockMode D r k J j negativeM M N ell‖^2 ≤
          3 * (2 * ‖actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell‖^2 *
            (initialChartCost C ε D r k false j M B₀ +
              initialChartCost C ε D r k true j M B₁) +
            ‖blockCuspComplement D r k negativeM J j M N ell‖^2 +
            ‖blockContinuous D r k negativeM J j M N ell‖^2) := by
  obtain ⟨C,hC,hbound⟩ := opposite_block_highV_initial_price hε
  refine ⟨C,hC,?_⟩
  intro D k x η M N ell hx hlarge hN ha
  let J := globalCutoff D x η
  let j := Nat.log 2 J
  obtain ⟨hj,hne,hZ⟩ := last_block_highV_of_large_cutoff D hx hlarge
  obtain ⟨B₀,hB₀,B₁,hB₁,h⟩ := hbound D k J j M N ell hN ha hZ
  exact ⟨hj,hne,B₀,hB₀,B₁,hB₁,h⟩

end ImbalancedChen.Part3.OriginalHighVLastBlock20261120
end
