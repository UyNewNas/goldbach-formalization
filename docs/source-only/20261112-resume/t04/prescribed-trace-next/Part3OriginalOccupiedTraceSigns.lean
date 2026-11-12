import ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov

/-! The arithmetic singleton has two genuine Poisson signs. Every
nonzero original primary coefficient supplies a row on each sign. -/
namespace ImbalancedChen.Part3.OriginalOccupiedTraceSigns20261112

noncomputable section
open Set Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (norm_e)
open ActualCompletedSquarePushforwardSourceOnly FixedRhoPrimarySignedFiniteSourceOnly
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalPoissonPrimaryRows20261102
open OriginalTwoZSourceAssembly20261102 OriginalTwoZFourierAssembly20261102
open OriginalSignedTraceInput20261102 OriginalOppositeMarkedKuznetsov20261112
open ImbalancedChen.P3ZActualPrimaryShortEndpoint (signedY)

def positiveLane (D : OriginalData) (k : BlockKey) : Bool := traceNegative D k false

theorem opposite_lanes (D : OriginalData) (k : BlockKey) :
    traceNegative D k (positiveLane D k)=false ∧ traceNegative D k (!(positiveLane D k))=true := by
  unfold positiveLane traceNegative
  cases k.2.2 <;> by_cases h : D.block.atom.residue<0 <;> simp [h]

/-- This is precisely the pair of summands in the actual nonzero
part of completedPiece 1, with their original signed kernels. -/
theorem original_nonzero_two_signs (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) :
    nonzeroBlocks D r J M N =
      ∑ k∈originalKeys D,∑ j∈blockIndices J,
        (rowPairing D r k (blockKernel J j (positiveLane D k) M N D.cScale D.block.atom.residue)+
         rowPairing D r k (blockKernel J j (!(positiveLane D k)) M N D.cScale D.block.atom.residue)) := by
  unfold nonzeroBlocks
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  cases positiveLane D k <;> simp [add_comm]

theorem occupied_both_signs (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (ha : D.block.atom.residue≠0)
    {zy : Output} (hb : jointBeta D r (nonzeroSource (originalSource D)) zy≠0)
    (upper : Bool) (J j : ℕ) (ell : D4 → ℤ) {p : ℕ} (hp : p∈commonMBlock J j) :
    ∃ (k : BlockKey) (z : Row D k) (n : ℕ), k∈originalKeys D ∧ n∈nCarrier D k z.val ∧
      decode k z.val n=zy ∧ 0<p ∧ 0<traceIndex D k (positiveLane D k) z.val n ∧
      traceIndex D k (!(positiveLane D k)) z.val n<0 ∧
      ∀ b : Bool,(commonPoissonCompleted J j (ell 1)).weight p*traceBeta D r k upper b ell z.val n≠0 := by
  obtain ⟨k,z,n,hk,hn,heq,hnz⟩ := nonzero_original_beta_has_row D r hb
  have sides := opposite_lanes D k
  let b := positiveLane D k
  have mag := traceIndex_natAbs_pos D k b z.val hn ha
  rw [traceIndex_natAbs] at mag
  have pos : 0<traceIndex D k b z.val n := by
    rw [traceIndex_eq_signedY,sides.1]
    simpa only [signedY,Bool.false_eq_true,if_false,Int.natCast_pos] using mag
  have nz : blockBeta D r k (decode k z.val n)≠0 := by
    intro e
    exact hnz (norm_eq_zero.mp (by rw [norm_rowCoefficient,e,norm_zero]))
  refine ⟨k,z,n,hk,hn,heq,lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hp).1,
    pos,negative_row_index D k _ hn ha sides.2,?_⟩
  intro lane
  apply mul_ne_zero
  · rw [commonPoissonCompleted_weight J j (ell 1) p hp]
    exact Complex.exp_ne_zero _
  · apply norm_ne_zero_iff.mp
    rw [norm_traceBeta]
    exact norm_ne_zero_iff.mpr nz

end
end ImbalancedChen.Part3.OriginalOccupiedTraceSigns20261112
