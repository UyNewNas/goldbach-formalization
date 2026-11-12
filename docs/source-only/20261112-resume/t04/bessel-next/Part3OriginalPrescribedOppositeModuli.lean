import ImbalancedChen.Part3ActualPrescribedOppositeKL
import ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov
import ImbalancedChen.Part3OriginalFullModulusCuspInput

/-! Absolute KL inversion over the original finite geometric support
of the prescribed test, including every original arithmetic phase. -/
namespace ImbalancedChen.Part3.OriginalPrescribedOppositeModuli20261112

noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalTwoZSourceAssembly20261102 OriginalNonzeroCuspOneSource20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusAssembly20261102
open OriginalFullModulusCuspInput20261102 ActualPrescribedOppositeKL20261112
open OriginalOppositeMarkedKuznetsov20261112

def modulusDensity (ell : D4 → ℤ) (Y : ℝ) (z p : ℕ) (h : ℤ) (c : ℕ) (t : ℝ) : ℂ :=
  if hc : 0<c ∧ c.Coprime z then
    letI : NeZero c := ⟨hc.1.ne'⟩
    cuspOneMatrixSum z c hc.2.symm (p : ℤ) h/(traceModulus z c : ℂ) *
      inverseDensity (spectralTest ell Y)
        (4*Real.pi*Real.sqrt ((p : ℝ)*(h.natAbs : ℝ))/traceModulus z c) t
  else 0

/-- This finite sum is the manuscript's own enlarged integer-modulus
support. The integral recovers the complete original arithmetic row
with its signed coefficient and common m phase. -/
theorem original_opposite_modulus_inverse (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool) (hs : traceNegative D k negativeM=true)
    (M : ℝ) {N : ℝ} (hN : 0<N) (hNC : N≤4*D.cScale) (ha : D.block.atom.residue ≠ 0)
    (ell : D4 → ℤ) {z n p : ℕ} (hz : z∈chartLevels D k upper)
    (hn : n∈nCarrier D k z) (hp : p∈commonMBlock J j) :
    let Y := chartY0 D k upper j N
    let h := traceIndex D k negativeM z n
    let w := (((M*Real.sqrt (fixedZ D upper) : ℝ) : ℂ)*(commonPoissonCompleted J j (ell 1)).weight p*
      traceBeta D r k upper negativeM ell z n)
    let F := fun t => w*∑ c∈enlargedModuli D,modulusDensity ell Y z p h c t
    IntegrableOn F (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ),F t)=fullModulusRow D r k upper J j negativeM M N ell z n p := by
  let Y := chartY0 D k upper j N
  let h := traceIndex D k negativeM z n
  let w := (((M*Real.sqrt (fixedZ D upper) : ℝ) : ℂ)*(commonPoissonCompleted J j (ell 1)).weight p*
    traceBeta D r k upper negativeM ell z n)
  let F := modulusDensity ell Y z p h
  have hY : 0<Y := original_spectral_scale_pos D k upper j hN ha
  have hz0 := (levelCarrier_licensed D k (chartLevels_subset D k upper hz)).1
  have hp0 : (0:ℝ)<p := by
    have lo : 2^j≤p := (Finset.mem_Ico.mp hp).1
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num : (0:ℕ)<2) _) lo)
  have hneg : h<0 := negative_row_index D k negativeM hn ha hs
  have hrow : (0:ℝ)<h.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hneg.ne
  have each (c : ℕ) : IntegrableOn (F c) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ),F c t)=bareCuspTerm D k upper j negativeM N ell z n p c := by
    by_cases hc : 0<c ∧ c.Coprime z
    · letI : NeZero c := ⟨hc.1.ne'⟩
      have hq := div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ)<4) Real.pi_pos)
        (Real.sqrt_pos.mpr (mul_pos hp0 hrow))) (traceModulus_pos hz0 hc.1)
      have P := prescribed_inverse ell hY hq
      simp only [F,modulusDensity,bareCuspTerm,dif_pos hc,Y,h] at *
      exact ⟨P.1.const_mul _,by rw [integral_const_mul,P.2]⟩
    · simp [F,modulusDensity,bareCuspTerm,hc]
  have sumI : Integrable (fun t => ∑ c∈enlargedModuli D,F c t) (volume.restrict (Ioi 0)) :=
    integrable_finsetSum _ (fun c _ => (each c).1)
  have S := bareCuspTerm_hasSum D k upper J j negativeM hN hNC ha ell hz hn hp
  refine ⟨sumI.const_mul w,?_⟩
  change (∫ t in Ioi (0 : ℝ),w*∑ c∈enlargedModuli D,F c t)=_
  rw [integral_const_mul,integral_finsetSum _ (fun c _ => (each c).1),
    fullModulusRow_eq_normalized_cusp_sum D r k upper J j negativeM M N ell hz,S.tsum_eq]
  exact congrArg (fun a => w*a) (Finset.sum_congr rfl (fun c _ => (each c).2))

end
end ImbalancedChen.Part3.OriginalPrescribedOppositeModuli20261112
