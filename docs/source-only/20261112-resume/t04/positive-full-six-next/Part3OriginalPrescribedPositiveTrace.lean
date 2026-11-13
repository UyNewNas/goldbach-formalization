import ImbalancedChen.Part3OriginalPositiveScalarRemainder
import ImbalancedChen.Part3OriginalHolomorphicProjectionMarks

/-! The actual same-sign formula at the manuscript test for the original
pair of finite marked rows. The equal-mark diagonal at level one cancels once. -/
namespace ImbalancedChen.Part3.OriginalPrescribedPositiveTrace20261112
noncomputable section
open Complex MeasureTheory
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalHolomorphicWeightSum20261112 (positive_mark_holomorphic oddProjection holSpectrum)
open OriginalPositiveScalarRemainder20261112
open OriginalPositiveScalarGeometry20261112 (positive_row_index)
open OriginalPositiveStrip20261112 (residual)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open OriginalPositiveCompactPretrace20261112 (marking)
open OriginalMarkedPacketLimits20261112 ActualPositiveNativeDiagonal20261112 ActualPrescribedPositiveJ20261112
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open OriginalOppositeMarkedKuznetsov20261112 (modulusTerm)
open ActualFullCuspEigenbasis20261026b

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4→ℤ)
local instance nzLevel : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
local notation "Z" => z.val
local notation "mark" => marking D r k z upper negativeM J j ell

def holomorphic (Y : ℝ) := mark (fun p b => holSpectrum Z p b.natAbs (spectralTest ell Y))

private theorem add_modulus (Φ Ψ : ℝ→ℂ) (p : ℕ) (b : ℤ) (d : ℕ+) :
    modulusTerm (fun q => Φ q+Ψ q) Z p b d=modulusTerm Φ Z p b d+modulusTerm Ψ Z p b d := by
  unfold modulusTerm
  split_ifs <;> ring

theorem original_prescribed_positive_trace (ha : D.block.atom.residue≠0) (hs : traceNegative D k negativeM=false)
    {Y : ℝ} (hY : 0<Y) :
    (∀ n∈nCarrier D k Z,∀ p∈commonMBlock J j,
      Summable (fun d : ℕ+ => ‖modulusTerm (spectralTest ell Y) Z p (traceIndex D k negativeM Z n) d‖)) ∧
    Integrable (fun t => (positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ))*cMark D r k z upper negativeM J j ell t) ∧
    Summable (fun i : actualCuspBasisIndex Z (NeZero.pos Z) => ‖nativeWeight Z (spectralTest ell Y) i*dMark D r k z upper negativeM J j ell i‖) ∧
    offDiagonal D r k z upper negativeM J j ell (spectralTest ell Y)=
      holomorphic D r k z upper negativeM J j ell Y+scalar D r k z upper negativeM J j ell Y := by
  let Γ := oddProjection ell Y
  let K := residual ell Y
  have e : spectralTest ell Y=fun q => Γ q+K q := funext (fun q => by dsimp [Γ,K,oddProjection]; ring)
  have S := original_scalar_remainder D r k z upper negativeM J j ell ha hs hY
  let ind := traceIndex D k negativeM Z
  have H (n : ℕ) (hn : n∈nCarrier D k Z) (p : ℕ) (hp : p∈commonMBlock J j) :=
    positive_mark_holomorphic Z p (b:=ind n) (lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hp).1)
      (positive_row_index D k negativeM hn ha hs) ell hY
  have v (n : ℕ) (hn : n∈nCarrier D k Z) (p : ℕ) (hp : p∈commonMBlock J j) :
      Summable (modulusTerm (spectralTest ell Y) Z p (ind n)) ∧
      (∑' d : ℕ+,modulusTerm (spectralTest ell Y) Z p (ind n) d)=
        holSpectrum Z p (ind n).natAbs (spectralTest ell Y)+
        (if Z=1 ∧ (p:ℤ)=ind n then diagonalMoment 0 (spectralTest ell Y)/(2*(Real.pi:ℂ)) else 0)+
        ∑' d : ℕ+,modulusTerm K Z p (ind n) d := by
    have J₁ := (H n hn p hp).1.of_norm
    have J₂ := (S.1 n hn p hp).of_norm
    have eq : modulusTerm (spectralTest ell Y) Z p (ind n)=fun d =>
        modulusTerm Γ Z p (ind n) d+modulusTerm K Z p (ind n) d := by
      rw [e]; funext d; exact add_modulus D k z Γ K p (ind n) d
    rw [eq]
    exact ⟨J₁.add J₂,by rw [J₁.tsum_add J₂,(H n hn p hp).2]⟩
  have G : offDiagonal D r k z upper negativeM J j ell (spectralTest ell Y)=
      holomorphic D r k z upper negativeM J j ell Y+collision D r k z upper negativeM J j ell Y+
        offDiagonal D r k z upper negativeM J j ell K := by
    simp only [offDiagonal,holomorphic,collision,marking,←Finset.sum_add_distrib,←mul_add]
    apply Finset.sum_congr rfl; intro n hn
    apply Finset.sum_congr rfl; intro p hp
    exact congrArg (fun a => _*a) (v n hn p hp).2
  refine ⟨fun n hn p hp => (v n hn p hp).1.norm,S.2.1,S.2.2.1,?_⟩
  linear_combination G+S.2.2.2

end
end ImbalancedChen.Part3.OriginalPrescribedPositiveTrace20261112
