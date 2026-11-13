import ImbalancedChen.Part3OriginalPositiveCompactPretrace
import ImbalancedChen.Part3OriginalPrescribedPositiveSpectralWeights

/-! The scalar remainder of the positive original marked row. The physical
identity cell is on the spectral side with a minus sign after solving
for the off-diagonal arithmetic series. -/
namespace ImbalancedChen.Part3.OriginalPositiveScalarRemainder20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalPositiveCompactPretrace20261112 OriginalPositiveHeightTest20261112 (height original)
open OriginalPositiveRatioWindows20261112 (unit ratio)
open OriginalPositiveScalarGeometry20261112 (residualPair windowPair original_positive_row positive_row_index original_moduli_absolute)
open OriginalPositiveStrip20261112 (residual)
open OriginalOppositeMarkedKuznetsov20261112 (modulusTerm)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open OriginalMarkedPacketLimits20261112 ActualPositiveScalarPacket20261112
open OriginalPrescribedPositiveSpectralWeights20261112 ActualPositiveNativeDiagonal20261112 ActualPrescribedPositiveJ20261112
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open ActualFullCuspEigenbasis20261026b

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (J j : ℕ) (ell : D4→ℤ)
local instance nzLevel : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
local notation "mark" => marking D r k z upper negativeM J j ell

private theorem marked_limit {f : ℕ→ℕ→ℤ→ℂ} {g : ℕ→ℤ→ℂ}
    (h : ∀ n∈nCarrier D k z.val,∀ p∈commonMBlock J j,
      Tendsto (fun a => f a p (traceIndex D k negativeM z.val n)) atTop (𝓝 (g p (traceIndex D k negativeM z.val n)))) :
    Tendsto (fun a => mark (f a)) atTop (𝓝 (mark g)) := by
  exact tendsto_finsetSum _ fun n hn => tendsto_finsetSum _ fun p hp => (h n hn p hp).const_mul _

def scalar (Y : ℝ) := total D r k z upper negativeM J j ell (nativeWeight z.val (spectralTest ell Y))
  (fun t => positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ))

def offDiagonal (Φ : ℝ→ℂ) := mark (fun p b => ∑' d : ℕ+,modulusTerm Φ z.val p b d)

def collision (Y : ℝ) := mark (fun p b => if z.val=1 ∧ (p:ℤ)=b then
  diagonalMoment 0 (spectralTest ell Y)/(2*(Real.pi:ℂ)) else 0)

/-- Each term uses the original Poisson weight, signed source beta and
the m=∞, n=1 observation frames. The full Eisenstein line is inside
`scalar` via the same nativeProduct with its 1/(4π), and the Maaß
sum has the unprojected complementary orders with the real cosine divisor. -/
theorem original_scalar_remainder (ha : D.block.atom.residue≠0) (hs : traceNegative D k negativeM=false)
    {Y : ℝ} (hY : 0<Y) :
    (∀ n∈nCarrier D k z.val,∀ p∈commonMBlock J j,
      Summable (fun d : ℕ+ => ‖modulusTerm (residual ell Y) z.val p (traceIndex D k negativeM z.val n) d‖)) ∧
    (Integrable (fun t => (positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ))*
      cMark D r k z upper negativeM J j ell t)) ∧
    Summable (fun i : actualCuspBasisIndex z.val (NeZero.pos z.val) => ‖nativeWeight z.val (spectralTest ell Y) i*
      dMark D r k z upper negativeM J j ell i‖) ∧
    offDiagonal D r k z upper negativeM J j ell (residual ell Y)=
      scalar D r k z upper negativeM J j ell Y-collision D r k z upper negativeM J j ell Y := by
  let M := orderTotal D r k z upper negativeM J j ell
  have rows (n : ℕ) (hn : n∈nCarrier D k z.val) (p : ℕ) (hp : p∈commonMBlock J j) :=
    original_positive_row D k z negativeM ha hs hn hp ell hY
  have first (n : ℕ) : mark (windowPair ell hY n z.val)=M (response (ratio ell hY n)) := by
    have g := marked_limit D r k z upper negativeM J j ell (f:=fun R : ℕ => pair D k z (original ell hY R n))
      (g:=windowPair ell hY n z.val) (fun m hm p hp => ((rows m hm p hp).1 n).comp tendsto_natCast_atTop_atTop)
    have s := product_limit D r k z upper negativeM J j ell ha hY n
    apply tendsto_nhds_unique g (s.congr' (Eventually.of_forall fun R => (compact_pretrace D r k z upper negativeM J j ell
      ha hs unit (ratio ell hY n) R).symm))
  have g := marked_limit D r k z upper negativeM J j ell (f:=fun n => windowPair ell hY n z.val)
    (g:=residualPair ell Y z.val) (fun m hm p hp => (rows m hm p hp).2)
  have s := ratio_limit D r k z upper negativeM J j ell ha hY
  have EQ : mark (residualPair ell Y z.val)=scalar D r k z upper negativeM J j ell Y :=
    tendsto_nhds_unique g (s.congr' (Eventually.of_forall fun n => (first n).symm))
  have C := original_positive_spectral_convergence D r k z ha upper negativeM J j ell hY
  refine ⟨fun n hn p hp => (original_moduli_absolute ell hY (levelCarrier_licensed D k z.property).1
    (lt_of_lt_of_le (pow_pos (by norm_num : 0<(2:ℕ)) j) (Finset.mem_Ico.mp hp).1) (positive_row_index D k negativeM hn ha hs)).2.2,
    C.1,C.2.1,?_⟩
  have add : mark (residualPair ell Y z.val)=collision D r k z upper negativeM J j ell Y+
      offDiagonal D r k z upper negativeM J j ell (residual ell Y) := by
    simp only [marking,residualPair,collision,offDiagonal,mul_add,Finset.sum_add_distrib]
  linear_combination EQ-add

end
end ImbalancedChen.Part3.OriginalPositiveScalarRemainder20261112
