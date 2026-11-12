import ImbalancedChen.Part3ActualMarkedGeometricSeries
import ImbalancedChen.Part3OriginalProjectedContinuousCovariance
import Batteries.Tactic.OpenPrivate

/-! The weight-zero pretrace formula for the original two marked
packets, with its induced test at every physical arithmetic modulus. -/
namespace ImbalancedChen.Part3.OriginalMarkedArithmeticTrace20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups UpperHalfPlane
open ActualCuspOneGeometricPairing20261112 ActualMarkedBruhatTest20261112
open ActualMarkedGeometricSeries20261112 OriginalProjectedContinuousCovariance20261112
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open ActualOrdinaryContinuousModes20261110 ActualContinuousClassFourier20261110
open OriginalContinuousClassRemoval20261110 OriginalContinuousCuspGram20261110
open ActualCuspDenominatorClasses20261110 OriginalNativeCuspFunctionals20261102
open ActualCuspBasisWhittakerCoefficients20261102 ActualFullCuspEigenbasis20261026b
open Gamma0QuotientCellPushforward20261025a OriginalCuspidalPoincareTrace20261110
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalTwoZSourceAssembly20261102 OriginalNonzeroCuspOneSource20261102
open P3NativePeriod64SamplingSourceOnly (D4)
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace

/-- The physical two-probe spectral weight in the dt/cosh(pi t)
convention. The arithmetic coefficients continue to be the original
R's in the expansion 2 sqrt(y) K_it(2 pi |n| y) R(n). -/
def probeWeight (ψ φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.cosh (Real.pi*t) : ℂ)*(star (radialProbe 1 ψ t)*radialProbe 1 φ t)

def regularIntegrand (N : ℕ) [NeZero N] (ψ φ : ℝ → ℂ) (t : ℝ) (X Y : Parameters N → ℂ) : ℂ :=
  probeWeight ψ φ t*(∑ a : Parameters N,star (X a)*Y a)/
    (4*(Real.pi : ℂ)*(Real.cosh (Real.pi*t) : ℂ))

private theorem regular_density (N : ℕ) [NeZero N] (ψ φ : ℝ → ℂ) (t : ℝ) (X Y : Parameters N → ℂ) :
    (star (radialProbe 1 ψ t)*radialProbe 1 φ t)*nativeProduct N X Y=regularIntegrand N ψ φ t X Y := by
  rw [nativeProduct,← Finset.sum_div,regularIntegrand,probeWeight]
  field_simp [Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  <;> ring

/-- The original physical Kloosterman sum is recovered with its
unconjugated marked beta. Both Fourier phases occur exactly once. -/
theorem original_modulus_phase (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (upper negativeM : Bool) (ell : D4 → ℤ) (n p : ℕ) (d : ℕ+) (ψ φ : ℝ → ℂ) :
    let h := traceIndex D k negativeM z.val n
    traceBeta D r k upper negativeM ell z.val n*geometricTerm z.val p h ψ φ d =
      if z.val.Coprime (d : ℕ) then
        modulatedBeta D r k upper ell z.val n *
          (sourceKloosterman D k negativeM z.val n d p/(traceModulus z.val d : ℂ)) *
          orbitTest h.sign ψ φ (4*Real.pi*Real.sqrt ((p : ℝ)*(h.natAbs : ℝ))/traceModulus z.val d)
      else 0 := by
  dsimp only
  by_cases h : z.val.Coprime (d : ℕ)
  · rw [if_pos h,geometricTerm,dif_pos h,sourceKloosterman_eq_positive_cuspOne D k negativeM z.val n d p
      (levelCarrier_licensed D k z.property).1 h,traceBeta]
    ring
  · simp only [geometricTerm,dif_neg h,if_neg h,mul_zero]

/-- Both arithmetic signs, the actual common M-interval and the original
N row. The diagonal is retained at level one. Each off-diagonal modulus
sum converges absolutely and the continuous numerator uses every
singular cusp of this same level. -/
theorem original_marked_arithmetic_trace (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let hN := NeZero.pos z.val
    let ind := traceIndex D k negativeM z.val
    let B := traceBeta D r k upper negativeM ell z.val
    let W := (commonPoissonCompleted J j (ell 1)).weight
    let G := fun t => regularIntegrand z.val ψ φ t
      (fun a => M J j ell (fun h => nativeR a false h t))
      (fun a => source D r k z upper negativeM ell (fun h => nativeR a true h t))
    let F := fun i : actualCuspBasisIndex z.val hN =>
      (star (orderProbe 1 ψ (basisOrder z.val hN i))*orderProbe 1 φ (basisOrder z.val hN i))*
        (star (originalMFunctional J j ell z.val hN i)*originalNFunctional D r k upper negativeM ell z.val hN i)
    Integrable G ∧ Summable F ∧
      (∀ n ∈ nCarrier D k z.val,∀ p ∈ commonMBlock J j,Summable (geometricTerm z.val p (ind n) ψ φ)) ∧
      (∑ n ∈ nCarrier D k z.val,∑ p ∈ commonMBlock J j,
        W p*B n*(pairDiagonal z.val p (ind n) ψ φ+∑' d : ℕ+,geometricTerm z.val p (ind n) ψ φ d)) =
        (∑' i,F i)+(∫ t,G t) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let S := commonMBlock J j
  let T := nCarrier D k z.val
  let b := traceBeta D r k upper negativeM ell z.val
  let w := (commonPoissonCompleted J j (ell 1)).weight
  let ind := traceIndex D k negativeM z.val
  let XM := mPacket z.val J j ell ψ
  let YN := nPacket D r k z upper negativeM ell φ
  let G := fun t => regularIntegrand z.val ψ φ t
    (fun a => M J j ell (fun h => nativeR a false h t))
    (fun a => source D r k z upper negativeM ell (fun h => nativeR a true h t))
  let v := originalMVector z.val J j ell ψ hψ hcψ hpψ
  let u := originalNVector D r k z ha upper negativeM ell φ hφ hcφ hpφ
  have hS (p : ℕ) (hp : p∈S) : 0<p := Nat.pos_of_ne_zero (fun h => common_nonzero J j p hp (by simp [h]))
  have hT (n : ℕ) (hn : n∈T) : ind n≠0 := row_nonzero D k z ha negativeM n hn
  have P := original_projected_trace D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ
  have GE : (fun t => nativeProduct z.val (fun a => spectrum z.val XM a t) (fun a => spectrum z.val YN a t))=G := by
    funext t
    exact (P.2.2.2.2 t).trans (by rw [original_projected_product D r k z upper negativeM J j ell t,regular_density])
  have IV : inner ℂ u v = ∫ q,star (YN q)*XM q ∂carrierPushforward z.val := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have H := original_packet_covariance D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ 0
    filter_upwards [H.1.coeFn_toLp,H.2.1.coeFn_toLp] with q hv hu
    simp only [RCLike.inner_apply',← Complex.star_def,show v q=XM q from hv,show u q=YN q from hu]
  have A := marked_pair z.val S T w b ind hS hT ψ φ hψ hcψ hpψ hφ hcφ hpφ
  refine ⟨GE ▸ P.1,P.2.2.1.summable,fun n hn p hp => (normalized_pair z.val (hS p hp) (hT n hn)
    ψ φ hψ hcψ hpψ hφ hcφ hpφ).1,?_⟩
  have HE := P.2.2.2.1
  change inner ℂ u v = _ at HE
  rw [IV,GE] at HE
  exact A.symm.trans HE

end
end ImbalancedChen.Part3.OriginalMarkedArithmeticTrace20261112
