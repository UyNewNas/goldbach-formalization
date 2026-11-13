import ImbalancedChen.Part3OriginalMarkedPacketLimits
import ImbalancedChen.Part3ActualPositiveTensorProbes
import ImbalancedChen.Part3PrescribedTensorSpectralExchange
import Batteries.Tactic.OpenPrivate

/-! The physical tensor series converges through the genuine Maaß basis and
through every incoming Eisenstein cusp at its original marked covariance. -/
namespace ImbalancedChen.Part3.OriginalPositiveTensorResolution20261112
noncomputable section
open Filter Set MeasureTheory Complex
open scoped Topology BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualPositiveTensorIntegral20261112 ActualPositiveTensorProbes20261112
open OriginalMarkedPacketLimits20261112 ActualPositiveScalarPacket20261112 RadialSchrodingerL2Form20261025a
open OriginalPositiveHeightTest20261112
open PrescribedTensorPacketPrice20261112 PrescribedTensorSpectralExchange20261112 PrescribedTensorSeedNorm20261112
open PrescribedLogTensorWindows20261112 PrescribedLogTensorCoefficients20261112 (Modes)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open OriginalContinuousCuspGram20261110 OriginalContinuousPoincarePackets20261110 OriginalContinuousClassRemoval20261110
open OriginalNativeCuspFunctionals20261102 ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110 ActualOrdinaryContinuousModes20261110
open ActualCriticalCuspEvaluation20261110 (criticalPoint)
open ActualContinuousClassFourier20261110 OriginalMarkedArithmeticTrace20261112 OriginalProjectedContinuousCovariance20261112
open ActualOppositeBesselTransform20261112 OriginalCuspidalPoincareTrace20261110
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace
open private probe_basis from ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov
open private center_bound from ImbalancedChen.Part3ActualPositiveCompactTensor

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue≠0) (upper negativeM : Bool) (J j : ℕ) (ell : D4→ℤ)
local instance nzLevel : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
local notation "Idx" => actualCuspBasisIndex z.val (NeZero.pos z.val)
local notation "A" => dMark D r k z upper negativeM J j ell
local notation "E" => cMark D r k z upper negativeM J j ell
local notation "rowTotal" => orderTotal D r k z upper negativeM J j ell

include ha in
private theorem budget (η H : RadialTest) (R : ℝ) :
    Summable (fun v : Modes => ‖coeff η H R v‖*(‖mVector z.val J j ell v‖*‖nVector D r k z ha upper negativeM ell v‖)) := by
  obtain ⟨B,_,centers⟩ := center_bound (log_compact η H R)
  obtain ⟨L,l,ml⟩ := packet_budget z.val false false (commonMBlock J j)
    (fun p => star ((commonPoissonCompleted J j (ell 1)).weight p)) (fun p => (p:ℤ)) (common_nonzero J j)
  obtain ⟨T,t,nt⟩ := packet_budget z.val true true (nCarrier D k z.val)
    (traceBeta D r k upper negativeM ell z.val) (traceIndex D k negativeM z.val) (row_nonzero D k z ha negativeM)
  apply ((coeff_summable η H R).mul_right ((L*(2*Real.exp B))*(T*(2*Real.exp B)))).of_nonneg_of_le (fun v => by positivity)
  intro v
  by_cases c : coeff η H R v=0
  · simp [c]
  obtain ⟨x,y⟩ := centers v c
  have p : ‖mVector z.val J j ell v‖≤L*(2*Real.exp B) := (ml _ _).trans (mul_le_mul_of_nonneg_left
    ((price_growth _).trans (by gcongr)) l)
  have q : ‖nVector D r k z ha upper negativeM ell v‖≤T*(2*Real.exp B) := (nt _ _).trans (mul_le_mul_of_nonneg_left
    ((price_growth _).trans (by gcongr)) t)
  exact mul_le_mul_of_nonneg_left (mul_le_mul p q (norm_nonneg _) (by positivity)) (norm_nonneg _)

private theorem atom_disc (q : Modes) (i : Idx) :
    discrete D r k z upper negativeM J j ell q i=probeProduct (basisOrder z.val (NeZero.pos z.val) i) q*A i := by
  simp only [probeProduct,probe_basis,discrete,dMark]

theorem atom_real (q : Modes) (t : ℝ) :
    probeProduct ((t:ℂ)*I) q =
      star (radialProbe 1 (pattern q.1.1 q.2.1) t)*radialProbe 1 (rightPattern q.1.2 q.2.2) t := by
  have eq : criticalPoint t-1/2=(t:ℂ)*I := by unfold criticalPoint; ring
  have c : star ((t:ℂ)*I)= -((t:ℂ)*I) := by simp [Complex.star_def]
  simp only [probeProduct,c,probe_neg_order,radialProbe,eq]

include ha in
private theorem atom_cont (q : Modes) (t : ℝ) :
    (∑ a : Parameters z.val,continuousRow D r k z upper negativeM J j ell q a t)=probeProduct ((t:ℂ)*I) q*E t := by
  have H := (original_projected_trace D r k z ha upper negativeM J j ell _ _
    (pattern_test q.1.1 q.2.1).1 (pattern_test _ _).2.1 (pattern_test _ _).2.2
    (right_test q.1.2 q.2.2).1 (right_test _ _).2.1 (right_test _ _).2.2).2.2.2.2 t
  change nativeProduct z.val _ _=_
  rw [H,original_projected_product D r k z upper negativeM J j ell t,atom_real]
  rfl

include ha in
theorem resolution (η H : RadialTest) (R : ℝ) :
    HasSum (fun v : Modes => coeff η H R v*rowTotal (fun ν => probeProduct ν v)) (rowTotal (packet η H R)) := by
  let c := coeff η H R
  let F := fun v (i : Idx) => c v*(probeProduct (basisOrder z.val (NeZero.pos z.val) i) v*A i)
  let G := fun v (t : ℝ) => c v*(probeProduct ((t:ℂ)*I) v*E t)
  have cost := budget D r k z ha upper negativeM J j ell η H R
  have P := discrete_price D r k z ha upper negativeM J j ell
  have C := continuous_price D r k z ha upper negativeM J j ell
  have D1 : Summable (Function.uncurry F) := by
    apply summable_norm_iff.mp
    simp only [Function.uncurry,F,←atom_disc,norm_mul]
    apply (summable_prod_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    refine ⟨fun q => (P q).1.mul_left _,?_⟩
    simp_rw [tsum_mul_left]
    exact cost.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _))
      (fun q => mul_le_mul_of_nonneg_left (P q).2 (norm_nonneg _))
  have dpoint (i : Idx) : (∑' v,F v i)=packet η H R (basisOrder z.val (NeZero.pos z.val) i)*A i := by
    have S := ((probes η H R (basisOrder z.val (NeZero.pos z.val) i)).mul_right (A i)).tsum_eq
    simpa only [F,c,mul_assoc] using S
  have DS := D1.prod.hasSum
  rw [D1.tsum_comm] at DS
  simp_rw [dpoint] at DS
  let Z := continuousRow D r k z upper negativeM J j ell
  have ig (v : Modes) : Integrable (G v) := by
    have eq : G v=fun t => ∑ a : Parameters z.val,c v*Z v a t := by
      funext t; rw [G,←atom_cont D r k z ha upper negativeM J j ell,Finset.mul_sum]
    rw [eq]; exact integrable_finsetSum _ (fun a _ => ((C v).1 a).const_mul _)
  have sg : Summable (fun v : Modes => ∫ t,‖G v t‖) := by
    apply cost.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    intro v
    have m (t : ℝ) : ‖G v t‖≤‖c v‖*∑ a : Parameters z.val,‖Z v a t‖ := by
      rw [G,norm_mul,←atom_cont D r k z ha upper negativeM J j ell]; exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    have B := integral_mono (ig v).norm ((integrable_finsetSum _ (fun a _ => ((C v).1 a).norm)).const_mul ‖c v‖) m
    rw [integral_const_mul,integral_finsetSum _ (fun a _ => ((C v).1 a).norm)] at B
    exact B.trans (mul_le_mul_of_nonneg_left (C v).2 (norm_nonneg _))
  have cpoint (t : ℝ) : (∑' v,G v t)=packet η H R ((t:ℂ)*I)*E t := by
    simpa only [G,c,mul_assoc] using ((probes η H R ((t:ℂ)*I)).mul_right (E t)).tsum_eq
  have CS := hasSum_integral_of_summable_integral_norm ig sg
  simp_rw [cpoint] at CS
  apply (DS.add CS).congr_fun
  intro v; simp only [orderTotal,total,F,G,c,tsum_mul_left,integral_const_mul,mul_add]

end
end ImbalancedChen.Part3.OriginalPositiveTensorResolution20261112
