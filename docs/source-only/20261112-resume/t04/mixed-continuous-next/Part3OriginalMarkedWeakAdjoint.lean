import ImbalancedChen.Part3ActualMarkedContinuousCoordinates
import ImbalancedChen.Part3OriginalResidualPoincarePackets
import Batteries.Tactic.OpenPrivate

/-! Compact spectral testing of both original finite marked packets,
with the original signed indices, common probes and operator phases.
The native covariance is absolutely integrable on the full line. -/
namespace ImbalancedChen.Part3.OriginalMarkedWeakAdjoint20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped MatrixGroups UpperHalfPlane BigOperators
open AngularFourierUnitary20261026b ActualMarkedHorocycleSupport20261112
open ActualMarkedContinuousCoordinates20261112
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110
open ActualOrdinaryContinuousModes20261110 ActualContinuousClassFourier20261110 ActualYoungFormalClass20261110
open OriginalContinuousPoincarePackets20261110 OriginalContinuousCuspGram20261110
open OriginalCuspidalPoincareTrace20261110 OriginalResidualPoincarePackets20261110
open OriginalContinuousClassRemoval20261110 OriginalSimultaneousPrefixCompletion20261102
open OriginalSignedTraceInput20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 P3NativePeriod64SamplingSourceOnly (D4)
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace

private theorem integrated_native (N : ℕ) [NeZero N] {X Y : Gamma0OrbitSpace N → ℂ}
    (hx : MemLp X 2 (carrierPushforward N)) (hy : MemLp Y 2 (carrierPushforward N))
    (cx : supportedInQuotientCompact N X) (cy : supportedInQuotientCompact N Y)
    (rx : (ℂ ∙ constantL2 N).starProjection (hx.toLp X)=0)
    (ry : (ℂ ∙ constantL2 N).starProjection (hy.toLp Y)=0) :
    let G := fun t => nativeProduct N (fun a => spectrum N X a t) (fun a => spectrum N Y a t)
    Integrable G ∧ inner ℂ (hy.toLp Y) (nativeSynthesis N (fun a => analysis N a (hx.toLp X))) = ∫ t,G t := by
  classical
  let h := fun a => analysis N a (hx.toLp X)
  let G := fun t => nativeProduct N (fun a => spectrum N X a t) (fun a => spectrum N Y a t)
  let F := fun t => ∑ a : Parameters N,spectrum N Y a t*h a t
  have A := (mixed_adjoint N hx cx rx).1
  have B := (mixed_adjoint N hy cy ry).2 h
  have AE (a : Parameters N) : (fun t => h a t) =ᵐ[volume] fun t => star (spectrum N X a t) := by
    have H := A a
    have hsc : ENNReal.ofReal ((2*Real.pi)⁻¹) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    rw [angularMeasure,Measure.ae_smul_measure_eq hsc volume] at H
    exact H
  let c : ℂ := (4*(Real.pi : ℂ))⁻¹
  have E : (fun t => c*F t) =ᵐ[volume] G := by
    filter_upwards [ae_all_iff.mpr AE] with t ht
    simp only [F,G,c,nativeProduct,Finset.mul_sum,ht,div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro a _
    ring
  refine ⟨(B.1.const_mul c).congr E,?_⟩
  calc
    _ = ((4*Real.pi)⁻¹ : ℝ) • ∫ t,F t := B.2
    _ = ∫ t,c*F t := by
      simp only [c,integral_const_mul,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_ofNat]
    _ = _ := integral_congr_ae E

/-- The actual manuscript vectors tested against every simultaneous
native-cusp L² spectral probe. This includes all compact spectral tests.
Their integrated covariance is paired in the original N,M order. -/
theorem original_marked_weak (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool)
    (J j : ℕ) (ell : D4 → ℤ) (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let X := mPacket z.val J j ell ψ
    let Y := nPacket D r k z upper negativeM ell φ
    let v := originalMVector z.val J j ell ψ hψ hcψ hpψ
    let w := originalNVector D r k z ha upper negativeM ell φ hφ hcφ hpφ
    let G := fun t => nativeProduct z.val (fun a => spectrum z.val X a t) (fun a => spectrum z.val Y a t)
    (∀ a : Parameters z.val,
      ((analysis z.val a v : ℝ → ℂ) =ᵐ[angularMeasure] fun t => star (spectrum z.val X a t)) ∧
      ((analysis z.val a w : ℝ → ℂ) =ᵐ[angularMeasure] fun t => star (spectrum z.val Y a t))) ∧
    (∀ h : Parameters z.val → AngularL2,
      (Integrable (fun t => ∑ a : Parameters z.val,spectrum z.val X a t*h a t) ∧
        inner ℂ v (nativeSynthesis z.val h) =
          ((4*Real.pi)⁻¹ : ℝ) • ∫ t,∑ a : Parameters z.val,spectrum z.val X a t*h a t) ∧
      (Integrable (fun t => ∑ a : Parameters z.val,spectrum z.val Y a t*h a t) ∧
        inner ℂ w (nativeSynthesis z.val h) =
          ((4*Real.pi)⁻¹ : ℝ) • ∫ t,∑ a : Parameters z.val,spectrum z.val Y a t*h a t)) ∧
    Integrable G ∧ inner ℂ w (nativeSynthesis z.val (fun a => analysis z.val a v)) = ∫ t,G t ∧
      ∀ t, G t = (star (radialProbe 1 ψ t)*radialProbe 1 φ t)*
        classProduct z.val (fun i => M J j ell (fun n => channelR i false n t))
          (fun i => source D r k z upper negativeM ell (fun n => channelR i true n t)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let X := mPacket z.val J j ell ψ
  let Y := nPacket D r k z upper negativeM ell φ
  have cx : supportedInQuotientCompact z.val X := marked_support z.val false _ _ _ (common_nonzero J j) ψ hψ hcψ hpψ
  have cy : supportedInQuotientCompact z.val Y := marked_support z.val true _ _ _ (row_nonzero D k z ha negativeM) φ hφ hcφ hpφ
  have HX := original_packet_covariance D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ
  have Z := original_residual_packets D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ
  have A := mixed_adjoint z.val (HX 0).1 cx Z.1
  have B := mixed_adjoint z.val (HX 0).2.1 cy Z.2
  have I := integrated_native z.val (HX 0).1 (HX 0).2.1 cx cy Z.1 Z.2
  exact ⟨fun a => ⟨A.1 a,B.1 a⟩,fun h => ⟨A.2 h,B.2 h⟩,I.1,I.2,fun t => (HX t).2.2⟩

end
end ImbalancedChen.Part3.OriginalMarkedWeakAdjoint20261112
