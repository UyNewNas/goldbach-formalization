import ImbalancedChen.Part3ActualContinuousPhysicalComplement
import ImbalancedChen.Part3OriginalMarkedWeakAdjoint
import ImbalancedChen.Part3OriginalCuspidalPoincareTrace

/-! The actual projected continuous covariance and the complete spatial
pairing of the two original marked weight-zero packets. -/
namespace ImbalancedChen.Part3.OriginalProjectedContinuousCovariance20261112

noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualContinuousPhysicalComplement20261112 ActualContinuousResolution20261112
open ActualMarkedContinuousCoordinates20261112 OriginalMarkedWeakAdjoint20261112
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open AllNormalizedCuspAnnihilator20261026b ActualFullCuspResolvent20261026b
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110
open ActualOrdinaryContinuousModes20261110 ActualContinuousClassFourier20261110
open ActualYoungFormalClass20261110 OriginalNativeCuspFunctionals20261102
open OriginalContinuousPoincarePackets20261110 OriginalContinuousCuspGram20261110
open OriginalCuspidalPoincareTrace20261110 OriginalResidualPoincarePackets20261110
open OriginalContinuousClassRemoval20261110 OriginalSimultaneousPrefixCompletion20261102
open OriginalSignedTraceInput20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 P3NativePeriod64SamplingSourceOnly (D4)

local instance cuspComplete (N : ℕ) [NeZero N] : CompleteSpace (allFrameCuspSubspace N (NeZero.pos N)) :=
  (allFrameCuspSubspace_closed N _).completeSpace_coe

/-- The three spatial components of the actual quotient Hilbert vector. -/
theorem physical_split (N : ℕ) [NeZero N] (v : QuotientL2 N) :
    v=(ℂ ∙ constantL2 N).starProjection v+(allFrameCuspSubspace N (NeZero.pos N)).starProjection v+
      (centeredSpace N).starProjection v := by
  let C := ℂ ∙ constantL2 N
  let D := allFrameCuspSubspace N (NeZero.pos N)
  let e := C.starProjection v
  let d := D.starProjection v
  let r := v-e-d
  have he : e ∈ C := C.starProjection_apply_mem v
  have hd : d ∈ D := D.starProjection_apply_mem v
  have hC : C ≤ Dᗮ := fun c hc w hw => inner_eq_zero_symm.mp ((cusp_le_constant_perp N hw) c hc)
  have hr : r ∈ centeredSpace N := by
    rw [centered_eq_physical_complement]
    refine ⟨Cᗮ.sub_mem (C.sub_starProjection_mem_orthogonal v) (cusp_le_constant_perp N hd),?_⟩
    have E : r=v-d-e := by dsimp [r]; abel
    rw [E]
    exact Dᗮ.sub_mem (D.sub_starProjection_mem_orthogonal v) (hC he)
  have hz : v-r ∈ (centeredSpace N)ᗮ := by
    intro w hw
    rw [centered_eq_physical_complement] at hw
    have E : v-r=e+d := by dsimp [r]; abel
    rw [E,inner_add_right,inner_eq_zero_symm.mp (hw.1 e he),inner_eq_zero_symm.mp (hw.2 d hd),add_zero]
  have P := (centeredSpace N).eq_starProjection_of_mem_orthogonal hr hz
  change v=e+d+(centeredSpace N).starProjection v
  rw [P]
  dsimp only [r]
  abel

private theorem projected_inner {N : ℕ} [NeZero N] (K : Submodule ℂ (QuotientL2 N))
    [K.HasOrthogonalProjection] (v w : QuotientL2 N) :
    inner ℂ v (K.starProjection w)=inner ℂ (K.starProjection v) (K.starProjection w) := by
  have H := K.starProjection_inner_eq_zero v (K.starProjection w) (K.starProjection_apply_mem w)
  rwa [inner_sub_left,sub_eq_zero] at H

theorem spatial_orthogonal_gram (N : ℕ) [NeZero N] (v w : QuotientL2 N) :
    let C := ℂ ∙ constantL2 N
    let D := allFrameCuspSubspace N (NeZero.pos N)
    inner ℂ v w = inner ℂ (C.starProjection v) (C.starProjection w)+
      inner ℂ (D.starProjection v) (D.starProjection w)+
      (1/2 : ℂ)*∑ a : Parameters N,inner ℂ (analysis N a v) (analysis N a w) := by
  dsimp only
  calc
    _ = inner ℂ v ((ℂ ∙ constantL2 N).starProjection w+(allFrameCuspSubspace N (NeZero.pos N)).starProjection w+
        (centeredSpace N).starProjection w) := congrArg (inner ℂ v) (physical_split N w)
    _ = _ := by
      rw [inner_add_right,inner_add_right,projected_inner (ℂ ∙ constantL2 N),
        projected_inner (allFrameCuspSubspace N (NeZero.pos N)),projected_inner (centeredSpace N),
        continuous_projection_gram]

/-- The continuous original native product is absolutely integrable and
equals the Gram of the two orthogonally projected original packets. The
space pairing also includes the original complete discrete cuspidal sum,
with its genuine order, signed functionals and common radial probes. -/
theorem original_projected_trace (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let hN := NeZero.pos z.val
    let X := mPacket z.val J j ell ψ
    let Y := nPacket D r k z upper negativeM ell φ
    let v := originalMVector z.val J j ell ψ hψ hcψ hpψ
    let w := originalNVector D r k z ha upper negativeM ell φ hφ hcφ hpφ
    let P := (centeredSpace z.val).starProjection
    let G := fun t => nativeProduct z.val (fun a => spectrum z.val X a t) (fun a => spectrum z.val Y a t)
    let F := fun i : actualCuspBasisIndex z.val hN =>
      (star (orderProbe 1 ψ (basisOrder z.val hN i))*orderProbe 1 φ (basisOrder z.val hN i))*
        (star (originalMFunctional J j ell z.val hN i)*originalNFunctional D r k upper negativeM ell z.val hN i)
    Integrable G ∧ inner ℂ (P w) (P v) = ∫ t,G t ∧
    HasSum F (inner ℂ (project z.val w) (project z.val v)) ∧ inner ℂ w v = (∑' i,F i)+(∫ t,G t) ∧
    (∀ t, G t=(star (radialProbe 1 ψ t)*radialProbe 1 φ t)*
      classProduct z.val (fun i => M J j ell (fun n => channelR i false n t))
        (fun i => source D r k z upper negativeM ell (fun n => channelR i true n t))) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let v := originalMVector z.val J j ell ψ hψ hcψ hpψ
  let w := originalNVector D r k z ha upper negativeM ell φ hφ hcφ hpφ
  let P := (centeredSpace z.val).starProjection
  let G := fun t => nativeProduct z.val (fun a => spectrum z.val (mPacket z.val J j ell ψ) a t)
    (fun a => spectrum z.val (nPacket D r k z upper negativeM ell φ) a t)
  have W := original_marked_weak D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ
  have J : inner ℂ (P w) (P v) = ∫ t,G t := by
    rw [← projected_inner (centeredSpace z.val) w v,← nativeSynthesis_analysis_eq_projection]
    exact W.2.2.2.1
  have S := original_cuspidal_trace D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ
  have Z := original_residual_packets D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ
  refine ⟨W.2.2.1,J,S,?_,W.2.2.2.2⟩
  have H := spatial_orthogonal_gram z.val w v
  dsimp only at H
  rw [Z.2,Z.1,inner_zero_left,zero_add,← continuous_projection_gram,J] at H
  rw [S.tsum_eq]
  exact H

end
end ImbalancedChen.Part3.OriginalProjectedContinuousCovariance20261112
