import ImbalancedChen.Part3ActualResidualVolumeNormalization
import ImbalancedChen.Part3OriginalCuspidalPoincareTrace

/-! The rank-one residue and original compact packets on the same
quotient. The signed frequencies of both manuscript packets remove the
physical residual projection at its actual volume normalization. -/
namespace ImbalancedChen.Part3.OriginalResidualPoincarePackets20261110

noncomputable section
open Set Complex Matrix MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open Gamma0ActualConstantMode20261025a Gamma0QuotientCellPushforward20261025a
open NormalizedCuspCompactPoincare20261026b NormalizedCuspCompactFourierFubini20261026b
open ActualCharacterCuspExpansion20261110 ActualNativeResidualChannel20261110
open ActualResidualVolumeNormalization20261110 ActualContinuousPoincarePairing20261110
open OriginalContinuousPoincarePackets20261110 OriginalCuspidalPoincareTrace20261110
open OriginalSignedTraceInput20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalContinuousClassRemoval20261110 P3NativePeriod64SamplingSourceOnly (D4)

local instance (N : ℕ) [NeZero N] : IsFiniteMeasure (carrierPushforward N) :=
  ⟨carrierPushforward_finite N⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Every cusp's computed residue has exactly the physical Hilbert
projection normalization for the constant vector. -/
theorem actual_residual_projection (N : ℕ) [NeZero N] (a : NativeCusps N) (V : QuotientL2 N) :
    (ℂ ∙ constantL2 N).starProjection V =
      (nativeResidue N a*(∫ u,V u ∂carrierPushforward N)) • constantL2 N := by
  rw [Submodule.starProjection_singleton,constantL2_inner,constantL2_norm_sq,native_residue_inverse_volume]
  congr 1
  ring

private theorem constant_horizontal (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (hm : m ≠ 0)
    (y : ℝ) (hy : 0 < y) : frameFourier N (NeZero.pos N) g (fun _ => 1) m y = 0 := by
  rw [frameFourier_positive_height N _ g _ m hy]
  simp only [mul_one,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  have hC : AddCircle.fourierCoeff (AddCircle.fourier (T := (1 : ℝ)) (-m)) 0 = 0 := by
    simpa [Pi.single_apply,hm,Ne.symm hm] using congrFun (AddCircle.fourierCoeff_fourier (T := (1 : ℝ)) (-m)) 0
  have HI := AddCircle.fourierCoeff_eq_intervalIntegral (AddCircle.fourier (T := (1 : ℝ)) (-m)) 0 (0 : ℝ)
  simpa only [hC,neg_zero,AddCircle.fourier_zero,one_smul,zero_add,one_div_one] using HI.symm

private theorem seed_zero (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hp : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (∫ u,originalPoincare N one m ψ u ∂carrierPushforward N) = 0 := by
  have H : (∫ u,star (originalPoincare N one m ψ u) ∂carrierPushforward N) = 0 := by
    rw [original_eq_framed N one m ψ hc hp]
    have J := framePoincare_pairing_eq_fourier N (NeZero.pos N) (originalFrame one) m ψ hψ hc hp
      (fun _ => (1 : ℂ)) (constant_memLp_two N)
    simp only [mul_one] at J
    rw [J]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [constant_horizontal N (originalFrame one) m hm y hy]
    simp
  simpa only [Complex.star_def,← integral_conj,Complex.conj_conj,map_zero] using congrArg conj H

private theorem packet_zero (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ)
    (hn : ∀ b ∈ S, ind b ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hp : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (∫ u,packet N one S w ind ψ u ∂carrierPushforward N) = 0 := by
  have hI (b : ℕ) (hb : b ∈ S) : Integrable (fun u => star (w b)*
      originalPoincare N one (ind b) (scaledSeed (ind b) ψ) u) (carrierPushforward N) := by
    obtain ⟨h₁,h₂,h₃⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hp
    rw [original_eq_framed N one (ind b) _ h₂ h₃]
    exact ((framePoincare_memLp_two N _ _ _ _ h₁ h₂ h₃).integrable (by norm_num)).const_mul _
  rw [packet,integral_finsetSum S hI]
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨h₁,h₂,h₃⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hp
  rw [integral_const_mul,seed_zero N one (ind b) (hn b hb) _ h₁ h₂ h₃,mul_zero]

private theorem packet_projection (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ)
    (w : ℕ → ℂ) (ind : ℕ → ℤ) (hn : ∀ b ∈ S, ind b ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hp : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (ℂ ∙ constantL2 N).starProjection ((packet_L2 N one S w ind hn ψ hψ hc hp).toLp
      (packet N one S w ind ψ)) = 0 := by
  rw [actual_residual_projection N (nativeFrameOrbit N 1)]
  rw [integral_congr_ae (packet_L2 N one S w ind hn ψ hψ hc hp).coeFn_toLp,
    packet_zero N one S w ind hn ψ hψ hc hp,mul_zero,zero_smul]

/-- Both original packets have zero projection onto the physical residue
line. The signed n-index may be negative; it has positive absolute value
on its actual retained carrier. Every common m-box index is positive. -/
theorem original_residual_packets (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool)
    (J j : ℕ) (ell : D4 → ℤ) (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    (ℂ ∙ constantL2 z.val).starProjection (originalMVector z.val J j ell ψ hψ hcψ hpψ) = 0 ∧
      (ℂ ∙ constantL2 z.val).starProjection (originalNVector D r k z ha upper negativeM ell φ hφ hcφ hpφ) = 0 := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  constructor
  · have hn (m : ℕ) (hm : m ∈ commonMBlock J j) : (m : ℤ) ≠ 0 := by
      exact_mod_cast (lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) j) (Finset.mem_Ico.mp hm).1).ne'
    exact packet_projection z.val false (commonMBlock J j)
      (fun m => star ((commonPoissonCompleted J j (ell 1)).weight m)) (fun m => (m : ℤ))
      hn ψ hψ hcψ hpψ
  · exact packet_projection z.val true (nCarrier D k z.val) (traceBeta D r k upper negativeM ell z.val)
      (traceIndex D k negativeM z.val) (fun n hn => Int.natAbs_pos.mp
        (traceIndex_natAbs_pos D k negativeM z.val hn ha)) φ hφ hcφ hpφ

end
end ImbalancedChen.Part3.OriginalResidualPoincarePackets20261110
