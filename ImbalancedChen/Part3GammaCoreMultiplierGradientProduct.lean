import ImbalancedChen.Part3GammaCompletedGradientClassicalRepresentative
import ImbalancedChen.Part3GammaSmoothCoreMultiplierEnergyLift
import ImbalancedChen.Part3Gamma0CarrierSmoothWeakGradient

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual global carrier gradient is the literal classical weighted
gradient of a smooth physical representative. An explicit OPEN exhaustion
inside the existing compact exhaustion pays the local-to-global seam.
Applied to the independently constructed actual core multiplier energy
lift, this proves the full gradient product rule, including the derivative
of the multiplier. Form membership and value representation are supplied
by the genuine minimal graph; gradient equality is proved here.
-/

namespace ImbalancedChen.Part3.GammaCoreMultiplierGradientProduct20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0FiniteMeasureCarrier20261024z
open MaassWeakOperatorCore20261024zz Gamma0CompactGreenProductL120261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0CompactCoreGradient20261025a Gamma0EnergyCompactGradientExtension20261025a
open Gamma0EnergyGeometricWeakGradient20261025a Gamma0CompletedGradientRestriction20261025a
open Gamma0CompactQuotientMeasureDomination20261025a
open Gamma0CarrierGradientHilbertMap20261026b Gamma0CarrierGradientExhaustion20261026b
open Gamma0CarrierSmoothWeakGradient20261026b UpperHalfPlaneCompactExhaustion20261025a
open CompactC2ProductMollifier20261026a ArbitraryCompactFirstGradientIBP20261026b
open GammaCompletedGradientClassicalRepresentative20261026b
open GammaSmoothMultiplierPeriodization20261026a GammaNativeMaassLeibniz20261026a
open GammaSmoothCoreMultiplierEnergyLift20261026b ActualGamma0MaassDescent20261025a
open OneCompactFirstGradientIBP20261025a

def openCoordinateExhaustion (n : ℕ) : Set Plane :=
  {p | |p.1| < (n : ℝ) ∧ 1 / ((n : ℝ)+1) < p.2 ∧ p.2 < (n : ℝ)+1}

theorem openCoordinateExhaustion_isOpen (n : ℕ) : IsOpen (openCoordinateExhaustion n) :=
  (isOpen_lt continuous_fst.abs continuous_const).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const))

theorem openCoordinateExhaustion_positive (n : ℕ) :
    openCoordinateExhaustion n ⊆ positiveChart := by
  intro p hp
  exact (one_div_pos.mpr (show 0 < (n : ℝ)+1 by positivity)).trans hp.2.1

theorem openCoordinateExhaustion_lift_subset (n : ℕ) (z : UpperHalfPlane)
    (hz : (z.re,z.im) ∈ openCoordinateExhaustion n) :
    z ∈ hyperbolicCompactExhaustion n :=
  (mem_hyperbolicCompactExhaustion_iff n z).mpr ⟨hz.1.le,hz.2.1.le,hz.2.2.le⟩

theorem exists_mem_openCoordinateExhaustion (z : UpperHalfPlane) :
    ∃ n : ℕ, (z.re,z.im) ∈ openCoordinateExhaustion n := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max |z.re| (max z.im (1/z.im)))
  have hx : |z.re| < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hy : z.im < (n : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hinv : 1/z.im < (n : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  have hprod : 1 < (n : ℝ)*z.im := (div_lt_iff₀ z.im_pos).mp hinv
  refine ⟨n,hx,?_,by linarith⟩
  apply (div_lt_iff₀ (show 0 < (n : ℝ)+1 by positivity)).mpr
  nlinarith [z.im_pos]

def nativeWeightedGradient (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : GradientFiber :=
  !₂[(z.im : ℂ)*nativeDx F z,(z.im : ℂ)*nativeDy F z]

/-- No scalar quotient descent of the two components is asserted. They
are genuine physical carrier fields, with the true local covariance. -/
theorem completedCarrierGradient_eq_native (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (F : UpperHalfPlane → ℂ) (hFi : IsGammaInvariant N F)
    (hFs : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hrep : ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N] quotientMultiplier N F hFi) :
    completedCarrierGradient N e =ᵐ[carrierVolume N] nativeWeightedGradient F := by
  have hcomponent (vertical : Bool) : ∀ᵐ z ∂carrierVolume N,
      (completedCarrierGradient N e) z (firstCoordinate vertical) =
        (z.im : ℂ)*sliceFirst vertical (extendUpper F) (z.re,z.im) := by
    have hn (n : ℕ) : ∀ᵐ z ∂carrierVolume N, (z.re,z.im) ∈ openCoordinateExhaustion n →
        (completedCarrierGradient N e) z (firstCoordinate vertical) =
          (z.im : ℂ)*sliceFirst vertical (extendUpper F) (z.re,z.im) := by
      let K := hyperbolicCompactExhaustion n
      have hK : IsCompact K := hyperbolicCompactExhaustion_isCompact n
      have hrepK : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict K),
          (physicalProjection N e) (orbitProjection N z) = extendUpper F (z.re,z.im) := by
        filter_upwards [(orbitProjection_compact_quasiMeasurePreserving N hK).ae hrep] with z hz
        simpa only [quotientMultiplier_projection,extendUpper_pair] using hz
      have hlocal := completedCompactGradient_eq_classical_component N hK vertical e
        (openCoordinateExhaustion_isOpen n) (openCoordinateExhaustion_positive n)
        (openCoordinateExhaustion_lift_subset n) (extendUpper F) hFs hrepK
      have hsame : ∀ᵐ z ∂carrierVolume N, z ∈ K →
          completedCarrierGradient N e z = completedCompactGradient N hK e z := by
        have ha := completedCarrierGradient_eq_local_ae N hK e
        have ha' : ∀ᵐ z ∂(carrierVolume N).restrict K,
            completedCarrierGradient N e z = completedCompactGradient N hK e z := by
          simpa only [carrierVolume,Measure.restrict_restrict hK.measurableSet,inter_comm] using ha
        exact (ae_restrict_iff' hK.measurableSet).mp ha'
      filter_upwards [ae_restrict_of_ae hlocal,hsame] with z hz hs
      intro hzU
      rw [hs (openCoordinateExhaustion_lift_subset n z hzU),hz hzU,
        ← sliceFirst_eq_directional vertical (hFs.differentiableOn (by norm_num)) z.im_pos]
    have hall : ∀ᵐ z ∂carrierVolume N, ∀ n : ℕ, (z.re,z.im) ∈ openCoordinateExhaustion n →
        (completedCarrierGradient N e) z (firstCoordinate vertical) =
          (z.im : ℂ)*sliceFirst vertical (extendUpper F) (z.re,z.im) := ae_all_iff.mpr hn
    filter_upwards [hall] with z hz
    obtain ⟨n,hnz⟩ := exists_mem_openCoordinateExhaustion z
    exact hz n hnz
  filter_upwards [hcomponent false,hcomponent true] with z hx hy
  ext i
  fin_cases i
  · simpa [firstCoordinate,nativeWeightedGradient,nativeDx,sliceFirst] using hx
  · simpa [firstCoordinate,nativeWeightedGradient,nativeDy,sliceFirst] using hy

theorem nativeWeightedGradient_mul (chi F : UpperHalfPlane → ℂ)
    (hcs : ContDiffOn ℝ 2 (extendUpper chi) positiveChart)
    (hFs : ContDiffOn ℝ 2 (extendUpper F) positiveChart) (z : UpperHalfPlane) :
    nativeWeightedGradient (chi*F) z =
      chi z • nativeWeightedGradient F z + F z • nativeWeightedGradient chi z := by
  ext i
  fin_cases i <;>
    simp only [nativeWeightedGradient,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,nativeDx_mul chi F hcs hFs,
      nativeDy_mul chi F hcs hFs] <;> ring

/-- The actual fixed-scale core multiplier has the genuine global
gradient product rule. Its form-domain membership comes from the native
minimal graph; neither this identity nor an energy bound is assumed. -/
theorem coreMultiplierEnergyLift_gradient_product (N : ℕ) [NeZero N]
    (u : smoothCore N) (chi : UpperHalfPlane → ℂ) (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    completedCarrierGradient N (coreMultiplierEnergyLift N u chi hc hcs) =ᵐ[carrierVolume N]
      (fun z => chi z • weightedCoreGradient N u z +
        coreRepresentative N u z • nativeWeightedGradient chi z) := by
  have hprod : ContDiffOn ℝ 2 (extendUpper (chi*coreRepresentative N u)) positiveChart := by
    rw [extendUpper_mul]
    exact (hcs.of_le (by simp)).mul ((coreRepresentative_cinfty N u).of_le (by simp))
  have he := completedCarrierGradient_eq_native N (coreMultiplierEnergyLift N u chi hc hcs)
    (chi*coreRepresentative N u) (smoothCoreProduct_invariant N u chi hc) hprod
    (coreMultiplierEnergyLift_smooth_representative_ae N u chi hc hcs)
  filter_upwards [he] with z hz
  rw [hz,nativeWeightedGradient_mul chi (coreRepresentative N u)
    (hcs.of_le (by simp)) ((coreRepresentative_cinfty N u).of_le (by simp))]
  rfl

end
end ImbalancedChen.Part3.GammaCoreMultiplierGradientProduct20261026b
