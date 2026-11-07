import ImbalancedChen.Part3Gamma0ArbitrarySmoothWeakGradient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The global physical carrier gradient is identified against every arbitrary
compact smooth coordinate test supported in a legal carrier chart. The
comparison is through the proved local/global gradient agreement on the
actual intersection measure; no local-to-global equality is assumed.
The coordinate test may be nonseparable, and its real Frechet derivative
and canonical hyperbolic density weights remain literal.
-/

namespace ImbalancedChen.Part3.Gamma0CarrierSmoothWeakGradient20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0QuotientCellPushforward20261025a
open MaassWeakOperatorCore20261024zz
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CompactCoreGradient20261025a
open Gamma0EnergyCompactGradientExtension20261025a
open Gamma0CompletedGradientRestriction20261025a
open Gamma0EnergyGeometricWeakGradient20261025a
open Gamma0CarrierGradientHilbertMap20261026b
open Gamma0CarrierGradientExhaustion20261026b
open CompactC2ProductMollifier20261026a
open ArbitraryCompactFirstGradientIBP20261026b
open Gamma0ArbitrarySmoothWeakGradient20261026b

private theorem restrict_integral_eq_inter {f : UpperHalfPlane → ℂ}
    {s t : Set UpperHalfPlane} (hs : MeasurableSet s)
    (hz : ∀ z, z ∉ s → f z = 0) :
    (∫ z in t, f z) = ∫ z in s ∩ t, f z := by
  symm
  rw [← Measure.restrict_restrict hs]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hz

theorem completedCarrierGradient_eq_local_ae (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    completedCarrierGradient N e =ᵐ[(volume : Measure UpperHalfPlane).restrict
      (gamma0Carrier N ∩ K)] completedCompactGradient N hK e := by
  have hl := compactGradientRestriction_coe_ae
    (inter_subset_left : gamma0Carrier N ∩ K ⊆ gamma0Carrier N) (completedCarrierGradient N e)
  have hr := compactGradientRestriction_coe_ae
    (inter_subset_right : gamma0Carrier N ∩ K ⊆ K) (completedCompactGradient N hK e)
  rw [completedCarrierGradient_local_agreement N hK e] at hl
  exact hl.symm.trans hr

private theorem carrier_integrable_of_inter (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {f : UpperHalfPlane → ℂ}
    (hi : Integrable f ((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N ∩ K)))
    (hz : ∀ z, z ∉ K → f z = 0) : Integrable f (carrierVolume N) := by
  have hOn : IntegrableOn f K (carrierVolume N) := by
    change Integrable f (((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)).restrict K)
    rw [Measure.restrict_restrict hK.measurableSet,inter_comm]
    exact hi
  have hsupport : Function.support f ⊆ K := by
    intro z hzf
    by_contra hn
    exact hzf (hz z hn)
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hOn

theorem completed_carrier_smooth_products_integrable (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hTK : chartTestSupport ψ ⊆ K)
    (e : EnergyCompletion N) :
    Integrable (fun z => star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (physicalProjection N e) (orbitProjection N z) * (z.im : ℂ)^2) (carrierVolume N) ∧
    Integrable (fun z => star (ψ (z.re,z.im)) *
      (completedCarrierGradient N e) z (firstCoordinate vertical) * (z.im : ℂ))
        (carrierVolume N) := by
  obtain ⟨hL,hR⟩ := completed_arbitrary_smooth_products_integrable N hK vertical hψ e
  have hdom : (volume : Measure UpperHalfPlane).restrict (gamma0Carrier N ∩ K) ≤
      (volume : Measure UpperHalfPlane).restrict K := restrictedVolume_le inter_subset_right
  constructor
  · apply carrier_integrable_of_inter N hK (hL.mono_measure hdom)
    intro z hz
    have hn : (z.re,z.im) ∉ tsupport ψ := fun hp => hz (hTK hp)
    have hd : directional (coordinateDirection vertical) ψ (z.re,z.im) = 0 := by
      simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
    simp only [hd,star_zero,zero_mul]
  · have hi : Integrable (fun z => star (ψ (z.re,z.im)) *
        (completedCarrierGradient N e) z (firstCoordinate vertical) * (z.im : ℂ))
        ((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N ∩ K)) := by
      apply (hR.mono_measure hdom).congr
      filter_upwards [completedCarrierGradient_eq_local_ae N hK e] with z hz
      rw [hz]
    apply carrier_integrable_of_inter N hK hi
    intro z hz
    have hv : ψ (z.re,z.im) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hp => hz (hTK hp))
    simp only [hv,star_zero,zero_mul]

theorem completed_carrier_arbitrary_smooth_weak_derivative (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hTK : chartTestSupport ψ ⊆ K)
    (hTC : chartTestSupport ψ ⊆ gamma0Carrier N) (e : EnergyCompletion N) :
    (∫ z, star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (physicalProjection N e) (orbitProjection N z) * (z.im : ℂ)^2 ∂carrierVolume N) =
      -(∫ z, star (ψ (z.re,z.im)) *
        (completedCarrierGradient N e) z (firstCoordinate vertical) * (z.im : ℂ)
          ∂carrierVolume N) := by
  let L : UpperHalfPlane → ℂ := fun z =>
    star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (physicalProjection N e) (orbitProjection N z) * (z.im : ℂ)^2
  let R : UpperHalfPlane → ℂ := fun z => star (ψ (z.re,z.im)) *
    (completedCompactGradient N hK e) z (firstCoordinate vertical) * (z.im : ℂ)
  let Q : UpperHalfPlane → ℂ := fun z => star (ψ (z.re,z.im)) *
    (completedCarrierGradient N e) z (firstCoordinate vertical) * (z.im : ℂ)
  have hDz {S : Set UpperHalfPlane} (hT : chartTestSupport ψ ⊆ S)
      (z : UpperHalfPlane) (hz : z ∉ S) :
      directional (coordinateDirection vertical) ψ (z.re,z.im) = 0 := by
    have hn : (z.re,z.im) ∉ tsupport ψ := fun hp => hz (hT hp)
    simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
  have hVz {S : Set UpperHalfPlane} (hT : chartTestSupport ψ ⊆ S)
      (z : UpperHalfPlane) (hz : z ∉ S) : ψ (z.re,z.im) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hp => hz (hT hp))
  have hLc : (∫ z, L z ∂carrierVolume N) = ∫ z in gamma0Carrier N ∩ K, L z := by
    change (∫ z in gamma0Carrier N, L z) = _
    rw [restrict_integral_eq_inter hK.measurableSet
      (fun z hz => by simp only [L,hDz hTK z hz,star_zero,zero_mul])]
    rw [inter_comm]
  have hLk : (∫ z in K, L z) = ∫ z in gamma0Carrier N ∩ K, L z :=
    restrict_integral_eq_inter (gamma0Carrier_measurable N)
      (fun z hz => by simp only [L,hDz hTC z hz,star_zero,zero_mul])
  have hRk : (∫ z in K, R z) = ∫ z in gamma0Carrier N ∩ K, R z :=
    restrict_integral_eq_inter (gamma0Carrier_measurable N)
      (fun z hz => by simp only [R,hVz hTC z hz,star_zero,zero_mul])
  have hQc : (∫ z, Q z ∂carrierVolume N) = ∫ z in gamma0Carrier N ∩ K, Q z := by
    change (∫ z in gamma0Carrier N, Q z) = _
    rw [restrict_integral_eq_inter hK.measurableSet
      (fun z hz => by simp only [Q,hVz hTK z hz,star_zero,zero_mul])]
    rw [inter_comm]
  change (∫ z, L z ∂carrierVolume N) = -(∫ z, Q z ∂carrierVolume N)
  calc
    _ = ∫ z in gamma0Carrier N ∩ K, L z := hLc
    _ = -(∫ z in gamma0Carrier N ∩ K, R z) := by
      rw [← hLk,← hRk]
      exact completed_arbitrary_smooth_weak_derivative N hK vertical hψ hc hs hTK e
    _ = -(∫ z in gamma0Carrier N ∩ K, Q z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [completedCarrierGradient_eq_local_ae N hK e] with z hz
      simp only [R,Q,hz]
    _ = _ := congrArg Neg.neg hQc.symm

theorem actual_form_carrier_arbitrary_smooth_weak_derivative (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hTK : chartTestSupport ψ ⊆ K)
    (hTC : chartTestSupport ψ ⊆ gamma0Carrier N) (u : actualEnergyFormDomain N) :
    (∫ z, star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (u : QuotientL2 N) (orbitProjection N z) * (z.im : ℂ)^2 ∂carrierVolume N) =
      -(∫ z, star (ψ (z.re,z.im)) *
        (actualFormCarrierGradient N u) z (firstCoordinate vertical) * (z.im : ℂ)
          ∂carrierVolume N) := by
  simpa only [actualEnergyLift_projection,actualFormCarrierGradient] using
    completed_carrier_arbitrary_smooth_weak_derivative N hK vertical hψ hc hs hTK hTC
      (actualEnergyLift N u)

end
end ImbalancedChen.Part3.Gamma0CarrierSmoothWeakGradient20261026b
