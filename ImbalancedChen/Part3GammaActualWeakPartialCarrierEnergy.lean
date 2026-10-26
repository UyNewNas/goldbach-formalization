import ImbalancedChen.Part3GammaActualFormWholeChartH1
import ImbalancedChen.Part3Gamma0CarrierSmoothWeakGradient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The genuine ordinary weak partials constructed from the local completed
gradient represent the SAME native carrier gradient. Positive height is
cancelled pointwise; local/global agreement is used only on the true
intersection measure. Their literal coordinate energy on compact carrier
pieces exhausts the existing form energy. Neither the gradient identity,
energy identity, nor scalar descent of either component is an input.
-/

namespace ImbalancedChen.Part3.GammaActualWeakPartialCarrierEnergy20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0FiniteMeasureCarrier20261024z Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CompactCoreGradient20261025a Gamma0EnergyGeometricWeakGradient20261025a
open Gamma0CarrierGradientHilbertMap20261026b Gamma0CarrierGradientExhaustion20261026b
open Gamma0CarrierSmoothWeakGradient20261026b
open GammaCompletedGradientClassicalRepresentative20261026b
open UpperHalfPlaneCompactExhaustion20261025a

def localWeakPartialEnergy (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (e : EnergyCompletion N) (z : UpperHalfPlane) : ℝ :=
  z.im^2 * (‖planarCompletedPartial N hK false e (z.re,z.im)‖^2 +
    ‖planarCompletedPartial N hK true e (z.re,z.im)‖^2)

/-- Native carrier components are the height-weighted ACTUAL weak
partials, on the legitimate carrier/local-chart intersection. -/
theorem completedCarrierGradient_eq_height_partial (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N)
    (vertical : Bool) :
    ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N ∩ K)),
      (completedCarrierGradient N e) z (firstCoordinate vertical) =
        (z.im : ℂ) * planarCompletedPartial N hK vertical e (z.re,z.im) := by
  have hmem := ae_restrict_mem ((gamma0Carrier_measurable N).inter hK.measurableSet)
  filter_upwards [completedCarrierGradient_eq_local_ae N hK e,hmem] with z hz hzin
  have hp := planarCompletedPartial_at_upper N hK vertical e z
  rw [Set.indicator_of_mem hzin.2] at hp
  rw [hz,hp]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt z.im_pos)
  rw [← mul_assoc,mul_inv_cancel₀ hy,one_mul]

theorem carrier_gradient_norm_sq_eq_weak_partials (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    (fun z => ‖completedCarrierGradient N e z‖^2) =ᵐ[
      (volume : Measure UpperHalfPlane).restrict (gamma0Carrier N ∩ K)]
      localWeakPartialEnergy N hK e := by
  filter_upwards [completedCarrierGradient_eq_height_partial N hK e false,
    completedCarrierGradient_eq_height_partial N hK e true] with z hx hy
  change (completedCarrierGradient N e) z 0 = _ at hx
  change (completedCarrierGradient N e) z 1 = _ at hy
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,hx,hy]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos,mul_pow]
  unfold localWeakPartialEnergy
  ring

/-- The literal coordinate energy density is honest L1, through its
proved AE identification with the actual native L2 gradient density. -/
theorem localWeakPartialEnergy_integrableOn (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    IntegrableOn (localWeakPartialEnergy N hK e) K (carrierVolume N) := by
  have h : IntegrableOn (fun z => ‖completedCarrierGradient N e z‖^2) K (carrierVolume N) :=
    (completedCarrierGradient_integrable_norm_sq N e).integrableOn
  change Integrable _ (((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)).restrict K) at h ⊢
  rw [Measure.restrict_restrict hK.measurableSet,inter_comm] at h ⊢
  exact h.congr (carrier_gradient_norm_sq_eq_weak_partials N hK e)

theorem compact_carrier_energy_eq_weak_partials (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    (∫ z in K, ‖completedCarrierGradient N e z‖^2 ∂carrierVolume N) =
      ∫ z in K, localWeakPartialEnergy N hK e z ∂carrierVolume N := by
  change (∫ z, _ ∂(((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)).restrict K)) =
    ∫ z, _ ∂(((volume : Measure UpperHalfPlane).restrict (gamma0Carrier N)).restrict K)
  rw [Measure.restrict_restrict hK.measurableSet,inter_comm]
  exact integral_congr_ae (carrier_gradient_norm_sq_eq_weak_partials N hK e)

/-- Literal ordinary-coordinate weak partial energies, using the SAME
energy vector on each explicit compact piece, recover full form energy. -/
theorem weak_partial_energy_exhaustion (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n : ℕ => ∫ z in hyperbolicCompactExhaustion n,
      localWeakPartialEnergy N (hyperbolicCompactExhaustion_isCompact n) e z
        ∂carrierVolume N) atTop (𝓝 ((actualDirichletPair N e e).re)) := by
  have heq : (fun n : ℕ => ∫ z in hyperbolicCompactExhaustion n,
      localWeakPartialEnergy N (hyperbolicCompactExhaustion_isCompact n) e z ∂carrierVolume N) =
      (fun n : ℕ => ∫ z in hyperbolicCompactExhaustion n,
        ‖completedCarrierGradient N e z‖^2 ∂carrierVolume N) := by
    funext n
    exact (compact_carrier_energy_eq_weak_partials N (hyperbolicCompactExhaustion_isCompact n) e).symm
  rw [heq]
  exact carrier_gradient_energy_exhaustion N e

end
end ImbalancedChen.Part3.GammaActualWeakPartialCarrierEnergy20261026b
