import ImbalancedChen.Part3Gamma0CarrierGradientHilbertMap
import ImbalancedChen.Part3UpperHalfPlaneCompactExhaustion
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The global carrier gradient agrees with the already represented local weak
gradient on every compact chart, on their actual common restricted measure.
The global physical gradient integral is exactly the actual closed form.
Its integrals over the explicit positive-height compact exhaustion converge
to that energy. Neither global energy identity nor exhaustion convergence
is a caller premise. Individual components are not scalar quotient fields.
-/

namespace ImbalancedChen.Part3.Gamma0CarrierGradientExhaustion20261026b
noncomputable section
open Set Filter MeasureTheory UniformSpace
open scoped UpperHalfPlane
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CompactCoreGradient20261025a
open Gamma0EnergyCompactGradientExtension20261025a
open Gamma0CompletedGradientRestriction20261025a
open Gamma0CarrierGradientHilbertMap20261026b
open UpperHalfPlaneCompactExhaustion20261025a

/-- Agreement on the physical part of each compact chart is proved from
the SAME literal core gradients and continuity of their two extensions. -/
theorem completedCarrierGradient_local_agreement (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    compactGradientRestriction (inter_subset_left : gamma0Carrier N ∩ K ⊆ gamma0Carrier N)
        (completedCarrierGradient N e) =
      compactGradientRestriction (inter_subset_right : gamma0Carrier N ∩ K ⊆ K)
        (completedCompactGradient N hK e) := by
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_eq
      ((compactGradientRestriction
        (inter_subset_left : gamma0Carrier N ∩ K ⊆ gamma0Carrier N)).continuous.comp
          (completedCarrierGradient N).continuous)
      ((compactGradientRestriction
        (inter_subset_right : gamma0Carrier N ∩ K ⊆ K)).continuous.comp
          (completedCompactGradient N hK).continuous)
  · intro u
    rw [completedCarrierGradient_core, completedCompactGradient_core]
    apply Lp.ext
    have hACc : (volume : Measure UpperHalfPlane).restrict (gamma0Carrier N ∩ K) ≪
        carrierVolume N :=
      Measure.absolutelyContinuous_of_le (restrictedVolume_le inter_subset_left)
    have hACk : (volume : Measure UpperHalfPlane).restrict (gamma0Carrier N ∩ K) ≪
        (volume : Measure UpperHalfPlane).restrict K :=
      Measure.absolutelyContinuous_of_le (restrictedVolume_le inter_subset_right)
    have hc := hACc.ae_eq (carrierCoreGradient_coe_ae N u)
    have hk := hACk.ae_eq (weightedCoreGradient_compact_memLp N hK u).coeFn_toLp
    exact ((compactGradientRestriction_coe_ae inter_subset_left _).trans hc).trans
      (((compactGradientRestriction_coe_ae inter_subset_right _).trans hk).symm)

theorem completedCarrierGradient_integrable_norm_sq (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    Integrable (fun z => ‖completedCarrierGradient N e z‖ ^ 2) (carrierVolume N) :=
  (Lp.memLp (completedCarrierGradient N e)).integrable_norm_pow (by decide)

/-- Exact physical gradient energy beyond the smooth core, with the
canonical carrier measure defining the existing quotient L2. -/
theorem actualDirichletPair_eq_carrier_gradient_integral (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    (actualDirichletPair N e e).re =
      ∫ z, ‖completedCarrierGradient N e z‖ ^ 2 ∂carrierVolume N := by
  rw [← completedCarrierGradient_norm_sq]
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    L2.inner_def (𝕜 := ℂ) (completedCarrierGradient N e) (completedCarrierGradient N e)

/-- Explicit compact exhaustion recovers the full unshifted form energy.
The exhaustion is |x|≤n, 1/(n+1)≤y≤n+1, rather than a target limit input. -/
theorem carrier_gradient_energy_exhaustion (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    Tendsto (fun n : ℕ => ∫ z in hyperbolicCompactExhaustion n,
      ‖completedCarrierGradient N e z‖ ^ 2 ∂carrierVolume N) atTop
      (𝓝 ((actualDirichletPair N e e).re)) := by
  have hi : IntegrableOn (fun z => ‖completedCarrierGradient N e z‖ ^ 2)
      (⋃ n : ℕ, hyperbolicCompactExhaustion n) (carrierVolume N) :=
    (completedCarrierGradient_integrable_norm_sq N e).integrableOn
  have ht := tendsto_setIntegral_of_monotone
    hyperbolicCompactExhaustion_measurableSet hyperbolicCompactExhaustion_mono hi
  simpa only [iUnion_hyperbolicCompactExhaustion, setIntegral_univ,
    ← actualDirichletPair_eq_carrier_gradient_integral N e] using ht

/-- The statement applies to every point of the original physical form
domain through its unique native lift, with no operator-domain premise. -/
theorem actual_form_energy_exhaustion (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    Tendsto (fun n : ℕ => ∫ z in hyperbolicCompactExhaustion n,
      ‖actualFormCarrierGradient N u z‖ ^ 2 ∂carrierVolume N) atTop
      (𝓝 ((actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re)) :=
  carrier_gradient_energy_exhaustion N (actualEnergyLift N u)

end
end ImbalancedChen.Part3.Gamma0CarrierGradientExhaustion20261026b
