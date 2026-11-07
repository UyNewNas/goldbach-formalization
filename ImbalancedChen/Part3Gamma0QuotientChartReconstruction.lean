import ImbalancedChen.Part3Gamma0FiniteChartReconstruction
import ImbalancedChen.Part3Gamma0QuotientL2Equivalence

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport of the actual finite chart reconstruction to the genuine Gamma0
orbit quotient and its original carrierPushforward measure. The measurable
reduced-carrier embedding supplies the quotient extension; no abstract
quotient section, reconstruction bound, or compact embedding is assumed.
The resulting error is bounded by the literal finite actual chart errors.

OPEN: local energy-controlled rectangle approximations for these pullbacks;
identification of all actual cusp zero modes and widths with the physical
closed graphs; and the final quotient L2 compact embedding.
-/

namespace ImbalancedChen.Part3.Gamma0QuotientChartReconstruction20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators ENNReal
open Gamma0FiniteChartReconstruction20261026b
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientL2Equivalence20261025a

def quotientCore (N : ℕ) [NeZero N] (Y : ℝ) : Set (Gamma0OrbitSpace N) :=
  reducedProjection N '' {z : reducedCarrier N | (z : UpperHalfPlane) ∈ core N Y}

theorem quotientCore_measurable (N : ℕ) [NeZero N] (Y : ℝ) :
    MeasurableSet (quotientCore N Y) :=
  (reducedProjection_measurableEmbedding N).measurableSet_image.mpr
    (measurable_subtype_coe (core_measurable N Y))

theorem quotientCore_projection_iff (N : ℕ) [NeZero N] (Y : ℝ)
    (z : reducedCarrier N) :
    reducedProjection N z ∈ quotientCore N Y ↔ (z : UpperHalfPlane) ∈ core N Y := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact ((reducedProjection_measurableEmbedding N).injective heq) ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

def quotientReconstruct (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) : Gamma0OrbitSpace N → ℂ :=
  quotientZeroExtension N (fun z => reconstruct N Y v (z : UpperHalfPlane))

theorem quotientReconstruct_projection (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (z : reducedCarrier N) :
    quotientReconstruct N Y v (reducedProjection N z) =
      reconstruct N Y v (z : UpperHalfPlane) :=
  quotientZeroExtension_projection N _ z

theorem reconstruct_measurable (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i)) :
    Measurable (reconstruct N Y v) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact ((hv i).comp (chartCoordinate_continuous N i).measurable).indicator
    (chartPiece_measurable N Y i)

theorem quotientReconstruct_measurable (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i)) :
    Measurable (quotientReconstruct N Y v) :=
  (reducedProjection_measurableEmbedding N).measurable_extend
    ((reconstruct_measurable N Y v hv).comp measurable_subtype_coe) measurable_const

/-- Exact reconstruction for every quotient function, with zero outside
the actual reduced-carrier compact chart image. -/
theorem quotientReconstruct_actual_pullbacks (N : ℕ) [NeZero N] (Y : ℝ)
    (F : Gamma0OrbitSpace N → ℂ) :
    quotientReconstruct N Y
      (fun i w => F (orbitProjection N (chartMatrix N i • w))) =
        (quotientCore N Y).indicator F := by
  classical
  funext q
  by_cases hq : q ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hq
    rw [quotientReconstruct_projection, reconstruct_actual_pullbacks]
    by_cases hz : (z : UpperHalfPlane) ∈ core N Y
    · rw [indicator_of_mem hz,
        indicator_of_mem ((quotientCore_projection_iff N Y z).mpr hz)]
    · rw [indicator_of_notMem hz,
        indicator_of_notMem (fun h => hz ((quotientCore_projection_iff N Y z).mp h))]
  · rw [quotientReconstruct, quotientZeroExtension_off_image N _ hq]
    apply (indicator_of_notMem _ _).symm
    rintro ⟨z, _, hz⟩
    exact hq ⟨z, hz⟩

/-- The genuine quotient error budget. The source and target measures are
the original hyperbolic carrier and its proved quotient pushforward.
There is no assumed norm comparison and no dropped finite index. -/
theorem quotient_reconstruction_square_error_budget (N : ℕ) [NeZero N] (Y : ℝ)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i)) :
    (∫⁻ q in quotientCore N Y,
      ENNReal.ofReal (‖F q - quotientReconstruct N Y v q‖ ^ 2)
        ∂carrierPushforward N) ≤
      ∑ i : ChartIndex N, ∫⁻ z in rawChartCell N Y i,
        ENNReal.ofReal
          (‖F (orbitProjection N z) - v i (chartCoordinate N i z)‖ ^ 2) := by
  let err : Gamma0OrbitSpace N → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (‖F q - quotientReconstruct N Y v q‖ ^ 2)
  let physicalErr : UpperHalfPlane → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (‖F (orbitProjection N z) - reconstruct N Y v z‖ ^ 2)
  have herr : Measurable err := by
    exact ((hF.sub (quotientReconstruct_measurable N Y v hv)).norm.pow_const 2).ennreal_ofReal
  calc
    _ = ∫⁻ z in reducedCarrier N,
        ((quotientCore N Y).indicator err) (orbitProjection N z) := by
      rw [← lintegral_indicator (quotientCore_measurable N Y)]
      exact lintegral_reducedCarrier N _ (herr.indicator (quotientCore_measurable N Y))
    _ = ∫⁻ z in reducedCarrier N, (core N Y).indicator physicalErr z := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (reducedCarrier_measurable N)] with z hz
      let w : reducedCarrier N := ⟨z, hz⟩
      have hext := quotientReconstruct_projection N Y v w
      by_cases hcore : z ∈ core N Y
      · rw [indicator_of_mem ((quotientCore_projection_iff N Y w).mpr hcore),
          indicator_of_mem hcore]
        dsimp [err, physicalErr]
        rw [show quotientReconstruct N Y v (orbitProjection N z) =
          reconstruct N Y v z from hext]
      · rw [indicator_of_notMem (fun h => hcore ((quotientCore_projection_iff N Y w).mp h)),
          indicator_of_notMem hcore]
    _ = ∫⁻ z in core N Y ∩ reducedCarrier N, physicalErr z := by
      rw [lintegral_indicator (core_measurable N Y),
        Measure.restrict_restrict (core_measurable N Y)]
    _ ≤ ∫⁻ z in core N Y, physicalErr z := lintegral_mono_set inter_subset_left
    _ ≤ _ := reconstruction_square_error_budget N Y (F ∘ orbitProjection N) v volume

theorem quotientReconstruct_outside_core (N : ℕ) [NeZero N] (Y : ℝ)
    (v : ChartIndex N → UpperHalfPlane → ℂ) {q : Gamma0OrbitSpace N}
    (hq : q ∉ quotientCore N Y) : quotientReconstruct N Y v q = 0 := by
  by_cases himage : q ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := himage
    rw [quotientReconstruct_projection]
    exact reconstruct_outside_core N Y v
      (fun hz => hq ((quotientCore_projection_iff N Y z).mpr hz))
  · exact quotientZeroExtension_off_image N _ himage

/-- The global error has precisely the finite chart error plus the actual
quotient tail mass. The tail remains visible, so a single infinity-cusp
estimate cannot silently replace an all-cusps estimate. -/
theorem global_reconstruction_square_error_budget (N : ℕ) [NeZero N] (Y : ℝ)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i)) :
    (∫⁻ q, ENNReal.ofReal (‖F q - quotientReconstruct N Y v q‖ ^ 2)
        ∂carrierPushforward N) ≤
      (∑ i : ChartIndex N, ∫⁻ z in rawChartCell N Y i,
        ENNReal.ofReal
          (‖F (orbitProjection N z) - v i (chartCoordinate N i z)‖ ^ 2)) +
      ∫⁻ q in (quotientCore N Y)ᶜ, ENNReal.ofReal (‖F q‖ ^ 2)
        ∂carrierPushforward N := by
  have htail : (∫⁻ q in (quotientCore N Y)ᶜ,
      ENNReal.ofReal (‖F q - quotientReconstruct N Y v q‖ ^ 2)
        ∂carrierPushforward N) =
      ∫⁻ q in (quotientCore N Y)ᶜ, ENNReal.ofReal (‖F q‖ ^ 2)
        ∂carrierPushforward N := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (quotientCore_measurable N Y).compl] with q hq
    rw [quotientReconstruct_outside_core N Y v hq, sub_zero]
  rw [← lintegral_add_compl _ (quotientCore_measurable N Y), htail]
  exact add_le_add_right (quotient_reconstruction_square_error_budget N Y F hF v hv) _

end
end ImbalancedChen.Part3.Gamma0QuotientChartReconstruction20261026b
