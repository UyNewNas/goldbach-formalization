import ImbalancedChen.Part3ActualRadialEnergySquareRootRange
import ImbalancedChen.Part3GenericResolventContinuousMultipliers
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The maximal actual radial closed-form domain on EVERY genuine cyclic
scalar block. Physical U*xi belongs to the original closed radial form
range iff xi/sqrt(t) belongs to the actual scalar L2 space. The proof
uses the constructed actual polar unitary, continuous sqrt(t) CFC and
the adjoint of the cyclic isometry; no assumed reverse invariant-domain
property is used. The full shifted form norm equals ||xi/sqrt(t)||_2.
The unshifted sqrt(lambda) reformulation is isolated downstream.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open Set MeasureTheory
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventContinuousMultipliers20261025a

def radialSqrtCoordinateReal : C(RadialBoundedSpectrum, ℝ) :=
  ⟨fun t => Real.sqrt (t : ℝ), Real.continuous_sqrt.comp continuous_subtype_val⟩

def radialSqrtCoordinate : C(RadialBoundedSpectrum, ℂ) :=
  complexOfReal radialUnitShiftResolvent radialSqrtCoordinateReal

def radialScalarSquareRoot (F : RadialL2) : RadialScalarL2 F →L[ℂ] RadialScalarL2 F :=
  continuousMultiplier radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint
    radialSqrtCoordinate F

theorem radialScalarSquareRoot_coe_ae (F : RadialL2) (ξ : RadialScalarL2 F) :
    radialScalarSquareRoot F ξ =ᵐ[radialBoundedScalarMeasure F]
      (fun t => (Real.sqrt (t : ℝ) : ℂ) * ξ t) :=
  continuousMultiplier_coe_ae radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialSqrtCoordinate F ξ

theorem radialResolventSquareRoot_eq_cyclicCFC :
    radialResolventSquareRoot = complexResolventCFC radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint radialSqrtCoordinate := by
  rw [radialSqrtCoordinate, complexResolventCFC_ofReal]
  change CFC.sqrt radialUnitShiftResolvent =
    resolventCFC radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint
      radialSqrtCoordinateReal
  rw [CFC.sqrt_eq_real_sqrt radialUnitShiftResolvent radialUnitShiftResolvent_nonneg,
    cfcₙ_eq_cfc]
  exact cfc_apply Real.sqrt radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint Real.continuous_sqrt.continuousOn

theorem radialScalarSquareRoot_intertwine (F : RadialL2) (ξ : RadialScalarL2 F) :
    cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F
      (radialScalarSquareRoot F ξ) =
        radialResolventSquareRoot
          (cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) := by
  rw [radialResolventSquareRoot_eq_cyclicCFC]
  exact cyclicExtension_continuous_intertwine radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialSqrtCoordinate F ξ

theorem radialScalarSquareRoot_inner (F : RadialL2) (ξ η : RadialScalarL2 F) :
    inner ℂ (radialScalarSquareRoot F ξ) η = inner ℂ ξ (radialScalarSquareRoot F η) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radialScalarSquareRoot_coe_ae F ξ,
    radialScalarSquareRoot_coe_ae F η] with t hξ hη
  rw [hξ, hη]
  simp only [RCLike.inner_apply', star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem radialCyclicExtension_adjoint_left_inverse (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    (cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F).adjoint
      (cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) = ξ := by
  apply ext_inner_left ℂ
  intro η
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (cyclicIsometry radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint F).inner_map_map η ξ

theorem radialScalarSquareRoot_adjoint_intertwine (F G : RadialL2) :
    radialScalarSquareRoot F
      ((cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F).adjoint G) =
    (cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F).adjoint
      (radialResolventSquareRoot G) := by
  apply ext_inner_left ℂ
  intro ξ
  rw [← radialScalarSquareRoot_inner,
    ContinuousLinearMap.adjoint_inner_right,
    radialScalarSquareRoot_intertwine,
    radialResolventSquareRoot_selfAdjoint.isSymmetric,
    ContinuousLinearMap.adjoint_inner_right]

def radialInverseSqrtProduct (F : RadialL2) (ξ : RadialScalarL2 F)
    (t : RadialBoundedSpectrum) : ℂ :=
  ((Real.sqrt (t : ℝ) : ℂ))⁻¹ * ξ t

/-- The TRUE physical square-root range criterion on an arbitrary actual
cyclic block. The preimage need not initially be assumed cyclic. -/
theorem radialSquareRoot_range_iff_inverseSqrtMemLp (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    (∃ G : RadialL2, radialResolventSquareRoot G =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) ↔
    MemLp (radialInverseSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F) := by
  constructor
  · rintro ⟨G, hG⟩
    let η := (cyclicExtension radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint F).adjoint G
    have hM : radialScalarSquareRoot F η = ξ := by
      rw [radialScalarSquareRoot_adjoint_intertwine, hG,
        radialCyclicExtension_adjoint_left_inverse]
    have hae : radialInverseSqrtProduct F ξ =ᵐ[radialBoundedScalarMeasure F] η := by
      have hm := radialScalarSquareRoot_coe_ae F η
      rw [hM] at hm
      filter_upwards [hm, radialBoundedScalarMeasure_ae_strict_unitInterval F] with t ht hp
      have hs : (Real.sqrt (t : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hp.1)
      change (Real.sqrt (t : ℝ) : ℂ)⁻¹ * ξ t = η t
      rw [ht, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    exact (memLp_congr_ae hae).mpr (Lp.memLp η)
  · intro hξ
    let η : RadialScalarL2 F := hξ.toLp (radialInverseSqrtProduct F ξ)
    have hM : radialScalarSquareRoot F η = ξ := by
      apply Lp.ext
      filter_upwards [radialScalarSquareRoot_coe_ae F η, hξ.coeFn_toLp,
        radialBoundedScalarMeasure_ae_strict_unitInterval F] with t hm hη hp
      have hs : (Real.sqrt (t : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hp.1)
      rw [hm, hη]
      change (Real.sqrt (t : ℝ) : ℂ) * ((Real.sqrt (t : ℝ) : ℂ)⁻¹ * ξ t) = ξ t
      rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    refine ⟨cyclicExtension radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint F η, ?_⟩
    rw [← radialScalarSquareRoot_intertwine, hM]

theorem radialClosedForm_domain_iff_inverseSqrtMemLp (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) ↔
    MemLp (radialInverseSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F) := by
  rw [radialClosedEnergyDomain_physical_iff_squareRoot_range]
  exact radialSquareRoot_range_iff_inverseSqrtMemLp F ξ

def radialClosedFormLift (F : RadialL2) (ξ : RadialScalarL2 F)
    (hξ : MemLp (radialInverseSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F)) :
    radialClosedEnergyDomain 1 :=
  radialEnergyPolarUnitary
    (cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F
      (hξ.toLp (radialInverseSqrtProduct F ξ)))

theorem radialClosedFormLift_physical (F : RadialL2) (ξ : RadialScalarL2 F)
    (hξ : MemLp (radialInverseSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F)) :
    radialPhysicalEmbedding 1 (radialClosedFormLift F ξ hξ) =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ := by
  rw [radialClosedFormLift, radialPhysicalEmbedding_polar,
    ← radialScalarSquareRoot_intertwine]
  congr 1
  apply Lp.ext
  filter_upwards [radialScalarSquareRoot_coe_ae F
    (hξ.toLp (radialInverseSqrtProduct F ξ)), hξ.coeFn_toLp,
    radialBoundedScalarMeasure_ae_strict_unitInterval F] with t hm hη hp
  have hs : (Real.sqrt (t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hp.1)
  rw [hm, hη]
  change (Real.sqrt (t : ℝ) : ℂ) * ((Real.sqrt (t : ℝ) : ℂ)⁻¹ * ξ t) = ξ t
  rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

theorem radialClosedFormLift_norm (F : RadialL2) (ξ : RadialScalarL2 F)
    (hξ : MemLp (radialInverseSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F)) :
    ‖radialClosedFormLift F ξ hξ‖ =
      ‖hξ.toLp (radialInverseSqrtProduct F ξ)‖ := by
  rw [radialClosedFormLift, radialEnergyPolarUnitary.norm_map, cyclicExtension_norm]

theorem radialClosedForm_full_norm (F : RadialL2) (ξ : RadialScalarL2 F)
    (e : radialClosedEnergyDomain 1)
    (he : radialPhysicalEmbedding 1 e =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) :
    ∃ hξ : MemLp (radialInverseSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F),
      ‖e‖ = ‖hξ.toLp (radialInverseSqrtProduct F ξ)‖ := by
  have hξ := (radialClosedForm_domain_iff_inverseSqrtMemLp F ξ).mp ⟨e, he⟩
  refine ⟨hξ, ?_⟩
  have heq : e = radialClosedFormLift F ξ hξ := by
    apply radialPhysicalEmbedding_injective 1 (by norm_num)
    rw [he, radialClosedFormLift_physical]
  rw [heq, radialClosedFormLift_norm]

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
