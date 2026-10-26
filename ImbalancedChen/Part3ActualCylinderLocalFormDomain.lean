import ImbalancedChen.Part3ActualCylinderClosedDirichletParseval
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An explicit local Fourier criterion for the actual closed cylinder
gradient domain. The reverse direction constructs convergent native
Fourier reconstruction of all three actual gradient coordinates. There
is no premise asserting global form-domain membership or summability
of mode energies. This is a whole-cylinder zero-mean realization.
-/

namespace ImbalancedChen.Part3.ActualCylinderLocalFormDomain20261026b
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z CuspCylinderBesselMode20261024z
open CuspModePhysicalCoreForm20261026a CuspModeNativeClosedForm20261026a
open ActualCylinderModeEmbeddings20261026a ActualCylinderFourierCoefficients20261026a
open ActualZeroMeanCylinderFourierUnitary20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open ActualCylinderFiniteEnergyCore20261026b
open ActualCylinderClosedEnergyHilbertSum20261026b
open ActualCylinderClosedDirichletParseval20261026b

/-- The inverse horizontal phase converts the signed actual horizontal
derivative into the positive physical potential coordinate. -/
def modeCoefficientTriple (X : CylinderEnergyHilbert) (n : NonzeroMode) : PhysicalEnergyHilbert :=
  WithLp.toLp 2 ![cylinderCoefficient n (X 0), cylinderCoefficient n (X 1),
    star (horizontalPhase n) • cylinderCoefficient n (X 2)]

theorem modeCoefficientTriple_of_closed (F : cylinderClosedEnergyDomain)
    (n : NonzeroMode) :
    modeCoefficientTriple (F : CylinderEnergyHilbert) n =
      (actualCylinderEnergyFourier F n : PhysicalEnergyHilbert) := by
  ext j
  fin_cases j
  · exact cylinderClosedCoordinate_coefficient 0 F n
  · exact cylinderClosedCoordinate_coefficient 1 F n
  · change star (horizontalPhase n) • cylinderCoefficient n (cylinderClosedCoordinate 2 F) =
      ((actualCylinderEnergyFourier F n : PhysicalEnergyHilbert) 2)
    rw [cylinderClosedCoordinate_coefficient]
    change star (horizontalPhase n) • (horizontalPhase n •
      ((actualCylinderEnergyFourier F n : PhysicalEnergyHilbert) 2)) = _
    rw [smul_smul, horizontalPhase_unit, one_smul]

theorem modeCoefficientTriple_mem_of_closed (F : cylinderClosedEnergyDomain)
    (n : NonzeroMode) :
    modeCoefficientTriple (F : CylinderEnergyHilbert) n ∈
      physicalClosedEnergyDomain (frequencyScale n) (frequencyScale_pos n.property) := by
  rw [modeCoefficientTriple_of_closed]
  exact (actualCylinderEnergyFourier F n).property

theorem local_mode_reconstructs_coordinate (X : CylinderEnergyHilbert) (n : NonzeroMode)
    (hn : modeCoefficientTriple X n ∈
      physicalClosedEnergyDomain (frequencyScale n) (frequencyScale_pos n.property))
    (j : Fin 3) :
    modeEnergyVector n ⟨modeCoefficientTriple X n, hn⟩ j =
      modeEmbedding n (cylinderCoefficient n (X j)) := by
  rw [modeEnergyVector_coordinate]
  congr 1
  fin_cases j
  · rfl
  · rfl
  · change horizontalPhase n • (star (horizontalPhase n) • cylinderCoefficient n (X 2)) = _
    rw [smul_smul, mul_comm (horizontalPhase n), horizontalPhase_unit, one_smul]

/-- The actual global closed form domain is characterized by actual
local closed form membership of its genuine Fourier coefficients.
No global energy identity or modal l2 premise is assumed. -/
theorem mem_cylinderClosedEnergyDomain_iff (X : CylinderEnergyHilbert) :
    X ∈ cylinderClosedEnergyDomain ↔
      (∀ j : Fin 3, X j ∈ zeroMeanCylinder) ∧
      ∀ n : NonzeroMode, modeCoefficientTriple X n ∈
        physicalClosedEnergyDomain (frequencyScale n) (frequencyScale_pos n.property) := by
  constructor
  · intro hX
    exact ⟨fun j => cylinderClosedCoordinate_zero_mean j ⟨X, hX⟩,
      fun n => modeCoefficientTriple_mem_of_closed ⟨X, hX⟩ n⟩
  · rintro ⟨hmean, hlocal⟩
    let d : ∀ n : NonzeroMode, ModeEnergy n := fun n => ⟨modeCoefficientTriple X n, hlocal n⟩
    have hs (j : Fin 3) :
        HasSum (fun n : NonzeroMode => modeEnergyVector n (d n) j) (X j) := by
      simpa only [d, local_mode_reconstructs_coordinate] using
        actualCylinderFourier_hasSum_reconstruction ⟨X j, hmean j⟩
    have hsPi : HasSum (fun n : NonzeroMode =>
        (fun j : Fin 3 => modeEnergyVector n (d n) j)) (fun j : Fin 3 => X j) :=
      Pi.hasSum.mpr hs
    have hsNative : HasSum (fun n : NonzeroMode => modeEnergyVector n (d n)) X := by
      simpa only [PiLp.coe_symm_continuousLinearEquiv] using
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => CylinderL2)).symm
          .toContinuousLinearMap.hasSum hsPi
    apply cylinderEnergyCoreSpan.isClosed_topologicalClosure.mem_of_tendsto hsNative
    apply Filter.Eventually.of_forall
    intro s
    exact Submodule.sum_mem _ (fun n hn => modeEnergyVector_mem n (d n))

/-- Local physical domain membership automatically pays the square-sum
energy bound once the three actual cylinder coordinates are in L2. -/
theorem local_form_domain_hasSum_norm (X : CylinderEnergyHilbert)
    (hmean : ∀ j : Fin 3, X j ∈ zeroMeanCylinder)
    (hlocal : ∀ n : NonzeroMode, modeCoefficientTriple X n ∈
      physicalClosedEnergyDomain (frequencyScale n) (frequencyScale_pos n.property)) :
    HasSum (fun n : NonzeroMode => ‖modeCoefficientTriple X n‖ ^ 2) ‖X‖ ^ 2 := by
  let F : cylinderClosedEnergyDomain :=
    ⟨X, (mem_cylinderClosedEnergyDomain_iff X).mpr ⟨hmean, hlocal⟩⟩
  have h : HasSum (fun n : NonzeroMode => ‖actualCylinderEnergyFourier F n‖ ^ 2)
      ‖actualCylinderEnergyFourier F‖ ^ 2 := by
    apply_mod_cast lp.hasSum_norm (by norm_num) (actualCylinderEnergyFourier F)
  rw [actualCylinderEnergyFourier.norm_map] at h
  change HasSum (fun n : NonzeroMode =>
    ‖(actualCylinderEnergyFourier F n : PhysicalEnergyHilbert)‖ ^ 2) ‖X‖ ^ 2 at h
  simpa only [← modeCoefficientTriple_of_closed] using h

end
end ImbalancedChen.Part3.ActualCylinderLocalFormDomain20261026b
