import ImbalancedChen.Part3ActualCylinderClosedEnergyHilbertSum
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The all-vector Dirichlet Parseval theorem on the actual closed gradient
domain. The physical projection is injective, so the gradient closure is
a genuine form domain in actual zero-mean cylinder L2. Fourier coordinates
of that physical projection are derived from convergent reconstruction.
Subtracting physical L2 Parseval from the proved graph-inner-product
Parseval yields the exact sum of actual physical closed mode forms.
No energy identity, form isometry, or Fourier Plancherel is assumed.
-/

namespace ImbalancedChen.Part3.ActualCylinderClosedDirichletParseval20261026b
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

def cylinderClosedCoordinate (j : Fin 3) : cylinderClosedEnergyDomain →L[ℂ] CylinderL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => CylinderL2) j).comp cylinderClosedEnergyDomain.subtypeL

def modeCoordinate (j : Fin 3) (n : NonzeroMode) (d : ModeEnergy n) : HeightL2 :=
  ![modeValue n d, modeVertical n d, modeHorizontal n d] j

theorem modeEnergyVector_coordinate (j : Fin 3) (n : NonzeroMode) (d : ModeEnergy n) :
    modeEnergyVector n d j = modeEmbedding n (modeCoordinate j n d) := by
  fin_cases j <;> rfl

/-- The native energy Fourier coordinate has the literal height coefficient
in each of the three physical gradient coordinates. -/
theorem cylinderClosedCoordinate_coefficient (j : Fin 3)
    (F : cylinderClosedEnergyDomain) (n : NonzeroMode) :
    cylinderCoefficient n (cylinderClosedCoordinate j F) =
      modeCoordinate j n (actualCylinderEnergyFourier F n) := by
  have hs := ((cylinderCoefficient (n : ℤ)).comp
    (PiLp.proj 2 (fun _ : Fin 3 => CylinderL2) j)).hasSum
      (actualCylinderEnergyFourier_reconstruction_ambient F)
  apply hs.unique
  convert hasSum_ite_eq n (modeCoordinate j n (actualCylinderEnergyFourier F n)) using 1
  ext m
  change cylinderCoefficient n (modeEnergyVector m (actualCylinderEnergyFourier F m) j) = _
  rw [modeEnergyVector_coordinate, cylinderCoefficient_mode]
  by_cases h : m = n
  · subst m
    simp
  · simp [h, Ne.symm h, Subtype.val_injective.eq_iff]

theorem cylinderClosedCoordinate_zero_mean (j : Fin 3) (F : cylinderClosedEnergyDomain) :
    cylinderClosedCoordinate j F ∈ zeroMeanCylinder := by
  have hs := ((cylinderCoefficient 0).comp
    (PiLp.proj 2 (fun _ : Fin 3 => CylinderL2) j)).hasSum
      (actualCylinderEnergyFourier_reconstruction_ambient F)
  have hz (n : NonzeroMode) :
      cylinderCoefficient 0 (modeEnergyVector n (actualCylinderEnergyFourier F n) j) = 0 := by
    rw [modeEnergyVector_coordinate, cylinderCoefficient_mode]
    simp [Ne.symm n.property]
  have hs0 : HasSum (fun _ : NonzeroMode => (0 : HeightL2))
      (cylinderCoefficient 0 (cylinderClosedCoordinate j F)) := by
    simpa only [ContinuousLinearMap.comp_apply, hz] using hs
  exact hs0.unique hasSum_zero

def cylinderClosedValue : cylinderClosedEnergyDomain →L[ℂ] zeroMeanCylinder :=
  (cylinderClosedCoordinate 0).codRestrict zeroMeanCylinder (cylinderClosedCoordinate_zero_mean 0)

theorem cylinderClosedValue_on_mode (n : NonzeroMode) (d : ModeEnergy n) :
    cylinderClosedValue (cylinderModeEnergy n d) = nonzeroCylinderMode n (modeValue n d) := rfl

theorem cylinderClosedValue_fourier (F : cylinderClosedEnergyDomain) (n : NonzeroMode) :
    actualCylinderFourier (cylinderClosedValue F) n =
      modeValue n (actualCylinderEnergyFourier F n) := by
  rw [actualCylinderFourier_apply]
  exact cylinderClosedCoordinate_coefficient 0 F n

theorem cylinderClosedValue_norm_le (F : cylinderClosedEnergyDomain) :
    ‖cylinderClosedValue F‖ ≤ ‖F‖ :=
  PiLp.norm_apply_le (F : CylinderEnergyHilbert) (0 : Fin 3)

theorem modeValue_norm_le (n : NonzeroMode) (d : ModeEnergy n) :
    ‖modeValue n d‖ ≤ ‖d‖ :=
  PiLp.norm_apply_le (d : PhysicalEnergyHilbert) (0 : Fin 3)

theorem modeValue_denseRange (n : NonzeroMode) : DenseRange (modeValue n) :=
  physicalClosedEmbedding_denseRange (frequencyScale n) (frequencyScale_pos n.property)

/-- No spurious vertical or horizontal gradient can survive with zero
physical value in this genuine closure. -/
theorem cylinderClosedValue_injective : Function.Injective cylinderClosedValue := by
  intro F G h
  apply actualCylinderEnergyFourier.injective
  ext n
  apply physicalClosedEmbedding_injective (frequencyScale n) (frequencyScale_pos n.property)
  change modeValue n (actualCylinderEnergyFourier F n) =
    modeValue n (actualCylinderEnergyFourier G n)
  rw [← cylinderClosedValue_fourier F n, ← cylinderClosedValue_fourier G n, h]

theorem cylinderClosedValue_denseRange : DenseRange cylinderClosedValue := by
  have hbot : (cylinderClosedValue.toLinearMap.range)ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro F hF
    apply Submodule.mem_bot.mpr
    apply actualCylinderFourier.injective
    ext n
    rw [map_zero]
    change actualCylinderFourier F n = 0
    rw [actualCylinderFourier_apply]
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    apply (physicalClosedEmbedding_denseRange (frequencyScale n)
      (frequencyScale_pos n.property)).induction_on
      (cylinderCoefficient n (F : CylinderL2))
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro d
      rw [cylinderCoefficient_inner]
      exact Submodule.inner_right_of_mem_orthogonal
        (show cylinderClosedValue (cylinderModeEnergy n d) ∈
          cylinderClosedValue.toLinearMap.range from ⟨cylinderModeEnergy n d, rfl⟩) hF
  change Dense ((cylinderClosedValue.toLinearMap.range : Submodule ℂ zeroMeanCylinder) : Set _)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]

def closedDirichletForm (F G : cylinderClosedEnergyDomain) : ℂ :=
  inner ℂ (cylinderClosedCoordinate 1 F) (cylinderClosedCoordinate 1 G) +
    inner ℂ (cylinderClosedCoordinate 2 F) (cylinderClosedCoordinate 2 G)

theorem closedDirichletForm_eq_inner_sub_value (F G : cylinderClosedEnergyDomain) :
    closedDirichletForm F G = inner ℂ F G -
      inner ℂ (cylinderClosedValue F) (cylinderClosedValue G) := by
  change inner ℂ ((F : CylinderEnergyHilbert) 1) ((G : CylinderEnergyHilbert) 1) +
    inner ℂ ((F : CylinderEnergyHilbert) 2) ((G : CylinderEnergyHilbert) 2) =
      inner ℂ (F : CylinderEnergyHilbert) (G : CylinderEnergyHilbert) -
        inner ℂ ((F : CylinderEnergyHilbert) 0) ((G : CylinderEnergyHilbert) 0)
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem modeClosedForm_eq_inner_sub_value (n : NonzeroMode) (d e : ModeEnergy n) :
    physicalClosedForm (frequencyScale n) (frequencyScale_pos n.property) d e =
      inner ℂ d e - inner ℂ (modeValue n d) (modeValue n e) := by
  change inner ℂ ((d : PhysicalEnergyHilbert) 1) ((e : PhysicalEnergyHilbert) 1) +
    inner ℂ ((d : PhysicalEnergyHilbert) 2) ((e : PhysicalEnergyHilbert) 2) =
      inner ℂ (d : PhysicalEnergyHilbert) (e : PhysicalEnergyHilbert) -
        inner ℂ ((d : PhysicalEnergyHilbert) 0) ((e : PhysicalEnergyHilbert) 0)
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- Exact all-vector closed Dirichlet Parseval. Both domain identification
and equality of energies are conclusions from genuine core closure. -/
theorem closedDirichletForm_hasSum_modes (F G : cylinderClosedEnergyDomain) :
    HasSum (fun n : NonzeroMode =>
      physicalClosedForm (frequencyScale n) (frequencyScale_pos n.property)
        (actualCylinderEnergyFourier F n) (actualCylinderEnergyFourier G n))
      (closedDirichletForm F G) := by
  have hgraph := actualCylinderEnergyFourier_hasSum_graph_pairing F G
  have hvalue : HasSum (fun n : NonzeroMode =>
      inner ℂ (modeValue n (actualCylinderEnergyFourier F n))
        (modeValue n (actualCylinderEnergyFourier G n)))
      (inner ℂ (cylinderClosedValue F) (cylinderClosedValue G)) := by
    simpa only [cylinderClosedValue_fourier, actualCylinderFourier.inner_map_map] using
      lp.hasSum_inner (actualCylinderFourier (cylinderClosedValue F))
        (actualCylinderFourier (cylinderClosedValue G))
  simpa only [modeClosedForm_eq_inner_sub_value, closedDirichletForm_eq_inner_sub_value] using
    hgraph.sub hvalue

theorem closedDirichletForm_eq_tsum_modes (F G : cylinderClosedEnergyDomain) :
    closedDirichletForm F G = ∑' n : NonzeroMode,
      physicalClosedForm (frequencyScale n) (frequencyScale_pos n.property)
        (actualCylinderEnergyFourier F n) (actualCylinderEnergyFourier G n) :=
  (closedDirichletForm_hasSum_modes F G).tsum_eq.symm

/-- The native complete energy Hilbert norm is exactly value plus
Dirichlet energy, rather than an assumed equivalent norm. -/
theorem closedDirichletForm_add_value_pairing (F G : cylinderClosedEnergyDomain) :
    closedDirichletForm F G + inner ℂ (cylinderClosedValue F) (cylinderClosedValue G) =
      inner ℂ F G := by
  rw [closedDirichletForm_eq_inner_sub_value]
  ring

theorem closedDirichletForm_weak_iff_shifted_pairing
    (G : cylinderClosedEnergyDomain) (v : zeroMeanCylinder) :
    (∀ F : cylinderClosedEnergyDomain,
      closedDirichletForm F G = inner ℂ (cylinderClosedValue F) v) ↔
    (∀ F : cylinderClosedEnergyDomain, inner ℂ F G =
      inner ℂ (cylinderClosedValue F) (cylinderClosedValue G + v)) := by
  constructor
  · intro h F
    rw [← closedDirichletForm_add_value_pairing, inner_add_right, h F]
    ring
  · intro h F
    rw [closedDirichletForm_eq_inner_sub_value, h F, inner_add_right]
    ring

end
end ImbalancedChen.Part3.ActualCylinderClosedDirichletParseval20261026b
