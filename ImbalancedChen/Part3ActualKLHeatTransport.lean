import ImbalancedChen.Part3ActualKLCompactMultiplier
import ImbalancedChen.Part3ActualKLNativeGraph
import ImbalancedChen.Part3GenericHeatStrongContinuity
import ImbalancedChen.Part3GenericPositiveResolventHeatGenerator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
The ACTUAL radial heat semigroup, constructed by the existing heat calculus
of the actual radial form resolvent, is diagonal under the actual onto KL
transform. Its coefficient is exp(-s*tau^2) on the original tauMeasure.

The required continuous-calculus transport is proved from the actual
unit-shift resolvent representative, via compact Stone--Weierstrass and
operator continuity. Strong continuity and initial recovery reuse the
existing positive-resolvent heat theorem at the actual radial data.
No heat diagonalization, domain, spectral measure or onto hypothesis is
supplied. This is the raw radial problem, not the Gamma quotient.
-/

namespace ImbalancedChen.Part3.ActualKLHeatTransport20261026a

noncomputable section
open Set MeasureTheory Filter Topology
open RadialSchrodingerL2Form20261025a
open ActualKLCoordinateMeasures20261025a ActualKLCoreTransform20261025a
open ActualKLOntoUnitary20261025a ActualKLNativeGraph20261026a
open ActualKLCompactMultiplier20261026a
open GenericPositiveResolventHeat20261025a
open GenericHeatStrongContinuity20261025a
open GenericPositiveResolventHeatGenerator20261025a

/-- These are the independently proved properties of the original radial
closed-form resolvent at kappa=1. -/
def actualRadialResolventData : ResolventData RadialL2 where
  R := radialUnitShiftResolvent
  selfAdjoint := radialUnitShiftResolvent_selfAdjoint
  nonneg := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr radialUnitShiftResolvent_positive
  norm_le_one := radialUnitShiftResolvent_opNorm_le_one
  injective := radialUnitShiftResolvent_injective

def radialSpectrumIntoUnit : C(Spectrum actualRadialResolventData, UnitCoordinateSpace) where
  toFun x := ⟨(x : ℝ), spectrum_coordinate_mem_unitInterval actualRadialResolventData x⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def physicalCompactCFC (φ : C(UnitCoordinateSpace, ℝ)) : RadialL2 →L[ℂ] RadialL2 :=
  cfcMap actualRadialResolventData (φ.comp radialSpectrumIntoUnit)

theorem physicalCompactCFC_continuous :
    Continuous physicalCompactCFC :=
  (cfcL actualRadialResolventData.selfAdjoint).continuous.comp
    (ContinuousMap.compCLM (R := ℝ) ℝ radialSpectrumIntoUnit).continuous

theorem physicalCompactCFC_const (c : ℝ) (F : RadialL2) :
    physicalCompactCFC (ContinuousMap.const UnitCoordinateSpace c) F = c • F := by
  have heq : (ContinuousMap.const UnitCoordinateSpace c).comp radialSpectrumIntoUnit =
      c • (1 : C(Spectrum actualRadialResolventData, ℝ)) := by ext x; simp
  unfold physicalCompactCFC
  rw [heq, map_smul, map_one]
  rfl

theorem physicalCompactCFC_coordinate :
    physicalCompactCFC ((ContinuousMap.id ℝ).restrict (Icc (0 : ℝ) 1)) = radialUnitShiftResolvent :=
  cfcMap_coordinate actualRadialResolventData

theorem physicalCompactCFC_add (φ ψ : C(UnitCoordinateSpace, ℝ)) :
    physicalCompactCFC (φ+ψ) = physicalCompactCFC φ + physicalCompactCFC ψ := by
  unfold physicalCompactCFC
  rw [ContinuousMap.add_comp, map_add]

theorem physicalCompactCFC_mul (φ ψ : C(UnitCoordinateSpace, ℝ)) :
    physicalCompactCFC (φ*ψ) = physicalCompactCFC φ * physicalCompactCFC ψ := by
  unfold physicalCompactCFC
  rw [ContinuousMap.mul_comp, map_mul]

/-- The base coordinate case uses the actual native radial graph result;
it does not assume a functional-calculus or heat intertwiner. -/
theorem actualKL_unitCoordinate_transport (F : RadialL2) :
    actualKLUnitary (physicalCompactCFC ((ContinuousMap.id ℝ).restrict (Icc (0 : ℝ) 1)) F) =
      rawCompactMultiply ((ContinuousMap.id ℝ).restrict (Icc (0 : ℝ) 1)) (actualKLUnitary F) := by
  rw [physicalCompactCFC_coordinate]
  apply Lp.ext
  filter_upwards [actualKL_unitShiftResolvent_ae F,
    rawCompactMultiply_coe_ae ((ContinuousMap.id ℝ).restrict (Icc (0 : ℝ) 1)) (actualKLUnitary F)]
      with tau hl hr
  rw [hl, hr]
  change (1+(tau : ℂ)^2)⁻¹ * actualKLUnitary F tau = ((1+tau^2)⁻¹ : ℝ) • actualKLUnitary F tau
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]

/-- All continuous functions of the compact actual resolvent coordinate
are transported by the same actual KL unitary. -/
theorem actualKL_compactCFC_transport (φ : C(UnitCoordinateSpace, ℝ)) (F : RadialL2) :
    actualKLUnitary (physicalCompactCFC φ F) = rawCompactMultiply φ (actualKLUnitary F) := by
  have hall : ∀ F : RadialL2,
      actualKLUnitary (physicalCompactCFC φ F) = rawCompactMultiply φ (actualKLUnitary F) := by
    apply ContinuousMap.induction_on_of_compact
      (p := fun ψ : C(UnitCoordinateSpace, ℝ) => ∀ F : RadialL2,
        actualKLUnitary (physicalCompactCFC ψ F) = rawCompactMultiply ψ (actualKLUnitary F))
      (f := φ)
    · intro c F
      rw [physicalCompactCFC_const, rawCompactMultiply_const]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    · exact actualKL_unitCoordinate_transport
    · simpa only [star_trivial] using actualKL_unitCoordinate_transport
    · intro ψ χ hψ hχ F
      rw [physicalCompactCFC_add, ContinuousLinearMap.add_apply, map_add,
        hψ F, hχ F, rawCompactMultiply_add]
    · intro ψ χ hψ hχ F
      rw [physicalCompactCFC_mul]
      change actualKLUnitary (physicalCompactCFC ψ (physicalCompactCFC χ F)) = _
      rw [hψ, hχ, rawCompactMultiply_mul]
    · intro ψ hfreq F
      have hclosed : IsClosed {χ : C(UnitCoordinateSpace, ℝ) |
          actualKLUnitary (physicalCompactCFC χ F) = rawCompactMultiply χ (actualKLUnitary F)} :=
        isClosed_eq
          (actualKLUnitary.continuous.comp
            ((ContinuousLinearMap.apply ℂ RadialL2 F).continuous.comp physicalCompactCFC_continuous))
          (rawCompactMultiply_continuous (actualKLUnitary F))
      exact hclosed.mem_of_frequently_of_tendsto (hfreq.mono fun χ hχ => hχ F) tendsto_id
  exact hall F

/-- The original radial closed-form heat family; it is defined before
and independently of its KL multiplier identity. -/
def actualRadialHeat (s : ℝ) : RadialL2 →L[ℂ] RadialL2 := heatOperator actualRadialResolventData s

def compactHeatScalar (s : ℝ) : C(UnitCoordinateSpace, ℝ) :=
  if 0 < s then
    ⟨fun x => Real.exp s * expNegInvGlue ((x : ℝ)/s),
      continuous_const.mul ((expNegInvGlue.contDiff : ContDiff ℝ 0 expNegInvGlue).continuous.comp
        (continuous_subtype_val.div_const s))⟩
  else 1

theorem compactHeatScalar_restriction (s : ℝ) :
    (compactHeatScalar s).comp radialSpectrumIntoUnit = heatScalar actualRadialResolventData s := by
  by_cases hs : 0 < s <;> ext x <;>
    simp only [compactHeatScalar, heatScalar, hs, if_true, if_false, ContinuousMap.comp_apply,
      ContinuousMap.one_apply, positiveHeatScalar, radialSpectrumIntoUnit]

theorem actualRadialHeat_eq_compactCFC (s : ℝ) :
    actualRadialHeat s = physicalCompactCFC (compactHeatScalar s) := by
  unfold actualRadialHeat heatOperator physicalCompactCFC
  rw [compactHeatScalar_restriction]

theorem compactHeatScalar_raw (s : ℝ) (hs : 0 ≤ s) (tau : ℝ) :
    compactHeatScalar s (rawUnitCoordinate tau) = Real.exp (-s*tau^2) := by
  by_cases hs0 : s = 0
  · subst s
    simp [compactHeatScalar]
  have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hc := rawUnitCoordinate_pos tau
  unfold compactHeatScalar
  rw [if_pos hsp]
  change Real.exp s * expNegInvGlue (((rawUnitCoordinate tau : ℝ))/s) = _
  rw [expNegInvGlue, if_neg (not_le.mpr (div_pos hc hsp)), ← Real.exp_add]
  congr 1
  change s - (((1+tau^2)⁻¹)/s)⁻¹ = -s*tau^2
  rw [inv_div, div_inv_eq_mul]
  ring

/-- Actual full-L2 KL heat diagonalization, on the unchanged raw measure. -/
theorem actualKL_heat_ae (s : ℝ) (hs : 0 ≤ s) (F : RadialL2) :
    (actualKLUnitary (actualRadialHeat s F) : ℝ → ℂ) =ᵐ[tauMeasure]
      (fun tau => (Real.exp (-s*tau^2) : ℂ) * actualKLUnitary F tau) := by
  rw [actualRadialHeat_eq_compactCFC, actualKL_compactCFC_transport]
  filter_upwards [rawCompactMultiply_coe_ae (compactHeatScalar s) (actualKLUnitary F)] with tau htau
  rw [htau, compactHeatScalar_raw s hs, Complex.real_smul]

/-- On actual compact tests, the input is the literal original K-integral. -/
theorem actualKL_heat_on_test_ae (s : ℝ) (hs : 0 ≤ s) (F : RadialTest) :
    (actualKLUnitary (actualRadialHeat s (radialCoreL2 F)) : ℝ → ℂ) =ᵐ[tauMeasure]
      (fun tau => (Real.exp (-s*tau^2) : ℂ) *
        ActualKLCompactTestIntegrationByParts20261025a.actualKtransform F.function tau) := by
  filter_upwards [actualKL_heat_ae s hs (radialCoreL2 F), actualKLUnitary_on_test_ae F] with tau hh ht
  rw [hh, ht]

theorem actualRadialHeat_zero : actualRadialHeat 0 = 1 := heatOperator_zero actualRadialResolventData

theorem actualRadialHeat_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    actualRadialHeat (s+t) = actualRadialHeat s * actualRadialHeat t :=
  heatOperator_add actualRadialResolventData hs ht

theorem actualRadialHeat_norm_le (s : ℝ) (F : RadialL2) : ‖actualRadialHeat s F‖ ≤ ‖F‖ :=
  heatOperator_norm_le actualRadialResolventData s F

theorem actualRadialHeat_strongly_continuous (F : RadialL2) :
    ContinuousOn (fun s : ℝ => actualRadialHeat s F) (Ici (0 : ℝ)) :=
  continuousOn_heatTrajectory_nonnegative actualRadialResolventData F

/-- Physical L2 recovery of the original input, not only transformed
pointwise convergence. -/
theorem actualRadialHeat_initial (F : RadialL2) :
    Tendsto (fun s : ℝ => actualRadialHeat s F) (𝓝[>] 0) (𝓝 F) :=
  tendsto_heatOperator_at_zero actualRadialResolventData F

theorem actualKL_heat_initial (F : RadialL2) :
    Tendsto (fun s : ℝ => actualKLUnitary (actualRadialHeat s F))
      (𝓝[>] 0) (𝓝 (actualKLUnitary F)) :=
  (actualKLUnitary.continuous.tendsto F).comp (actualRadialHeat_initial F)

/-- The strong right generator is exactly the negative original native
radial Friedrichs graph, including its genuine domain. -/
theorem actualRadialHeat_generator_iff (u v : RadialL2) :
    (u,v) ∈ actualRadialFriedrichs.graph ↔
      Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (actualRadialHeat s u-u)) (𝓝[>] 0) (𝓝 (-v)) :=
  (actualRadialFriedrichs_graph_iff u v).trans
    ((mem_resolventGraph_iff actualRadialResolventData (u,v)).symm.trans
      (mem_resolventGraph_iff_heat_difference_quotient actualRadialResolventData u v))

end
end ImbalancedChen.Part3.ActualKLHeatTransport20261026a

