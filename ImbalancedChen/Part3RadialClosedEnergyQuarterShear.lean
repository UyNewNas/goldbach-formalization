import ImbalancedChen.Part3ActualRadialFriedrichsOperator
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED.

The compact first-derivative Green identity extends to BOTH arguments in
the actual closed radial energy domain. This is proved from its actual
closed-span definition and its weak derivative graph. It is not assumed
for arbitrary energy vectors. Consequently the affine derivative D+1/2
adds exactly a quarter to the closed form, with no surviving mixed term.
This is the closed-energy primitive needed by the physical cusp bridge.
-/

namespace ImbalancedChen.Part3.RadialClosedEnergyQuarterShear20261026a
noncomputable section
open Set
open RadialSchrodingerL2Form20261025a

private def greenKernel (d : radialClosedEnergyDomain 1) :
    Submodule ℂ RadialEnergyHilbert where
  carrier := {x | inner ℂ (radialClosedDerivative 1 d) (energyPhysicalCoordinate 1 x) +
    inner ℂ (radialPhysicalEmbedding 1 d) (energyDerivativeCoordinate x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_add, inner_add_right] at *
    linear_combination hx + hy
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, map_smul, inner_smul_right] at *
    linear_combination c * hx

private theorem greenKernel_closed (d : radialClosedEnergyDomain 1) :
    IsClosed (greenKernel d : Set RadialEnergyHilbert) :=
  isClosed_eq
    ((continuous_const.inner (energyPhysicalCoordinate 1).continuous).add
      (continuous_const.inner energyDerivativeCoordinate.continuous)) continuous_const

private theorem radial_domain_le_greenKernel (d : radialClosedEnergyDomain 1) :
    radialClosedEnergyDomain 1 ≤ greenKernel d := by
  apply (radialEnergyCoreSpan 1).topologicalClosure_minimal _ (greenKernel_closed d)
  apply Submodule.span_le.2
  rintro _ ⟨T, rfl⟩
  have hd := (radialClosedEnergyDomain_le_good 1 (by norm_num) d.property).1
  have h := hd T
  change inner ℂ (radialClosedDerivative 1 d) (radialCoreL2 T) =
    -inner ℂ (radialPhysicalEmbedding 1 d) (radialDerivativeL2 T) at h
  change inner ℂ (radialClosedDerivative 1 d)
      (energyPhysicalCoordinate 1 (radialEnergyCoreVector 1 T)) +
    inner ℂ (radialPhysicalEmbedding 1 d) (radialDerivativeL2 T) = 0
  rw [energyPhysical_core 1 (by norm_num), h]
  ring

/-- Integration by parts survives actual form closure in both slots. -/
theorem radial_closed_Green (d e : radialClosedEnergyDomain 1) :
    inner ℂ (radialClosedDerivative 1 d) (radialPhysicalEmbedding 1 e) =
      -inner ℂ (radialPhysicalEmbedding 1 d) (radialClosedDerivative 1 e) := by
  have h := radial_domain_le_greenKernel d e.property
  change inner ℂ (radialClosedDerivative 1 d) (radialPhysicalEmbedding 1 e) +
    inner ℂ (radialPhysicalEmbedding 1 d) (radialClosedDerivative 1 e) = 0 at h
  linear_combination h

def radialHalfShiftedDerivative : radialClosedEnergyDomain 1 →L[ℂ] RadialL2 :=
  radialClosedDerivative 1 + (1 / 2 : ℂ) • radialPhysicalEmbedding 1

def radialQuarterForm (d e : radialClosedEnergyDomain 1) : ℂ :=
  inner ℂ (radialHalfShiftedDerivative d) (radialHalfShiftedDerivative e) +
    inner ℂ (radialClosedExponential 1 d) (radialClosedExponential 1 e)

theorem radialQuarterForm_eq (d e : radialClosedEnergyDomain 1) :
    radialQuarterForm d e =
      inner ℂ (radialClosedDerivative 1 d) (radialClosedDerivative 1 e) +
      inner ℂ (radialClosedExponential 1 d) (radialClosedExponential 1 e) +
      (1 / 4 : ℂ) * inner ℂ (radialPhysicalEmbedding 1 d) (radialPhysicalEmbedding 1 e) := by
  unfold radialQuarterForm radialHalfShiftedDerivative
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [radial_closed_Green d e]
  norm_num <;> ring

/-- The physical energy plus three quarters of the norm is exactly the
actual complete radial energy Hilbert inner product. -/
theorem radialQuarterForm_shift_threeQuarters (d e : radialClosedEnergyDomain 1) :
    radialQuarterForm d e + (3 / 4 : ℂ) *
      inner ℂ (radialPhysicalEmbedding 1 d) (radialPhysicalEmbedding 1 e) =
      inner ℂ d e := by
  rw [radialQuarterForm_eq, radialClosedEnergy_inner 1 (by norm_num)]
  norm_num <;> ring

/-- Exact weak-graph identification on the real completed form domain,
prior to any physical-coordinate transport. -/
theorem actualRadialFriedrichs_quarter_graph_iff (u v : RadialL2) :
    (u, v - (1 / 4 : ℂ) • u) ∈ actualRadialFriedrichs.graph ↔
      ∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = u ∧
        ∀ d : radialClosedEnergyDomain 1,
          radialQuarterForm d e = inner ℂ (radialPhysicalEmbedding 1 d) v := by
  rw [actualRadialFriedrichs_graph_iff_weak_radial_energy]
  constructor
  · rintro ⟨e, he, hw⟩
    refine ⟨e, he, fun d => ?_⟩
    rw [radialQuarterForm_eq, he, hw d, inner_sub_right, inner_smul_right]
    ring
  · rintro ⟨e, he, hw⟩
    refine ⟨e, he, fun d => ?_⟩
    have h := hw d
    rw [radialQuarterForm_eq, he] at h
    rw [inner_sub_right, inner_smul_right]
    linear_combination h

end
end ImbalancedChen.Part3.RadialClosedEnergyQuarterShear20261026a
