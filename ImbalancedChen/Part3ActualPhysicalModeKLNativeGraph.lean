import ImbalancedChen.Part3CuspModeNativeClosedForm
import ImbalancedChen.Part3ActualKLNativeGraph

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual physical closed-form mode operator, under the actual weighted
height unitary and actual onto KL unitary, has the complete native graph
of multiplication by tau^2+1/4. Both directions of the graph and the
exact multiplier domain are proved. The reverse implication constructs
the weighted raw KL L2 output and pulls it back by the actual unitary.

The quarter comes from the proved physical closed-form graph conjugacy;
it is not inserted into a formal differential equation. The raw measure
is tauMeasure=(2/pi^2)tau*sinh(pi*tau)d tau on tau>0. There is no quotient,
automorphic normalization, or truncated-cusp boundary assertion.
-/

namespace ImbalancedChen.Part3.ActualPhysicalModeKLNativeGraph20261026b
noncomputable section
open Set MeasureTheory
open CuspModePhysicalCoreForm20261026a CuspModeNativeClosedForm20261026a
open WeightedHeightNativeUnitary20261026a
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLOntoUnitary20261025a ActualKLNativeGraph20261026a

def physicalModeKL (a : ℝ) (ha : 0 < a) : PhysicalHeightL2 ≃ₗᵢ[ℂ] RawTauL2 :=
  (weightedHeightUnitary a ha).trans actualKLUnitary

def physicalLambdaProduct (g : RawTauL2) (tau : ℝ) : ℂ :=
  ((tau : ℂ) ^ 2 + (1 / 4 : ℂ)) * g tau

/-- Exact native graph of the ACTUAL physical energy operator, including
all vectors in its true domain, not just compact smooth test functions. -/
theorem physicalModeKL_native_graph_iff (a : ℝ) (ha : 0 < a)
    (u v : PhysicalHeightL2) :
    (u, v) ∈ (actualModeFriedrichs a ha).graph ↔
      (physicalModeKL a ha v : ℝ → ℂ) =ᵐ[tauMeasure]
        physicalLambdaProduct (physicalModeKL a ha u) := by
  rw [actualModeFriedrichs_graph_conjugacy, actualKL_native_graph_iff]
  have hlin : actualKLUnitary (weightedHeightUnitary a ha v -
      (1 / 4 : ℂ) • weightedHeightUnitary a ha u) =
        physicalModeKL a ha v - (1 / 4 : ℂ) • physicalModeKL a ha u := by
    simp only [physicalModeKL, LinearIsometryEquiv.trans_apply, map_sub, map_smul]
  rw [hlin]
  have hrep : (physicalModeKL a ha v - (1 / 4 : ℂ) • physicalModeKL a ha u : RawTauL2)
      =ᵐ[tauMeasure] (fun tau =>
        physicalModeKL a ha v tau - (1 / 4 : ℂ) * physicalModeKL a ha u tau) := by
    filter_upwards [Lp.coeFn_sub (physicalModeKL a ha v)
      ((1 / 4 : ℂ) • physicalModeKL a ha u),
      Lp.coeFn_smul (1 / 4 : ℂ) (physicalModeKL a ha u)] with tau hsub hsmul
    rw [hsub, hsmul]
    rfl
  constructor
  · intro h
    filter_upwards [h, hrep] with tau ht hr
    change physicalModeKL a ha v tau =
      ((tau : ℂ) ^ 2 + (1 / 4 : ℂ)) * physicalModeKL a ha u tau
    rw [hr] at ht
    change physicalModeKL a ha v tau - (1 / 4 : ℂ) * physicalModeKL a ha u tau =
      (tau : ℂ) ^ 2 * physicalModeKL a ha u tau at ht
    linear_combination ht
  · intro h
    filter_upwards [h, hrep] with tau ht hr
    rw [hr]
    change physicalModeKL a ha v tau =
      ((tau : ℂ) ^ 2 + (1 / 4 : ℂ)) * physicalModeKL a ha u tau at ht
    change physicalModeKL a ha v tau - (1 / 4 : ℂ) * physicalModeKL a ha u tau =
      (tau : ℂ) ^ 2 * physicalModeKL a ha u tau
    linear_combination ht

/-- The actual physical operator domain is precisely the true raw KL
L2 multiplier domain. The output in the reverse direction is constructed. -/
theorem physicalModeKL_native_domain_iff (a : ℝ) (ha : 0 < a)
    (u : PhysicalHeightL2) :
    u ∈ (actualModeFriedrichs a ha).domain ↔
      MemLp (physicalLambdaProduct (physicalModeKL a ha u)) 2 tauMeasure := by
  constructor
  · intro hu
    have hg := LinearPMap.mem_graph (actualModeFriedrichs a ha) ⟨u, hu⟩
    exact (Lp.memLp (physicalModeKL a ha (actualModeFriedrichs a ha ⟨u, hu⟩))).congr
      ((physicalModeKL_native_graph_iff a ha _ _).mp hg)
  · intro hweighted
    let w : RawTauL2 := hweighted.toLp (physicalLambdaProduct (physicalModeKL a ha u))
    let v : PhysicalHeightL2 := (physicalModeKL a ha).symm w
    have hae : (physicalModeKL a ha v : ℝ → ℂ) =ᵐ[tauMeasure]
        physicalLambdaProduct (physicalModeKL a ha u) := by
      change (physicalModeKL a ha ((physicalModeKL a ha).symm w) : ℝ → ℂ) =ᵐ[tauMeasure] _
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hweighted.coeFn_toLp
    exact LinearPMap.mem_domain_iff.mpr
      ⟨v, (physicalModeKL_native_graph_iff a ha u v).mpr hae⟩

theorem physicalModeKL_native_action (a : ℝ) (ha : 0 < a)
    (u : (actualModeFriedrichs a ha).domain) :
    (physicalModeKL a ha (actualModeFriedrichs a ha u) : ℝ → ℂ) =ᵐ[tauMeasure]
      physicalLambdaProduct (physicalModeKL a ha (u : PhysicalHeightL2)) :=
  (physicalModeKL_native_graph_iff a ha _ _).mp (LinearPMap.mem_graph _ u)

theorem physicalModeKL_native_domain_image (a : ℝ) (ha : 0 < a) :
    physicalModeKL a ha '' ((actualModeFriedrichs a ha).domain : Set PhysicalHeightL2) =
      {g : RawTauL2 | MemLp (physicalLambdaProduct g) 2 tauMeasure} := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (physicalModeKL_native_domain_iff a ha u).mp hu
  · intro hg
    refine ⟨(physicalModeKL a ha).symm g, ?_, (physicalModeKL a ha).apply_symm_apply g⟩
    apply (physicalModeKL_native_domain_iff a ha _).mpr
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hg

end
end ImbalancedChen.Part3.ActualPhysicalModeKLNativeGraph20261026b
