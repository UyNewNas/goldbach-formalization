import ImbalancedChen.Part3ActualKLOntoUnitary
import ImbalancedChen.Part3ActualRadialShiftGreenBinding
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic

/-!
# Complete native radial unbounded graph under the actual KL unitary

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The native radial Friedrichs operator is the one constructed from the
closed derivative/exponential energy form.  Its actual half-shift Green
inverse has KL multiplier (1/4+tau^2)^(-1).  The graph equation for that
same inverse, combined with the already proved actual unitary, determines
both directions of the unbounded tau^2 multiplication graph.

For the reverse domain implication the tau^2-weighted L2 vector is first
constructed by MemLp.toLp and then pulled back by the genuine surjective
KL unitary.  Thus no graph, norm, domain or surjectivity premise is added.
The final unit-shift formula uses a native graph pair only AFTER the
half-shift graph proof.  This is the raw radial KL model, with no Gamma
quotient spectral or Kuznetsov normalization assertion.
-/

namespace ImbalancedChen.Part3.ActualKLNativeGraph20261026a

noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLOntoUnitary20261025a ActualKLExtendedGreenIntertwining20261025a
open ActualKLResolventCoordinate20261025a ActualKLResolventMultiplier20261025a
open PositiveContractionResolventCalculus20261025a
open ActualGreenL2IntegralInverse20261025a

/-- The fixed physical inverse is the kappa=1/2 inverse of this SAME
native graph; the scalar in the forcing equation is exactly 1/4. -/
theorem native_graph_iff_halfGreen (F G : RadialL2) :
    (F, G) ∈ actualRadialFriedrichs.graph ↔
      halfGreenOperator (((1 / 4 : ℝ) : ℂ) • F + G) = F := by
  constructor
  · intro hgraph
    have hg : (F, G) ∈ resolventGraph radialUnitShiftResolvent :=
      (actualRadialFriedrichs_graph_iff F G).mp hgraph
    have hs := shiftedResolvent_on_graph radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_nonneg
      radialUnitShiftResolvent_opNorm_le_one (a := (1 / 4 : ℝ)) (by norm_num) hg
    simpa only [halfGreenOperator,
      actualGreenL2Operator_eq_native_shiftedResolvent (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1), show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] using hs
  · intro hhalf
    have hpair := actualGreenL2Operator_native_graph_pair
      (kappa := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      ((((1 / 4 : ℝ) : ℂ) • F) + G)
    change (halfGreenOperator ((((1 / 4 : ℝ) : ℂ) • F) + G),
      ((((1 / 4 : ℝ) : ℂ) • F) + G) -
        (((1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) •
          halfGreenOperator ((((1 / 4 : ℝ) : ℂ) • F) + G)) ∈
      actualRadialFriedrichs.graph at hpair
    rw [hhalf] at hpair
    norm_num only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] at hpair
    have hcancel : ((((1 / 4 : ℝ) : ℂ) • F) + G) -
        (((1 / 4 : ℝ) : ℂ) • F) = G := by abel
    simpa only [hcancel] using hpair

private theorem half_coordinate_equation (tau : ℝ) (u v : ℂ) :
    (klResolventCoordinate tau : ℂ) * ((((1 / 4 : ℝ) : ℂ) * u) + v) = u ↔
      v = (tau : ℂ) ^ 2 * u := by
  have hd : ((((1 / 4 : ℝ) : ℂ)) + (tau : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (klDenominator_pos tau).ne'
  have hm : (klResolventCoordinate tau : ℂ) =
      ((((1 / 4 : ℝ) : ℂ)) + (tau : ℂ) ^ 2)⁻¹ := by
    unfold klResolventCoordinate
    push_cast
    rfl
  rw [hm]
  constructor
  · intro h
    have hh := congrArg
      (fun z : ℂ => ((((1 / 4 : ℝ) : ℂ)) + (tau : ℂ) ^ 2) * z) h
    field_simp [hd] at hh
    linear_combination hh
  · intro h
    rw [h]
    field_simp [hd]
    <;> ring

/-- The complete actual native graph is precisely multiplication by
tau^2 under the original, genuinely onto KL unitary. -/
theorem actualKL_native_graph_iff (F G : RadialL2) :
    (F, G) ∈ actualRadialFriedrichs.graph ↔
      (actualKLUnitary G : ℝ → ℂ) =ᵐ[tauMeasure]
        (fun tau => (tau : ℂ) ^ 2 * actualKLUnitary F tau) := by
  rw [native_graph_iff_halfGreen]
  let H : RadialL2 := (((1 / 4 : ℝ) : ℂ) • F) + G
  have hlin : actualKLUnitary H =
      (((1 / 4 : ℝ) : ℂ) • actualKLUnitary F) + actualKLUnitary G := by
    simp only [H, map_add, map_smul]
  have hlinear_ae : (actualKLUnitary H : ℝ → ℂ) =ᵐ[tauMeasure]
      (fun tau => (((1 / 4 : ℝ) : ℂ) * actualKLUnitary F tau) + actualKLUnitary G tau) := by
    rw [hlin]
    filter_upwards [Lp.coeFn_add ((((1 / 4 : ℝ) : ℂ) • actualKLUnitary F))
      (actualKLUnitary G), Lp.coeFn_smul (((1 / 4 : ℝ) : ℂ)) (actualKLUnitary F)]
        with tau hadd hsmul
    rw [hadd, hsmul]
    rfl
  constructor
  · intro hhalf
    have hM := rawKLResolventMultiplier_coe_ae (actualKLUnitary H)
    have hEq : rawKLResolventMultiplier (actualKLUnitary H) = actualKLUnitary F := by
      rw [← actualKLUnitary_halfGreen_intertwine, hhalf]
    rw [hEq] at hM
    filter_upwards [hM, hlinear_ae] with tau hm hlinTau
    rw [hlinTau] at hm
    exact (half_coordinate_equation tau _ _).mp hm.symm
  · intro hgraph
    have hEq : rawKLResolventMultiplier (actualKLUnitary H) = actualKLUnitary F := by
      apply Lp.ext
      filter_upwards [rawKLResolventMultiplier_coe_ae (actualKLUnitary H),
        hlinear_ae, hgraph] with tau hm hlinTau hact
      rw [hm, hlinTau]
      exact (half_coordinate_equation tau _ _).mpr hact
    apply actualKLUnitary.injective
    rw [actualKLUnitary_halfGreen_intertwine]
    exact hEq

/-- Full domain criterion, with the reverse direction using the actual
unitary inverse of the newly constructed tau^2-weighted L2 vector. -/
theorem actualKL_native_domain_iff (F : RadialL2) :
    F ∈ actualRadialFriedrichs.domain ↔
      MemLp (fun tau : ℝ => (tau : ℂ) ^ 2 * actualKLUnitary F tau) 2 tauMeasure := by
  constructor
  · intro hF
    have hgraph := LinearPMap.mem_graph actualRadialFriedrichs ⟨F, hF⟩
    have hae := (actualKL_native_graph_iff F (actualRadialFriedrichs ⟨F, hF⟩)).mp hgraph
    exact (Lp.memLp (actualKLUnitary (actualRadialFriedrichs ⟨F, hF⟩))).congr hae
  · intro hweighted
    let V : RawTauL2 := hweighted.toLp
      (fun tau : ℝ => (tau : ℂ) ^ 2 * actualKLUnitary F tau)
    let G : RadialL2 := actualKLUnitary.symm V
    have hG : actualKLUnitary G = V := actualKLUnitary.apply_symm_apply V
    have hae : (actualKLUnitary G : ℝ → ℂ) =ᵐ[tauMeasure]
        (fun tau => (tau : ℂ) ^ 2 * actualKLUnitary F tau) := by
      rw [hG]
      exact hweighted.coeFn_toLp
    have hgraph := (actualKL_native_graph_iff F G).mpr hae
    obtain ⟨u, hu, _⟩ := (LinearPMap.mem_graph_iff actualRadialFriedrichs).mp hgraph
    exact hu ▸ u.property

/-- The exact action on every vector of the actual native operator domain. -/
theorem actualKL_native_action (F : actualRadialFriedrichs.domain) :
    (actualKLUnitary (actualRadialFriedrichs F) : ℝ → ℂ) =ᵐ[tauMeasure]
      (fun tau => (tau : ℂ) ^ 2 * actualKLUnitary (F : RadialL2) tau) :=
  (actualKL_native_graph_iff (F : RadialL2) (actualRadialFriedrichs F)).mp
    (LinearPMap.mem_graph actualRadialFriedrichs F)

/-- Exact set equality: all and only square-weighted raw KL L2 vectors
are images of the complete native radial operator domain. -/
theorem actualKL_native_domain_image :
    actualKLUnitary '' (actualRadialFriedrichs.domain : Set RadialL2) =
      {g : RawTauL2 | MemLp (fun tau : ℝ => (tau : ℂ) ^ 2 * g tau) 2 tauMeasure} := by
  ext g
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact (actualKL_native_domain_iff F).mp hF
  · intro hg
    refine ⟨actualKLUnitary.symm g, ?_, actualKLUnitary.apply_symm_apply g⟩
    apply (actualKL_native_domain_iff (actualKLUnitary.symm g)).mpr
    simpa only [actualKLUnitary.apply_symm_apply] using hg

/-- Native graph conjugacy as a set of pairs, including both domain and
action. This is stronger than an identity only on compact smooth tests. -/
theorem actualKL_native_graph_image :
    (fun p : RadialL2 × RadialL2 => (actualKLUnitary p.1, actualKLUnitary p.2)) ''
        (actualRadialFriedrichs.graph : Set (RadialL2 × RadialL2)) =
      {p : RawTauL2 × RawTauL2 | (p.2 : ℝ → ℂ) =ᵐ[tauMeasure]
        (fun tau => (tau : ℂ) ^ 2 * p.1 tau)} := by
  ext p
  constructor
  · rintro ⟨⟨F, G⟩, hgraph, rfl⟩
    exact (actualKL_native_graph_iff F G).mp hgraph
  · intro hp
    refine ⟨(actualKLUnitary.symm p.1, actualKLUnitary.symm p.2), ?_, ?_⟩
    · apply (actualKL_native_graph_iff _ _).mpr
      simpa only [actualKLUnitary.apply_symm_apply] using hp
    · simp only [actualKLUnitary.apply_symm_apply]

/-- The unit-shift multiplier is derived from the actual native graph
pair, not substituted for the half-shift multiplier in the proof above. -/
theorem actualKL_unitShiftResolvent_ae (F : RadialL2) :
    (actualKLUnitary (radialUnitShiftResolvent F) : ℝ → ℂ) =ᵐ[tauMeasure]
      (fun tau => (1 + (tau : ℂ) ^ 2)⁻¹ * actualKLUnitary F tau) := by
  have hg := (actualKL_native_graph_iff (radialUnitShiftResolvent F)
    (F - radialUnitShiftResolvent F)).mp (actualRadialFriedrichs_resolvent_pair F)
  have hsub : actualKLUnitary (F - radialUnitShiftResolvent F) =
      actualKLUnitary F - actualKLUnitary (radialUnitShiftResolvent F) := map_sub _ _ _
  rw [hsub] at hg
  filter_upwards [hg, Lp.coeFn_sub (actualKLUnitary F)
    (actualKLUnitary (radialUnitShiftResolvent F))] with tau hgraph hrep
  rw [hrep] at hgraph
  have hd : (1 + (tau : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + tau ^ 2 ≠ 0 by positivity)
  field_simp [hd]
  linear_combination -hgraph

end
end ImbalancedChen.Part3.ActualKLNativeGraph20261026a
