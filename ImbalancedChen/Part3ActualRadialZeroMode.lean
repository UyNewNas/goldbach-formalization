import ImbalancedChen.Part3ActualRadialFriedrichsOperator
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual radial operator -d²/dr²+exp(2r) has trivial native kernel.
The weak radial energy graph gives the derivative and exp-coordinate
norms. For a zero output both norms vanish. The ACTUAL closed
exponential multiplication graph then identifies exp(r) times the
physical L2 class with zero; exp(r) is everywhere nonzero, so the
physical class itself is zero. No spectral gap or lower bound on exp
over the whole real line is used. This is not a constant cusp-mode claim.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory

theorem actualRadialFriedrichs_zero_output {u : RadialL2}
    (hu : (u, 0) ∈ actualRadialFriedrichs.graph) : u = 0 := by
  obtain ⟨e, he, hweak⟩ :=
    (actualRadialFriedrichs_graph_iff_weak_radial_energy u 0).1 hu
  have henergy := hweak e
  simp only [inner_zero_right] at henergy
  have hreal : ‖radialClosedDerivative 1 e‖ ^ 2 +
      ‖radialClosedExponential 1 e‖ ^ 2 = 0 := by
    have h := congrArg Complex.re henergy
    simpa only [Complex.add_re, Complex.zero_re, inner_self_eq_norm_sq_to_K,
      ← Complex.ofReal_pow, Complex.ofReal_re] using h
  have hE : radialClosedExponential 1 e = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖radialClosedDerivative 1 e‖,
      norm_nonneg (radialClosedExponential 1 e)]
  have hrelation : (radialClosedExponential 1 e : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      exponentialProduct (radialPhysicalEmbedding 1 e) :=
    (radialClosedEnergyDomain_le_good 1 (by norm_num) e.2).2
  rw [hE] at hrelation
  have hphysical : radialPhysicalEmbedding 1 e = 0 := by
    apply Lp.ext
    filter_upwards [hrelation, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with r hr hz
    have hprod : (Real.exp r : ℂ) * radialPhysicalEmbedding 1 e r = 0 := by
      simpa only [exponentialProduct, hz] using hr.symm
    have hexp : (Real.exp r : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero r
    have hzero := (mul_eq_zero.mp hprod).resolve_left hexp
    exact hzero.trans hz.symm
  exact he.symm.trans hphysical

theorem actualRadialFriedrichs_kernel_eq_bot : actualRadialFriedrichs.toFun.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  apply Subtype.ext
  have hg := LinearPMap.mem_graph actualRadialFriedrichs u
  rw [hu] at hg
  exact actualRadialFriedrichs_zero_output hg

/-- A fixed vector of the actual bounded R1 would be a native A-zero
mode. The genuine radial energy argument rules it out. -/
theorem radialUnitShiftResolvent_fixedPoint_zero (F : RadialL2)
    (hF : radialUnitShiftResolvent F = F) : F = 0 := by
  have hpair := actualRadialFriedrichs_resolvent_pair F
  rw [hF, sub_self] at hpair
  exact actualRadialFriedrichs_zero_output hpair

theorem radialUnitShiftResolvent_no_eigenvalue_one :
    ¬ ∃ F : RadialL2, F ≠ 0 ∧ radialUnitShiftResolvent F = F := by
  rintro ⟨F, hF, hfixed⟩
  exact hF (radialUnitShiftResolvent_fixedPoint_zero F hfixed)

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
