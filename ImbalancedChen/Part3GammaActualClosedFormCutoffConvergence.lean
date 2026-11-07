import ImbalancedChen.Part3GammaActualClosedFormCutoffMultiplier

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ACTUAL modular cutoffs converge strongly to the identity on every
existing energy-form vector. The proof uses the PROVED uniform operator
bound and original-core eventual EXACTNESS; no cutoff convergence is an
input. The physical same-quotient mass, global carrier gradient, and true
closed Dirichlet energy consequently converge to their original values.
This does not place an arbitrary adjoint defect in the form domain.
-/

namespace ImbalancedChen.Part3.GammaActualClosedFormCutoffConvergence20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CarrierGradientHilbertMap20261026b Gamma0WeightedCutoffDefectLimit20261026a
open GammaCompactSeedCutoffPlateau20261026a GammaOriginalCutoffCoreEnergyExact20261026b
open GammaActualQuotientCutoffMultiplier20261026b GammaActualClosedFormCutoffMultiplier20261026b

/-- Uniform boundedness and dense original-core eventual exactness give
strong convergence on the ENTIRE genuine form completion. -/
theorem actualClosedFormCutoff_tendsto (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n => actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) e)
      atTop (𝓝 e) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  let C := actualCutoffEnergyBound
  have hC : 0 ≤ C := actualCutoffEnergyBound_nonneg
  have hCp : 0 < C+1 := by linarith
  let delta := epsilon/(C+1)
  have hdelta : 0 < delta := div_pos hepsilon hCp
  obtain ⟨w,hw,hnear⟩ := Metric.mem_closure_iff.mp ((coreEmbedding_denseRange N) e) delta hdelta
  obtain ⟨u,rfl⟩ := hw
  have hnorm : ‖e-coreEmbedding N u‖ < delta := by
    simpa only [dist_eq_norm] using hnear
  have hsmall : (C+1)*‖e-coreEmbedding N u‖ < epsilon := by
    have hh := (lt_div_iff₀ hCp).mp hnorm
    simpa only [mul_comm] using hh
  obtain ⟨a,b,ha,hab,hexact⟩ := exists_actualCutoffCoreEnergy_eventual_exact N u
  have hfix : ∀ᶠ n in atTop,
      actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) (coreEmbedding N u) =
        coreEmbedding N u := by
    filter_upwards [cutoffHeight_tendsto.eventually (eventually_ge_atTop (plateauThreshold a b))]
      with n hn
    rw [actualClosedFormCutoff_core]
    exact hexact (cutoffHeight n) hn
  filter_upwards [hfix] with n hn
  rw [dist_eq_norm]
  have hdecomp :
      actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) e - e =
      actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) (e-coreEmbedding N u) +
        (coreEmbedding N u-e) := by
    rw [map_sub,hn]
    abel
  have hrev : ‖coreEmbedding N u-e‖ = ‖e-coreEmbedding N u‖ := norm_sub_rev _ _
  calc
    _ = ‖actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) (e-coreEmbedding N u) +
        (coreEmbedding N u-e)‖ := congrArg norm hdecomp
    _ ≤ ‖actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) (e-coreEmbedding N u)‖ +
        ‖coreEmbedding N u-e‖ := norm_add_le _ _
    _ ≤ C*‖e-coreEmbedding N u‖ + ‖coreEmbedding N u-e‖ :=
      add_le_add_right (actualClosedFormCutoff_norm_le N (cutoffHeight n)
        (cutoffHeight_gt_one n) (e-coreEmbedding N u)) _
    _ = (C+1)*‖e-coreEmbedding N u‖ := by rw [hrev]; ring
    _ < epsilon := hsmall

/-- The same-quotient actual cutoff multiplication converges physically
on every actual form input, with the exact original physical vector. -/
theorem actualClosedFormCutoff_physical_tendsto
    (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n => actualQuotientCutoffMultiplier N (cutoffHeight n)
        (cutoffHeight_gt_one n) (physicalProjection N e))
      atTop (𝓝 (physicalProjection N e)) := by
  simpa only [actualClosedFormCutoff_physical] using
    ((physicalProjection N).continuous.tendsto e).comp (actualClosedFormCutoff_tendsto N e)

/-- Global physical gradient convergence, not convergence only on one
compact carrier chart or on the interior of a chosen fundamental cell. -/
theorem actualClosedFormCutoff_carrier_gradient_tendsto
    (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n => completedCarrierGradient N
        (actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) e))
      atTop (𝓝 (completedCarrierGradient N e)) :=
  ((completedCarrierGradient N).continuous.tendsto e).comp (actualClosedFormCutoff_tendsto N e)

theorem actualClosedFormCutoff_mass_tendsto
    (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n => ‖actualQuotientCutoffMultiplier N (cutoffHeight n)
        (cutoffHeight_gt_one n) (physicalProjection N e)‖^2)
      atTop (𝓝 (‖physicalProjection N e‖^2)) :=
  (actualClosedFormCutoff_physical_tendsto N e).norm.pow 2

/-- The actual unshifted complex form converges, so both its real
energy and every mixed pairing remain available to downstream IMS. -/
theorem actualClosedFormCutoff_Dirichlet_tendsto
    (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n => actualDirichletPair N
        (actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) e)
        (actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) e))
      atTop (𝓝 (actualDirichletPair N e e)) := by
  have he := actualClosedFormCutoff_tendsto N e
  have hp := ((physicalProjection N).continuous.tendsto e).comp he
  unfold actualDirichletPair
  exact (he.inner he).sub (hp.inner hp)

theorem actualClosedFormCutoff_gradient_energy_tendsto
    (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    Tendsto (fun n => ‖completedCarrierGradient N
        (actualClosedFormCutoff N (cutoffHeight n) (cutoffHeight_gt_one n) e)‖^2)
      atTop (𝓝 ((actualDirichletPair N e e).re)) := by
  simpa only [completedCarrierGradient_norm_sq] using
    (actualClosedFormCutoff_carrier_gradient_tendsto N e).norm.pow 2

/-- On the original physical form domain, convergence is explicitly in
its genuine transported energy norm through the unique original lift. -/
theorem actualFormCutoffPoint_energy_tendsto
    (N : ℕ) [NeZero N] (u : actualEnergyFormDomain N) :
    Tendsto (fun n => actualEnergyLift N
        (actualFormCutoffPoint N (cutoffHeight n) (cutoffHeight_gt_one n) u))
      atTop (𝓝 (actualEnergyLift N u)) := by
  simpa only [actualFormCutoffPoint_energyLift] using
    actualClosedFormCutoff_tendsto N (actualEnergyLift N u)

end
end ImbalancedChen.Part3.GammaActualClosedFormCutoffConvergence20261026b
