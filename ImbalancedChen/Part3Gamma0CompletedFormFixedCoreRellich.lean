import ImbalancedChen.Part3Gamma0QuotientFormChartBudgets

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Bounded balls of the ACTUAL completed quotient form are totally bounded
after restriction to the actual fixed truncated quotient core. The proof
uses the genuine core form-to-chart estimate and actual density, with a
strict A+1 approximation budget. No compact embedding, chart H1 budget,
or completed approximation estimate is supplied as a hypothesis.
Global compactness still requires the separate all-cusps tail theorem. -/

namespace ImbalancedChen.Part3.Gamma0CompletedFormFixedCoreRellich20261026b
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped UpperHalfPlane
open Gamma0QuotientFormChartBudgets20261026b
open Gamma0QuotientCellPushforward20261025a
open Gamma0QuotientChartReconstruction20261026b
open Gamma0FixedCoreRellich20261026b
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0ActualFriedrichsOperator20261025a

def quotientCoreRestriction (N : ℕ) [NeZero N] (Y : ℝ) (u : QuotientL2 N) : QuotientL2 N :=
  (u.memLp.indicator (quotientCore_measurable N Y)).toLp ((quotientCore N Y).indicator u)

theorem quotientCoreRestriction_coe_ae (N : ℕ) [NeZero N] (Y : ℝ) (u : QuotientL2 N) :
    quotientCoreRestriction N Y u =ᵐ[carrierPushforward N] (quotientCore N Y).indicator u :=
  (u.memLp.indicator (quotientCore_measurable N Y)).coeFn_toLp

def quotientCoreRestrictionLinear (N : ℕ) [NeZero N] (Y : ℝ) :
    QuotientL2 N →ₗ[ℂ] QuotientL2 N where
  toFun := quotientCoreRestriction N Y
  map_add' u v := by
    apply Lp.ext
    filter_upwards [quotientCoreRestriction_coe_ae N Y (u+v),
      quotientCoreRestriction_coe_ae N Y u,quotientCoreRestriction_coe_ae N Y v,
      Lp.coeFn_add u v,Lp.coeFn_add (quotientCoreRestriction N Y u)
        (quotientCoreRestriction N Y v)] with q hsum hu hv hin hout
    rw [hsum,hout,hu,hv]
    by_cases hq : q ∈ quotientCore N Y <;> simp [hq,hin]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [quotientCoreRestriction_coe_ae N Y (c • u),
      quotientCoreRestriction_coe_ae N Y u,Lp.coeFn_smul c u,
      Lp.coeFn_smul c (quotientCoreRestriction N Y u)] with q hmul hu hin hout
    rw [hmul,hout,hu]
    by_cases hq : q ∈ quotientCore N Y <;> simp [hq,hin]

theorem quotientCoreRestriction_norm_le (N : ℕ) [NeZero N] (Y : ℝ) (u : QuotientL2 N) :
    ‖quotientCoreRestriction N Y u‖ ≤ ‖u‖ := by
  have h : ‖quotientCoreRestriction N Y u‖ ≤ 1 * ‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [quotientCoreRestriction_coe_ae N Y u] with q hq
    rw [hq,one_mul]
    by_cases hm : q ∈ quotientCore N Y <;> simp [hm]
  simpa only [one_mul] using h

def quotientCoreRestrictionCLM (N : ℕ) [NeZero N] (Y : ℝ) :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  (quotientCoreRestrictionLinear N Y).mkContinuous 1 (fun u => by
    simpa only [one_mul] using quotientCoreRestriction_norm_le N Y u)

def completedCoreRestriction (N : ℕ) [NeZero N] (Y : ℝ) :
    EnergyCompletion N →L[ℂ] QuotientL2 N :=
  (quotientCoreRestrictionCLM N Y).comp (physicalProjection N)

theorem completedCoreRestriction_norm_le (N : ℕ) [NeZero N] (Y : ℝ) (e : EnergyCompletion N) :
    ‖completedCoreRestriction N Y e‖ ≤ ‖e‖ :=
  (quotientCoreRestriction_norm_le N Y (physicalProjection N e)).trans
    (physicalProjection_norm_le N e)

theorem completedCoreRestriction_dist_le (N : ℕ) [NeZero N] (Y : ℝ)
    (e f : EnergyCompletion N) :
    dist (completedCoreRestriction N Y e) (completedCoreRestriction N Y f) ≤ dist e f := by
  simpa only [dist_eq_norm,map_sub] using completedCoreRestriction_norm_le N Y (e-f)

theorem completedCoreRestriction_core (N : ℕ) [NeZero N] (Y : ℝ) (u : EnergyCore N) :
    completedCoreRestriction N Y (coreEmbedding N u) = coreL2 N Y (coreSmoothQuotient N u) := by
  change quotientCoreRestriction N Y (physicalProjection N (coreEmbedding N u)) = _
  rw [physicalProjection_core]
  apply Lp.ext
  filter_upwards [quotientCoreRestriction_coe_ae N Y (physicalCore N u),
    ((coreSmoothQuotient N u).memLp.indicator (quotientCore_measurable N Y)).coeFn_toLp,
    (chosenRepresentative_spec N u).1] with q hl hr hq
  rw [hl,hr]
  by_cases hm : q ∈ quotientCore N Y <;> simp [hm,coreSmoothQuotient,hq]

/-- Genuine dense-core approximation with a UNIFORM enlarged energy
budget. The enlarged bound is proved before using local compactness. -/
theorem exists_core_approx_with_energy_budget (N : ℕ) [NeZero N] (A : ℝ)
    (e : EnergyCompletion N) (he : ‖e‖^2 ≤ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : EnergyCore N, ‖u‖^2 ≤ A+1 ∧ dist (coreEmbedding N u) e < ε := by
  have hA : 0 ≤ A := (sq_nonneg ‖e‖).trans he
  have hAp : 0 < A+1 := by linarith
  have hroot : ‖e‖ < Real.sqrt (A+1) := by
    have hs := Real.sq_sqrt hAp.le
    have hn := Real.sqrt_nonneg (A+1)
    nlinarith [norm_nonneg e]
  let η := (Real.sqrt (A+1)-‖e‖)/2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨u,hu⟩ := (coreEmbedding_denseRange N).exists_dist_lt e
    (lt_min hε hη : 0 < min ε η)
  rw [dist_comm] at hu
  refine ⟨u,?_,hu.trans_le (min_le_left _ _)⟩
  have hd : dist (coreEmbedding N u) e < η := hu.trans_le (min_le_right _ _)
  have htri := dist_triangle (coreEmbedding N u) e (0 : EnergyCompletion N)
  simp only [dist_zero_right,coreEmbedding_norm] at htri
  have hn : ‖u‖ < Real.sqrt (A+1) := by dsimp [η] at hd; linarith
  have hs := Real.sq_sqrt hAp.le
  have hroot0 := Real.sqrt_nonneg (A+1)
  nlinarith [norm_nonneg u]

theorem completed_core_energy_ball_subset_core_closure (N : ℕ) [NeZero N]
    (Y A : ℝ) :
    completedCoreRestriction N Y '' {e : EnergyCompletion N | ‖e‖^2 ≤ A} ⊆
      closure ((fun u : EnergyCore N => coreL2 N Y (coreSmoothQuotient N u)) ''
        {u : EnergyCore N | ‖u‖^2 ≤ A+1}) := by
  rintro v ⟨e,he,rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨u,huB,huε⟩ := exists_core_approx_with_energy_budget N A e he ε hε
  refine ⟨coreL2 N Y (coreSmoothQuotient N u),⟨u,huB,rfl⟩,?_⟩
  rw [← completedCoreRestriction_core]
  simpa only [dist_comm] using
    (completedCoreRestriction_dist_le N Y (coreEmbedding N u) e).trans_lt huε

/-- Actual bounded COMPLETED Gamma0 form balls are compact locally on
the genuine truncated quotient core. This is derived, not a compact
embedding assumption. No cusp tail or global spectral claim follows. -/
theorem actual_completed_form_fixed_core_totallyBounded (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded (completedCoreRestriction N Y '' {e : EnergyCompletion N | ‖e‖^2 ≤ A}) := by
  apply (actual_quotient_core_energy_ball_totallyBounded N Y hY (A+1)
    (by linarith)).closure.subset
  exact completed_core_energy_ball_subset_core_closure N Y A

theorem actual_completed_form_fixed_core_compact_closure (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (A : ℝ) (hA : 0 ≤ A) :
    IsCompact (closure (completedCoreRestriction N Y ''
      {e : EnergyCompletion N | ‖e‖^2 ≤ A})) :=
  (actual_completed_form_fixed_core_totallyBounded N Y hY A hA).closure.isCompact
    isClosed_closure.isComplete

/-- The physical-domain version uses exactly its original quotient
norm plus the actual Dirichlet pairing of its unique energy lift. -/
theorem actual_physical_form_fixed_core_totallyBounded (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded ((fun u : actualEnergyFormDomain N =>
      quotientCoreRestriction N Y (u : QuotientL2 N)) ''
      {u : actualEnergyFormDomain N | ‖(u : QuotientL2 N)‖^2 +
        (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re ≤ A}) := by
  apply (actual_completed_form_fixed_core_totallyBounded N Y hY A hA).subset
  rintro v ⟨u,hu,rfl⟩
  refine ⟨actualEnergyLift N u,?_,?_⟩
  · simpa only [actualEnergyLift_shifted_norm] using hu
  · change quotientCoreRestriction N Y (physicalProjection N (actualEnergyLift N u)) = _
    rw [actualEnergyLift_projection]

end
end ImbalancedChen.Part3.Gamma0CompletedFormFixedCoreRellich20261026b
