import ImbalancedChen.Part3Gamma0QuotientCoreExhaustion
import Mathlib.Topology.Sequences

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An honest tightness criterion on the ORIGINAL actual quotient energy
completion: fixed-core compactness is supplied by its proved theorem;
the additional hypothesis is stated literally as uniform smallness of
actual quotient-complement square integrals. This module does NOT prove
that hypothesis for all cuspidal vectors or identify an all-cusps graph.

The criterion gives actual global quotient L2 total boundedness and a
strongly convergent subsequence for sequences satisfying the displayed
energy bound and displayed uniform tail condition. The corresponding
physical form-domain result uses its original norm and Dirichlet pair.
-/

namespace ImbalancedChen.Part3.Gamma0UniformTailCompactnessCriterion20261026b
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0QuotientChartReconstruction20261026b
open Gamma0CompletedFormFixedCoreRellich20261026b
open Gamma0QuotientCoreExhaustion20261026b

/-- This is the remaining concrete uniform tail obligation, not an
assertion that arbitrary energy balls already satisfy it. -/
def UniformQuotientTail (N : ℕ) [NeZero N] (S : Set (EnergyCompletion N)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 1 ≤ Y ∧ ∀ e ∈ S,
    (∫ q in (quotientCore N Y)ᶜ, ‖(physicalProjection N e) q‖^2
      ∂carrierPushforward N) < ε

/-- Real fixed-core Rellich plus the explicit actual uniform tail
condition gives the original quotient L2 total boundedness. -/
theorem completed_family_totallyBounded_of_uniform_tail (N : ℕ) [NeZero N]
    (S : Set (EnergyCompletion N)) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ e ∈ S, ‖e‖^2 ≤ A) (htail : UniformQuotientTail N S) :
    TotallyBounded (physicalProjection N '' S) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨Y, hY, htailY⟩ := htail ((ε/2)^2) (sq_pos_of_pos (by linarith))
  obtain ⟨T, hTsub, hTfin, hTcover⟩ := Metric.finite_approx_of_totallyBounded
    (actual_completed_form_fixed_core_totallyBounded N Y hY A hA)
    (ε/2) (by linarith)
  refine ⟨T, hTfin, ?_⟩
  rintro v ⟨e, he, rfl⟩
  obtain ⟨w, hw, hd⟩ := mem_iUnion₂.mp (hTcover ⟨e, henergy e he, rfl⟩)
  refine mem_iUnion₂.mpr ⟨w, hw, ?_⟩
  rw [mem_ball] at hd ⊢
  have hsmall : dist (physicalProjection N e) (completedCoreRestriction N Y e) < ε/2 := by
    have herr := restriction_error_square N Y (physicalProjection N e)
    have htailE := htailY e he
    change ‖physicalProjection N e-completedCoreRestriction N Y e‖^2 = _ at herr
    rw [← herr] at htailE
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (physicalProjection N e-completedCoreRestriction N Y e)]
  exact (dist_triangle _ (completedCoreRestriction N Y e) _).trans_lt
    (by linarith)

/-- A concrete strong L2 subsequence extraction. The only unproved
geometric input remains the explicitly displayed uniform tail predicate. -/
theorem completed_sequence_has_L2_subsequence (N : ℕ) [NeZero N]
    (e : ℕ → EnergyCompletion N) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ n, ‖e n‖^2 ≤ A) (htail : UniformQuotientTail N (range e)) :
    ∃ u : QuotientL2 N, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => physicalProjection N (e (φ n))) atTop (𝓝 u) := by
  have htb := completed_family_totallyBounded_of_uniform_tail N (range e) A hA
    (by rintro v ⟨n, rfl⟩; exact henergy n) htail
  have hc := htb.closure.isCompact isClosed_closure.isComplete
  obtain ⟨u, hu, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (fun n => subset_closure ⟨e n, ⟨n, rfl⟩, rfl⟩)
  exact ⟨u, φ, hφ, hlim⟩

/-- The same explicit criterion for the EXISTING physical form domain;
its budget is original quotient mass plus actual Dirichlet energy. -/
theorem physical_form_family_totallyBounded_of_uniform_tail (N : ℕ) [NeZero N]
    (S : Set (actualEnergyFormDomain N)) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ u ∈ S, ‖(u : QuotientL2 N)‖^2 +
      (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re ≤ A)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 1 ≤ Y ∧ ∀ u ∈ S,
      (∫ q in (quotientCore N Y)ᶜ, ‖(u : QuotientL2 N) q‖^2
        ∂carrierPushforward N) < ε) :
    TotallyBounded ((fun u : actualEnergyFormDomain N => (u : QuotientL2 N)) '' S) := by
  have he : ∀ e ∈ actualEnergyLift N '' S, ‖e‖^2 ≤ A := by
    rintro e ⟨u, hu, rfl⟩
    simpa only [actualEnergyLift_shifted_norm] using henergy u hu
  have ht : UniformQuotientTail N (actualEnergyLift N '' S) := by
    intro ε hε
    obtain ⟨Y, hY, htailY⟩ := htail ε hε
    refine ⟨Y, hY, ?_⟩
    rintro e ⟨u, hu, rfl⟩
    simpa only [actualEnergyLift_projection] using htailY u hu
  have htb := completed_family_totallyBounded_of_uniform_tail N
    (actualEnergyLift N '' S) A hA he ht
  have himage : physicalProjection N '' (actualEnergyLift N '' S) =
      (fun u : actualEnergyFormDomain N => (u : QuotientL2 N)) '' S := by
    rw [← image_comp]
    congr 1
    funext u
    exact actualEnergyLift_projection N u
  exact himage ▸ htb

end
end ImbalancedChen.Part3.Gamma0UniformTailCompactnessCriterion20261026b
