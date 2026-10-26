import ImbalancedChen.Part3Gamma0UniformTailCompactnessCriterion

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Strong exhaustion and an actual complementary-restriction contraction
make the literal quotient tail uniformly small on every totally bounded
subset of the original quotient L2 space. Consequently, on actual bounded
energy families the displayed uniform quotient-tail condition is exactly
equivalent to global quotient L2 total boundedness.

This equivalence isolates the missing all-cusps estimate. It does not
assert that the actual cuspidal family satisfies that condition.
-/

namespace ImbalancedChen.Part3.Gamma0UniformTailNecessity20261026b
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0QuotientChartReconstruction20261026b
open Gamma0CompletedFormFixedCoreRellich20261026b
open Gamma0QuotientCoreExhaustion20261026b
open Gamma0UniformTailCompactnessCriterion20261026b

theorem quotient_remainder_norm_le (N : ℕ) [NeZero N] (Y : ℝ) (u : QuotientL2 N) :
    ‖u-quotientCoreRestriction N Y u‖ ≤ ‖u‖ := by
  have h : ‖u-quotientCoreRestriction N Y u‖ ≤ 1*‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [quotientCoreRestriction_coe_ae N Y u,
      Lp.coeFn_sub u (quotientCoreRestriction N Y u)] with q hres hsub
    rw [hsub, hres, one_mul]
    by_cases hq : q ∈ quotientCore N Y <;> simp [hq]
  simpa only [one_mul] using h

/-- The actual omitted-tail restriction is a contraction, uniformly in
the height; this is proved at the L2 representative level. -/
theorem quotient_remainder_dist_le (N : ℕ) [NeZero N] (Y : ℝ) (u v : QuotientL2 N) :
    dist (u-quotientCoreRestriction N Y u) (v-quotientCoreRestriction N Y v) ≤ dist u v := by
  have hlinear : quotientCoreRestriction N Y (u-v) =
      quotientCoreRestriction N Y u-quotientCoreRestriction N Y v :=
    (quotientCoreRestrictionCLM N Y).map_sub u v
  have heq : (u-quotientCoreRestriction N Y u)-(v-quotientCoreRestriction N Y v) =
      (u-v)-quotientCoreRestriction N Y (u-v) := by
    rw [hlinear]
    abel
  simpa only [dist_eq_norm, heq] using quotient_remainder_norm_le N Y (u-v)

/-- A finite genuine L2 net and strong exhaustion of its finitely many
centres produce uniform actual complement integrals on the whole set. -/
theorem quotient_totallyBounded_implies_uniform_tail (N : ℕ) [NeZero N]
    (S : Set (QuotientL2 N)) (hS : TotallyBounded S) :
    ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 1 ≤ Y ∧ ∀ u ∈ S,
      (∫ q in (quotientCore N Y)ᶜ, ‖u q‖^2 ∂carrierPushforward N) < ε := by
  intro ε hε
  let r := Real.sqrt ε/2
  have hr : 0 < r := div_pos (Real.sqrt_pos.mpr hε) (by norm_num)
  obtain ⟨T, hTsub, hTfin, hTcover⟩ := Metric.finite_approx_of_totallyBounded hS r hr
  have hevent : ∀ᶠ Y : ℝ in atTop, ∀ v ∈ T,
      ‖v-quotientCoreRestriction N Y v‖ < r := by
    apply hTfin.eventually_all.mpr
    intro v hv
    exact (quotientCoreRestriction_norm_error_tendsto_zero N v).eventually (gt_mem_nhds hr)
  obtain ⟨Y, hY, hcentres⟩ := ((eventually_ge_atTop (1 : ℝ)).and hevent).exists
  refine ⟨Y, hY, ?_⟩
  intro u hu
  obtain ⟨v, hv, hd⟩ := mem_iUnion₂.mp (hTcover hu)
  rw [mem_ball] at hd
  have hrem := quotient_remainder_dist_le N Y u v
  have htri := dist_triangle (u-quotientCoreRestriction N Y u)
    (v-quotientCoreRestriction N Y v) 0
  simp only [dist_zero_right] at htri
  have hvsmall := hcentres v hv
  have hnorm : ‖u-quotientCoreRestriction N Y u‖ < Real.sqrt ε := by
    dsimp [r] at hd hvsmall
    linarith
  rw [← restriction_error_square N Y u]
  have hsqrt := Real.sq_sqrt hε.le
  nlinarith [norm_nonneg (u-quotientCoreRestriction N Y u), Real.sqrt_nonneg ε]

/-- The uniform tail condition is NECESSARY and SUFFICIENT on bounded
families of the original completed quotient energy space. This is a
criterion, not an unconditional cuspidal compact embedding theorem. -/
theorem completed_bounded_family_totallyBounded_iff_uniform_tail
    (N : ℕ) [NeZero N] (S : Set (EnergyCompletion N)) (A : ℝ) (hA : 0 ≤ A)
    (henergy : ∀ e ∈ S, ‖e‖^2 ≤ A) :
    TotallyBounded (physicalProjection N '' S) ↔ UniformQuotientTail N S := by
  constructor
  · intro htb ε hε
    obtain ⟨Y, hY, htail⟩ := quotient_totallyBounded_implies_uniform_tail N
      (physicalProjection N '' S) htb ε hε
    exact ⟨Y, hY, fun e he => htail _ ⟨e, he, rfl⟩⟩
  · exact completed_family_totallyBounded_of_uniform_tail N S A hA henergy

end
end ImbalancedChen.Part3.Gamma0UniformTailNecessity20261026b
