import ImbalancedChen.Part3GammaActualSmoothRepresentativeIMS

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact actual quotient closed-form IMS for EVERY existing energy vector.
Native smooth-representative IMS is extended through the actual dense
core by continuity of the proved cutoff and error multipliers. The square
test is M applied twice, with literal actual chi_Y^2 physical coefficient.
The shifted norm version pays the physical mass identity explicitly.
-/

namespace ImbalancedChen.Part3.GammaActualClosedFormIMS20261026b

noncomputable section
open Set Filter MeasureTheory UniformSpace
open scoped Topology UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaActualQuotientCutoffMultiplier20261026b GammaActualClosedFormCutoffMultiplier20261026b
open GammaActualCutoffErrorQuadratic20261026b GammaActualSmoothRepresentativeIMS20261026b
open ActualModularCutoffEnergyBudget20261025a ActualModularCutoffMaassBudget20261025a

/-- Full native actual closed-form IMS. Its weighted error integral is
the genuine quotient gradient-energy coefficient, not a caller budget. -/
theorem actualClosedFormCutoff_IMS
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (e : EnergyCompletion N) :
    let M := actualClosedFormCutoff N Y hY
    (actualDirichletPair N (M e) (M e)).re = (actualDirichletPair N (M (M e)) e).re +
      ∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q *
        ‖physicalProjection N e q‖^2 ∂carrierPushforward N := by
  let M := actualClosedFormCutoff N Y hY
  let W := actualCutoffErrorMultiplier N Y hY
  change (actualDirichletPair N (M e) (M e)).re = _
  rw [← actualCutoffError_quadratic_integral N Y hY (physicalProjection N e)]
  refine Completion.induction_on e ?_ ?_
  · apply isClosed_eq
    · unfold actualDirichletPair
      fun_prop
    · unfold actualDirichletPair
      fun_prop
  · intro u
    have hquot : quotientMultiplier N (coreRepresentative N u)
        (coreRepresentative_gamma0_invariant N u) = chosenQuotientRepresentative N u := by
      funext q
      exact Quotient.inductionOn q (fun z => rfl)
    have hrep : ((physicalProjection N (coreEmbedding N u) : QuotientL2 N) :
        Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N (coreRepresentative N u) (coreRepresentative_gamma0_invariant N u) := by
      rw [hquot,physicalProjection_core]
      exact (chosenRepresentative_spec N u).1
    have hh := actualClosedFormCutoff_IMS_of_smooth_representative N Y hY (coreEmbedding N u)
      (coreRepresentative N u) (coreRepresentative_gamma0_invariant N u)
      ((coreRepresentative_cinfty N u).of_le (by simp)) hrep
    simpa only [actualCutoffError_quadratic_integral] using hh

private theorem quotientCutoffCoefficient_star (N : ℕ) (Y : ℝ) (q : Gamma0OrbitSpace N) :
    star (quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) q) =
      quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) q := by
  refine Quotient.inductionOn q (fun z => ?_)
  change star (complexGlobalH Y z) = complexGlobalH Y z
  simp only [complexGlobalH,Complex.star_def,Complex.conj_ofReal]

/-- Exact actual physical mass pairing for the square multiplier,
proved from the real original cutoff coefficient on arbitrary L2 input. -/
theorem actualQuotientCutoff_norm_sq_pairing
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    let Q := actualQuotientCutoffMultiplier N Y hY
    ‖Q f‖^2 = (inner ℂ (Q (Q f)) f).re := by
  let Q := actualQuotientCutoffMultiplier N Y hY
  change ‖Q f‖^2 = (inner ℂ (Q (Q f)) f).re
  rw [InnerProductSpace.norm_sq_eq_re_inner,L2.inner_def,L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (Q f) (Q f)),
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (Q (Q f)) f)]
  apply integral_congr_ae
  filter_upwards [actualQuotientCutoffMultiplier_coe_ae N Y hY f,
    actualQuotientCutoffMultiplier_coe_ae N Y hY (Q f)] with q hf hQf
  simp only [Pi.mul_apply] at hf hQf
  rw [hf,hQf,hf]
  simp only [RCLike.inner_apply',star_mul,quotientCutoffCoefficient_star N Y q]
  congr 1
  ring

theorem actualClosedFormCutoff_physical_square_pairing
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (e : EnergyCompletion N) :
    let M := actualClosedFormCutoff N Y hY
    ‖physicalProjection N (M e)‖^2 =
      (inner ℂ (physicalProjection N (M (M e))) (physicalProjection N e)).re := by
  simpa only [actualClosedFormCutoff_physical] using
    actualQuotientCutoff_norm_sq_pairing N Y hY (physicalProjection N e)

/-- The exact shifted-norm endpoint used by native defect testing.
The original actual cutoff-square test is M(M e), so its literal physical
coefficient is chi_Y^2; no independent square operator is postulated. -/
theorem actualClosedFormCutoff_shifted_IMS
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (e : EnergyCompletion N) :
    let M := actualClosedFormCutoff N Y hY
    ‖M e‖^2 = (inner ℂ e (M (M e))).re +
      ∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q *
        ‖physicalProjection N e q‖^2 ∂carrierPushforward N := by
  have hIMS := actualClosedFormCutoff_IMS N Y hY e
  have hmass := actualClosedFormCutoff_physical_square_pairing N Y hY e
  have hsym := inner_re_symm (𝕜 := ℂ)
    (actualClosedFormCutoff N Y hY (actualClosedFormCutoff N Y hY e)) e
  unfold actualDirichletPair at hIMS
  rw [Complex.sub_re,Complex.sub_re,← InnerProductSpace.norm_sq_eq_re_inner,
    ← InnerProductSpace.norm_sq_eq_re_inner] at hIMS
  dsimp only at hIMS hmass ⊢
  linarith

end
end ImbalancedChen.Part3.GammaActualClosedFormIMS20261026b
