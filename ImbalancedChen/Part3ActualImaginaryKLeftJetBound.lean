import ImbalancedChen.Part3ActualImaginaryKIConnection
import ImbalancedChen.Part3GeneralISmallQWronskian
import ImbalancedChen.Part3GeneralActualRadialGreen

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual bounded left-end value and first logarithmic derivative of K_(i*tau),
for nonzero real tau. The bound is derived from the literal I-series scaled
limits and the proved actual imaginary K/I connection. No oscillatory
asymptotic, endpoint bound, or transform identity is assumed.
-/
namespace ImbalancedChen.Part3.ActualImaginaryKLeftJetBound20261025a
noncomputable section
open Set Filter Topology
open GeneralComplexISeriesSourceOnly GeneralISmallQWronskian20261025a
open GeneralActualRadialGreenSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ActualImaginaryKIConnectionSourceOnly

private theorem scaled_power_norm_one {nu : ℂ} (hnu : nu.re = 0) (r : ℝ) :
    ‖(((Real.exp r / 2 : ℝ) : ℂ) ^ (-nu))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < Real.exp r / 2)]
  simp only [Complex.neg_re, hnu, neg_zero, Real.rpow_zero]

theorem exists_radialI_left_jet_bound {nu : ℂ} (hnu : nu.re = 0) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r ≤ R,
      ‖radialI nu r‖ ≤ C ∧ ‖deriv (radialI nu) r‖ ≤ C := by
  have hn : -1 < nu.re := by rw [hnu]; norm_num
  let A : ℂ := (Complex.Gamma (nu + 1))⁻¹
  let B : ℂ := nu * A
  have hI : Tendsto (fun r : ℝ => ‖radialI nu r‖) atBot (𝓝 ‖A‖) := by
    have h := ((tendsto_scaled_generalI_zero hn).norm).comp
      Real.tendsto_exp_atBot_nhdsGT
    simpa only [Function.comp_def, norm_mul, scaled_power_norm_one hnu,
      one_mul, radialI] using h
  have hD : Tendsto (fun r : ℝ => ‖deriv (radialI nu) r‖) atBot (𝓝 ‖B‖) := by
    have h := ((tendsto_scaled_generalI_deriv_zero hn).norm).comp
      Real.tendsto_exp_atBot_nhdsGT
    have he (r : ℝ) : ‖deriv (radialI nu) r‖ =
        ‖(Real.exp r : ℂ) * (((Real.exp r / 2 : ℝ) : ℂ) ^ (-nu)) *
          deriv (generalI nu) (Real.exp r)‖ := by
      rw [(radialI_hasDerivAt hn r).deriv]
      simp only [Complex.real_smul, norm_mul, scaled_power_norm_one hnu, mul_one]
    simpa only [Function.comp_def, ← he] using h
  let C : ℝ := ‖A‖ + ‖B‖ + 2
  have he : ∀ᶠ r : ℝ in atBot,
      ‖radialI nu r‖ ≤ C ∧ ‖deriv (radialI nu) r‖ ≤ C := by
    filter_upwards [hI.eventually (gt_mem_nhds (lt_add_one ‖A‖)),
      hD.eventually (gt_mem_nhds (lt_add_one ‖B‖))] with r hrI hrD
    constructor <;> dsimp [C] <;> linarith [norm_nonneg A, norm_nonneg B]
  obtain ⟨R, hR⟩ := eventually_atBot.mp he
  exact ⟨C, R, by dsimp [C]; positivity, hR⟩

/-- Both members of the actual K jet are bounded at the left endpoint.
The exclusion tau=0 is explicit; all positive KL spectral parameters are covered. -/
theorem exists_imaginaryK_left_jet_bound (tau : ℝ) (htau : tau ≠ 0) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r ≤ R,
      ‖radialK ((tau : ℂ) * Complex.I) r‖ ≤ C ∧
        ‖deriv (radialK ((tau : ℂ) * Complex.I)) r‖ ≤ C := by
  let nu : ℂ := (tau : ℂ) * Complex.I
  let c : ℂ := (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu))
  have hn : nu.re = 0 := by simp [nu]
  have hmn : (-nu).re = 0 := by simp only [Complex.neg_re, hn, neg_zero]
  obtain ⟨CP, RP, hCP, hp⟩ := exists_radialI_left_jet_bound hn
  obtain ⟨CM, RM, hCM, hm⟩ := exists_radialI_left_jet_bound hmn
  have hvalue : radialK nu = fun r => c * (radialI (-nu) r - radialI nu r) := by
    funext r
    exact complexOrderK_imaginary_eq_generalI_sub tau htau (Real.exp_pos r)
  have hderiv (r : ℝ) : deriv (radialK nu) r =
      c * (deriv (radialI (-nu)) r - deriv (radialI nu) r) := by
    rw [hvalue]
    exact (((radialI_C2 (by rw [hmn]; norm_num)).differentiable (by norm_num) r).hasDerivAt.sub
      ((radialI_C2 (by rw [hn]; norm_num)).differentiable (by norm_num) r).hasDerivAt).const_mul c |>.deriv
  refine ⟨‖c‖ * (CM + CP) + 1, min RM RP, by positivity, ?_⟩
  intro r hr
  have hm' := hm r (hr.trans (min_le_left _ _))
  have hp' := hp r (hr.trans (min_le_right _ _))
  constructor
  · change ‖radialK nu r‖ ≤ _
    rw [hvalue, norm_mul]
    exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hm'.1 hp'.1))
      (norm_nonneg c)).trans (by linarith)
  · change ‖deriv (radialK nu) r‖ ≤ _
    rw [hderiv, norm_mul]
    exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hm'.2 hp'.2))
      (norm_nonneg c)).trans (by linarith)

end
end ImbalancedChen.Part3.ActualImaginaryKLeftJetBound20261025a
