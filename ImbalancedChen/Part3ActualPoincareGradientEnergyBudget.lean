import ImbalancedChen.Part3ActualPoincareDirichletTrace
import ImbalancedChen.Part3Gamma0CompactGlobalOverlap
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Uniform finite-hit first-gradient and weighted energy budget

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The original compact seed container controls the supports of the actual
translated FIRST derivatives: outside that closed container the seed
vanishes on a neighborhood, so both derivative germs vanish. Actual global
compact overlap therefore bounds the number of nonzero gradient terms.
Finite Cauchy and actual Mobius covariance give a pointwise hyperbolic
energy budget, before any integration or quotient energy assumption.
-/

namespace ImbalancedChen.Part3.ActualPoincareGradientEnergyBudget20261025a
noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a
open ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a
open ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a
open ImbalancedChen.Part3.ActualPoincareDirichletTrace20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a

def chartEnergy (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  p.2 ^ 2 * (‖sliceDx F p‖ ^ 2 + ‖sliceDy F p‖ ^ 2)

theorem chartEnergy_nonneg (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    0 ≤ chartEnergy F p := mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem chartEnergy_eq_re_hyperbolicDirichlet (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    chartEnergy F p = (hyperbolicChartDirichlet F F p).re := by
  rw [hyperbolicChartDirichlet, chartDirichlet_self_eq]
  simp only [chartEnergy, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
    ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem chartLift_continuousAt_positive {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt chartLift p := by
  apply (UpperHalfPlane.contMDiffAt_ofComplex (n := 2) hp).continuousAt.comp
  have heq : complexOfPair = (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
    funext q
    ext <;> simp [complexOfPair]
  rw [heq]
  fun_prop

/-- The SAME original compact container controls derivative germs, even
at points where the seed value happens to vanish inside its support. -/
theorem translated_seed_zero_germ_of_outside_compact (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (q : effectiveGamma0 N)
    {p : ℝ × ℝ} (hp : 0 < p.2)
    (hq : effectiveMatrixAction N q (chartLift p) ∉ finiteCompactTensorSupportK s T) :
    translatedFiniteTensorChart N q s T =ᶠ[𝓝 p] (fun _ => 0) := by
  have hact : Continuous (effectiveMatrixAction N q) := by
    change Continuous (fun w : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ (effectiveRepresentative N q : SL(2, ℤ))) • w)
    exact continuous_const_smul _
  have hc := hact.continuousAt.comp (chartLift_continuousAt_positive hp)
  have hout : ∀ᶠ p' in 𝓝 p,
      effectiveMatrixAction N q (chartLift p') ∉ finiteCompactTensorSupportK s T :=
    hc ((finiteCompactTensorSupportK_isCompact s T).isClosed.isOpen_compl.mem_nhds hq)
  have hpos : ∀ᶠ p' in 𝓝 p, 0 < p'.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  filter_upwards [hout,hpos] with p' hpout hp'
  rw [translatedFiniteTensorChart_eq_actual N q s T hp']
  by_contra hnonzero
  exact hpout (finiteCoreFunction_support_subset s T hnonzero)

theorem actualPoincare_slice_first_eq_tsum (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) {p : ℝ × ℝ} (hp : 0 < p.2) :
    sliceDx (extendUpper (finiteCompactTensorPoincare N s T)) p =
      ∑' q : effectiveGamma0 N, sliceDx (translatedFiniteTensorChart N q s T) p ∧
    sliceDy (extendUpper (finiteCompactTensorPoincare N s T)) p =
      ∑' q : effectiveGamma0 N, sliceDy (translatedFiniteTensorChart N q s T) p := by
  classical
  obtain ⟨S,hfinite,hzero⟩ := actualPoincare_firstGradient_local_finite N s T hp
  have hdiff : ∀ q ∈ S, DifferentiableAt ℝ (translatedFiniteTensorChart N q s T) p :=
    fun q _ => (translatedFiniteTensorChart_contDiffAt N q s T hp).differentiableAt (by norm_num)
  constructor
  · rw [sliceDx_eq_of_eventuallyEq hfinite, sliceDx_finsetSum S _ p hdiff]
    symm
    apply tsum_eq_sum
    intro q hq
    simpa only [sliceDx, deriv_const] using sliceDx_eq_of_eventuallyEq (hzero q hq)
  · rw [sliceDy_eq_of_eventuallyEq hfinite, sliceDy_finsetSum S _ p hdiff]
    symm
    apply tsum_eq_sum
    intro q hq
    simpa only [sliceDy, deriv_const] using sliceDy_eq_of_eventuallyEq (hzero q hq)

/-- A single finite hit set, of cardinal bounded BEFORE p is chosen,
represents both first gradients. This is stronger than mere localfinite
derivative summability. -/
theorem actualPoincare_uniform_firstGradient_finite (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ∃ S : Finset (effectiveGamma0 N),
      S.card ≤ compactOverlapBound N (finiteCompactTensorSupportK s T) ∧
      (∀ q ∉ S, sliceDx (translatedFiniteTensorChart N q s T) p = 0 ∧
        sliceDy (translatedFiniteTensorChart N q s T) p = 0) ∧
      sliceDx (extendUpper (finiteCompactTensorPoincare N s T)) p =
        ∑ q ∈ S, sliceDx (translatedFiniteTensorChart N q s T) p ∧
      sliceDy (extendUpper (finiteCompactTensorPoincare N s T)) p =
        ∑ q ∈ S, sliceDy (translatedFiniteTensorChart N q s T) p := by
  classical
  have hh := compact_hits_finite_and_card_le N (finiteCompactTensorSupportK_isCompact s T) (chartLift p)
  let S := hh.1.toFinset
  have hcard : S.card ≤ compactOverlapBound N (finiteCompactTensorSupportK s T) := by
    change hh.1.toFinset.card ≤ _
    rw [← Set.ncard_eq_toFinset_card _ hh.1]
    exact hh.2.trans (Nat.le_succ _)
  have hzero : ∀ q ∉ S, sliceDx (translatedFiniteTensorChart N q s T) p = 0 ∧
      sliceDy (translatedFiniteTensorChart N q s T) p = 0 := by
    intro q hq
    have hout : effectiveMatrixAction N q (chartLift p) ∉ finiteCompactTensorSupportK s T := by
      intro h
      exact hq (hh.1.mem_toFinset.mpr h)
    have hg := translated_seed_zero_germ_of_outside_compact N s T q hp hout
    constructor
    · simpa only [sliceDx, deriv_const] using sliceDx_eq_of_eventuallyEq hg
    · simpa only [sliceDy, deriv_const] using sliceDy_eq_of_eventuallyEq hg
  have htsum := actualPoincare_slice_first_eq_tsum N s T hp
  refine ⟨S,hcard,hzero,?_,?_⟩
  · exact htsum.1.trans (tsum_eq_sum (fun q hq => (hzero q hq).1))
  · exact htsum.2.trans (tsum_eq_sum (fun q hq => (hzero q hq).2))

private theorem finite_complex_cauchy {κ : Type*} (S : Finset κ) (f : κ → ℂ) :
    ‖∑ q ∈ S, f q‖ ^ 2 ≤ (S.card : ℝ) * ∑ q ∈ S, ‖f q‖ ^ 2 := by
  have hn := norm_sum_le S f
  have hsq := pow_le_pow_left₀ (norm_nonneg (∑ q ∈ S, f q)) hn 2
  have hCS : (∑ q ∈ S, ‖f q‖) ^ 2 ≤ (S.card : ℝ) * ∑ q ∈ S, ‖f q‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun q => ‖f q‖)
  exact hsq.trans hCS

/-- Uniform finite Cauchy budget for the genuine weighted first-gradient
energy. The summands are actual Mobius pullbacks of the original seed. -/
theorem actualPoincare_pointwise_gradient_energy_budget (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) {p : ℝ × ℝ} (hp : 0 < p.2) :
    chartEnergy (extendUpper (finiteCompactTensorPoincare N s T)) p ≤
      (compactOverlapBound N (finiteCompactTensorSupportK s T) : ℝ) *
        ∑' q : effectiveGamma0 N, chartEnergy (translatedFiniteTensorChart N q s T) p := by
  classical
  obtain ⟨S,hcard,hzero,hx,hy⟩ := actualPoincare_uniform_firstGradient_finite N s T hp
  have hsum : (∑' q : effectiveGamma0 N, chartEnergy (translatedFiniteTensorChart N q s T) p) =
      ∑ q ∈ S, chartEnergy (translatedFiniteTensorChart N q s T) p := by
    apply tsum_eq_sum
    intro q hq
    simp only [chartEnergy, (hzero q hq).1, (hzero q hq).2, norm_zero, zero_pow
      (by decide : 2 ≠ 0), add_zero, mul_zero]
  rw [hsum]
  have hxCS := finite_complex_cauchy S (fun q => sliceDx (translatedFiniteTensorChart N q s T) p)
  have hyCS := finite_complex_cauchy S (fun q => sliceDy (translatedFiniteTensorChart N q s T) p)
  have hsq : ‖sliceDx (extendUpper (finiteCompactTensorPoincare N s T)) p‖ ^ 2 +
      ‖sliceDy (extendUpper (finiteCompactTensorPoincare N s T)) p‖ ^ 2 ≤
      (S.card : ℝ) * (∑ q ∈ S, (‖sliceDx (translatedFiniteTensorChart N q s T) p‖ ^ 2 +
        ‖sliceDy (translatedFiniteTensorChart N q s T) p‖ ^ 2)) := by
    rw [hx,hy]
    simpa only [Finset.sum_add_distrib, mul_add] using add_le_add hxCS hyCS
  have hweighted := mul_le_mul_of_nonneg_left hsq (sq_nonneg p.2)
  have hfinite : chartEnergy (extendUpper (finiteCompactTensorPoincare N s T)) p ≤
      (S.card : ℝ) * ∑ q ∈ S, chartEnergy (translatedFiniteTensorChart N q s T) p := by
    simpa only [chartEnergy, Finset.mul_sum, mul_left_comm] using hweighted
  exact hfinite.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
    (Finset.sum_nonneg (fun q _ => chartEnergy_nonneg _ p)))

/-- The actual y-squared compensation transports each positive summand
to the original seed energy evaluated at the genuine action point. -/
theorem translated_chartEnergy_eq_actual (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (q : effectiveGamma0 N)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    chartEnergy (translatedFiniteTensorChart N q s T) p =
      chartEnergy (extendUpper (finiteCoreFunction s T))
        ((effectiveMatrixAction N q (chartLift p)).re,
          (effectiveMatrixAction N q (chartLift p)).im) := by
  have hsmooth : ContDiff ℝ 2 (finiteChartFunction s T) := by
    apply ContDiff.sum
    intro i _
    exact ((T i).horizontal_smooth.comp contDiff_fst).mul
      ((T i).vertical_smooth.comp contDiff_snd)
  let g : SL(2, ℤ) := (effectiveRepresentative N q : SL(2, ℤ))
  have hC1 : ContDiffAt ℝ 1 (finiteChartFunction s T) (mobiusChart g p) :=
    hsmooth.contDiffAt.of_le (by norm_num)
  have hcov := hyperbolicChartDirichlet_comp_mobiusChart g
    (finiteChartFunction s T) (finiteChartFunction s T) p hp hC1 hC1
  rw [chartEnergy_eq_re_hyperbolicDirichlet, chartEnergy_eq_re_hyperbolicDirichlet]
  simpa only [translatedFiniteTensorChart, extendUpper_finiteCoreFunction,
    mobiusChart_eq_actual _ hp] using congrArg Complex.re hcov

/-- Actual hyperbolic gradient energy of the actual Poincare seed is
bounded by the same compact-overlap constant times the actual positive
trace of the original seed energy. No energy-integrability premise. -/
theorem actualPoincare_pointwise_seed_energy_budget (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane) :
    chartEnergy (extendUpper (finiteCompactTensorPoincare N s T)) (z.re,z.im) ≤
      (compactOverlapBound N (finiteCompactTensorSupportK s T) : ℝ) *
        ∑' q : effectiveGamma0 N, chartEnergy (extendUpper (finiteCoreFunction s T))
          ((effectiveMatrixAction N q z).re,(effectiveMatrixAction N q z).im) := by
  have hbudget := actualPoincare_pointwise_gradient_energy_budget N s T z.im_pos
  have heq : (fun q : effectiveGamma0 N => chartEnergy (translatedFiniteTensorChart N q s T)
      (z.re,z.im)) = (fun q => chartEnergy (extendUpper (finiteCoreFunction s T))
        ((effectiveMatrixAction N q z).re,(effectiveMatrixAction N q z).im)) := by
    funext q
    simpa only [chartLift_pair] using translated_chartEnergy_eq_actual N s T q z.im_pos
  rwa [heq] at hbudget

end
end ImbalancedChen.Part3.ActualPoincareGradientEnergyBudget20261025a
