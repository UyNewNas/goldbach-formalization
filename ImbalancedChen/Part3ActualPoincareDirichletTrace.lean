import ImbalancedChen.Part3ActualMobiusDirichletCovariance
import ImbalancedChen.Part3ActualGamma0MaassDescent
import ImbalancedChen.Part3Gamma0ComplexL1PoincareUnfolding

/-!
# Actual locally finite first-gradient Dirichlet trace

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual effective Gamma0 Poincare sum differentiates as a finite sum
of first derivatives near every point. Pairing with an invariant C2
function and using actual Mobius covariance identifies its hyperbolic
Dirichlet density with the actual complex trace of the compact-seed
pairing. No derivative identity, energy bound or integrability conclusion
is an input. Integration and quotient Green identities are separate.
-/

namespace ImbalancedChen.Part3.ActualPoincareDirichletTrace20261025a
noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a
open ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a
open ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a

theorem sliceDx_eq_of_eventuallyEq {F G : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (h : F =ᶠ[𝓝 p] G) : sliceDx F p = sliceDx G p := by
  have hx : (fun x : ℝ => F (x,p.2)) =ᶠ[𝓝 p.1]
      (fun x : ℝ => G (x,p.2)) :=
    (continuousAt_id.prodMk continuousAt_const).eventually h
  exact hx.deriv_eq

theorem sliceDy_eq_of_eventuallyEq {F G : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (h : F =ᶠ[𝓝 p] G) : sliceDy F p = sliceDy G p := by
  have hy : (fun y : ℝ => F (p.1,y)) =ᶠ[𝓝 p.2]
      (fun y : ℝ => G (p.1,y)) :=
    (continuousAt_const.prodMk continuousAt_id).eventually h
  exact hy.deriv_eq

theorem hyperbolicChartDirichlet_congr_of_eventuallyEq
    {F F' G G' : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hF : F =ᶠ[𝓝 p] F') (hG : G =ᶠ[𝓝 p] G') :
    hyperbolicChartDirichlet F G p = hyperbolicChartDirichlet F' G' p := by
  unfold hyperbolicChartDirichlet chartDirichlet
  rw [sliceDx_eq_of_eventuallyEq hF, sliceDy_eq_of_eventuallyEq hF,
    sliceDx_eq_of_eventuallyEq hG, sliceDy_eq_of_eventuallyEq hG]

theorem sliceDx_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) p) :
    sliceDx (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, sliceDx (F i) p := by
  apply deriv_fun_sum
  intro i hi
  exact (hF i hi).comp p.1 (differentiableAt_id.prodMk differentiableAt_const)

theorem sliceDy_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) p) :
    sliceDy (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, sliceDy (F i) p := by
  apply deriv_fun_sum
  intro i hi
  exact (hF i hi).comp p.2 (differentiableAt_const.prodMk differentiableAt_id)

theorem hyperbolicChartDirichlet_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ × ℝ → ℂ) (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) p) :
    hyperbolicChartDirichlet (fun q => ∑ i ∈ s, F i q) G p =
      ∑ i ∈ s, hyperbolicChartDirichlet (F i) G p := by
  unfold hyperbolicChartDirichlet chartDirichlet
  rw [sliceDx_finsetSum s F p hF, sliceDy_finsetSum s F p hF]
  simp only [Complex.star_def, map_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]

/-- Both the sum formula and the zero germs of every omitted translate
come from the actual proper action on the very same neighborhood. -/
theorem actualPoincare_firstGradient_local_finite (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ∃ S : Finset (effectiveGamma0 N),
      (extendUpper (finiteCompactTensorPoincare N s T) =ᶠ[𝓝 p]
        (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s T p')) ∧
      ∀ q ∉ S, translatedFiniteTensorChart N q s T =ᶠ[𝓝 p] (fun _ => 0) := by
  classical
  obtain ⟨U,hU,S,hS⟩ := compact_seed_locally_finite N (finiteCoreFunction s T)
    (finiteCompactTensorSupportK_isCompact s T) (finiteCoreFunction_support_subset s T)
    (chartLift p)
  have hcont : ContinuousAt chartLift p :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n := 2) hp).continuousAt.comp
      (by
        have heq : complexOfPair =
            (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
          funext q
          ext <;> simp [complexOfPair]
        rw [heq]
        fun_prop)
  have hpre : ∀ᶠ p' in 𝓝 p, chartLift p' ∈ U := hcont hU
  have hpos : ∀ᶠ p' in 𝓝 p, 0 < p'.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  refine ⟨S, ?_, ?_⟩
  · filter_upwards [hpre,hpos] with p' hpU hp'
    rw [extendUpper_chartLift _ p' hp']
    have hsum : finiteCompactTensorPoincare N s T (chartLift p') =
        ∑ q ∈ S, finiteCoreFunction s T (effectiveMatrixAction N q (chartLift p')) :=
      tsum_eq_sum (fun q hq => hS (chartLift p') hpU q hq)
    rw [hsum]
    apply Finset.sum_congr rfl
    intro q _
    exact (translatedFiniteTensorChart_eq_actual N q s T hp').symm
  · intro q hq
    filter_upwards [hpre,hpos] with p' hpU hp'
    rw [translatedFiniteTensorChart_eq_actual N q s T hp']
    exact hS (chartLift p') hpU q hq

/-- A pointwise derivative trace, with omitted derivative terms proved
zero from their genuine neighborhood germs. No derivative-series premise. -/
theorem actualPoincare_hyperbolicDirichlet_eq_tsum (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (G : ℝ × ℝ → ℂ)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    hyperbolicChartDirichlet (extendUpper (finiteCompactTensorPoincare N s T)) G p =
      ∑' q : effectiveGamma0 N,
        hyperbolicChartDirichlet (translatedFiniteTensorChart N q s T) G p := by
  classical
  obtain ⟨S,hfinite,hzero⟩ := actualPoincare_firstGradient_local_finite N s T hp
  calc
    _ = hyperbolicChartDirichlet
        (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s T p') G p :=
      hyperbolicChartDirichlet_congr_of_eventuallyEq hfinite Filter.EventuallyEq.rfl
    _ = ∑ q ∈ S, hyperbolicChartDirichlet (translatedFiniteTensorChart N q s T) G p := by
      apply hyperbolicChartDirichlet_finsetSum
      intro q _
      exact (translatedFiniteTensorChart_contDiffAt N q s T hp).differentiableAt (by norm_num)
    _ = _ := by
      symm
      apply tsum_eq_sum
      intro q hq
      have hx : sliceDx (translatedFiniteTensorChart N q s T) p = 0 := by
        simpa only [sliceDx, deriv_const] using sliceDx_eq_of_eventuallyEq (hzero q hq)
      have hy : sliceDy (translatedFiniteTensorChart N q s T) p = 0 := by
        simpa only [sliceDy, deriv_const] using sliceDy_eq_of_eventuallyEq (hzero q hq)
      simp only [hyperbolicChartDirichlet, chartDirichlet, hx, hy,
        star_zero, zero_mul, add_zero, mul_zero]

private theorem finiteChartFunction_C2 {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) : ContDiff ℝ 2 (finiteChartFunction s T) := by
  apply ContDiff.sum
  intro i _
  exact ((T i).horizontal_smooth.comp contDiff_fst).mul
    ((T i).vertical_smooth.comp contDiff_snd)

/-- Pulling back the invariant outer does not change its derivative
germ; simultaneous actual pullback covariance then transports the seed. -/
theorem translated_hyperbolicDirichlet_eq_actual (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (q : effectiveGamma0 N) {p : ℝ × ℝ} (hp : 0 < p.2) :
    hyperbolicChartDirichlet (translatedFiniteTensorChart N q s T) (extendUpper F) p =
      hyperbolicChartDirichlet (extendUpper (finiteCoreFunction s T)) (extendUpper F)
        ((effectiveMatrixAction N q (chartLift p)).re,
          (effectiveMatrixAction N q (chartLift p)).im) := by
  let γ : CongruenceSubgroup.Gamma0 N := effectiveRepresentative N q
  have hq : 0 < (mobiusChart (γ : SL(2, ℤ)) p).2 := by
    rw [mobiusChart_eq_actual _ hp]
    exact (γ • chartLift p).im_pos
  have hFq : ContDiffAt ℝ 1 (extendUpper F) (mobiusChart (γ : SL(2, ℤ)) p) :=
    ((hF _ hq).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hq)).of_le
      (by norm_num)
  have hseed : ContDiffAt ℝ 1 (finiteChartFunction s T)
      (mobiusChart (γ : SL(2, ℤ)) p) :=
    (finiteChartFunction_C2 s T).contDiffAt.of_le (by norm_num)
  calc
    _ = hyperbolicChartDirichlet (fun p' => finiteChartFunction s T (mobiusChart (γ : SL(2, ℤ)) p'))
        (fun p' => extendUpper F (mobiusChart (γ : SL(2, ℤ)) p')) p := by
      apply hyperbolicChartDirichlet_congr_of_eventuallyEq Filter.EventuallyEq.rfl
      exact (invariant_mobius_chart_germ N F hInv γ p hp).symm
    _ = hyperbolicChartDirichlet (finiteChartFunction s T) (extendUpper F)
        (mobiusChart (γ : SL(2, ℤ)) p) :=
      hyperbolicChartDirichlet_comp_mobiusChart (γ : SL(2, ℤ)) _ _ p hp hseed hFq
    _ = _ := by
      simpa only [extendUpper_finiteCoreFunction, mobiusChart_eq_actual _ hp]

/-- The genuine first-gradient unfolding identity requested by the Green
argument. The left side is the literal actual periodized Dirichlet
density, and the right side is the actual effective Gamma0 complex trace.
The C2 and invariance inputs concern only the arbitrary outer function. -/
theorem actualPoincare_hyperbolicDirichlet_eq_complexSeedTrace (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (z : UpperHalfPlane) :
    hyperbolicChartDirichlet (extendUpper (finiteCompactTensorPoincare N s T))
      (extendUpper F) (z.re,z.im) =
      complexSeedTrace N (fun w => hyperbolicChartDirichlet
        (extendUpper (finiteCoreFunction s T)) (extendUpper F) (w.re,w.im)) z := by
  rw [actualPoincare_hyperbolicDirichlet_eq_tsum N s T (extendUpper F) z.im_pos]
  unfold complexSeedTrace
  apply tsum_congr
  intro q
  have h := translated_hyperbolicDirichlet_eq_actual N s T F hF hInv q z.im_pos
  rw [chartLift_pair] at h
  exact h

end
end ImbalancedChen.Part3.ActualPoincareDirichletTrace20261025a
