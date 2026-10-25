import ImbalancedChen.Part3Gamma0OneCompactChartGreen
import ImbalancedChen.Part3ActualMobiusDirichletCovariance

/-!
# Actual one-compact Dirichlet Green identity

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The actual second-coordinate operator paired with a compact positive
tensor seed is the integral of the actual first-coordinate cross energy.
The other C2 function may be noncompact and is only regular at positive
height. All Fubini inputs come from proved compact-product L1 theorems.
This is the analytic input for unfolding actual automorphic energy.
-/

namespace ImbalancedChen.Part3.OneCompactDirichletGreen20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.OneCompactCrossGreen20261025a
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a
open ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a

def tensorDirichlet (T : CompactTensor) (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (deriv T.horizontal p.1*T.vertical p.2)*sliceDx G p +
    star (T.horizontal p.1*deriv T.vertical p.2)*sliceDy G p

private theorem tsupport_star_eq (f : ℝ → ℂ) :
    tsupport (fun x => star (f x)) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  simp only [Function.mem_support, ne_eq, star_eq_zero]

private theorem horizontal_dirichlet_slices (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) (y : ℝ) :
    (∫ x : ℝ, star (T.horizontal x*T.vertical y)*sliceDxx G (x,y)) =
      -(∫ x : ℝ, star (deriv T.horizontal x*T.vertical y)*sliceDx G (x,y)) := by
  by_cases hy : 0 < y
  · have hg : ContDiff ℝ 2 (fun x : ℝ => G (x,y)) :=
      hG.comp_contDiff (by fun_prop) (fun _ => hy)
    have hparts := integral_star_mul_secondDeriv_one_compact T.horizontal
      (fun x : ℝ => G (x,y)) T.horizontal_smooth hg T.horizontal_compact
    calc
      _ = star (T.vertical y) *
          ∫ x : ℝ, star (T.horizontal x)*deriv (deriv (fun x : ℝ => G (x,y))) x := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by simp only [sliceDxx, sliceDx, star_mul]; ring)
      _ = -(star (T.vertical y) * ∫ x : ℝ, star (deriv T.horizontal x)*deriv (fun x : ℝ => G (x,y)) x) := by
        rw [hparts, mul_neg]
      _ = _ := by
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by simp only [sliceDx, star_mul]; ring)
  · have hz : T.vertical y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (T.vertical_positive h))
    simp only [hz, mul_zero, star_zero, zero_mul, integral_zero, neg_zero]

private theorem vertical_dirichlet_slices_ae (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    ∀ᵐ x : ℝ,
      (∫ y : ℝ, star (T.horizontal x*T.vertical y)*sliceDyy G (x,y)) =
        -(∫ y : ℝ, star (T.horizontal x*deriv T.vertical y)*sliceDy G (x,y)) := by
  have hDy := compact_product_Dy _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hDyy := compact_product_Dyy _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hVDy := compact_product_Dy T.horizontal (deriv T.vertical) T.horizontal_smooth.continuous
    (seed_first_derivative_continuous _ T.vertical_smooth)
    T.horizontal_compact T.vertical_compact.deriv (seed_deriv_positive _ T.vertical_positive) G hG
  filter_upwards [hDy.prod_right_ae, hDyy.prod_right_ae, hVDy.prod_right_ae] with x hi₀ hi₁ hi₂
  let f : ℝ → ℂ := fun y => T.horizontal x*T.vertical y
  let g : ℝ → ℂ := fun y => G (x,y)
  have hf : ContDiff ℝ 2 f := contDiff_const.mul T.vertical_smooth
  have hfs : ContDiff ℝ ((1 : ℕ∞ω)+1) f := by simpa using hf
  have hfd := (contDiff_succ_iff_deriv.mp hfs).1
  have hfpos : tsupport f ⊆ Ioi (0 : ℝ) := tsupport_mul_subset_right.trans T.vertical_positive
  have hf₁ : deriv f = fun y => T.horizontal x*deriv T.vertical y := by
    funext y
    exact deriv_const_mul_field _
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun y : ℝ => star (f y)) (v := deriv g)
    (u' := fun y : ℝ => star (deriv f y)) (v' := deriv (deriv g))
    (fun y _ => (hfd y).hasDerivAt.star)
    (fun y hy => by
      have hypos : 0 < y := hfpos (by simpa only [tsupport_star_eq] using hy)
      have hslice : ContDiffOn ℝ 2 g (Ioi 0) :=
        hG.comp (by fun_prop) (fun _ h => h)
      have hgAt : ContDiffAt ℝ 2 g y := (hslice y hypos).contDiffAt (isOpen_Ioi.mem_nhds hypos)
      have hgd : ContDiffAt ℝ 1 (deriv g) y := hgAt.derivWithin (by norm_num)
      exact (hgd.differentiableAt (by norm_num)).hasDerivAt)
    (by simpa only [f, g, sliceDyy, sliceDy] using hi₁)
    (by simpa only [hf₁, g, sliceDy] using hi₂)
    (by simpa only [f, g, sliceDy] using hi₀)
  simpa only [f, g, hf₁, sliceDyy, sliceDy] using hparts

theorem plane_one_compact_dirichlet (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ p : ℝ × ℝ, -(star (T.horizontal p.1*T.vertical p.2)*(sliceDxx G p+sliceDyy G p))) =
      ∫ p : ℝ × ℝ, tensorDirichlet T G p := by
  have hxx := compact_product_Dxx _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hyy := compact_product_Dyy _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hDx := compact_product_Dx (deriv T.horizontal) T.vertical
    (seed_first_derivative_continuous _ T.horizontal_smooth) T.vertical_smooth.continuous
    T.horizontal_compact.deriv T.vertical_compact T.vertical_positive G hG
  have hDy := compact_product_Dy T.horizontal (deriv T.vertical) T.horizontal_smooth.continuous
    (seed_first_derivative_continuous _ T.vertical_smooth)
    T.horizontal_compact T.vertical_compact.deriv (seed_deriv_positive _ T.vertical_positive) G hG
  have hxParts : (∫ p : ℝ × ℝ, star (T.horizontal p.1*T.vertical p.2)*sliceDxx G p) =
      -(∫ p : ℝ × ℝ, star (deriv T.horizontal p.1*T.vertical p.2)*sliceDx G p) := by
    rw [integral_prod_symm _ hxx, integral_prod_symm _ hDx, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall (horizontal_dirichlet_slices T G hG))
  have hyParts : (∫ p : ℝ × ℝ, star (T.horizontal p.1*T.vertical p.2)*sliceDyy G p) =
      -(∫ p : ℝ × ℝ, star (T.horizontal p.1*deriv T.vertical p.2)*sliceDy G p) := by
    rw [integral_prod _ hyy, integral_prod _ hDy, ← integral_neg]
    exact integral_congr_ae (vertical_dirichlet_slices_ae T G hG)
  simp_rw [mul_add]
  rw [integral_neg, integral_add hxx hyy, hxParts, hyParts]
  unfold tensorDirichlet
  rw [integral_add hDx hDy]
  ring

private theorem weight_cancel (p : ℝ × ℝ) (hp : p ∈ upperChart) :
    (((chartWeight p : ℝ) : ℂ)*(p.2 : ℂ)^2) = 1 := by
  have h : (p.2⁻¹)^2*p.2^2 = (1 : ℝ) := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hp), one_pow]
  exact_mod_cast h

/-- Actual-H Dirichlet identity, with the full arbitrary positive-chart
test function. The density and the y-squared operator/energy weights are
the canonical ones and cancel by a proved pointwise equality. -/
theorem canonical_one_compact_tensor_dirichlet (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ z : UpperHalfPlane, star (tensorFunctionH T.horizontal T.vertical z)*chartMaass G (z.re,z.im)) =
      ∫ z : UpperHalfPlane, (z.im : ℂ)^2*tensorDirichlet T G (z.re,z.im) := by
  have hleft : (∫ z : UpperHalfPlane,
      star (tensorFunctionH T.horizontal T.vertical z)*chartMaass G (z.re,z.im)) =
      ∫ p : ℝ × ℝ, -(star (T.horizontal p.1*T.vertical p.2)*(sliceDxx G p+sliceDyy G p)) := by
    change (∫ z : UpperHalfPlane,
      (fun p : ℝ × ℝ => star (tensorFunction T.horizontal T.vertical p)*chartMaass G p)
        (Complex.measurableEquivRealProd (z : ℂ))) = _
    rw [canonical_integral_eq_chart_integral]
    unfold chartMeasure
    rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
    calc
      _ = ∫ p in upperChart, -(star (T.horizontal p.1*T.vertical p.2)*(sliceDxx G p+sliceDyy G p)) := by
        apply setIntegral_congr_fun upperChart_measurable
        intro p hp
        have hcancel := weight_cancel p hp
        simp only [chartMaass, tensorFunction, sliceDxx, sliceDyy, sliceDx, sliceDy,
          NNReal.smul_def, Complex.real_smul]
        calc
          _ = -((((chartWeight p : ℝ) : ℂ)*(p.2 : ℂ)^2)*
              (star (T.horizontal p.1*T.vertical p.2)*
                (deriv (deriv (fun x : ℝ => G (x,p.2))) p.1+
                  deriv (deriv (fun y : ℝ => G (p.1,y))) p.2))) := by ring
          _ = _ := by rw [hcancel, one_mul]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        have hz : T.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hp (T.vertical_positive h))
        simp only [hz, mul_zero, star_zero, zero_mul, neg_zero])
  have hright : (∫ z : UpperHalfPlane, (z.im : ℂ)^2*tensorDirichlet T G (z.re,z.im)) =
      ∫ p : ℝ × ℝ, tensorDirichlet T G p := by
    change (∫ z : UpperHalfPlane, (fun p : ℝ × ℝ => (p.2 : ℂ)^2*tensorDirichlet T G p)
      (Complex.measurableEquivRealProd (z : ℂ))) = _
    rw [canonical_integral_eq_chart_integral]
    unfold chartMeasure
    rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
    calc
      _ = ∫ p in upperChart, tensorDirichlet T G p := by
        apply setIntegral_congr_fun upperChart_measurable
        intro p hp
        simp only [NNReal.smul_def, Complex.real_smul]
        rw [← mul_assoc, weight_cancel p hp, one_mul]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        have hz : T.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hp (T.vertical_positive h))
        have hdz : deriv T.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hp (T.vertical_positive (tsupport_deriv_subset h)))
        simp only [tensorDirichlet, hz, hdz, mul_zero, star_zero, zero_mul, add_zero])
  rw [hleft, hright]
  exact plane_one_compact_dirichlet T G hG

theorem sliceDx_finiteChartFunction {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (p : ℝ × ℝ) :
    sliceDx (finiteChartFunction s T) p =
      ∑ i ∈ s, deriv (T i).horizontal p.1*(T i).vertical p.2 := by
  unfold sliceDx finiteChartFunction
  rw [deriv_fun_sum (fun i _ =>
    ((T i).horizontal_smooth.differentiable (by norm_num) p.1).mul_const _)]
  simp only [deriv_mul_const_field]

theorem sliceDy_finiteChartFunction {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (p : ℝ × ℝ) :
    sliceDy (finiteChartFunction s T) p =
      ∑ i ∈ s, (T i).horizontal p.1*deriv (T i).vertical p.2 := by
  unfold sliceDy finiteChartFunction
  rw [deriv_fun_sum (fun i _ =>
    ((T i).vertical_smooth.differentiable (by norm_num) p.2).const_mul _)]
  simp only [deriv_const_mul_field]

/-- Actual coordinate first derivatives, including every finite seed
cross term, rather than a chosen tensor decomposition of the full test. -/
theorem chartDirichlet_finite_seed_eq_sum {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    chartDirichlet (finiteChartFunction s T) G p = ∑ i ∈ s, tensorDirichlet (T i) G p := by
  rw [chartDirichlet, sliceDx_finiteChartFunction, sliceDy_finiteChartFunction]
  simp only [star_sum, Finset.sum_mul, ← Finset.sum_add_distrib, tensorDirichlet]

theorem tensorDirichlet_H_integrable (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun z : UpperHalfPlane => (z.im : ℂ)^2*tensorDirichlet T G (z.re,z.im)) := by
  have hweight : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ)^2) positiveChart := by fun_prop
  have hDx := compact_product_H_integrable (deriv T.horizontal) T.vertical
    (seed_first_derivative_continuous _ T.horizontal_smooth) T.vertical_smooth.continuous
    T.horizontal_compact.deriv T.vertical_compact T.vertical_positive
    (fun p : ℝ × ℝ => (p.2 : ℂ)^2*sliceDx G p)
    (hweight.mul (sliceDx_contDiffOn_one G hG).continuousOn)
  have hDy := compact_product_H_integrable T.horizontal (deriv T.vertical)
    T.horizontal_smooth.continuous (seed_first_derivative_continuous _ T.vertical_smooth)
    T.horizontal_compact T.vertical_compact.deriv (seed_deriv_positive _ T.vertical_positive)
    (fun p : ℝ × ℝ => (p.2 : ℂ)^2*sliceDy G p)
    (hweight.mul (sliceDy_contDiffOn_one G hG).continuousOn)
  convert hDx.add hDy using 1
  funext z
  unfold tensorDirichlet
  ring

/-- Genuine one-compact finite-seed H Dirichlet identity, ready for the
independently proved automorphic first-gradient covariance/unfolding. -/
theorem canonical_one_compact_finite_seed_dirichlet {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ z : UpperHalfPlane, star (finiteCoreFunction s T z)*chartMaass G (z.re,z.im)) =
      ∫ z : UpperHalfPlane, hyperbolicChartDirichlet (finiteChartFunction s T) G (z.re,z.im) := by
  have hiL (i : ι) : Integrable (fun z : UpperHalfPlane =>
      star (tensorFunctionH (T i).horizontal (T i).vertical z)*chartMaass G (z.re,z.im)) := by
    simpa only [finiteCoreFunction, Finset.sum_singleton] using
      finite_core_chartMaass_pair_H_integrable ({()} : Finset Unit) (fun _ => T i) G hG
  calc
    _ = ∫ z : UpperHalfPlane, ∑ i ∈ s,
        star (tensorFunctionH (T i).horizontal (T i).vertical z)*chartMaass G (z.re,z.im) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by simp only [finiteCoreFunction, star_sum, Finset.sum_mul])
    _ = ∑ i ∈ s, ∫ z : UpperHalfPlane,
        star (tensorFunctionH (T i).horizontal (T i).vertical z)*chartMaass G (z.re,z.im) :=
      integral_finsetSum s (fun i _ => hiL i)
    _ = ∑ i ∈ s, ∫ z : UpperHalfPlane, (z.im : ℂ)^2*tensorDirichlet (T i) G (z.re,z.im) := by
      apply Finset.sum_congr rfl
      intro i _
      exact canonical_one_compact_tensor_dirichlet (T i) G hG
    _ = ∫ z : UpperHalfPlane, ∑ i ∈ s, (z.im : ℂ)^2*tensorDirichlet (T i) G (z.re,z.im) :=
      (integral_finsetSum s (fun i _ => tensorDirichlet_H_integrable (T i) G hG)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        simp only [hyperbolicChartDirichlet, chartDirichlet_finite_seed_eq_sum, Finset.mul_sum])

theorem upperMaass_one_compact_finite_seed_dirichlet {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) :
    (∫ z : UpperHalfPlane, star (finiteCoreFunction s T z)*upperMaass F z) =
      ∫ z : UpperHalfPlane, hyperbolicChartDirichlet
        (extendUpper (finiteCoreFunction s T)) (extendUpper F) (z.re,z.im) := by
  rw [extendUpper_finiteCoreFunction]
  simpa only [upperMaass] using canonical_one_compact_finite_seed_dirichlet s T (extendUpper F) hF

end
end ImbalancedChen.Part3.OneCompactDirichletGreen20261025a
