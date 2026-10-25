import ImbalancedChen.Part3OneCompactDirichletGreen
import ImbalancedChen.Part3MaassFirstGradientWeakLimit

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
First-order compact tensor integration by parts against a noncompact
positive-chart C2 function. The derivative is required only at positive
height; all product integrability and slice hypotheses are derived from
the actual compact seed. Canonical hyperbolic volume is transported with
the literal y-squared weight, not replaced by planar volume. -/

namespace ImbalancedChen.Part3.OneCompactFirstGradientIBP20261025a
noncomputable section
open Set Filter Function MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a

def sliceFirst (vertical : Bool) (G : ℝ × ℝ → ℂ) :=
  if vertical then sliceDy G else sliceDx G

private theorem star_tsupport (f : ℝ → ℂ) : tsupport (fun x => star (f x)) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  simp only [mem_support,ne_eq,star_eq_zero]

private theorem first_parts (f g : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x)
    (h₀ : Integrable (fun x => star (f x)*g x))
    (h₁ : Integrable (fun x => star (f x)*deriv g x))
    (h₂ : Integrable (fun x => star (deriv f x)*g x)) :
    (∫ x, star (deriv f x)*g x) = -(∫ x, star (f x)*deriv g x) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => star (f x)) (v := g)
    (u' := fun x => star (deriv f x)) (v' := deriv g)
    (fun x _ => (hf x).hasDerivAt.star)
    (fun x hx => (hg x (by simpa only [star_tsupport] using hx)).hasDerivAt) h₁ h₂ h₀
  calc
    _ = -(-(∫ x, star (deriv f x)*g x)) := by simp
    _ = _ := congrArg Neg.neg h.symm

theorem plane_one_compact_first (vertical : Bool) (T : CompactTensor)
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ p : ℝ × ℝ, star (tensorGradient vertical T p)*G p) =
      -(∫ p : ℝ × ℝ, star (tensorFunction T.horizontal T.vertical p)*sliceFirst vertical G p) := by
  have h₀ := compact_product_G _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  cases vertical
  · have h₁ := compact_product_Dx _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
      T.horizontal_compact T.vertical_compact T.vertical_positive G hG
    have h₂ := compact_product_G (deriv T.horizontal) T.vertical
      (seed_first_derivative_continuous _ T.horizontal_smooth) T.vertical_smooth.continuous
      T.horizontal_compact.deriv T.vertical_compact T.vertical_positive G hG
    have hslice : ∀ᵐ y : ℝ,
        (∫ x, star (deriv T.horizontal x*T.vertical y)*G (x,y)) =
          -(∫ x, star (T.horizontal x*T.vertical y)*sliceDx G (x,y)) := by
      filter_upwards [h₀.prod_left_ae,h₁.prod_left_ae,h₂.prod_left_ae] with y hi₀ hi₁ hi₂
      by_cases hy : 0 < y
      · let f : ℝ → ℂ := fun x => T.horizontal x*T.vertical y
        let g : ℝ → ℂ := fun x => G (x,y)
        have hgf : ContDiff ℝ 2 g := hG.comp_contDiff (by fun_prop) (fun _ => hy)
        have hdf : deriv f = fun x => deriv T.horizontal x*T.vertical y := by
          funext x
          exact deriv_mul_const_field _
        simpa only [f,g,hdf,sliceDx] using first_parts f g
          ((T.horizontal_smooth.differentiable (by norm_num)).mul_const _)
          (fun x _ => hgf.differentiable (by norm_num) x) hi₀ hi₁
          (by simpa only [hdf] using hi₂)
      · have hz : T.vertical y=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hy (T.vertical_positive h))
        simp only [hz,mul_zero,star_zero,zero_mul,integral_zero,neg_zero]
    change (∫ p : ℝ × ℝ, star (deriv T.horizontal p.1*T.vertical p.2)*G p) = _
    rw [integral_prod_symm _ h₂,integral_prod_symm _ h₁,← integral_neg]
    exact integral_congr_ae hslice
  · have h₁ := compact_product_Dy _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
      T.horizontal_compact T.vertical_compact T.vertical_positive G hG
    have h₂ := compact_product_G T.horizontal (deriv T.vertical) T.horizontal_smooth.continuous
      (seed_first_derivative_continuous _ T.vertical_smooth)
      T.horizontal_compact T.vertical_compact.deriv (seed_deriv_positive _ T.vertical_positive) G hG
    have hslice : ∀ᵐ x : ℝ,
        (∫ y, star (T.horizontal x*deriv T.vertical y)*G (x,y)) =
          -(∫ y, star (T.horizontal x*T.vertical y)*sliceDy G (x,y)) := by
      filter_upwards [h₀.prod_right_ae,h₁.prod_right_ae,h₂.prod_right_ae] with x hi₀ hi₁ hi₂
      let f : ℝ → ℂ := fun y => T.horizontal x*T.vertical y
      let g : ℝ → ℂ := fun y => G (x,y)
      have hf : Differentiable ℝ f :=
        (T.vertical_smooth.differentiable (by norm_num)).const_mul _
      have hdf : deriv f = fun y => T.horizontal x*deriv T.vertical y := by
        funext y
        exact deriv_const_mul_field _
      have hg : ∀ y ∈ tsupport f, DifferentiableAt ℝ g y := by
        intro y hy
        have hypos : 0 < y := T.vertical_positive (tsupport_mul_subset_right hy)
        have hc : ContDiffOn ℝ 2 g (Ioi 0) := hG.comp (by fun_prop) (fun _ h => h)
        exact ((hc y hypos).contDiffAt (isOpen_Ioi.mem_nhds hypos)).differentiableAt (by norm_num)
      simpa only [f,g,hdf,sliceDy] using first_parts f g hf hg hi₀ hi₁
        (by simpa only [hdf] using hi₂)
    change (∫ p : ℝ × ℝ, star (T.horizontal p.1*deriv T.vertical p.2)*G p) = _
    rw [integral_prod _ h₂,integral_prod _ h₁,← integral_neg]
    exact integral_congr_ae hslice

/-- Literal canonical density cancellation for a positive-height plane
integrand; no global integrability of its unweighted H partner is needed. -/
theorem canonical_ySq_integral (a : ℝ × ℝ → ℂ)
    (ha : ∀ p, p ∉ upperChart → a p=0) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^2*a (z.re,z.im)) = ∫ p : ℝ × ℝ, a p := by
  change (∫ z : UpperHalfPlane, (fun p : ℝ × ℝ => (p.2 : ℂ)^2*a p)
    (Complex.measurableEquivRealProd (z : ℂ))) = _
  rw [canonical_integral_eq_chart_integral]
  unfold chartMeasure
  rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
  calc
    _ = ∫ p in upperChart, a p := by
      apply setIntegral_congr_fun upperChart_measurable
      intro p hp
      have hc : (((chartWeight p : ℝ) : ℂ)*(p.2 : ℂ)^2)=1 := by
        have hreal : (p.2⁻¹)^2*p.2^2=(1 : ℝ) := by
          rw [← mul_pow,inv_mul_cancel₀ (ne_of_gt hp),one_pow]
        exact_mod_cast hreal
      simp only [NNReal.smul_def,Complex.real_smul]
      rw [← mul_assoc,hc,one_mul]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero ha

theorem canonical_one_compact_first (vertical : Bool) (T : CompactTensor)
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^2*
      (star (tensorGradient vertical T (z.re,z.im))*G (z.re,z.im))) =
    -(∫ z : UpperHalfPlane, (z.im : ℂ)^2*
      (star (tensorFunctionH T.horizontal T.vertical z)*sliceFirst vertical G (z.re,z.im))) := by
  have htestzero (p : ℝ × ℝ) (hp : p ∉ upperChart) :
      tensorFunction T.horizontal T.vertical p=0 := by
    have hz : T.vertical p.2=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (T.vertical_positive h))
    simp [tensorFunction,hz]
  have hgradzero (p : ℝ × ℝ) (hp : p ∉ upperChart) : tensorGradient vertical T p=0 := by
    have hz : T.vertical p.2=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (T.vertical_positive h))
    have hdz : deriv T.vertical p.2=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (T.vertical_positive (tsupport_deriv_subset h)))
    cases vertical <;> simp [tensorGradient,tensorDx,tensorDy,hz,hdz]
  change (∫ z : UpperHalfPlane, (z.im : ℂ)^2*
      (star (tensorGradient vertical T (z.re,z.im))*G (z.re,z.im))) =
    -(∫ z : UpperHalfPlane, (z.im : ℂ)^2*
      (star (tensorFunction T.horizontal T.vertical (z.re,z.im))*sliceFirst vertical G (z.re,z.im)))
  rw [canonical_ySq_integral _ (fun p hp => by rw [hgradzero p hp,star_zero,zero_mul]),
    canonical_ySq_integral _ (fun p hp => by rw [htestzero p hp,star_zero,zero_mul])]
  exact plane_one_compact_first vertical T G hG

end
end ImbalancedChen.Part3.OneCompactFirstGradientIBP20261025a
