import ImbalancedChen.Part3OneCompactCrossGreen
import ImbalancedChen.Part3Gamma0CompactGreenProductL1

/-!
# One compact tensor against an unrestricted positive-chart C2 function

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The vertical test function need only be C2 at positive height. Pinned
integration by parts asks for its derivative on the support of the compact
seed, so no artificial smooth extension across height zero is assumed.
The actual mixed-product L1 supplier supplies the Fubini prerequisites.
-/

namespace ImbalancedChen.Part3.Gamma0OneCompactChartGreen20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.OneCompactCrossGreen20261025a
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a

private theorem tsupport_star_eq (f : ℝ → ℂ) :
    tsupport (fun x => star (f x)) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  simp only [Function.mem_support, ne_eq, star_eq_zero]

private theorem horizontal_contDiff (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) (y : ℝ) (hy : 0 < y) :
    ContDiff ℝ 2 (fun x : ℝ => G (x,y)) := by
  exact hG.comp_contDiff (by fun_prop) (fun _ => hy)

private theorem vertical_contDiffAt (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) (x y : ℝ) (hy : 0 < y) :
    ContDiffAt ℝ 2 (fun y : ℝ => G (x,y)) y := by
  have hlocal : ContDiffOn ℝ 2 (fun y : ℝ => G (x,y)) (Ioi 0) :=
    hG.comp (by fun_prop) (fun _ h => h)
  exact (hlocal y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)

/-- Local C2 regularity on the open positive half-line suffices, since
the compact first factor and its derivatives are supported there. The
five L1 products below are supplied by genuine joint compact-product
theorems when this lemma is used in the two-dimensional identity. -/
private theorem vertical_local_green
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hfpos : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : ∀ x : ℝ, 0 < x → ContDiffAt ℝ 2 g x)
    (hi₀ : Integrable (fun x => star (f x) * deriv g x))
    (hi₁ : Integrable (fun x => star (f x) * deriv (deriv g) x))
    (hi₂ : Integrable (fun x => star (deriv f x) * deriv g x))
    (hj₀ : Integrable (fun x => star (deriv f x) * g x))
    (hj₁ : Integrable (fun x => star (deriv (deriv f) x) * g x)) :
    (∫ x : ℝ, star (f x) * deriv (deriv g) x) =
      ∫ x : ℝ, star (deriv (deriv f) x) * g x := by
  have hfs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  have hfd := (contDiff_succ_iff_deriv.mp hfs).1
  have hdf := (contDiff_succ_iff_deriv.mp hfs).2.2
  have hfd' : Differentiable ℝ (deriv f) := hdf.differentiable_one
  have hfirst := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => star (f x)) (v := deriv g)
    (u' := fun x : ℝ => star (deriv f x)) (v' := deriv (deriv g))
    (fun x _ => (hfd x).hasDerivAt.star)
    (fun x hx => by
      have hxpos : 0 < x := hfpos (by simpa only [tsupport_star_eq] using hx)
      have hdg : ContDiffAt ℝ 1 (deriv g) x :=
        (hg x hxpos).derivWithin (by norm_num)
      exact (hdg.differentiableAt (by norm_num)).hasDerivAt)
    hi₁ hi₂ hi₀
  have hsecond := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := fun x : ℝ => star (deriv f x))
    (u' := deriv g) (v' := fun x : ℝ => star (deriv (deriv f) x))
    (fun x hx => by
      have hx' : x ∈ tsupport (deriv f) := by simpa only [tsupport_star_eq] using hx
      have hxpos : 0 < x := hfpos (tsupport_deriv_subset hx')
      exact ((hg x hxpos).differentiableAt (by norm_num)).hasDerivAt)
    (fun x _ => (hfd' x).hasDerivAt.star)
    (by simpa only [mul_comm] using hj₁)
    (by simpa only [mul_comm] using hi₂)
    (by simpa only [mul_comm] using hj₀)
  have hsecond' : (∫ x : ℝ, star (deriv (deriv f) x) * g x) =
      -(∫ x : ℝ, star (deriv f x) * deriv g x) := by
    simpa only [mul_comm] using hsecond
  exact hfirst.trans hsecond'.symm

private theorem horizontal_green_slices (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) (y : ℝ) :
    (∫ x : ℝ, star (T.horizontal x * T.vertical y) * sliceDxx G (x,y)) =
      ∫ x : ℝ, star (deriv (deriv T.horizontal) x * T.vertical y) * G (x,y) := by
  by_cases hy : 0 < y
  · have hg := horizontal_contDiff G hG y hy
    have hfirst := integral_star_mul_secondDeriv_one_compact T.horizontal
      (fun x : ℝ => G (x,y)) T.horizontal_smooth hg T.horizontal_compact
    have hsecond := integral_secondDeriv_star_mul_one_compact T.horizontal
      (fun x : ℝ => G (x,y)) T.horizontal_smooth hg T.horizontal_compact
    have hgreen : (∫ x : ℝ, star (T.horizontal x) * deriv (deriv (fun x : ℝ => G (x,y))) x) =
        ∫ x : ℝ, star (deriv (deriv T.horizontal) x) * G (x,y) :=
      hfirst.trans hsecond.symm
    calc
      _ = star (T.vertical y) *
          ∫ x : ℝ, star (T.horizontal x) * deriv (deriv (fun x : ℝ => G (x,y))) x := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by simp only [sliceDxx, sliceDx, star_mul]; ring)
      _ = star (T.vertical y) *
          ∫ x : ℝ, star (deriv (deriv T.horizontal) x) * G (x,y) := by rw [hgreen]
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by simp only [star_mul]; ring)
  · have hz : T.vertical y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (T.vertical_positive h))
    simp only [hz, mul_zero, star_zero, zero_mul, integral_zero]

/-- The vertical Green identity holds on almost every actual horizontal
slice. Joint L1 products, not an assumed slice or Green theorem, supply
each integrability condition of the pinned one-dimensional theorem. -/
private theorem vertical_green_slices_ae (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    ∀ᵐ x : ℝ,
      (∫ y : ℝ, star (T.horizontal x * T.vertical y) * sliceDyy G (x,y)) =
        ∫ y : ℝ, star (T.horizontal x * deriv (deriv T.vertical) y) * G (x,y) := by
  have hDy := compact_product_Dy _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hDyy := compact_product_Dyy _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hVDy := compact_product_Dy T.horizontal (deriv T.vertical) T.horizontal_smooth.continuous
    (seed_first_derivative_continuous _ T.vertical_smooth)
    T.horizontal_compact T.vertical_compact.deriv (seed_deriv_positive _ T.vertical_positive) G hG
  have hVG := compact_product_G T.horizontal (deriv T.vertical) T.horizontal_smooth.continuous
    (seed_first_derivative_continuous _ T.vertical_smooth)
    T.horizontal_compact T.vertical_compact.deriv (seed_deriv_positive _ T.vertical_positive) G hG
  have hVVG := compact_product_second_vertical_G T G hG
  filter_upwards [hDy.prod_right_ae, hDyy.prod_right_ae,
    hVDy.prod_right_ae, hVG.prod_right_ae, hVVG.prod_right_ae] with x hi₀ hi₁ hi₂ hj₀ hj₁
  let f : ℝ → ℂ := fun y => T.horizontal x * T.vertical y
  let g : ℝ → ℂ := fun y => G (x,y)
  have hf : ContDiff ℝ 2 f := contDiff_const.mul T.vertical_smooth
  have hfpos : tsupport f ⊆ Ioi (0 : ℝ) :=
    tsupport_mul_subset_right.trans T.vertical_positive
  have hf₁ : deriv f = fun y => T.horizontal x * deriv T.vertical y := by
    funext y
    exact deriv_const_mul_field _
  have hf₂ : deriv (deriv f) = fun y => T.horizontal x * deriv (deriv T.vertical) y := by
    rw [hf₁]
    funext y
    exact deriv_const_mul_field _
  have hg := vertical_local_green f g hf hfpos
    (fun y hy => vertical_contDiffAt G hG x y hy)
    (by simpa only [f, g, sliceDy] using hi₀)
    (by simpa only [f, g, sliceDyy, sliceDy] using hi₁)
    (by simpa only [hf₁, g, sliceDy] using hi₂)
    (by simpa only [hf₁, g] using hj₀)
    (by simpa only [hf₂, g] using hj₁)
  simpa only [f, g, hf₂, sliceDyy, sliceDy] using hg

/-- True two-dimensional Green identity against a full arbitrary C2
positive-chart function. Its negative Euclidean Laplacian is unweighted
because the canonical hyperbolic density cancels the actual y-squared
operator multiplier in the final H transport below. -/
theorem plane_one_compact_tensor_green (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ p : ℝ × ℝ, -(star (T.horizontal p.1 * T.vertical p.2) *
        (sliceDxx G p + sliceDyy G p))) =
      ∫ p : ℝ × ℝ, -(star (deriv (deriv T.horizontal) p.1 * T.vertical p.2) * G p +
        star (T.horizontal p.1 * deriv (deriv T.vertical) p.2) * G p) := by
  have hxx := compact_product_Dxx _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hyy := compact_product_Dyy _ _ T.horizontal_smooth.continuous T.vertical_smooth.continuous
    T.horizontal_compact T.vertical_compact T.vertical_positive G hG
  have hxxG := compact_product_second_horizontal_G T G hG
  have hyyG := compact_product_second_vertical_G T G hG
  have hxGreen : (∫ p : ℝ × ℝ, star (T.horizontal p.1*T.vertical p.2)*sliceDxx G p) =
      ∫ p : ℝ × ℝ, star (deriv (deriv T.horizontal) p.1*T.vertical p.2)*G p := by
    rw [integral_prod_symm _ hxx, integral_prod_symm _ hxxG]
    apply integral_congr_ae
    exact Eventually.of_forall (horizontal_green_slices T G hG)
  have hyGreen : (∫ p : ℝ × ℝ, star (T.horizontal p.1*T.vertical p.2)*sliceDyy G p) =
      ∫ p : ℝ × ℝ, star (T.horizontal p.1*deriv (deriv T.vertical) p.2)*G p := by
    rw [integral_prod _ hyy, integral_prod _ hyyG]
    exact integral_congr_ae (vertical_green_slices_ae T G hG)
  simp_rw [mul_add]
  rw [integral_neg, integral_add hxx hyy, hxGreen, hyGreen,
    integral_neg, integral_add hxxG hyyG]

private theorem weight_cancel (p : ℝ × ℝ) (hp : p ∈ upperChart) :
    (((chartWeight p : ℝ) : ℂ) * (p.2 : ℂ) ^ 2) = 1 := by
  have h : (p.2⁻¹) ^ 2 * p.2 ^ 2 = (1 : ℝ) := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hp), one_pow]
  exact_mod_cast h

private theorem seed_zero_off_positive (T : CompactTensor) (p : ℝ × ℝ)
    (hp : p ∉ upperChart) : T.vertical p.2 = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hp (T.vertical_positive h))

private theorem second_seed_zero_off_positive (T : CompactTensor) (p : ℝ × ℝ)
    (hp : p ∉ upperChart) : deriv (deriv T.vertical) p.2 = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h =>
    hp (T.vertical_positive (tsupport_deriv_subset (tsupport_deriv_subset h))))

/-- The actual canonical hyperbolic H pairing with one compact tensor
has full Green symmetry against any C2 positive-chart function. The
second argument is unrestricted outside the positive chart and need
not be compact or a finite tensor sum. -/
theorem canonical_one_compact_tensor_green (T : CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ z : UpperHalfPlane, star (tensorFunctionH T.horizontal T.vertical z) *
        chartMaass G (z.re,z.im)) =
      ∫ z : UpperHalfPlane, star (tensorHyperbolicLaplacianH T.horizontal T.vertical z) *
        G (z.re,z.im) := by
  have hleft : (∫ z : UpperHalfPlane, star (tensorFunctionH T.horizontal T.vertical z) *
      chartMaass G (z.re,z.im)) =
      ∫ p : ℝ × ℝ, -(star (T.horizontal p.1*T.vertical p.2) * (sliceDxx G p+sliceDyy G p)) := by
    change (∫ z : UpperHalfPlane,
      (fun p : ℝ × ℝ => star (tensorFunction T.horizontal T.vertical p) * chartMaass G p)
        (Complex.measurableEquivRealProd (z : ℂ))) = _
    rw [canonical_integral_eq_chart_integral]
    unfold chartMeasure
    rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
    calc
      _ = ∫ p in upperChart, -(star (T.horizontal p.1*T.vertical p.2) *
          (sliceDxx G p+sliceDyy G p)) := by
        apply setIntegral_congr_fun upperChart_measurable
        intro p hp
        have hcancel := weight_cancel p hp
        simp only [chartMaass, tensorFunction, sliceDxx, sliceDyy, sliceDx, sliceDy,
          NNReal.smul_def, Complex.real_smul]
        calc
          _ = -((((chartWeight p : ℝ) : ℂ)*(p.2 : ℂ)^2) *
              (star (T.horizontal p.1*T.vertical p.2) *
                (deriv (deriv (fun x : ℝ => G (x,p.2))) p.1 +
                 deriv (deriv (fun y : ℝ => G (p.1,y))) p.2))) := by ring
          _ = _ := by rw [hcancel, one_mul]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        simp only [seed_zero_off_positive T p hp, mul_zero, star_zero, zero_mul, neg_zero])
  have hright : (∫ z : UpperHalfPlane,
      star (tensorHyperbolicLaplacianH T.horizontal T.vertical z) * G (z.re,z.im)) =
      ∫ p : ℝ × ℝ, -(star (deriv (deriv T.horizontal) p.1*T.vertical p.2)*G p +
        star (T.horizontal p.1*deriv (deriv T.vertical) p.2)*G p) := by
    change (∫ z : UpperHalfPlane,
      (fun p : ℝ × ℝ => star (tensorHyperbolicLaplacian T.horizontal T.vertical p) * G p)
        (Complex.measurableEquivRealProd (z : ℂ))) = _
    rw [canonical_integral_eq_chart_integral]
    unfold chartMeasure
    rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
    calc
      _ = ∫ p in upperChart,
          -(star (deriv (deriv T.horizontal) p.1*T.vertical p.2)*G p +
            star (T.horizontal p.1*deriv (deriv T.vertical) p.2)*G p) := by
        apply setIntegral_congr_fun upperChart_measurable
        intro p hp
        have hcancel := weight_cancel p hp
        simp only [tensorHyperbolicLaplacian, NNReal.smul_def, Complex.real_smul,
          star_neg, star_mul, star_add, star_pow, Complex.star_def, map_pow, Complex.conj_ofReal]
        calc
          _ = -((((chartWeight p : ℝ) : ℂ)*(p.2 : ℂ)^2) *
              (star (deriv (deriv T.horizontal) p.1*T.vertical p.2)*G p +
                star (T.horizontal p.1*deriv (deriv T.vertical) p.2)*G p)) := by
            simp only [Complex.star_def, map_mul]
            ring
          _ = _ := by rw [hcancel, one_mul]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        simp only [seed_zero_off_positive T p hp, second_seed_zero_off_positive T p hp,
          mul_zero, star_zero, zero_mul, add_zero, neg_zero])
  rw [hleft, hright]
  exact plane_one_compact_tensor_green T G hG

/-- The intrinsic actual H Maass operator is paired against an arbitrary
full C2 H function; the positive-chart representative supplies regularity. -/
theorem upperMaass_one_compact_tensor_green (T : CompactTensor)
    (F : UpperHalfPlane → ℂ) (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) :
    (∫ z : UpperHalfPlane, star (tensorFunctionH T.horizontal T.vertical z) * upperMaass F z) =
      ∫ z : UpperHalfPlane, star (tensorHyperbolicLaplacianH T.horizontal T.vertical z) * F z := by
  have hchart := canonical_one_compact_tensor_green T (extendUpper F) hF
  have hext (z : UpperHalfPlane) : extendUpper F (z.re,z.im) = F z := by
    rw [extendUpper, dif_pos z.im_pos]
    congr 1
    apply UpperHalfPlane.ext
    ext <;> rfl
  simpa only [upperMaass, hext] using hchart

/-- Finite cross terms are retained for the actual compact tensor seed;
the unrestricted second argument is a single full C2 chart function. -/
theorem canonical_one_compact_finite_seed_green {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) * chartMaass G (z.re,z.im)) =
      ∫ z : UpperHalfPlane, star (finiteCoreLaplacian s T z) * G (z.re,z.im) := by
  have hiL (i : ι) : Integrable (fun z : UpperHalfPlane =>
      star (tensorFunctionH (T i).horizontal (T i).vertical z) * chartMaass G (z.re,z.im)) := by
    simpa only [finiteCoreFunction, Finset.sum_singleton] using
      finite_core_chartMaass_pair_H_integrable ({()} : Finset Unit) (fun _ => T i) G hG
  have hiR (i : ι) : Integrable (fun z : UpperHalfPlane =>
      star (tensorHyperbolicLaplacianH (T i).horizontal (T i).vertical z) * G (z.re,z.im)) := by
    simpa only [finiteCoreLaplacian, Finset.sum_singleton] using
      finite_core_second_pair_H_integrable ({()} : Finset Unit) (fun _ => T i) G hG
  calc
    _ = ∫ z : UpperHalfPlane, ∑ i ∈ s,
        star (tensorFunctionH (T i).horizontal (T i).vertical z) * chartMaass G (z.re,z.im) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by simp only [finiteCoreFunction, star_sum, Finset.sum_mul])
    _ = ∑ i ∈ s, ∫ z : UpperHalfPlane,
        star (tensorFunctionH (T i).horizontal (T i).vertical z) * chartMaass G (z.re,z.im) :=
      integral_finsetSum s (fun i _ => hiL i)
    _ = ∑ i ∈ s, ∫ z : UpperHalfPlane,
        star (tensorHyperbolicLaplacianH (T i).horizontal (T i).vertical z) * G (z.re,z.im) := by
      apply Finset.sum_congr rfl
      intro i _
      exact canonical_one_compact_tensor_green (T i) G hG
    _ = _ := by
      rw [← integral_finsetSum s (fun i _ => hiR i)]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by simp only [finiteCoreLaplacian, star_sum, Finset.sum_mul])

/-- One genuine compact finite seed versus a full noncompact H function.
Both products are genuinely integrable by the imported compact support
supplier, and all second derivatives in the identity are the actual ones. -/
theorem upperMaass_one_compact_finite_seed_green {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) :
    (∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) * upperMaass F z) =
      ∫ z : UpperHalfPlane, star (finiteCoreLaplacian s T z) * F z := by
  have hext (z : UpperHalfPlane) : extendUpper F (z.re,z.im) = F z := by
    rw [extendUpper, dif_pos z.im_pos]
    congr 1
    apply UpperHalfPlane.ext
    ext <;> rfl
  simpa only [upperMaass, hext] using
    canonical_one_compact_finite_seed_green s T (extendUpper F) hF

end
end ImbalancedChen.Part3.Gamma0OneCompactChartGreen20261025a
