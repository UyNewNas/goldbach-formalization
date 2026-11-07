import ImbalancedChen.Part3ActualInfinityCuspPeriodicGreen
import ImbalancedChen.Part3PositiveCompactVerticalGreen
import ImbalancedChen.Part3ActualHeightCutoffMaassCommutator

/-!
# Actual infinity-cusp Green with a compact vertical cutoff

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The test is P(z)=b(Im z)F(z), with b a genuine compact positive-height
smooth function and F,G actual Gamma0-invariant C2 functions. P is only
claimed parabolically periodic. A bounded horizontal window equal to one
on [0,1] proves all mixed L1 products. Horizontal periodic Green and
one-compact positive-height vertical IBP give the planar strip identity.
The ACTUAL canonical H density then cancels its actual y^2 weight.

No whole-H compact support of F, G or P, no Green supplier, and no
adjoint-domain regularity or essential self-adjointness is assumed.
-/

namespace ImbalancedChen.Part3.ActualInfinityAnnularGreen20261025a

noncomputable section
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane
open CanonicalTensorHyperbolicLaplacianForm20261024z
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a
open GammaInfinityTranslationStrip20261025a
open ActualCuspStripCutoff20261025a
open ActualInfinityCuspPeriodicGreen20261025a
open PositiveCompactVerticalGreen20261025a
open ActualGamma0MaassDescent20261025a
open ActualHeightCutoffMaassCommutator20261025a

def stripRectangle : Set (ℝ × ℝ) := Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
theorem stripRectangle_measurable : MeasurableSet stripRectangle :=
  measurableSet_Ico.prod measurableSet_Ioi

private theorem cast_tsupport_subset (b : ℝ → ℝ) :
    tsupport (fun y => (b y : ℂ)) ⊆ tsupport b :=
  tsupport_comp_subset rfl b

/-- Actual mixed plane L1 on bounded x and the compact positive support
of b, obtained by inserting the fixed horizontal window chi=1 on [0,1]. -/
theorem strip_product_integrable (b : ℝ → ℝ) (hb : Continuous b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (J : ℝ × ℝ → ℂ) (hJ : ContinuousOn J positiveChart) :
    IntegrableOn (fun p => (b p.2 : ℂ)*J p) stripRectangle := by
  have hi := compact_product_integrable (fun x => (chi x : ℂ)) (fun y => (b y : ℂ))
    (Complex.continuous_ofReal.comp chi_cinfty.continuous)
    (Complex.continuous_ofReal.comp hb)
    (chi_compact.comp_left (by simp)) (hbc.comp_left (by simp))
    ((cast_tsupport_subset b).trans hbp) J hJ
  apply hi.integrableOn.congr_fun _ stripRectangle_measurable
  intro p hp
  have hx : chi p.1 = 1 := chi_eq_one ⟨hp.1.1,hp.1.2.le⟩
  simp [hx]

/-- The same actual mixed L1 statement for canonical hyperbolic H volume.
Only the auxiliary horizontal window is globally compact. -/
theorem strip_product_H_integrable (b : ℝ → ℝ) (hb : Continuous b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (J : ℝ × ℝ → ℂ) (hJ : ContinuousOn J positiveChart) :
    IntegrableOn (fun z : UpperHalfPlane => (b z.im : ℂ)*J (z.re,z.im)) strip := by
  have hi := compact_product_H_integrable (fun x => (chi x : ℂ)) (fun y => (b y : ℂ))
    (Complex.continuous_ofReal.comp chi_cinfty.continuous)
    (Complex.continuous_ofReal.comp hb)
    (chi_compact.comp_left (by simp)) (hbc.comp_left (by simp))
    ((cast_tsupport_subset b).trans hbp) J hJ
  apply hi.integrableOn.congr_fun _ strip_measurable
  intro z hz
  have hx : chi z.re = 1 := chi_eq_one ⟨hz.1,hz.2.le⟩
  simp [hx]

def verticalProductChart (b : ℝ → ℝ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (b p.2 : ℂ)*F p
def verticalProductH (b : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (b z.im : ℂ)*F z

theorem verticalProductChart_dx (b : ℝ → ℝ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    sliceDx (verticalProductChart b F) p = (b p.2 : ℂ)*sliceDx F p := by
  exact deriv_const_mul_field _

theorem verticalProductChart_dy (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (F : ℝ × ℝ → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    sliceDy (verticalProductChart b F) p =
      (deriv b p.2 : ℂ)*F p+(b p.2 : ℂ)*sliceDy F p := by
  have hs : ContDiffOn ℝ 2 (fun y : ℝ => F (p.1,y)) (Ioi (0 : ℝ)) :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => hy)
  have hba := (hb.differentiable (by simp) p.2).hasDerivAt.ofReal_comp
  have hfa := (((hs p.2 hp).contDiffAt (isOpen_Ioi.mem_nhds hp)).differentiableAt (by norm_num)).hasDerivAt
  exact (hba.mul hfa).deriv

def secondXPair (b : ℝ → ℝ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (verticalProductChart b F p)*(-sliceDxx G p)
def secondYPair (b : ℝ → ℝ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (verticalProductChart b F p)*(-sliceDyy G p)
def firstXPair (b : ℝ → ℝ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (sliceDx (verticalProductChart b F) p)*sliceDx G p
def firstYPair (b : ℝ → ℝ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (sliceDy (verticalProductChart b F) p)*sliceDy G p

/-- Every separated operator/gradient product is L1 on the same actual
bounded-x/compact-y rectangle, including the b-prime product. -/
theorem all_plane_mixed_integrable (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (F G : ℝ × ℝ → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    IntegrableOn (secondXPair b F G) stripRectangle ∧
      IntegrableOn (secondYPair b F G) stripRectangle ∧
      IntegrableOn (firstXPair b F G) stripRectangle ∧
      IntegrableOn (firstYPair b F G) stripRectangle := by
  have hxF := (sliceDx_contDiffOn_one F hF).continuousOn
  have hyF := (sliceDy_contDiffOn_one F hF).continuousOn
  have hxG := (sliceDx_contDiffOn_one G hG).continuousOn
  have hyG := (sliceDy_contDiffOn_one G hG).continuousOn
  have hxx := strip_product_integrable b hb.continuous hbc hbp
    (fun p => star (F p)*(-sliceDxx G p)) (hF.continuousOn.star.mul (sliceDxx_continuousOn G hG).neg)
  have hyy := strip_product_integrable b hb.continuous hbc hbp
    (fun p => star (F p)*(-sliceDyy G p)) (hF.continuousOn.star.mul (sliceDyy_continuousOn G hG).neg)
  have hfx := strip_product_integrable b hb.continuous hbc hbp
    (fun p => star (sliceDx F p)*sliceDx G p) (hxF.star.mul hxG)
  have hfy₀ := strip_product_integrable (deriv b) (hb.continuous_deriv (by simp)) hbc.deriv
    (tsupport_deriv_subset.trans hbp)
    (fun p => star (F p)*sliceDy G p) (hF.continuousOn.star.mul hyG)
  have hfy₁ := strip_product_integrable b hb.continuous hbc hbp
    (fun p => star (sliceDy F p)*sliceDy G p) (hyF.star.mul hyG)
  refine ⟨hxx.congr_fun ?_ stripRectangle_measurable,
    hyy.congr_fun ?_ stripRectangle_measurable,hfx.congr_fun ?_ stripRectangle_measurable,
    (hfy₀.add hfy₁).congr_fun ?_ stripRectangle_measurable⟩
  · intro p _; simp [secondXPair,verticalProductChart,star_mul,mul_assoc,mul_comm,mul_left_comm]
  · intro p _; simp [secondYPair,verticalProductChart,star_mul,mul_assoc,mul_comm,mul_left_comm]
  · intro p _; simp [firstXPair,verticalProductChart_dx,star_mul,mul_assoc,mul_comm,mul_left_comm]
  · intro p hp
    rw [firstYPair,verticalProductChart_dy b hb F hF p hp.2,star_add]
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
    ring

/-- All four actual-H mixed terms are integrable independently of the
Green identity; their y-squared factor is included before integration. -/
theorem all_H_mixed_integrable (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (F G : ℝ × ℝ → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    IntegrableOn (fun z : UpperHalfPlane => (z.im : ℂ)^2*secondXPair b F G (z.re,z.im)) strip ∧
      IntegrableOn (fun z : UpperHalfPlane => (z.im : ℂ)^2*secondYPair b F G (z.re,z.im)) strip ∧
      IntegrableOn (fun z : UpperHalfPlane => (z.im : ℂ)^2*firstXPair b F G (z.re,z.im)) strip ∧
      IntegrableOn (fun z : UpperHalfPlane => (z.im : ℂ)^2*firstYPair b F G (z.re,z.im)) strip := by
  have hy : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ)^2) positiveChart := by fun_prop
  have hxF := (sliceDx_contDiffOn_one F hF).continuousOn
  have hvF := (sliceDy_contDiffOn_one F hF).continuousOn
  have hxG := (sliceDx_contDiffOn_one G hG).continuousOn
  have hvG := (sliceDy_contDiffOn_one G hG).continuousOn
  have hxx := strip_product_H_integrable b hb.continuous hbc hbp
    (fun p => (p.2 : ℂ)^2*(star (F p)*(-sliceDxx G p)))
    (hy.mul (hF.continuousOn.star.mul (sliceDxx_continuousOn G hG).neg))
  have hyy := strip_product_H_integrable b hb.continuous hbc hbp
    (fun p => (p.2 : ℂ)^2*(star (F p)*(-sliceDyy G p)))
    (hy.mul (hF.continuousOn.star.mul (sliceDyy_continuousOn G hG).neg))
  have hfx := strip_product_H_integrable b hb.continuous hbc hbp
    (fun p => (p.2 : ℂ)^2*(star (sliceDx F p)*sliceDx G p)) (hy.mul (hxF.star.mul hxG))
  have hfy₀ := strip_product_H_integrable (deriv b) (hb.continuous_deriv (by simp)) hbc.deriv
    (tsupport_deriv_subset.trans hbp)
    (fun p => (p.2 : ℂ)^2*(star (F p)*sliceDy G p)) (hy.mul (hF.continuousOn.star.mul hvG))
  have hfy₁ := strip_product_H_integrable b hb.continuous hbc hbp
    (fun p => (p.2 : ℂ)^2*(star (sliceDy F p)*sliceDy G p)) (hy.mul (hvF.star.mul hvG))
  refine ⟨hxx.congr_fun ?_ strip_measurable,hyy.congr_fun ?_ strip_measurable,
    hfx.congr_fun ?_ strip_measurable,(hfy₀.add hfy₁).congr_fun ?_ strip_measurable⟩
  · intro z _; simp [secondXPair,verticalProductChart,star_mul,mul_assoc,mul_comm,mul_left_comm]
  · intro z _; simp [secondYPair,verticalProductChart,star_mul,mul_assoc,mul_comm,mul_left_comm]
  · intro z _; simp [firstXPair,verticalProductChart_dx,star_mul,mul_assoc,mul_comm,mul_left_comm]
  · intro z _
    rw [firstYPair,verticalProductChart_dy b hb F hF (z.re,z.im) z.im_pos,star_add]
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
    ring

private theorem vertical_slices_green (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (F G : ℝ × ℝ → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (hG : ContDiffOn ℝ 2 G positiveChart) (x : ℝ) :
    (∫ y in Ioi (0 : ℝ), secondYPair b F G (x,y)) =
      ∫ y in Ioi (0 : ℝ), firstYPair b F G (x,y) := by
  let a : ℝ → ℂ := fun y => (b y : ℂ)
  let f : ℝ → ℂ := fun y => F (x,y)
  let g : ℝ → ℂ := fun y => G (x,y)
  have hap : tsupport a ⊆ Ioi (0 : ℝ) := (cast_tsupport_subset b).trans hbp
  have ha : ContDiff ℝ 2 a := (Complex.ofRealCLM.contDiff.comp hb).of_le (by simp)
  have hf : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)) :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => hy)
  have hg : ContDiffOn ℝ 2 g (Ioi (0 : ℝ)) :=
    hG.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => hy)
  have hP : ContDiff ℝ 2 (fun y => a y*f y) := positive_mask_C2 a f ha hap hf
  have hPc : HasCompactSupport (fun y => a y*f y) := (hbc.comp_left (by simp)).mul_right
  have hPp : tsupport (fun y => a y*f y) ⊆ Ioi (0 : ℝ) := tsupport_mul_subset_left.trans hap
  simpa only [a,f,g,secondYPair,firstYPair,verticalProductChart,sliceDy,sliceDyy] using
    positive_compact_vertical_green (fun y => a y*f y) g hP hPc hPp hg

private theorem horizontal_slices_green (N : ℕ) (b : ℝ → ℝ) (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart)
    (hFI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (hGI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, G (γ • z) = G z)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0 : ℝ) 1, secondXPair b (extendUpper F) (extendUpper G) (x,y)) =
      ∫ x in Ico (0 : ℝ) 1, firstXPair b (extendUpper F) (extendUpper G) (x,y) := by
  have h := actual_gamma0_horizontal_green_Ico N F G hF hG hFI hGI hy
  have hm := congrArg (fun c : ℂ => (b y : ℂ)*c) h
  simpa only [← integral_const_mul,secondXPair,firstXPair,verticalProductChart,
    verticalProductChart_dx,star_mul,Complex.star_def,Complex.conj_ofReal,mul_assoc,
    mul_left_comm,mul_comm] using hm

/-- The Euclidean strip identity uses periodicity only in x and compact
positive support only in y; no separated tensor representation is used. -/
theorem plane_annular_green (N : ℕ) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart)
    (hFI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (hGI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, G (γ • z) = G z) :
    (∫ p in stripRectangle, secondXPair b (extendUpper F) (extendUpper G) p+
      secondYPair b (extendUpper F) (extendUpper G) p) =
      ∫ p in stripRectangle, firstXPair b (extendUpper F) (extendUpper G) p+
        firstYPair b (extendUpper F) (extendUpper G) p := by
  obtain ⟨hxx,hyy,hfx,hfy⟩ := all_plane_mixed_integrable b hb hbc hbp _ _ hF hG
  have hx : (∫ p in stripRectangle, secondXPair b (extendUpper F) (extendUpper G) p) =
      ∫ p in stripRectangle, firstXPair b (extendUpper F) (extendUpper G) p := by
    unfold stripRectangle at hxx hfx ⊢
    rw [Measure.volume_eq_prod,← Measure.prod_restrict] at hxx hfx ⊢
    rw [integral_prod_symm _ hxx,integral_prod_symm _ hfx]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact horizontal_slices_green N b F G hF hG hFI hGI hy
  have hy : (∫ p in stripRectangle, secondYPair b (extendUpper F) (extendUpper G) p) =
      ∫ p in stripRectangle, firstYPair b (extendUpper F) (extendUpper G) p := by
    unfold stripRectangle at hyy hfy ⊢
    rw [Measure.volume_eq_prod,← Measure.prod_restrict] at hyy hfy ⊢
    rw [integral_prod _ hyy,integral_prod _ hfy]
    exact integral_congr_ae (Eventually.of_forall (vertical_slices_green b hb hbc hbp _ _ hF hG))
  rw [integral_add hxx hyy,integral_add hfx hfy,hx,hy]

private theorem canonical_strip_integral (J : ℝ × ℝ → ℂ) :
    (∫ z : UpperHalfPlane in strip, J (z.re,z.im)) =
      ∫ p in stripRectangle, chartWeight p • J p := by
  let A : Set (ℝ × ℝ) := {p | p.1 ∈ Ico (0 : ℝ) 1}
  have hA : MeasurableSet A := measurableSet_Ico.preimage measurable_fst
  have hI : upperChart ∩ A = stripRectangle := by
    ext p
    simp only [upperChart,A,stripRectangle,mem_inter_iff,mem_setOf_eq,mem_prod]
    exact and_comm
  calc
    _ = ∫ z : UpperHalfPlane, A.indicator J (z.re,z.im) := by
      rw [← integral_indicator strip_measurable]
      rfl
    _ = ∫ p : ℝ × ℝ, A.indicator J p ∂chartMeasure :=
      canonical_integral_eq_chart_integral _
    _ = ∫ p in upperChart, A.indicator (fun p => chartWeight p • J p) p := by
      unfold chartMeasure
      rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
      apply setIntegral_congr_fun upperChart_measurable
      intro p _
      by_cases hp : p ∈ A <;> simp [hp]
    _ = _ := by rw [setIntegral_indicator hA,hI]

private theorem weight_cancel (p : ℝ × ℝ) (hp : 0 < p.2) :
    (((chartWeight p : ℝ) : ℂ)*(p.2 : ℂ)^2) = 1 := by
  have h : (p.2⁻¹)^2*p.2^2 = (1 : ℝ) := by
    rw [← mul_pow,inv_mul_cancel₀ hp.ne',one_pow]
  exact_mod_cast h

/-- The two exact native integrands of the final theorem are L1, in
addition to the four separate weighted derivative products. -/
theorem actual_annular_native_integrable (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart) :
    IntegrableOn (fun z : UpperHalfPlane => star (verticalProductH b F z)*upperMaass G z) strip ∧
      IntegrableOn (fun z : UpperHalfPlane => (z.im : ℂ)^2 *
        (star (sliceDx (extendUpper (verticalProductH b F)) (z.re,z.im))*sliceDx (extendUpper G) (z.re,z.im)+
          star (sliceDy (extendUpper (verticalProductH b F)) (z.re,z.im))*sliceDy (extendUpper G) (z.re,z.im))) strip := by
  obtain ⟨hxx,hyy,hx,hy⟩ := all_H_mixed_integrable b hb hbc hbp _ _ hF hG
  have hext : extendUpper (verticalProductH b F) = verticalProductChart b (extendUpper F) :=
    extendUpper_height_mul (fun y => (b y : ℂ)) F
  refine ⟨(hxx.add hyy).congr_fun ?_ strip_measurable,
    (hx.add hy).congr_fun ?_ strip_measurable⟩
  · intro z _
    simp only [secondXPair,secondYPair,verticalProductChart,verticalProductH,
      extendUpper_pair,upperMaass,chartMaass,sliceDxx,sliceDyy,sliceDx,sliceDy]
    ring
  · intro z _
    rw [hext]
    simp only [firstXPair,firstYPair]
    ring

/-- Actual single-cusp strip Green for a NONSEPARABLE periodic seed
with a compact vertical cutoff. All mixed L1 statements are proved above. -/
theorem actual_infinity_annular_green (N : ℕ) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart)
    (hFI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (hGI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, G (γ • z) = G z) :
    (∫ z : UpperHalfPlane in strip, star (verticalProductH b F z)*upperMaass G z) =
      ∫ z : UpperHalfPlane in strip, (z.im : ℂ)^2 *
        (star (sliceDx (extendUpper (verticalProductH b F)) (z.re,z.im))*sliceDx (extendUpper G) (z.re,z.im)+
          star (sliceDy (extendUpper (verticalProductH b F)) (z.re,z.im))*sliceDy (extendUpper G) (z.re,z.im)) := by
  have hext : extendUpper (verticalProductH b F) = verticalProductChart b (extendUpper F) :=
    extendUpper_height_mul (fun y => (b y : ℂ)) F
  have hleft : (∫ z : UpperHalfPlane in strip, star (verticalProductH b F z)*upperMaass G z) =
      ∫ p in stripRectangle, secondXPair b (extendUpper F) (extendUpper G) p+
        secondYPair b (extendUpper F) (extendUpper G) p := by
    calc
      _ = ∫ z : UpperHalfPlane in strip,
          star (verticalProductChart b (extendUpper F) (z.re,z.im))*chartMaass (extendUpper G) (z.re,z.im) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by
          simp only [verticalProductH,verticalProductChart,extendUpper_pair,upperMaass])
      _ = ∫ p in stripRectangle, chartWeight p •
          (star (verticalProductChart b (extendUpper F) p)*chartMaass (extendUpper G) p) :=
        canonical_strip_integral _
      _ = _ := by
        apply setIntegral_congr_fun stripRectangle_measurable
        intro p hp
        have hc := weight_cancel p hp.2
        simp only [secondXPair,secondYPair,chartMaass,sliceDxx,sliceDyy,sliceDx,sliceDy,
          NNReal.smul_def,Complex.real_smul]
        calc
          _ = (((chartWeight p : ℝ) : ℂ)*(p.2 : ℂ)^2)*
              (star (verticalProductChart b (extendUpper F) p)*
                (-deriv (deriv (fun x => extendUpper G (x,p.2))) p.1)+
               star (verticalProductChart b (extendUpper F) p)*
                (-deriv (deriv (fun y => extendUpper G (p.1,y))) p.2)) := by ring
          _ = _ := by rw [hc,one_mul]
  have hright : (∫ z : UpperHalfPlane in strip, (z.im : ℂ)^2 *
      (star (sliceDx (extendUpper (verticalProductH b F)) (z.re,z.im))*sliceDx (extendUpper G) (z.re,z.im)+
        star (sliceDy (extendUpper (verticalProductH b F)) (z.re,z.im))*sliceDy (extendUpper G) (z.re,z.im))) =
      ∫ p in stripRectangle, firstXPair b (extendUpper F) (extendUpper G) p+
        firstYPair b (extendUpper F) (extendUpper G) p := by
    rw [hext]
    rw [canonical_strip_integral]
    apply setIntegral_congr_fun stripRectangle_measurable
    intro p hp
    simp only [firstXPair,firstYPair,NNReal.smul_def,Complex.real_smul]
    rw [← mul_assoc,weight_cancel p hp.2,one_mul]
  rw [hleft,hright]
  exact plane_annular_green N b hb hbc hbp F G hF hG hFI hGI

end
end ImbalancedChen.Part3.ActualInfinityAnnularGreen20261025a
