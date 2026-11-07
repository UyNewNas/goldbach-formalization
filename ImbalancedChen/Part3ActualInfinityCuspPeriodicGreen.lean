import ImbalancedChen.Part3GammaInfinityTranslationStrip
import ImbalancedChen.Part3Gamma0CompactGreenProductL1
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Actual Gamma0 infinity-cusp horizontal periodic Green identity

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The literal integral translation T is an actual member of Gamma0(N).
Consequently every invariant positive-chart C2 function has a genuine
period-one horizontal slice, as does its total first derivative. Native
interval integration by parts then gives horizontal Green on one period;
the actual endpoint values cancel by those proved periodic identities.
Actual locally finite compact-seed Poincare functions instantiate all
regularity and invariance inputs below without boundary/Green premises.

No regularity of an adjoint-domain defect, annular vertical Green,
essential self-adjointness or global cutoff graph membership is claimed.
-/

namespace ImbalancedChen.Part3.ActualInfinityCuspPeriodicGreen20261025a

noncomputable section
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0ActualCuspsSourceOnly
open GammaInfinityTranslationStrip20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a

def pointAtHeight (y : ℝ) (hy : 0 < y) (x : ℝ) : UpperHalfPlane := ⟨⟨x,y⟩,hy⟩

theorem translate_one_pointAtHeight (y : ℝ) (hy : 0 < y) (x : ℝ) :
    translate 1 (pointAtHeight y hy x) = pointAtHeight y hy (x+1) := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (translate 1 (pointAtHeight y hy x)).re = x+1
    rw [translate_re]
    simp only [Int.cast_one,pointAtHeight]
    ring
  · change (translate 1 (pointAtHeight y hy x)).im = y
    rw [translate_eq_vadd,UpperHalfPlane.vadd_im]
    rfl

def horizontalSlice (F : UpperHalfPlane → ℂ) (y : ℝ) (x : ℝ) : ℂ :=
  extendUpper F (x,y)

@[simp] theorem horizontalSlice_eq_actual (F : UpperHalfPlane → ℂ)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    horizontalSlice F y x = F (pointAtHeight y hy x) := by
  rw [horizontalSlice,extendUpper,dif_pos hy]
  rfl

/-- Period one is supplied by the actual T in Gamma0(N), rather than a
boundary-value assumption on a free chart function. -/
theorem actual_gamma0_horizontalSlice_periodic (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    {y : ℝ} (hy : 0 < y) : Function.Periodic (horizontalSlice F y) 1 := by
  intro x
  have h := hInv (infinityTranslation N 1).val (pointAtHeight y hy x)
  change F (translate 1 (pointAtHeight y hy x)) = F (pointAtHeight y hy x) at h
  rw [translate_one_pointAtHeight] at h
  simpa only [horizontalSlice_eq_actual F hy] using h

/-- Native total derivative translation identity also covers possible
nondifferentiability; actual C2 regularity is used later for integration. -/
theorem periodic_deriv (f : ℝ → ℂ) (hf : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  have heq : (fun x : ℝ => f (x+1)) = f := funext hf
  intro x
  calc
    deriv f (x+1) = deriv (fun t : ℝ => f (t+1)) x :=
      (deriv_comp_add_const f 1 x).symm
    _ = deriv f x := by rw [heq]

theorem actual_gamma0_horizontalSlice_deriv_periodic (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    {y : ℝ} (hy : 0 < y) : Function.Periodic (deriv (horizontalSlice F y)) 1 :=
  periodic_deriv _ (actual_gamma0_horizontalSlice_periodic N F hInv hy)

theorem horizontalSlice_C2 (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) {y : ℝ} (hy : 0 < y) :
    ContDiff ℝ 2 (horizontalSlice F y) :=
  hF.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun _ => hy)

theorem actual_horizontal_products_intervalIntegrable (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (fun x => star (horizontalSlice F y x)*
      (-deriv (deriv (horizontalSlice G y)) x)) volume 0 1 ∧
      IntervalIntegrable (fun x => star (deriv (horizontalSlice F y) x)*
        deriv (horizontalSlice G y) x) volume 0 1 := by
  have hf := horizontalSlice_C2 F hF hy
  have hg := horizontalSlice_C2 G hG hy
  have hfd : ContDiff ℝ 1 (deriv (horizontalSlice F y)) := hf.deriv'
  have hgd : ContDiff ℝ 1 (deriv (horizontalSlice G y)) := hg.deriv'
  have hgdd : Continuous (deriv (deriv (horizontalSlice G y))) :=
    hgd.continuous_deriv (by norm_num)
  exact ⟨(hf.continuous.star.mul hgdd.neg).intervalIntegrable 0 1,
    (hfd.continuous.star.mul hgd.continuous).intervalIntegrable 0 1⟩

/-- Genuine periodic integration by parts. Its endpoint cancellation is
proved from the two periodic functions, including the derivative period. -/
theorem periodic_horizontal_green (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfp : Function.Periodic f 1) (hgp : Function.Periodic g 1) :
    (∫ x in (0 : ℝ)..1, star (f x)*(-deriv (deriv g) x)) =
      ∫ x in (0 : ℝ)..1, star (deriv f x)*deriv g x := by
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hgd : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hgdd : Continuous (deriv (deriv g)) := hgd.continuous_deriv (by norm_num)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1) (u := fun x => star (f x)) (v := deriv g)
    (u' := fun x => star (deriv f x)) (v' := deriv (deriv g))
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt.star)
    (fun x _ => (hgd.differentiable (by norm_num) x).hasDerivAt)
    (hfd.continuous.star.intervalIntegrable 0 1) (hgdd.intervalIntegrable 0 1)
  have hf01 : f 1 = f 0 := by simpa only [zero_add] using hfp 0
  have hgd01 : deriv g 1 = deriv g 0 := by
    simpa only [zero_add] using periodic_deriv g hgp 0
  have hboundary : star (f 1)*deriv g 1-star (f 0)*deriv g 0 = 0 := by
    rw [hf01,hgd01,sub_self]
  rw [hboundary,zero_sub] at hparts
  simp_rw [mul_neg]
  rw [intervalIntegral.integral_neg,hparts,neg_neg]

/-- The exact actual infinity-cusp identity requested by the strip
Green argument; all endpoint information comes from actual Gamma0. -/
theorem actual_gamma0_horizontal_green (N : ℕ) (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart)
    (hFI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (hGI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, G (γ • z) = G z)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, star (horizontalSlice F y x)*(-deriv (deriv (horizontalSlice G y)) x)) =
      ∫ x in (0 : ℝ)..1, star (deriv (horizontalSlice F y) x)*deriv (horizontalSlice G y) x :=
  periodic_horizontal_green _ _ (horizontalSlice_C2 F hF hy) (horizontalSlice_C2 G hG hy)
    (actual_gamma0_horizontalSlice_periodic N F hFI hy)
    (actual_gamma0_horizontalSlice_periodic N G hGI hy)

/-- Same identity on the literal half-open representative strip used by
the actual parabolic quotient, with native endpoint-null conversion. -/
theorem actual_gamma0_horizontal_green_Ico (N : ℕ) (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hG : ContDiffOn ℝ 2 (extendUpper G) positiveChart)
    (hFI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (hGI : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, G (γ • z) = G z)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0 : ℝ) 1, star (extendUpper F (x,y))*(-sliceDxx (extendUpper G) (x,y))) =
      ∫ x in Ico (0 : ℝ) 1, star (sliceDx (extendUpper F) (x,y))*sliceDx (extendUpper G) (x,y) := by
  have h := actual_gamma0_horizontal_green N F G hF hG hFI hGI hy
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at h
  rw [integral_Ico_eq_integral_Ioc,integral_Ico_eq_integral_Ioc]
  simpa only [horizontalSlice,sliceDxx,sliceDx] using h

/-- A concrete actual Poincare specialization supplies all genuine
invariance/regularity fields; there is no hGreen or hBoundary parameter. -/
theorem actual_poincare_horizontal_green_Ico (N : ℕ) {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in Ico (0 : ℝ) 1,
      star (extendUpper (finiteCompactTensorPoincare N s T) (x,y))*
        (-sliceDxx (extendUpper (finiteCompactTensorPoincare N t U)) (x,y))) =
      ∫ x in Ico (0 : ℝ) 1,
        star (sliceDx (extendUpper (finiteCompactTensorPoincare N s T)) (x,y))*
          sliceDx (extendUpper (finiteCompactTensorPoincare N t U)) (x,y) :=
  actual_gamma0_horizontal_green_Ico N _ _
    (finiteCompactTensorPoincare_contDiffOn_chart N s T)
    (finiteCompactTensorPoincare_contDiffOn_chart N t U)
    (finiteCompactTensorPoincare_gamma0_invariant N s T)
    (finiteCompactTensorPoincare_gamma0_invariant N t U) hy

end
end ImbalancedChen.Part3.ActualInfinityCuspPeriodicGreen20261025a
