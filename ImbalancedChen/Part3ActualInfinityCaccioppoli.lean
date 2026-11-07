import ImbalancedChen.Part3ActualInfinityAnnularGreen

/-!
# Actual C2 negative-eigenfunction localization on the infinity cusp

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

Testing actual strip Green with eta^2 F gives the exact IMS identity
E(eta F)+lambda*M(eta F)=cutoffError for Delta F=-lambda F.
All three real terms are proved integrable from compact positive vertical
support. Their positivity gives Caccioppoli without an energy premise.
The C2/invariance/equation inputs concern the actual function F; no
regularity of an abstract adjoint-domain vector is inferred here.
-/

namespace ImbalancedChen.Part3.ActualInfinityCaccioppoli20261025a

noncomputable section
open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a
open GammaInfinityTranslationStrip20261025a
open ActualGamma0MaassDescent20261025a
open ActualInfinityAnnularGreen20261025a

private theorem square_compact (eta : ℝ → ℝ) (hc : HasCompactSupport eta) :
    HasCompactSupport (fun y => eta y^2) := by
  have ht : HasCompactSupport (fun y => eta y*eta y) := hc.mul_right
  simpa only [pow_two] using ht

private theorem square_positive (eta : ℝ → ℝ) (hp : tsupport eta ⊆ Ioi (0 : ℝ)) :
    tsupport (fun y => eta y^2) ⊆ Ioi (0 : ℝ) := by
  have ht : tsupport (fun y => eta y*eta y) ⊆ tsupport eta := tsupport_mul_subset_left
  simpa only [pow_two] using ht.trans hp

def localizedMass (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℝ :=
  eta z.im^2*Complex.normSq (F z)

def localizedEnergy (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℝ :=
  z.im^2*(Complex.normSq (sliceDx (verticalProductChart eta (extendUpper F)) (z.re,z.im))+
    Complex.normSq (sliceDy (verticalProductChart eta (extendUpper F)) (z.re,z.im)))

def cutoffError (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℝ :=
  z.im^2*(deriv eta z.im)^2*Complex.normSq (F z)

def localizedPair (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℂ)^2*
    (star (sliceDx (verticalProductChart (fun y => eta y^2) (extendUpper F)) (z.re,z.im))*
      sliceDx (extendUpper F) (z.re,z.im)+
     star (sliceDy (verticalProductChart (fun y => eta y^2) (extendUpper F)) (z.re,z.im))*
      sliceDy (extendUpper F) (z.re,z.im))

theorem localizedMass_nonneg (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    0 ≤ localizedMass eta F z := mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
theorem localizedEnergy_nonneg (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    0 ≤ localizedEnergy eta F z :=
  mul_nonneg (sq_nonneg _) (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
theorem cutoffError_nonneg (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    0 ≤ cutoffError eta F z :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Complex.normSq_nonneg _)

/-- Each term of the eventual localization identity is independently L1. -/
theorem localization_terms_integrable (eta : ℝ → ℝ) (he : ContDiff ℝ ∞ eta)
    (hec : HasCompactSupport eta) (hep : tsupport eta ⊆ Ioi (0 : ℝ))
    (F : UpperHalfPlane → ℂ) (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart) :
    IntegrableOn (localizedMass eta F) strip ∧
      IntegrableOn (localizedEnergy eta F) strip ∧ IntegrableOn (cutoffError eta F) strip := by
  have hmass := strip_product_H_integrable (fun y => eta y^2) (he.continuous.pow 2)
    (square_compact eta hec) (square_positive eta hep)
    (fun p => star (extendUpper F p)*extendUpper F p) (hF.continuousOn.star.mul hF.continuousOn)
  have hP : ContDiffOn ℝ 2 (verticalProductChart eta (extendUpper F)) positiveChart :=
    ((Complex.ofRealCLM.contDiff.comp (he.comp contDiff_snd)).of_le (by simp)).contDiffOn.mul hF
  obtain ⟨_,_,hEx,hEy⟩ := all_H_mixed_integrable eta he hec hep (extendUpper F)
    (verticalProductChart eta (extendUpper F)) hF hP
  have hd : Continuous (deriv eta) := he.continuous_deriv (by simp)
  have hdp : tsupport (deriv eta) ⊆ Ioi (0 : ℝ) := tsupport_deriv_subset.trans hep
  have herr := strip_product_H_integrable (fun y => (deriv eta y)^2) (hd.pow 2)
    (square_compact _ hec.deriv) (square_positive _ hdp)
    (fun p => (p.2 : ℂ)^2*(star (extendUpper F p)*extendUpper F p))
    ((by fun_prop : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ)^2) positiveChart).mul
      (hF.continuousOn.star.mul hF.continuousOn))
  refine ⟨hmass.re.congr_fun ?_ strip_measurable,
    (hEx.add hEy).re.congr_fun ?_ strip_measurable,herr.re.congr_fun ?_ strip_measurable⟩
  · intro z _
    simp only [extendUpper_pair,localizedMass,Complex.normSq_apply,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring
  · intro z _
    simp only [firstXPair,firstYPair,localizedEnergy,Complex.normSq_apply,← Complex.ofReal_pow,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring
  · intro z _
    simp only [extendUpper_pair,cutoffError,Complex.normSq_apply,← Complex.ofReal_pow,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring

private theorem deriv_eta_square (eta : ℝ → ℝ) (he : ContDiff ℝ ∞ eta) (y : ℝ) :
    deriv (fun t => eta t^2) y = 2*eta y*deriv eta y := by
  simpa only [pow_one] using
    ((he.differentiable (by simp) y).hasDerivAt.pow 2).deriv

/-- Exact pointwise IMS expansion, including both actual coordinate
derivatives. This is polynomial algebra after the actual product rules. -/
theorem localization_pointwise (eta : ℝ → ℝ) (he : ContDiff ℝ ∞ eta)
    (F : UpperHalfPlane → ℂ) (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (z : UpperHalfPlane) :
    localizedEnergy eta F z-cutoffError eta F z = (localizedPair eta F z).re := by
  unfold localizedEnergy cutoffError localizedPair
  rw [verticalProductChart_dx,verticalProductChart_dy eta he _ hF _ z.im_pos,
    verticalProductChart_dx,verticalProductChart_dy (fun y => eta y^2) (he.pow 2) _ hF _ z.im_pos,
    deriv_eta_square eta he]
  simp only [extendUpper_pair]
  simp only [Complex.normSq_apply,← Complex.ofReal_pow,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

private theorem negative_eigen_pair_re (eta : ℝ → ℝ) (F : UpperHalfPlane → ℂ)
    (lambda : ℝ) (hEig : ∀ z : UpperHalfPlane, upperMaass F z = -(lambda : ℂ)*F z)
    (z : UpperHalfPlane) :
    (star (verticalProductH (fun y => eta y^2) F z)*upperMaass F z).re =
      -lambda*localizedMass eta F z := by
  rw [hEig]
  simp only [verticalProductH,localizedMass,Complex.normSq_apply,star_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

/-- Genuine C2 negative-eigenfunction localization. No energy inequality
or cutoff-error bound is a premise; Green and all integrability came first. -/
theorem actual_infinity_IMS (N : ℕ) (eta : ℝ → ℝ) (he : ContDiff ℝ ∞ eta)
    (hec : HasCompactSupport eta) (hep : tsupport eta ⊆ Ioi (0 : ℝ))
    (F : UpperHalfPlane → ℂ) (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (lambda : ℝ) (hEig : ∀ z : UpperHalfPlane, upperMaass F z = -(lambda : ℂ)*F z) :
    (∫ z in strip, localizedEnergy eta F z) + lambda*(∫ z in strip, localizedMass eta F z) =
      ∫ z in strip, cutoffError eta F z := by
  have hc := square_compact eta hec
  have hp := square_positive eta hep
  have hGreen := actual_infinity_annular_green N (fun y => eta y^2) (he.pow 2)
    hc hp F F hF hF hInv hInv
  obtain ⟨hL,hR⟩ := actual_annular_native_integrable (fun y => eta y^2) (he.pow 2) hc hp F F hF hF
  have hext : extendUpper (verticalProductH (fun y => eta y^2) F) =
      verticalProductChart (fun y => eta y^2) (extendUpper F) :=
    ActualHeightCutoffMaassCommutator20261025a.extendUpper_height_mul
      (fun y => ((eta y^2 : ℝ) : ℂ)) F
  rw [hext] at hGreen hR
  obtain ⟨hM,hE,hErr⟩ := localization_terms_integrable eta he hec hep F hF
  have hreal := congrArg Complex.re hGreen
  rw [← integral_re hL,← integral_re hR] at hreal
  have hleft : (∫ z in strip,
      (star (verticalProductH (fun y => eta y^2) F z)*upperMaass F z).re) =
      -lambda*(∫ z in strip, localizedMass eta F z) := by
    simp_rw [negative_eigen_pair_re eta F lambda hEig]
    rw [integral_const_mul]
  have hright : (∫ z in strip, (localizedPair eta F z).re) =
      (∫ z in strip, localizedEnergy eta F z)-(∫ z in strip, cutoffError eta F z) := by
    calc
      _ = ∫ z in strip, localizedEnergy eta F z-cutoffError eta F z :=
        integral_congr_ae (Eventually.of_forall (fun z => (localization_pointwise eta he F hF z).symm))
      _ = _ := integral_sub hE hErr
  change (∫ z in strip,
    (star (verticalProductH (fun y => eta y^2) F z)*upperMaass F z).re) =
      ∫ z in strip, (localizedPair eta F z).re at hreal
  rw [hleft,hright] at hreal
  linarith

/-- Caccioppoli for the actual C2 negative-eigenfunction; regularity of
an arbitrary adjoint vector remains a separate, unproved prerequisite. -/
theorem actual_infinity_Caccioppoli (N : ℕ) (eta : ℝ → ℝ) (he : ContDiff ℝ ∞ eta)
    (hec : HasCompactSupport eta) (hep : tsupport eta ⊆ Ioi (0 : ℝ))
    (F : UpperHalfPlane → ℂ) (hF : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hInv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ • z) = F z)
    (lambda : ℝ) (hEig : ∀ z : UpperHalfPlane, upperMaass F z = -(lambda : ℂ)*F z) :
    lambda*(∫ z in strip, localizedMass eta F z) ≤ ∫ z in strip, cutoffError eta F z := by
  have h := actual_infinity_IMS N eta he hec hep F hF hInv lambda hEig
  have hE : 0 ≤ ∫ z in strip, localizedEnergy eta F z :=
    integral_nonneg (localizedEnergy_nonneg eta F)
  linarith

end
end ImbalancedChen.Part3.ActualInfinityCaccioppoli20261025a
