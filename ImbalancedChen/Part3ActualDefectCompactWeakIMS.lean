import ImbalancedChen.Part3ActualCompactCutoffMassTransport
import ImbalancedChen.Part3CoordinateLocalH1CompactProducts
import ImbalancedChen.Part3Gamma0WholeChartCoordinateWeakEquation
import ImbalancedChen.Part3WholeUpperChartWeakH1Patching

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual compact weak IMS for a native Gamma minimal-adjoint defect, on
arbitrary positive-height rectangles INCLUDING carrier seams. The native
whole-H transpose and actual local H1 suppliers are invoked. The mass is
exactly y^-2, the nonsmooth cutoff-square test is constructed, and all
three ordinary energy integrands are L1. There is no PDE, H1, legal-test,
IMS, gradient-bound or spectral conclusion premise.
-/
namespace ImbalancedChen.Part3.ActualDefectCompactWeakIMS20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a CompactC2JetCutoffEstimate20261026a
open SupportedH1FiniteTensorDensity20261026a WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open LocalH1Tests20261026b LocalH1WeakPDEExtension20261026b
open LocalH1SecondOrderWeakPDEExtension20261026b LocalWeakH1CutoffProduct20261026b
open LocalGradientH1WeakTesting20261026b GenuineWeakCutoffIMS20261026b
open CoordinateLocalH1CompactProducts20261026b ActualCompactCutoffMassTransport20261026b
open PlanarLocalWeakGradientExtraction20261026b ActualPullbackLocalH1Transfer20261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0SmoothedPotentialL2Budget20261026a
open Gamma0WholeChartCoordinateWeakEquation20261026b WholeUpperChartWeakH1Patching20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z

/-- The genuine whole-chart PDE uses the support-preserving tensor
density directly. No reduced-carrier hypothesis is introduced into a
whole-H test theorem. -/
theorem whole_chart_H1_test {Ω : Set Plane}
    (F m : Plane → ℂ) (hm : MemLp m 2 volume)
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p)))
    (L R a b : ℝ) (ha : 0 < a) (hLR : L < R) (hab : a < b)
    (hUΩ : openRect L R a b ⊆ Ω)
    (hPDE : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ openRect L R a b → secondOrderEquation F m ψ)
    (J : CompactH1Jet) (hJx : HasCompactSupport J.dx) (hJy : HasCompactSupport J.dy)
    (hJs : tsupport J.value ⊆ openRect L R a b) :
    H1FirstOrderResidual ![m,(gx : Plane → ℂ),(gy : Plane → ℂ)] J = 0 := by
  let c : Fin 3 → Plane → ℂ := ![m,(gx : Plane → ℂ),(gy : Plane → ℂ)]
  have hc : ∀ i, MemLp (c i) 2 volume := by
    intro i
    fin_cases i
    · exact hm
    · exact Lp.memLp gx
    · exact Lp.memLp gy
  have hdense := compactH1_mem_localFiniteTensorJets_closure J hJx hJy L R a b ha hLR hab hJs
  have hclosed : IsClosed {v : Fin 3 → ProductKernelL2TranslationAverage20261026a.PlaneL2 |
      weakResidual (coefficientClass c hc) v = 0} :=
    isClosed_eq (weakResidual_continuous _) continuous_const
  have hsub : localFiniteTensorJets L R a b ⊆
      {v | weakResidual (coefficientClass c hc) v = 0} := by
    rintro v ⟨ι,s,T,hTc,hTs,rfl⟩
    rw [smoothResidual_eq]
    have hGs := finiteSmoothChart_contDiff s T
    have hsupport := finiteTensor_tsupport_openRect s T L R a b hTs
    exact local_gradient_secondOrder_firstOrder gx gy hgrad hGs hTc
      (hsupport.trans hUΩ) (hPDE _ hGs hTc hsupport)
  have hz := (closure_minimal hsub hclosed) hdense
  exact (H1Residual_eq c hc J) ▸ hz

/-- ACTUAL defect weak IMS on every compact positive-height chart
cutoff. The returned L2 gradient extensions are used only on this compact
rectangle, while the displayed value is the ORIGINAL orbit pullback. -/
theorem actual_defect_compact_weak_IMS (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (L R a b : ℝ) (ha : 0 < a) (hLR : L < R) (hab : a < b)
    {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ openRect L R a b) :
    ∃ gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2,
      Integrable (fun p => ‖productDerivative (complexCutoff χ) (actualPlanePullback N f) gx ex p‖^2 +
        ‖productDerivative (complexCutoff χ) (actualPlanePullback N f) gy ey p‖^2) volume ∧
      Integrable (fun p => (χ p)^2 * heightPotential p * ‖actualPlanePullback N f p‖^2) volume ∧
      Integrable (fun p => (‖directional ex (complexCutoff χ) p‖^2 +
        ‖directional ey (complexCutoff χ) p‖^2) * ‖actualPlanePullback N f p‖^2) volume ∧
      (∫ p, ‖productDerivative (complexCutoff χ) (actualPlanePullback N f) gx ex p‖^2 +
        ‖productDerivative (complexCutoff χ) (actualPlanePullback N f) gy ey p‖^2) +
        (∫ p, (χ p)^2 * heightPotential p * ‖actualPlanePullback N f p‖^2) =
      ∫ p, (‖directional ex (complexCutoff χ) p‖^2 +
        ‖directional ey (complexCutoff χ) p‖^2) * ‖actualPlanePullback N f p‖^2 := by
  let Ω : Set Plane := Icc L R ×ˢ Icc a b
  let F := actualPlanePullback N f
  let G := Ω.indicator F
  have hΩ : MeasurableSet Ω := measurableSet_Icc.prod measurableSet_Icc
  have hUΩ : openRect L R a b ⊆ Ω := Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hloc := actual_defect_every_positive_rectangle_H1 N f hf L R a b hLR.le hab.le ha
  obtain ⟨hG,gx,gy,hgrad⟩ := indicator_hasLocalL2Gradient hΩ hloc
  have hg : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * G p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * G p)) := hgrad
  let m : Plane → ℂ := fun p => (cappedPotential a p : ℂ) * G p
  have hm : MemLp m 2 volume := by
    apply hG.of_le_mul ((Complex.continuous_ofReal.comp (cappedPotential_continuous ha)).aestronglyMeasurable.mul
      hG.aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      change ‖(cappedPotential a p : ℂ) * G p‖ ≤ (a⁻¹)^2 * ‖G p‖
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (cappedPotential_nonneg a p)]
      exact mul_le_mul_of_nonneg_right (cappedPotential_le ha p) (norm_nonneg _)
  have hmΩ (p : Plane) (hp : p ∈ Ω) : m p = coordinatePotential N f p := by
    simp only [m,G,indicator_of_mem hp,cappedPotential,max_eq_right hp.2.1,
      coordinatePotential,F]
  have hPDE : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ openRect L R a b → secondOrderEquation G m ψ := by
    intro ψ hψ hc hs
    have hsΩ := hs.trans hUΩ
    have hsupper : tsupport ψ ⊆ upperChart := fun p hp => ha.trans (hs hp).2.1
    have hraw := actual_defect_coordinate_transpose N f hf hψ hc hsupper
    have hsecondSupport (v : Plane) : tsupport (directional v (directional v ψ)) ⊆ tsupport ψ :=
      (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_fderiv_apply_subset ℝ v)
    have hLap : (∫ p, star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p) * F p) =
        ∫ p, star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p) * G p := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        by_cases hp : p ∈ Ω
        · simp only [G,indicator_of_mem hp]
        · have hn : p ∉ tsupport ψ := fun h => hp (hsΩ h)
          have hx : directional ex (directional ex ψ) p = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h => hn (hsecondSupport ex h))
          have hy : directional ey (directional ey ψ) p = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h => hn (hsecondSupport ey h))
          change star (directional ex (directional ex ψ) p + directional ey (directional ey ψ) p) * F p =
            star (directional ex (directional ex ψ) p + directional ey (directional ey ψ) p) * G p
          rw [hx,hy,add_zero,star_zero,zero_mul,zero_mul]
    have hMass : (∫ p, star (ψ p) * coordinatePotential N f p) = ∫ p, star (ψ p) * m p := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        by_cases hp : p ∈ Ω
        · rw [hmΩ p hp]
        · have hz : ψ p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsΩ h))
          simp only [hz,star_zero,zero_mul]
    have hi (v : Plane) : Integrable (fun p => star (directional v (directional v ψ) p) * G p) volume :=
      MemLp.integrable_mul (p := 2) (q := 2)
        (((directional_smooth v (directional_smooth v hψ)).continuous.memLp_of_hasCompactSupport
          (directional_compact v (directional_compact v hc))).star) hG
    change (∫ p, star (directional ex (directional ex ψ) p) * G p) +
      (∫ p, star (directional ey (directional ey ψ) p) * G p) = _
    calc
      _ = ∫ p, star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p) * G p := by
        rw [← integral_add (hi ex) (hi ey)]
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          change star (directional ex (directional ex ψ) p) * G p +
            star (directional ey (directional ey ψ) p) * G p =
              star (directional ex (directional ex ψ) p + directional ey (directional ey ψ) p) * G p
          simp only [star_add,add_mul]
      _ = _ := hLap.symm.trans (hraw.trans hMass)
  let C := complexCutoff χ
  have hC : ContDiff ℝ ∞ C := Complex.ofRealCLM.contDiff.comp hχ
  have hCc : HasCompactSupport C := hχc.comp_left (g := Complex.ofReal) (by simp)
  have hCU : tsupport C ⊆ openRect L R a b :=
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) χ).trans hχU
  let S : Plane → ℂ := fun p => C p * C p
  have hS : ContDiff ℝ ∞ S := hC.mul hC
  have hSc : HasCompactSupport S := hCc.mul_right
  have hSU : tsupport S ⊆ openRect L R a b := tsupport_mul_subset_left.trans hCU
  let J := cutoffJet hG gx gy hS hSc (hSU.trans hUΩ) hg
  have hJs := cutoffJet_supports hG gx gy hS hSc (hSU.trans hUΩ) hg
  have htest := whole_chart_H1_test G m hm gx gy hg L R a b ha hLR hab hUΩ hPDE J
    (hSc.of_isClosed_subset isClosed_tsupport hJs.2.1)
    (hSc.of_isClosed_subset isClosed_tsupport hJs.2.2) (hJs.1.trans hSU)
  have hmass : ∀ p ∈ tsupport χ, m p = (heightPotential p : ℂ) * G p := by
    intro p hp
    have hy := (hχU hp).2.1.le
    simp only [m,cappedPotential,max_eq_right hy,heightPotential]
  have hIMS := weak_IMS_of_cutoff_square_identity G m heightPotential χ hG hm gx gy hχ hχc hmass htest
  have hL1 := weak_IMS_energy_integrable G m heightPotential χ hG hm gx gy hχ hχc hmass
  have hχzero (p : Plane) (hp : p ∉ Ω) : χ p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp (hUΩ (hχU h)))
  have hCzero (p : Plane) (hp : p ∉ Ω) : C p = 0 := by simp only [C,complexCutoff,hχzero p hp,Complex.ofReal_zero]
  have hDzero (v p : Plane) (hp : p ∉ Ω) : directional v C p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp (hUΩ (hCU (tsupport_fderiv_apply_subset ℝ v h))))
  have hprod (v : Plane) (g : Plane → ℂ) : productDerivative C G g v = productDerivative C F g v := by
    funext p
    by_cases hp : p ∈ Ω
    · simp only [productDerivative,G,indicator_of_mem hp]
    · simp only [productDerivative,hCzero p hp,hDzero v p hp,zero_mul,add_zero]
  have hmassFn : (fun p => (χ p)^2 * heightPotential p * ‖G p‖^2) =
      (fun p => (χ p)^2 * heightPotential p * ‖F p‖^2) := by
    funext p
    by_cases hp : p ∈ Ω
    · simp only [G,indicator_of_mem hp]
    · simp only [hχzero p hp,zero_pow (by norm_num : 2 ≠ 0),zero_mul]
  have herrorFn : (fun p => (‖directional ex C p‖^2 + ‖directional ey C p‖^2) * ‖G p‖^2) =
      (fun p => (‖directional ex C p‖^2 + ‖directional ey C p‖^2) * ‖F p‖^2) := by
    funext p
    by_cases hp : p ∈ Ω
    · simp only [G,indicator_of_mem hp]
    · simp only [hDzero ex p hp,hDzero ey p hp,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero,zero_mul]
  simp_rw [hprod] at hIMS hL1
  rw [hmassFn,herrorFn] at hIMS hL1
  exact ⟨gx,gy,hL1.1,hL1.2.1,hL1.2.2,hIMS⟩

end
end ImbalancedChen.Part3.ActualDefectCompactWeakIMS20261026b

