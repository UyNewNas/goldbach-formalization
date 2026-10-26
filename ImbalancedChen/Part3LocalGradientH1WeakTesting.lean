import ImbalancedChen.Part3LocalWeakH1CutoffProduct

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The local weak-gradient interface is used only on compact derivative
tests that stay in its original region. This derives the finite first-
order PDE from the local transposed PDE and extends to genuine compact H1
tests. In particular the cutoff-square product is a legal nonsmooth test.
-/
namespace ImbalancedChen.Part3.LocalGradientH1WeakTesting20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a CompactProductKernelSixJet20261025a
open CompactC2JetCutoffEstimate20261026a
open SupportedH1FiniteTensorDensity20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open LocalH1Tests20261026b LocalH1WeakPDEExtension20261026b
open LocalH1SecondOrderWeakPDEExtension20261026b LocalWeakH1CutoffProduct20261026b

/-- The finite sum's topological support stays in the prescribed OPEN
rectangle. One uses the finite union of closed factor supports, so the
closure operation does not lose the strict factor margins. -/
theorem finiteTensor_tsupport_openRect {ι : Type*} (s : Finset ι)
    (T : ι → SmoothCompactTensor) (L R a b : ℝ)
    (hs : ∀ t, tsupport (T t).horizontal ⊆ Ioo L R ∧
      tsupport (T t).vertical ⊆ Ioo a b) :
    tsupport (finiteChartFunction s (fun t => (T t).toCompactTensor)) ⊆ openRect L R a b := by
  let K : Set Plane := ⋃ t : {t // t ∈ s},
    tsupport (T t).horizontal ×ˢ tsupport (T t).vertical
  have hK : IsCompact K := isCompact_iUnion fun t =>
    (T t).horizontal_compact.prod (T t).vertical_compact
  have hsupport : Function.support (finiteChartFunction s
      (fun t => (T t).toCompactTensor)) ⊆ K := by
    intro p hp
    by_contra hn
    apply hp
    change (∑ t ∈ s, (T t).horizontal p.1 * (T t).vertical p.2) = 0
    apply Finset.sum_eq_zero
    intro t ht
    by_cases hx : p.1 ∈ tsupport (T t).horizontal
    · have hy : p.2 ∉ tsupport (T t).vertical := by
        intro hy
        exact hn (mem_iUnion.mpr ⟨⟨t,ht⟩,hx,hy⟩)
      simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  apply (closure_minimal hsupport hK.isClosed).trans
  intro p hp
  obtain ⟨t,ht⟩ := mem_iUnion.mp hp
  exact ⟨(hs t).1 ht.1, (hs t).2 ht.2⟩

/-- The transposed PDE becomes first order using ONLY local weak-gradient
identities. No global weak derivative of the uncut function is inferred. -/
theorem local_gradient_secondOrder_firstOrder {Ω : Set Plane}
    {F m G : Plane → ℂ}
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p)))
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) (hGΩ : tsupport G ⊆ Ω)
    (hPDE : secondOrderEquation F m G) :
    smoothFirstOrderResidual ![m,(gx : Plane → ℂ),(gy : Plane → ℂ)] G = 0 := by
  have hxx := (hgrad (directional ex G) (directional_smooth ex hG)
    (directional_compact ex hGc) ((tsupport_fderiv_apply_subset ℝ ex).trans hGΩ)).1
  have hyy := (hgrad (directional ey G) (directional_smooth ey hG)
    (directional_compact ey hGc) ((tsupport_fderiv_apply_subset ℝ ey).trans hGΩ)).2
  have hx : (fun p => partialJet (firstIndex 1) G p) = directional ex G := by
    funext p
    rw [partialJet_eq_mixedJet hG]
    rfl
  have hy : (fun p => partialJet (firstIndex 2) G p) = directional ey G := by
    funext p
    rw [partialJet_eq_mixedJet hG]
    rfl
  change (∫ p, star (partialJet (firstIndex 1) G p) * gx p) +
    (∫ p, star (partialJet (firstIndex 2) G p) * gy p) + (∫ p, star (G p) * m p) = 0
  simp_rw [congrFun hx,congrFun hy]
  rw [hxx,hyy]
  change (∫ p, star (directional ex (directional ex G) p) * F p) +
    (∫ p, star (directional ey (directional ey G) p) * F p) = _ at hPDE
  linear_combination -hPDE

/-- Genuine local H1 test extension for an actual local coefficient
triple. The original second-order equation is required only for compact
smooth tests INSIDE U, and the local gradient only on a containing Ω. -/
theorem local_gradient_H1_test {Ω : Set Plane}
    (N : ℕ) (F m : Plane → ℂ) (hm : MemLp m 2 volume)
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p)))
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hUΩ : openRect uL uR vL vR ⊆ Ω)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo uL uR → z.im ∈ Ioo vL vR →
      z ∈ reducedCarrier N)
    (hPDE : ∀ G : Plane → ℂ, ContDiff ℝ ∞ G → HasCompactSupport G →
      tsupport G ⊆ openRect uL uR vL vR → secondOrderEquation F m G)
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (hs : tsupport J.value ⊆ openRect uL uR vL vR) :
    (∫ p, star (J.dx p) * gx p) + (∫ p, star (J.dy p) * gy p) +
      (∫ p, star (J.value p) * m p) = 0 := by
  have hc : ∀ i : Fin 3, MemLp (![m,(gx : Plane → ℂ),(gy : Plane → ℂ)] i) 2 volume := by
    intro i
    fin_cases i
    · exact hm
    · exact Lp.memLp gx
    · exact Lp.memLp gy
  apply local_finite_weakPDE_extends_to_H1 N _ hc uL uR vL vR hvL hu hv hU ?_ J hx hy hs
  intro ι s T hTs hK
  have hGs := finiteSmoothChart_contDiff s T
  have hGsupport := finiteTensor_tsupport_openRect s T uL uR vL vR hTs
  have hGc : HasCompactSupport (finiteChartFunction s (fun t => (T t).toCompactTensor)) := by
    have hclosed := finiteTensor_tsupport_rect s T uL uR vL vR (fun t =>
      ⟨(hTs t).1.trans Ioo_subset_Icc_self,(hTs t).2.trans Ioo_subset_Icc_self⟩)
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
      (subset_closure.trans hclosed)
  exact local_gradient_secondOrder_firstOrder gx gy hgrad hGs hGc
    (hGsupport.trans hUΩ) (hPDE _ hGs hGc hGsupport)

/-- The cutoff-square product is constructed as an actual H1 test with
its TWO Leibniz derivatives. This is the missing test-legality step in
weak IMS; no closure-membership hypothesis occurs. -/
theorem local_gradient_cutoff_square_test {Ω : Set Plane}
    (N : ℕ) (F m χ : Plane → ℂ) (hF : MemLp F 2 volume) (hm : MemLp m 2 volume)
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p) * gx p) = -(∫ p, star (directional ex ψ p) * F p)) ∧
      ((∫ p, star (ψ p) * gy p) = -(∫ p, star (directional ey ψ p) * F p)))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (uL uR vL vR : ℝ) (hvL : 0 < vL) (hu : uL < uR) (hv : vL < vR)
    (hUΩ : openRect uL uR vL vR ⊆ Ω)
    (hχU : tsupport χ ⊆ openRect uL uR vL vR)
    (hU : ∀ z : UpperHalfPlane, z.re ∈ Ioo uL uR → z.im ∈ Ioo vL vR →
      z ∈ reducedCarrier N)
    (hPDE : ∀ G : Plane → ℂ, ContDiff ℝ ∞ G → HasCompactSupport G →
      tsupport G ⊆ openRect uL uR vL vR → secondOrderEquation F m G) :
    (∫ p, star (productDerivative (fun q => χ q * χ q) F gx ex p) * gx p) +
    (∫ p, star (productDerivative (fun q => χ q * χ q) F gy ey p) * gy p) +
    (∫ p, star (χ p * χ p * F p) * m p) = 0 := by
  let C : Plane → ℂ := fun p => χ p * χ p
  have hC : ContDiff ℝ ∞ C := hχ.mul hχ
  have hCc : HasCompactSupport C := hχc.mul_right
  have hCU : tsupport C ⊆ openRect uL uR vL vR := tsupport_mul_subset_left.trans hχU
  have hCΩ := hCU.trans hUΩ
  let J := cutoffJet hF gx gy hC hCc hCΩ hgrad
  have hJs := cutoffJet_supports hF gx gy hC hCc hCΩ hgrad
  have hJx : HasCompactSupport J.dx :=
    hCc.of_isClosed_subset isClosed_tsupport hJs.2.1
  have hJy : HasCompactSupport J.dy :=
    hCc.of_isClosed_subset isClosed_tsupport hJs.2.2
  exact local_gradient_H1_test N F m hm gx gy hgrad uL uR vL vR hvL hu hv
    hUΩ hU hPDE J hJx hJy (hJs.1.trans hCU)

end
end ImbalancedChen.Part3.LocalGradientH1WeakTesting20261026b
