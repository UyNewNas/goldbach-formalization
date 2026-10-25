import ImbalancedChen.Part3Gamma0CompactLaplacianSeed
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Genuine L1/Fubini prerequisites for a compact positive-height tensor seed
paired with an arbitrary noncompact C2 positive-chart function. Literal
slice derivatives are identified with the actual Frechet directional
derivatives, proving their JOINT continuity on the positive chart.

A compact rectangle supporting a(x)b(y) lies wholly inside that chart.
Every product star(a(x)b(y))*J(x,y) is integrable when J is continuous on
the positive chart, even if J is arbitrary outside it. This applies to
G, DxG, DyG, DxxG, DyyG and to continuous first/second seed derivatives.
Canonical upper-half-plane pairing integrability is also proved directly
from the same compact support and canonical hyperbolic volume.
No target integrability, Fubini, Green identity or cutoff premise is used.
-/

namespace ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a

def sliceDx (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun x : ℝ => G (x,p.2)) p.1

def sliceDy (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun y : ℝ => G (p.1,y)) p.2

def sliceDxx (G : ℝ × ℝ → ℂ) := sliceDx (sliceDx G)
def sliceDyy (G : ℝ × ℝ → ℂ) := sliceDy (sliceDy G)

theorem positiveChart_isOpen : IsOpen positiveChart :=
  isOpen_lt continuous_const continuous_snd

theorem sliceDx_eq_fderiv (G : ℝ × ℝ → ℂ)
    (hG : DifferentiableOn ℝ G positiveChart) {p : ℝ × ℝ} (hp : p ∈ positiveChart) :
    sliceDx G p = (fderiv ℝ G p) (1,0) := by
  have hGa : DifferentiableAt ℝ G p :=
    (hG p hp).differentiableAt (positiveChart_isOpen.mem_nhds hp)
  have hline : HasDerivAt (fun x : ℝ => (x,p.2)) (1,0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hGa.hasFDerivAt.comp_hasDerivAt p.1 hline).deriv

theorem sliceDy_eq_fderiv (G : ℝ × ℝ → ℂ)
    (hG : DifferentiableOn ℝ G positiveChart) {p : ℝ × ℝ} (hp : p ∈ positiveChart) :
    sliceDy G p = (fderiv ℝ G p) (0,1) := by
  have hGa : DifferentiableAt ℝ G p :=
    (hG p hp).differentiableAt (positiveChart_isOpen.mem_nhds hp)
  have hline : HasDerivAt (fun y : ℝ => (p.1,y)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hGa.hasFDerivAt.comp_hasDerivAt p.2 hline).deriv

theorem sliceDx_contDiffOn_one (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    ContDiffOn ℝ 1 (sliceDx G) positiveChart := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ G) positiveChart :=
    hG.fderiv_of_isOpen positiveChart_isOpen (by norm_num)
  have hA : ContDiffOn ℝ 1 (fun p => (fderiv ℝ G p) (1,0)) positiveChart :=
    hD.clm_apply contDiffOn_const
  exact hA.congr (fun p hp =>
    (sliceDx_eq_fderiv G (hG.differentiableOn (by norm_num)) hp).symm)

theorem sliceDy_contDiffOn_one (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    ContDiffOn ℝ 1 (sliceDy G) positiveChart := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ G) positiveChart :=
    hG.fderiv_of_isOpen positiveChart_isOpen (by norm_num)
  have hA : ContDiffOn ℝ 1 (fun p => (fderiv ℝ G p) (0,1)) positiveChart :=
    hD.clm_apply contDiffOn_const
  exact hA.congr (fun p hp =>
    (sliceDy_eq_fderiv G (hG.differentiableOn (by norm_num)) hp).symm)

theorem sliceDx_continuousOn_of_C1 (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 1 G positiveChart) : ContinuousOn (sliceDx G) positiveChart := by
  have hD : ContDiffOn ℝ 0 (fderiv ℝ G) positiveChart :=
    hG.fderiv_of_isOpen positiveChart_isOpen (by norm_num)
  have hA := (hD.clm_apply (contDiffOn_const : ContDiffOn ℝ 0 (fun _ : ℝ × ℝ => (1,0)) positiveChart)).continuousOn
  exact hA.congr (fun p hp =>
    (sliceDx_eq_fderiv G (hG.differentiableOn (by norm_num)) hp).symm)

theorem sliceDy_continuousOn_of_C1 (G : ℝ × ℝ → ℂ)
    (hG : ContDiffOn ℝ 1 G positiveChart) : ContinuousOn (sliceDy G) positiveChart := by
  have hD : ContDiffOn ℝ 0 (fderiv ℝ G) positiveChart :=
    hG.fderiv_of_isOpen positiveChart_isOpen (by norm_num)
  have hA := (hD.clm_apply (contDiffOn_const : ContDiffOn ℝ 0 (fun _ : ℝ × ℝ => (0,1)) positiveChart)).continuousOn
  exact hA.congr (fun p hp =>
    (sliceDy_eq_fderiv G (hG.differentiableOn (by norm_num)) hp).symm)

theorem sliceDxx_continuousOn (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    ContinuousOn (sliceDxx G) positiveChart :=
  sliceDx_continuousOn_of_C1 _ (sliceDx_contDiffOn_one G hG)

theorem sliceDyy_continuousOn (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    ContinuousOn (sliceDyy G) positiveChart :=
  sliceDy_continuousOn_of_C1 _ (sliceDy_contDiffOn_one G hG)

theorem chartMaass_continuousOn (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    ContinuousOn (chartMaass G) positiveChart := by
  change ContinuousOn (fun p : ℝ × ℝ =>
    -((p.2 : ℂ)^2*(sliceDxx G p+sliceDyy G p))) positiveChart
  exact (((Complex.continuous_ofReal.comp continuous_snd).pow 2).continuousOn.mul
    ((sliceDxx_continuousOn G hG).add (sliceDyy_continuousOn G hG))).neg

/-- The generic L1 primitive. Only a and b have compact support; J may be
noncompact and is required continuous solely on the true positive chart. -/
theorem compact_product_integrable (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (J : ℝ × ℝ → ℂ) (hJ : ContinuousOn J positiveChart) :
    Integrable (fun p : ℝ × ℝ => star (a p.1*b p.2)*J p) (volume : Measure (ℝ × ℝ)) := by
  let K := tsupport a ×ˢ tsupport b
  have hK : IsCompact K := hac.prod hbc
  have hKpos : K ⊆ positiveChart := fun p hp => hbp hp.2
  have hcont : ContinuousOn (fun p : ℝ × ℝ => star (a p.1*b p.2)*J p) K :=
    ((ha.comp continuous_fst).mul (hb.comp continuous_snd)).star.continuousOn.mul (hJ.mono hKpos)
  have hsupp : Function.support (fun p : ℝ × ℝ => star (a p.1*b p.2)*J p) ⊆ K := by
    intro p hp
    by_contra hnot
    apply hp
    by_cases hx : p.1 ∈ tsupport a
    · have hy : p.2 ∉ tsupport b := fun h => hnot ⟨hx,h⟩
      simp [image_eq_zero_of_notMem_tsupport hy]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (ContinuousOn.integrableOn_compact hK hcont)

theorem compact_product_G (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p : ℝ × ℝ => star (a p.1*b p.2)*G p) :=
  compact_product_integrable a b ha hb hac hbc hbp G hG.continuousOn

theorem compact_product_Dx (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p : ℝ × ℝ => star (a p.1*b p.2)*sliceDx G p) :=
  compact_product_integrable a b ha hb hac hbc hbp _ (sliceDx_contDiffOn_one G hG).continuousOn

theorem compact_product_Dy (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p : ℝ × ℝ => star (a p.1*b p.2)*sliceDy G p) :=
  compact_product_integrable a b ha hb hac hbc hbp _ (sliceDy_contDiffOn_one G hG).continuousOn

theorem compact_product_Dxx (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p : ℝ × ℝ => star (a p.1*b p.2)*sliceDxx G p) :=
  compact_product_integrable a b ha hb hac hbc hbp _ (sliceDxx_continuousOn G hG)

theorem compact_product_Dyy (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p : ℝ × ℝ => star (a p.1*b p.2)*sliceDyy G p) :=
  compact_product_integrable a b ha hb hac hbc hbp _ (sliceDyy_continuousOn G hG)

theorem seed_first_derivative_continuous (a : ℝ → ℂ) (ha : ContDiff ℝ 2 a) :
    Continuous (deriv a) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω)+1) a := by simpa using ha
  exact (contDiff_succ_iff_deriv.mp hs).2.2.continuous

theorem seed_deriv_positive (b : ℝ → ℂ) (hb : tsupport b ⊆ Ioi (0 : ℝ)) :
    tsupport (deriv b) ⊆ Ioi (0 : ℝ) := fun y hy => hb (tsupport_deriv_subset hy)

theorem seed_second_deriv_positive (b : ℝ → ℂ) (hb : tsupport b ⊆ Ioi (0 : ℝ)) :
    tsupport (deriv (deriv b)) ⊆ Ioi (0 : ℝ) :=
  fun y hy => hb (tsupport_deriv_subset (tsupport_deriv_subset hy))

theorem compact_product_second_horizontal_G (T : CompactTensor)
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p : ℝ × ℝ =>
      star (deriv (deriv T.horizontal) p.1*T.vertical p.2)*G p) :=
  compact_product_G _ _ (compactTensor_second_derivative_continuous _ T.horizontal_smooth)
    T.vertical_smooth.continuous T.horizontal_compact.deriv.deriv T.vertical_compact
    T.vertical_positive G hG

theorem compact_product_second_vertical_G (T : CompactTensor)
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p : ℝ × ℝ =>
      star (T.horizontal p.1*deriv (deriv T.vertical) p.2)*G p) :=
  compact_product_G _ _ T.horizontal_smooth.continuous
    (compactTensor_second_derivative_continuous _ T.vertical_smooth)
    T.horizontal_compact T.vertical_compact.deriv.deriv
    (seed_second_deriv_positive _ T.vertical_positive) G hG

/-- A compact chart seed also gives a compact subset of the ACTUAL H. -/
theorem positive_tensor_supportH_compact (a b : ℝ → ℂ)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ)) :
    IsCompact {z : UpperHalfPlane | z.re ∈ tsupport a ∧ z.im ∈ tsupport b} := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have heq : ((↑) : UpperHalfPlane → ℂ) '' {z | z.re ∈ tsupport a ∧ z.im ∈ tsupport b} =
      (fun p : ℝ × ℝ => (⟨p.1,p.2⟩ : ℂ)) '' (tsupport a ×ˢ tsupport b) := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(z.re,z.im),hz,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨⟨p.1,p.2⟩,hbp hp.2⟩,hp,rfl⟩
  rw [heq]
  exact (hac.prod hbc).image (by fun_prop)

/-- Genuine L1 for canonical hyperbolic volume, independently of any
coordinate cancellation or assumed Green/Fubini contract. -/
theorem compact_product_H_integrable (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) (hbp : tsupport b ⊆ Ioi (0 : ℝ))
    (J : ℝ × ℝ → ℂ) (hJ : ContinuousOn J positiveChart) :
    Integrable (fun z : UpperHalfPlane => star (a z.re*b z.im)*J (z.re,z.im))
      (volume : Measure UpperHalfPlane) := by
  let K : Set UpperHalfPlane := {z | z.re ∈ tsupport a ∧ z.im ∈ tsupport b}
  have hK : IsCompact K := positive_tensor_supportH_compact a b hac hbc hbp
  have hJH : Continuous (fun z : UpperHalfPlane => J (z.re,z.im)) :=
    hJ.comp_continuous (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)
      (fun z => z.im_pos)
  have hcont : Continuous (fun z : UpperHalfPlane => star (a z.re*b z.im)*J (z.re,z.im)) :=
    ((ha.comp UpperHalfPlane.continuous_re).mul (hb.comp UpperHalfPlane.continuous_im)).star.mul hJH
  have hsupp : Function.support (fun z : UpperHalfPlane => star (a z.re*b z.im)*J (z.re,z.im)) ⊆ K := by
    intro z hz
    by_contra hnot
    apply hz
    by_cases hx : z.re ∈ tsupport a
    · have hy : z.im ∉ tsupport b := fun h => hnot ⟨hx,h⟩
      simp [image_eq_zero_of_notMem_tsupport hy]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hcompact : HasCompactSupport (fun z : UpperHalfPlane => star (a z.re*b z.im)*J (z.re,z.im)) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hsupp hK.isClosed)
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Finite compact seeds against one full noncompact chart factor. -/
theorem finite_chart_product_integrable {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (J : ℝ × ℝ → ℂ) (hJ : ContinuousOn J positiveChart) :
    Integrable (fun p : ℝ × ℝ => star (finiteChartFunction s T p)*J p) := by
  have hsum : Integrable (fun p : ℝ × ℝ =>
      ∑ i ∈ s, star ((T i).horizontal p.1*(T i).vertical p.2)*J p) :=
    integrable_finsetSum s (fun i _ => compact_product_integrable _ _
      (T i).horizontal_smooth.continuous (T i).vertical_smooth.continuous
      (T i).horizontal_compact (T i).vertical_compact (T i).vertical_positive J hJ)
  convert hsum using 1
  funext p
  simp only [finiteChartFunction,star_sum,Finset.sum_mul]

/-- Generic actual-H compact pairing, also applicable to the C0 second
derivative seed, which must not be relabeled as a C2 CompactTensor. -/
theorem compact_H_pair_integrable (A B : UpperHalfPlane → ℂ)
    (hA : Continuous A) (hB : Continuous B) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hsupp : Function.support A ⊆ K) :
    Integrable (fun z => star (A z)*B z) (volume : Measure UpperHalfPlane) := by
  have hs : Function.support (fun z => star (A z)*B z) ⊆ K := by
    intro z hz
    apply hsupp
    intro hzero
    exact hz (by simp [hzero])
  have hc : HasCompactSupport (fun z => star (A z)*B z) :=
    hK.of_isClosed_subset isClosed_closure (closure_minimal hs hK.isClosed)
  exact (hA.star.mul hB).integrable_of_hasCompactSupport hc

theorem finite_core_second_pair_H_integrable {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun z : UpperHalfPlane => star (finiteCoreLaplacian s T z)*G (z.re,z.im))
      (volume : Measure UpperHalfPlane) := by
  have hGH : Continuous (fun z : UpperHalfPlane => G (z.re,z.im)) :=
    hG.continuousOn.comp_continuous
      (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im) (fun z => z.im_pos)
  exact compact_H_pair_integrable _ _ (finiteCoreLaplacian_continuous s T) hGH
    (finiteCompactTensorSupportK_isCompact s T) (finiteCoreLaplacian_support_subset s T)

theorem finite_core_chartMaass_pair_H_integrable {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (G : ℝ × ℝ → ℂ) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun z : UpperHalfPlane => star (finiteCoreFunction s T z)*chartMaass G (z.re,z.im))
      (volume : Measure UpperHalfPlane) := by
  have hJH : Continuous (fun z : UpperHalfPlane => chartMaass G (z.re,z.im)) :=
    (chartMaass_continuousOn G hG).comp_continuous
      (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im) (fun z => z.im_pos)
  exact compact_H_pair_integrable _ _ (continuous_finiteCoreFunction s T) hJH
    (finiteCompactTensorSupportK_isCompact s T) (finiteCoreFunction_support_subset s T)

end
end ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a
