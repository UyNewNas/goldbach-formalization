import ImbalancedChen.Part3Gamma0CompactTensorPoincareC2Core
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual coordinate Maass differentiation is local, even for the total
derivative operation at a nonsmooth function.  The local finite formula
for the genuine Gamma0 Poincare sum may therefore be differentiated twice.
The result is a finite sum of actual Maass derivatives of the Mobius
pullbacks.  Identifying each pullback derivative with the transformed seed
Laplacian is a separate geometric equivariance theorem, not a premise here.
-/

namespace ImbalancedChen.Part3.ActualPoincareMaassLocalFinite20261025a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a

theorem chartMaass_eq_of_eventuallyEq {F G : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (h : F =ᶠ[𝓝 p] G) : chartMaass F p = chartMaass G p := by
  have hx : (fun x : ℝ => F (x,p.2)) =ᶠ[𝓝 p.1]
      (fun x : ℝ => G (x,p.2)) :=
    (continuousAt_id.prodMk continuousAt_const).eventually h
  have hy : (fun y : ℝ => F (p.1,y)) =ᶠ[𝓝 p.2]
      (fun y : ℝ => G (p.1,y)) :=
    (continuousAt_const.prodMk continuousAt_id).eventually h
  simp only [chartMaass, hx.deriv.deriv_eq, hy.deriv.deriv_eq]

private theorem positiveChart_isOpen : IsOpen positiveChart :=
  isOpen_lt continuous_const continuous_snd

private theorem sliceX_contDiffAt {F : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ 2 F positiveChart) {x y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ 2 (fun t : ℝ => F (t,y)) x := by
  have h := (hF (x,y) hy).contDiffAt (positiveChart_isOpen.mem_nhds hy)
  exact h.comp x (contDiffAt_id.prodMk contDiffAt_const)

private theorem sliceY_contDiffAt {F : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ 2 F positiveChart) {x y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ 2 (fun t : ℝ => F (x,t)) y := by
  have h := (hF (x,y) hy).contDiffAt (positiveChart_isOpen.mem_nhds hy)
  exact h.comp y (contDiffAt_const.prodMk contDiffAt_id)

/-- Both second derivatives distribute over a genuine finite family of
C2 functions.  Only the vertical germ is used; no regularity below y=0
is required of any chart extension. -/
theorem chartMaass_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ × ℝ → ℂ)
    (hF : ∀ i ∈ s, ContDiffOn ℝ 2 (F i) positiveChart)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    chartMaass (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, chartMaass (F i) p := by
  have hfirstX : deriv (fun x : ℝ => ∑ i ∈ s, F i (x,p.2)) =
      (fun x => ∑ i ∈ s, deriv (fun t : ℝ => F i (t,p.2)) x) := by
    funext x
    exact deriv_fun_sum (fun i hi =>
      (sliceX_contDiffAt (hF i hi) hp).differentiableAt (by norm_num))
  have hsecondX :
      deriv (deriv (fun x : ℝ => ∑ i ∈ s, F i (x,p.2))) p.1 =
        ∑ i ∈ s, deriv (deriv (fun x : ℝ => F i (x,p.2))) p.1 := by
    rw [hfirstX]
    exact deriv_fun_sum (fun i hi =>
      ((sliceX_contDiffAt (hF i hi) hp).derivWithin
        (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hfirstY : deriv (fun y : ℝ => ∑ i ∈ s, F i (p.1,y)) =ᶠ[𝓝 p.2]
      (fun y => ∑ i ∈ s, deriv (fun t : ℝ => F i (p.1,t)) y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hp] with y hy
    exact deriv_fun_sum (fun i hi =>
      (sliceY_contDiffAt (hF i hi) hy).differentiableAt (by norm_num))
  have hsecondY :
      deriv (deriv (fun y : ℝ => ∑ i ∈ s, F i (p.1,y))) p.2 =
        ∑ i ∈ s, deriv (deriv (fun y : ℝ => F i (p.1,y))) p.2 := by
    rw [hfirstY.deriv_eq]
    exact deriv_fun_sum (fun i hi =>
      ((sliceY_contDiffAt (hF i hi) hp).derivWithin
        (m := 1) (by norm_num)).differentiableAt (by norm_num))
  unfold chartMaass
  rw [hsecondX,hsecondY,← Finset.sum_add_distrib,Finset.mul_sum,
    Finset.sum_neg_distrib]

/-- Actual Gamma0 periodization differentiates as one finite sum of
actual translated seed derivatives at every positive coordinate point.
This derives the local differentiation licence from integral-matrix
properness, rather than accepting a differentiable-series hypothesis. -/
theorem actualPoincare_chartMaass_eq_finiteSum (N : ℕ) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ∃ S : Finset (effectiveGamma0 N),
      chartMaass (extendUpper (finiteCompactTensorPoincare N s T)) p =
        ∑ q ∈ S, chartMaass (translatedFiniteTensorChart N q s T) p := by
  obtain ⟨U,hU,S,hS⟩ :=
    finiteCompactTensorPoincare_locally_eq_finsetSum N s T (chartLift p)
  have hcont : ContinuousAt chartLift p :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n := 2) hp).continuousAt.comp
      (by
        have heq : complexOfPair =
            (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ)*Complex.I) := by
          funext q
          ext <;> simp [complexOfPair]
        rw [heq]
        fun_prop)
  have hpre : ∀ᶠ p' in 𝓝 p, chartLift p' ∈ U := hcont hU
  have hpos : ∀ᶠ p' in 𝓝 p, 0 < p'.2 := positiveChart_isOpen.mem_nhds hp
  have heq : extendUpper (finiteCompactTensorPoincare N s T) =ᶠ[𝓝 p]
      (fun p' => ∑ q ∈ S, translatedFiniteTensorChart N q s T p') := by
    filter_upwards [hpre,hpos] with p' hpU hp'
    have hext : extendUpper (finiteCompactTensorPoincare N s T) p' =
        finiteCompactTensorPoincare N s T (chartLift p') := by
      rw [extendUpper,dif_pos hp',chartLift_of_positive hp']
      rfl
    rw [hext,hS (chartLift p') hpU]
    apply Finset.sum_congr rfl
    intro q _
    exact (translatedFiniteTensorChart_eq_actual N q s T hp').symm
  refine ⟨S,(chartMaass_eq_of_eventuallyEq heq).trans ?_⟩
  apply chartMaass_finsetSum S (fun q => translatedFiniteTensorChart N q s T)
  intro q hq p' hp'
  exact (translatedFiniteTensorChart_contDiffAt N q s T hp').contDiffWithinAt

end
end ImbalancedChen.Part3.ActualPoincareMaassLocalFinite20261025a
