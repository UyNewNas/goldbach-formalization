import ImbalancedChen.Part3StandardModularCellGraph
import ImbalancedChen.Part3PeriodicCuspStripStokes
import ImbalancedChen.Part3ActualCompletedGreenCurrentRegularity
import Mathlib.Tactic

/-!
# Actual curved-cell current pullback and divergence Jacobian

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
For the literal modular lower graph, the pulled-back outward current is
Kx=(T-h)Jx and Kr=Jy-(1-r)h'Jx at Phi(x,r)=(x,h+(T-h)r).
The actual Frechet chain/product rules prove div K=(T-h)(div J) o Phi.
The cancellation is proved pointwise; no Jacobian/divergence identity is
assumed. C1 of the pullback holds on its genuine positive open chart.
-/
namespace ImbalancedChen.Part3.StandardModularCellCurrentPullback20261026b
noncomputable section
open Set MeasureTheory
open StandardModularCellGraph20261026b PeriodicCuspStripStokes20261026b
open ActualCompletedGreenCurrentRegularity20261026b

def graphPullbackX (T : ℝ) (Jx : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((T - modularBottom p.1 : ℝ) : ℂ) * Jx (graphMap T p)

def graphPullbackY (T : ℝ) (Jx Jy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  Jy (graphMap T p) - (((1 - p.2) * bottomSlope p.1 : ℝ) : ℂ) * Jx (graphMap T p)

theorem graphPullbackX_contDiffOn (T : ℝ) (Jx : ℝ × ℝ → ℂ)
    (hx : ContDiffOn ℝ 1 Jx positiveStripChart) :
    ContDiffOn ℝ 1 (graphPullbackX T Jx) (graphDomain T) := by
  have hh : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => modularBottom p.1) (graphDomain T) :=
    (modularBottom_contDiffOn.comp contDiffOn_fst (fun _ hp => hp.1)).of_le (by norm_num)
  have hL := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hh)
  have hJ := hx.comp ((graphMap_contDiffOn T).of_le (by norm_num)) (fun _ hp => hp.2)
  exact hL.mul hJ

theorem graphPullbackY_contDiffOn (T : ℝ) (Jx Jy : ℝ × ℝ → ℂ)
    (hx : ContDiffOn ℝ 1 Jx positiveStripChart) (hy : ContDiffOn ℝ 1 Jy positiveStripChart) :
    ContDiffOn ℝ 1 (graphPullbackY T Jx Jy) (graphDomain T) := by
  have hs : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => bottomSlope p.1) (graphDomain T) :=
    (bottomSlope_contDiffOn.comp contDiffOn_fst (fun _ hp => hp.1)).of_le (by norm_num)
  have hv := Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_const.sub contDiffOn_snd).mul hs)
  have hJx := hx.comp ((graphMap_contDiffOn T).of_le (by norm_num)) (fun _ hp => hp.2)
  have hJy := hy.comp ((graphMap_contDiffOn T).of_le (by norm_num)) (fun _ hp => hp.2)
  exact hJy.sub (hv.mul hJx)

theorem graphMap_hasDerivAt_horizontal (T x r : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun z : ℝ => graphMap T (z,r)) (1, (1 - r) * bottomSlope x) x := by
  have hh := modularBottom_hasDerivAt hx
  convert (hasDerivAt_id x).prodMk
    (hh.add (((hasDerivAt_const x T).sub hh).mul_const r)) using 1
  <;> simp [graphMap, graphHeight] <;> ring

theorem graphMap_hasDerivAt_vertical (T x r : ℝ) :
    HasDerivAt (fun z : ℝ => graphMap T (x,z)) (0, T - modularBottom x) r := by
  convert (hasDerivAt_const r x).prodMk
    (((hasDerivAt_id r).const_mul (T - modularBottom x)).const_add (modularBottom x)) using 1
  <;> simp [graphMap, graphHeight] <;> ring

private theorem linear_horizontal_decomposition (D : (ℝ × ℝ) →L[ℝ] ℂ) (v : ℝ) :
    D (1,v) = D (1,0) + (v : ℂ) * D (0,1) := by
  have hv : (1,v) = ((1,0) : ℝ × ℝ) + v • ((0,1) : ℝ × ℝ) := by ext <;> simp
  rw [hv, map_add, map_smul, Complex.real_smul]

private theorem linear_vertical_decomposition (D : (ℝ × ℝ) →L[ℝ] ℂ) (v : ℝ) :
    D (0,v) = (v : ℂ) * D (0,1) := by
  have hv : (0,v) = v • ((0,1) : ℝ × ℝ) := by ext <;> simp
  rw [hv, map_smul, Complex.real_smul]

/-- The exact divergence/Jacobian identity for the actual graph map,
including fibers where T=h(x); no division by T-h(x) occurs. -/
theorem graphPullback_divergence (T : ℝ) (Jx Jy : ℝ × ℝ → ℂ)
    (hx : ContDiffOn ℝ 1 Jx positiveStripChart) (hy : ContDiffOn ℝ 1 Jy positiveStripChart)
    (x r : ℝ) (hp : (x,r) ∈ graphDomain T) :
    stripDivergence (graphPullbackX T Jx) (graphPullbackY T Jx Jy) (x,r) =
      ((T - modularBottom x : ℝ) : ℂ) * stripDivergence Jx Jy (graphMap T (x,r)) := by
  have hqx : DifferentiableAt ℝ Jx (graphMap T (x,r)) :=
    ((hx _ hp.2).contDiffAt (positiveStripChart_isOpen.mem_nhds hp.2)).differentiableAt (by norm_num)
  have hqy : DifferentiableAt ℝ Jy (graphMap T (x,r)) :=
    ((hy _ hp.2).contDiffAt (positiveStripChart_isOpen.mem_nhds hp.2)).differentiableAt (by norm_num)
  have hmapx := graphMap_hasDerivAt_horizontal T x r hp.1
  have hmapr := graphMap_hasDerivAt_vertical T x r
  have hJxx := hqx.hasFDerivAt.comp_hasDerivAt x hmapx
  have hJxr := hqx.hasFDerivAt.comp_hasDerivAt r hmapr
  have hJyr := hqy.hasFDerivAt.comp_hasDerivAt r hmapr
  have hLx : HasDerivAt (fun z : ℝ => ((T - modularBottom z : ℝ) : ℂ))
      (-(bottomSlope x : ℂ)) x := by
    simpa only [zero_sub, Complex.ofReal_neg] using
      ((hasDerivAt_const x T).sub (modularBottom_hasDerivAt hp.1)).ofReal_comp
  have hVr : HasDerivAt (fun z : ℝ => (((1 - z) * bottomSlope x : ℝ) : ℂ))
      (-(bottomSlope x : ℂ)) r := by
    convert (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).mul_const (bottomSlope x)).ofReal_comp using 1
    <;> push_cast <;> ring
  have hKx := hLx.mul hJxx
  have hKy := hJyr.sub (hVr.mul hJxr)
  have hKxAt := ((graphPullbackX_contDiffOn T Jx hx) (x,r) hp).contDiffAt
    ((graphDomain_isOpen T).mem_nhds hp)
  have hKyAt := ((graphPullbackY_contDiffOn T Jx Jy hx hy) (x,r) hp).contDiffAt
    ((graphDomain_isOpen T).mem_nhds hp)
  unfold stripDivergence
  rw [← slice_deriv_x_eq_fderiv (hKxAt.differentiableAt (by norm_num)),
    ← slice_deriv_y_eq_fderiv (hKyAt.differentiableAt (by norm_num))]
  change deriv (fun z : ℝ => ((T - modularBottom z : ℝ) : ℂ) * Jx (graphMap T (z,r))) x +
    deriv (fun z : ℝ => Jy (graphMap T (x,z)) -
      (((1 - z) * bottomSlope x : ℝ) : ℂ) * Jx (graphMap T (x,z))) r = _
  rw [hKx.deriv, hKy.deriv,
    linear_horizontal_decomposition (fderiv ℝ Jx (graphMap T (x,r))) ((1 - r) * bottomSlope x),
    linear_vertical_decomposition (fderiv ℝ Jy (graphMap T (x,r))) (T - modularBottom x),
    linear_vertical_decomposition (fderiv ℝ Jx (graphMap T (x,r))) (T - modularBottom x)]
  push_cast
  ring

end
end ImbalancedChen.Part3.StandardModularCellCurrentPullback20261026b

