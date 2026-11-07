import ImbalancedChen.Part3Gamma0FiniteCosetGreenTrace
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Honest boundary-integral transport of the actual finite Gamma0 Green
trace. Only local C1 on the compact parameter interval is required, so
the result applies to the actual standard vertical and circular charts.
Every summand is proved continuous and interval-integrable from genuine
completed-field smoothness, the actual Mobius map and its exact tangent.
Native finite integral interchange then unfolds the traced boundary
integral into the actual inverse-coset-image edge integrals. No integral
interchange, transformed-edge derivative or side cancellation is a premise.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.Gamma0FiniteCosetGreenTrace20261026b
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.Gamma0GreenTraceEdges20261026b

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

theorem slFactor_continuousAt (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    ContinuousAt (slFactor g) (z : ℂ) := by
  have hd : ContinuousAt (fun w : ℂ => UpperHalfPlane.denom (realGL g) w) (z : ℂ) := by
    unfold UpperHalfPlane.denom
    fun_prop
  exact continuousAt_const.div (hd.pow 2)
    (pow_ne_zero 2 (UpperHalfPlane.denom_ne_zero (realGL g) z))

def matrixEdge (g : SL(2, ℤ)) (c : ℝ → UpperHalfPlane) (t : ℝ) : UpperHalfPlane := g • c t

theorem matrixEdge_hasDerivAt (g : SL(2, ℤ)) (c : ℝ → UpperHalfPlane) (t : ℝ)
    (hc : DifferentiableAt ℝ (fun r : ℝ => (c r : ℂ)) t) :
    HasDerivAt (fun r : ℝ => (matrixEdge g c r : ℂ))
      (slFactor (realSL g) (c t) * deriv (fun r : ℝ => (c r : ℂ)) t) t := by
  have h := (slMap_hasFDerivAt (realSL g) (c t)).comp_hasDerivAt t hc.hasDerivAt
  have heq : (fun r : ℝ => slMap (realSL g) (c r)) =
      (fun r : ℝ => (matrixEdge g c r : ℂ)) := by
    funext r
    simp only [matrixEdge, slMap_eq_action, realSL_action_int]
  rw [heq] at h
  exact h

private theorem greenOneForm_continuousAt_along (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ G (z : ℂ))
    (c : ℝ → UpperHalfPlane) (v : ℝ → ℂ) (t : ℝ)
    (hc : ContinuousAt (fun r : ℝ => (c r : ℂ)) t) (hv : ContinuousAt v t) :
    ContinuousAt (fun r => greenOneForm F G (c r) (v r)) t := by
  have hn : ContinuousAt (fun r => -I * v r) t := continuousAt_const.mul hv
  have hFv := (hF (c t)).continuousAt.comp t hc
  have hGv := (hG (c t)).continuousAt.comp t hc
  have hFn := (((hF (c t)).continuousAt_fderiv (by simp)).comp t hc).clm_apply hn
  have hGn := (((hG (c t)).continuousAt_fderiv (by simp)).comp t hc).clm_apply hn
  simpa only [greenOneForm, Complex.star_def] using
    (hFv.star.mul hGn).sub (hFn.star.mul hGv)

private theorem curve_deriv_continuousAt (c : ℝ → UpperHalfPlane) (t : ℝ)
    (hc : ContDiffAt ℝ 1 (fun r : ℝ => (c r : ℂ)) t) :
    ContinuousAt (deriv (fun r : ℝ => (c r : ℂ))) t := by
  simpa only [fderiv_apply_one_eq_deriv] using
    (hc.continuousAt_fderiv (by norm_num)).clm_apply (continuousAt_const (c := (1 : ℝ)))

/-- A physical pullback current summand is continuous under genuine local
C1 of the original edge, without requiring a global chart extension. -/
theorem actualTraceTerm_edge_continuousAt (N : ℕ) [NeZero N] (s u : ℂ)
    (q : gamma0Classes N) (c : ℝ → UpperHalfPlane) (t : ℝ)
    (hc : ContDiffAt ℝ 1 (fun r : ℝ => (c r : ℂ)) t) :
    ContinuousAt (fun r => traceTerm N (completedComplexField N s) (completedComplexField N u)
      q (c r) (deriv (fun v : ℝ => (c v : ℂ)) r)) t := by
  let g := inverseClassRep N q
  have hct := hc.continuousAt
  have hmap : ContinuousAt (fun r : ℝ => (matrixEdge g c r : ℂ)) t := by
    have h := (slMap_hasFDerivAt (realSL g) (c t)).continuousAt.comp t hct
    simpa only [slMap_eq_action, realSL_action_int, matrixEdge] using h
  have hf := (slFactor_continuousAt (realSL g) (c t)).comp t hct
  have hv := hf.mul (curve_deriv_continuousAt c t hc)
  have h := greenOneForm_continuousAt_along _ _ (completedComplexField_contDiffAt N s)
    (completedComplexField_contDiffAt N u) (matrixEdge g c)
    (fun r => slFactor (realSL g) (c r) * deriv (fun v : ℝ => (c v : ℂ)) r) t hmap hv
  have heq (r : ℝ) : traceTerm N (completedComplexField N s) (completedComplexField N u)
      q (c r) (deriv (fun v : ℝ => (c v : ℂ)) r) =
      greenOneForm (completedComplexField N s) (completedComplexField N u) (matrixEdge g c r)
        (slFactor (realSL g) (c r) * deriv (fun v : ℝ => (c v : ℂ)) r) :=
    traceTerm_eq_physical N _ _
      (fun z => (completedComplexField_contDiffAt N s z).differentiableAt (by simp))
      (fun z => (completedComplexField_contDiffAt N u z).differentiableAt (by simp)) q (c r) _
  simpa only [heq] using h

theorem actualTraceTerm_edge_intervalIntegrable (N : ℕ) [NeZero N] (s u : ℂ)
    (q : gamma0Classes N) (c : ℝ → UpperHalfPlane) (a b : ℝ)
    (hc : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 (fun r : ℝ => (c r : ℂ)) t) :
    IntervalIntegrable (fun t => traceTerm N (completedComplexField N s)
      (completedComplexField N u) q (c t) (deriv (fun r : ℝ => (c r : ℂ)) t)) volume a b :=
  (show ContinuousOn (fun t => traceTerm N (completedComplexField N s)
      (completedComplexField N u) q (c t) (deriv (fun r : ℝ => (c r : ℂ)) t)) (uIcc a b) from
    fun t ht => (actualTraceTerm_edge_continuousAt N s u q c t (hc t ht)).continuousWithinAt).intervalIntegrable

/-- Exact finite trace boundary unfolding, with every summand integrable
and each transformed tangent proved from the actual group action. -/
theorem actualCompletedGreenTrace_edge_integral_eq_sum (N : ℕ) [NeZero N] (s u : ℂ)
    (c : ℝ → UpperHalfPlane) (a b : ℝ)
    (hc : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 (fun r : ℝ => (c r : ℂ)) t) :
    (∫ t in a..b, actualCompletedGreenTrace N s u (c t)
      (deriv (fun r : ℝ => (c r : ℂ)) t)) =
      ∑ q : gamma0Classes N, ∫ t in a..b,
        greenOneForm (completedComplexField N s) (completedComplexField N u)
          (matrixEdge (inverseClassRep N q) c t)
          (deriv (fun r : ℝ => (matrixEdge (inverseClassRep N q) c r : ℂ)) t) := by
  unfold actualCompletedGreenTrace greenTrace
  rw [intervalIntegral.integral_finsetSum (fun q hq => actualTraceTerm_edge_intervalIntegrable N s u q c a b hc)]
  apply Finset.sum_congr rfl
  intro q hq
  apply intervalIntegral.integral_congr
  intro t ht
  rw [traceTerm_eq_physical N _ _
    (fun z => (completedComplexField_contDiffAt N s z).differentiableAt (by simp))
    (fun z => (completedComplexField_contDiffAt N u z).differentiableAt (by simp))]
  rw [(matrixEdge_hasDerivAt (inverseClassRep N q) c t
    ((hc t ht).differentiableAt (by norm_num))).deriv]
  rfl

end ImbalancedChen.Part3.Gamma0GreenTraceEdges20261026b
