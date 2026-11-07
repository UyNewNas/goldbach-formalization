import ImbalancedChen.Part3ActualMobiusGreenPullbackDivergence
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The coordinate vector of Prime's ACTUAL finite SL2Z/Gamma0(N) Green trace.
The original inverseClassRep and actual pulled completed fields are used.
Finite Frechet differentiation is justified by genuine C1 summands. The
trace divergence is the exact spectral difference times the finite sum
of actual translated native field products divided by y^2. The coordinate
one-form is proved equal to the ORIGINAL actualCompletedGreenTrace, and
to the finite physical-side current sum with literal Mobius tangent.
No trace identity, C1 bound, or divergence is assumed. Side cancellation
and curved-cell Stokes remain the separate Prime/Mellin suppliers.
-/

namespace ImbalancedChen.Part3.ActualFiniteCosetGreenDivergence20261026b
noncomputable section
open Set Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups BigOperators
open AllLevelContinuedMaass20261026a LevelOldformScattering20261026a
open ContinuedFourierSpatialContDiffTwo
open ActualCompletedGamma0Sides20261026b SLRealGreenCurrent20261026b
open Gamma0FiniteMeasureCarrier20261024z Gamma0FiniteCosetGreenTrace20261026b FrickeNormalizer
open ActualAllLevelGreenInterior20261026b ActualMobiusCompletedPullback20261026b
open ActualMobiusGreenPullbackDivergence20261026b

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

def actualCosetTraceX (N : ℕ) [NeZero N] (s u : ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ q : gamma0Classes N, pulledGreenX N s u (inverseClassRep N q) p

def actualCosetTraceY (N : ℕ) [NeZero N] (s u : ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ q : gamma0Classes N, pulledGreenY N s u (inverseClassRep N q) p

def actualCosetTraceProduct (N : ℕ) [NeZero N] (s u : ℂ) (p : ℝ × ℝ) : ℂ :=
  ∑ q : gamma0Classes N, star (pulledCompletedChart N s (inverseClassRep N q) p) *
    pulledCompletedChart N u (inverseClassRep N q) p

def actualCosetTraceOneForm (N : ℕ) [NeZero N] (s u : ℂ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  coordinateLinear (-actualCosetTraceY N s u p) (actualCosetTraceX N s u p)

theorem actualCosetTraceX_contDiffOn_one (N : ℕ) [NeZero N] (s u : ℂ) :
    ContDiffOn ℝ 1 (actualCosetTraceX N s u) upperChart := by
  apply ContDiffOn.sum
  intro q hq
  exact pulledGreenX_contDiffOn_one N s u (inverseClassRep N q)

theorem actualCosetTraceY_contDiffOn_one (N : ℕ) [NeZero N] (s u : ℂ) :
    ContDiffOn ℝ 1 (actualCosetTraceY N s u) upperChart := by
  apply ContDiffOn.sum
  intro q hq
  exact pulledGreenY_contDiffOn_one N s u (inverseClassRep N q)

theorem actualCosetTraceOneForm_contDiffOn_one (N : ℕ) [NeZero N] (s u : ℂ) :
    ContDiffOn ℝ 1 (actualCosetTraceOneForm N s u) upperChart := by
  simpa only [actualCosetTraceOneForm, coordinateLinear] using
    ((firstLift.contDiff.comp_contDiffOn (actualCosetTraceY_contDiffOn_one N s u).neg).add
      (secondLift.contDiff.comp_contDiffOn (actualCosetTraceX_contDiffOn_one N s u)))

/-- Actual finite trace derivative: every summand has proved Frechet C1,
so there is no sum/interchange or trace-divergence assumption. -/
theorem actualCosetTrace_divergence_eq (N : ℕ) [NeZero N] (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (x y : ℝ) (hy : 0 < y) :
    fderiv ℝ (actualCosetTraceX N s u) (x, y) (1, 0) +
      fderiv ℝ (actualCosetTraceY N s u) (x, y) (0, 1) =
      (star (s * (1 - s)) - u * (1 - u)) * actualCosetTraceProduct N s u (x, y) / (y : ℂ) ^ 2 := by
  have hX (q : gamma0Classes N) : DifferentiableAt ℝ (pulledGreenX N s u (inverseClassRep N q)) (x, y) :=
    (((pulledGreenX_contDiffOn_one N s u (inverseClassRep N q)) (x, y) hy).contDiffAt
      (upperChart_isOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hY (q : gamma0Classes N) : DifferentiableAt ℝ (pulledGreenY N s u (inverseClassRep N q)) (x, y) :=
    (((pulledGreenY_contDiffOn_one N s u (inverseClassRep N q)) (x, y) hy).contDiffAt
      (upperChart_isOpen.mem_nhds hy)).differentiableAt (by norm_num)
  unfold actualCosetTraceX actualCosetTraceY
  rw [fderiv_fun_sum (fun q hq => hX q), fderiv_fun_sum (fun q hq => hY q)]
  simp only [ContinuousLinearMap.sum_apply]
  rw [← Finset.sum_add_distrib]
  change (∑ q : gamma0Classes N, pulledGreenDivergence N s u (inverseClassRep N q) (x, y)) = _
  calc
    _ = ∑ q : gamma0Classes N, (star (s * (1 - s)) - u * (1 - u)) *
        star (pulledCompletedChart N s (inverseClassRep N q) (x, y)) *
          pulledCompletedChart N u (inverseClassRep N q) (x, y) / (y : ℂ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact pulledGreenDivergence_eq N s u hs hu (inverseClassRep N q) x y hy
    _ = _ := by
      unfold actualCosetTraceProduct
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem pulledCompletedChart_eq_native (N : ℕ) (s : ℂ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    pulledCompletedChart N s g (z.re, z.im) = completedLevelOldform N s (g • z) := by
  simp only [pulledCompletedChart, pulledField, slMap_eq_action, Gamma0PairedEdgeGreen20261026b.realSL_action_int,
    completedComplexField_eq_native]

/-- Required physical mass density of the ACTUAL original finite trace:
the sum is over genuine inverse representatives and native translated E. -/
theorem actualCosetTrace_divergence_native (N : ℕ) [NeZero N] (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N) (z : UpperHalfPlane) :
    fderiv ℝ (actualCosetTraceX N s u) (z.re, z.im) (1, 0) +
      fderiv ℝ (actualCosetTraceY N s u) (z.re, z.im) (0, 1) =
      (star (s * (1 - s)) - u * (1 - u)) *
        (∑ q : gamma0Classes N, star (completedLevelOldform N s (inverseClassRep N q • z)) *
          completedLevelOldform N u (inverseClassRep N q • z)) / (z.im : ℂ) ^ 2 := by
  rw [actualCosetTrace_divergence_eq N s u hs hu z.re z.im z.im_pos]
  simp only [actualCosetTraceProduct, pulledCompletedChart_eq_native]

private theorem actualCosetTraceOneForm_eq_sum (N : ℕ) [NeZero N] (s u : ℂ)
    (p h : ℝ × ℝ) : actualCosetTraceOneForm N s u p h =
      ∑ q : gamma0Classes N, pulledGreenOneForm N s u (inverseClassRep N q) p h := by
  simp only [actualCosetTraceOneForm, actualCosetTraceX, actualCosetTraceY,
    pulledGreenOneForm, coordinateLinear_apply, Complex.real_smul,
    Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_neg]

/-- Identification with Prime's ORIGINAL actualCompletedGreenTrace.
This is the current used by full SL2Z coset reindexing and S/T side formulas. -/
theorem actualCosetTraceOneForm_eq_actualTrace (N : ℕ) [NeZero N] (s u : ℂ)
    (z : UpperHalfPlane) (v : ℂ) :
    actualCosetTraceOneForm N s u (z.re, z.im) (v.re, v.im) = actualCompletedGreenTrace N s u z v := by
  rw [actualCosetTraceOneForm_eq_sum]
  unfold actualCompletedGreenTrace greenTrace
  apply Finset.sum_congr rfl
  intro q hq
  exact pulledGreenOneForm_eq_complex N s u (inverseClassRep N q) z v

/-- Literal physical summand formula, with every transformed tangent and
its sign retained; no new boundary-current definition is substituted. -/
theorem actualCosetTraceOneForm_eq_physical_sum (N : ℕ) [NeZero N] (s u : ℂ)
    (z : UpperHalfPlane) (v : ℂ) :
    actualCosetTraceOneForm N s u (z.re, z.im) (v.re, v.im) =
      ∑ q : gamma0Classes N, actualLevelGreenOneForm N s u
        ((inverseClassRep N q • z).re, (inverseClassRep N q • z).im)
        ((slFactor (realSL (inverseClassRep N q)) z * v).re,
          (slFactor (realSL (inverseClassRep N q)) z * v).im) := by
  rw [actualCosetTraceOneForm_eq_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact pulledGreenOneForm_eq_physical N s u (inverseClassRep N q) z v

end
end ImbalancedChen.Part3.ActualFiniteCosetGreenDivergence20261026b
