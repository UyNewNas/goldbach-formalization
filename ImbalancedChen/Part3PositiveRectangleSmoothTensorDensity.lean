import ImbalancedChen.Part3MaassWeakOperatorCore
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A genuine compact-rectangle tensor approximation theorem. On every
[-A,A] x [a,b], A>=0 and 0<a<=b, complex finite linear combinations of
restrictions of real C-infinity compact separated products are uniformly
dense in the actual continuous complex functions on that rectangle.
Every vertical factor has topological support in y>0.

Explicit smooth cutoffs construct the constant and both coordinate tests.
Products remain single separated tests, and all tests are real valued,
so their complex algebra is a star algebra. Stone-Weierstrass is applied
only after these facts and actual point separation have been proved.
No density or approximation conclusion occurs among the hypotheses.

This supplies the local separated approximation ingredient, not the full
canonical hyperbolic L2 density theorem. Global positive-chart exhaustion,
L2 passage and its quotient transport remain separate obligations.
-/

namespace ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a

noncomputable section
open Set Metric

/-- Real factors suffice: the span and approximation coefficients are complex. -/
structure SmoothPositiveTensor where
  horizontal : ℝ → ℝ
  vertical : ℝ → ℝ
  horizontal_smooth : ContDiff ℝ ∞ horizontal
  vertical_smooth : ContDiff ℝ ∞ vertical
  horizontal_compact : HasCompactSupport horizontal
  vertical_compact : HasCompactSupport vertical
  vertical_positive : tsupport vertical ⊆ Ioi (0 : ℝ)

/-- These are literal tests in the already defined canonical Maass core. -/
def toMaassTensor (T : SmoothPositiveTensor) :
    ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz.CompactTensor where
  horizontal := Complex.ofRealCLM ∘ T.horizontal
  vertical := Complex.ofRealCLM ∘ T.vertical
  horizontal_smooth := (Complex.ofRealCLM.contDiff.comp T.horizontal_smooth).of_le (by simp)
  vertical_smooth := (Complex.ofRealCLM.contDiff.comp T.vertical_smooth).of_le (by simp)
  horizontal_compact := T.horizontal_compact.comp_left rfl
  vertical_compact := T.vertical_compact.comp_left rfl
  vertical_positive := (tsupport_comp_subset rfl _).trans T.vertical_positive

def rectangle (A a b : ℝ) : Set (ℝ × ℝ) := Icc (-A) A ×ˢ Icc a b

instance rectangle_compactSpace (A a b : ℝ) : CompactSpace (rectangle A a b) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)

def restrictTensor (A a b : ℝ) (T : SmoothPositiveTensor) :
    C(rectangle A a b, ℂ) where
  toFun p := ((T.horizontal p.1.1 * T.vertical p.1.2 : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((T.horizontal_smooth.continuous.comp
      (continuous_fst.comp continuous_subtype_val)).mul
    (T.vertical_smooth.continuous.comp
      (continuous_snd.comp continuous_subtype_val)))

theorem restrictTensor_eq_actual_canonical_tensor (A a b : ℝ)
    (T : SmoothPositiveTensor) (z : UpperHalfPlane)
    (hz : (z.re, z.im) ∈ rectangle A a b) :
    restrictTensor A a b T ⟨(z.re, z.im), hz⟩ =
      ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z.tensorFunctionH
        (toMaassTensor T).horizontal (toMaassTensor T).vertical z := by
  simp [restrictTensor, toMaassTensor,
    ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z.tensorFunctionH_eq,
    Complex.ofReal_mul]

def multiplyTensor (T U : SmoothPositiveTensor) : SmoothPositiveTensor where
  horizontal x := T.horizontal x * U.horizontal x
  vertical y := T.vertical y * U.vertical y
  horizontal_smooth := T.horizontal_smooth.mul U.horizontal_smooth
  vertical_smooth := T.vertical_smooth.mul U.vertical_smooth
  horizontal_compact := U.horizontal_compact.mul_left
  vertical_compact := U.vertical_compact.mul_left
  vertical_positive := tsupport_mul_subset_right.trans U.vertical_positive

theorem restrict_multiplyTensor (A a b : ℝ) (T U : SmoothPositiveTensor) :
    restrictTensor A a b (multiplyTensor T U) =
      restrictTensor A a b T * restrictTensor A a b U := by
  ext p
  simp only [restrictTensor, multiplyTensor, ContinuousMap.mul_apply]
  push_cast
  ring

theorem star_restrictTensor (A a b : ℝ) (T : SmoothPositiveTensor) :
    star (restrictTensor A a b T) = restrictTensor A a b T := by
  ext p
  simp [restrictTensor, Complex.star_def]

def horizontalBump (A : ℝ) (hA : 0 ≤ A) : ContDiffBump (0 : ℝ) where
  rIn := A + 1
  rOut := A + 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def verticalBump (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 2 + a / 4
  rOut := (b - a) / 2 + a / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

theorem horizontalBump_eq_one (A : ℝ) (hA : 0 ≤ A) {x : ℝ}
    (hx : x ∈ Icc (-A) A) : horizontalBump A hA x = 1 := by
  apply (horizontalBump A hA).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
  change -(A + 1) ≤ x ∧ x ≤ A + 1
  constructor <;> linarith [hx.1, hx.2]

theorem verticalBump_eq_one (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    {y : ℝ} (hy : y ∈ Icc a b) : verticalBump a b ha hab y = 1 := by
  apply (verticalBump a b ha hab).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -((b - a) / 2 + a / 4) ≤ y - (a + b) / 2 ∧
    y - (a + b) / 2 ≤ (b - a) / 2 + a / 4
  constructor <;> linarith [hy.1, hy.2]

theorem verticalBump_positive_support (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    tsupport (verticalBump a b ha hab) ⊆ Ioi (0 : ℝ) := by
  intro y hy
  rw [(verticalBump a b ha hab).tsupport_eq,
    Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
  change -((b - a) / 2 + a / 2) ≤ y - (a + b) / 2 ∧
    y - (a + b) / 2 ≤ (b - a) / 2 + a / 2 at hy
  change 0 < y
  linarith [hy.1]

def cutoffTensor (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    SmoothPositiveTensor where
  horizontal := horizontalBump A hA
  vertical := verticalBump a b ha hab
  horizontal_smooth := (horizontalBump A hA).contDiff
  vertical_smooth := (verticalBump a b ha hab).contDiff
  horizontal_compact := (horizontalBump A hA).hasCompactSupport
  vertical_compact := (verticalBump a b ha hab).hasCompactSupport
  vertical_positive := verticalBump_positive_support a b ha hab

def horizontalCoordinateTensor (T : SmoothPositiveTensor) : SmoothPositiveTensor where
  horizontal x := x * T.horizontal x
  vertical := T.vertical
  horizontal_smooth := contDiff_id.mul T.horizontal_smooth
  vertical_smooth := T.vertical_smooth
  horizontal_compact := T.horizontal_compact.mul_left
  vertical_compact := T.vertical_compact
  vertical_positive := T.vertical_positive

def verticalCoordinateTensor (T : SmoothPositiveTensor) : SmoothPositiveTensor where
  horizontal := T.horizontal
  vertical y := y * T.vertical y
  horizontal_smooth := T.horizontal_smooth
  vertical_smooth := contDiff_id.mul T.vertical_smooth
  horizontal_compact := T.horizontal_compact
  vertical_compact := T.vertical_compact.mul_left
  vertical_positive := tsupport_mul_subset_right.trans T.vertical_positive

theorem restrict_cutoffTensor (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) :
    restrictTensor A a b (cutoffTensor A a b hA ha hab) = 1 := by
  ext p
  change ((horizontalBump A hA p.1.1 * verticalBump a b ha hab p.1.2 : ℝ) : ℂ) = 1
  rw [horizontalBump_eq_one A hA p.2.1, verticalBump_eq_one a b ha hab p.2.2]
  norm_num

theorem restrict_horizontalCoordinateTensor (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) (p : rectangle A a b) :
    restrictTensor A a b
      (horizontalCoordinateTensor (cutoffTensor A a b hA ha hab)) p = (p.1.1 : ℂ) := by
  change (((p.1.1 * horizontalBump A hA p.1.1) *
    verticalBump a b ha hab p.1.2 : ℝ) : ℂ) = _
  rw [horizontalBump_eq_one A hA p.2.1, verticalBump_eq_one a b ha hab p.2.2]
  simp

theorem restrict_verticalCoordinateTensor (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) (p : rectangle A a b) :
    restrictTensor A a b
      (verticalCoordinateTensor (cutoffTensor A a b hA ha hab)) p = (p.1.2 : ℂ) := by
  change ((horizontalBump A hA p.1.1 *
    (p.1.2 * verticalBump a b ha hab p.1.2) : ℝ) : ℂ) = _
  rw [horizontalBump_eq_one A hA p.2.1, verticalBump_eq_one a b ha hab p.2.2]
  simp

def tensorRestrictions (A a b : ℝ) : Set C(rectangle A a b, ℂ) :=
  Set.range (restrictTensor A a b)

def tensorRestrictionMonoid (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) : Submonoid C(rectangle A a b, ℂ) where
  carrier := tensorRestrictions A a b
  one_mem' := ⟨cutoffTensor A a b hA ha hab, restrict_cutoffTensor A a b hA ha hab⟩
  mul_mem' := by
    rintro f g ⟨T, rfl⟩ ⟨U, rfl⟩
    exact ⟨multiplyTensor T U, restrict_multiplyTensor A a b T U⟩

def tensorAlgebra (A a b : ℝ) : Subalgebra ℂ C(rectangle A a b, ℂ) :=
  Algebra.adjoin ℂ (tensorRestrictions A a b)

theorem tensorAlgebra_eq_span (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) :
    (tensorAlgebra A a b).toSubmodule =
      Submodule.span ℂ (tensorRestrictions A a b) := by
  rw [tensorAlgebra, Algebra.adjoin_eq_span]
  have hclosure : Submonoid.closure (tensorRestrictions A a b) =
      tensorRestrictionMonoid A a b hA ha hab :=
    (tensorRestrictionMonoid A a b hA ha hab).closure_eq
  rw [hclosure]
  rfl

theorem tensorAlgebra_star_mem (A a b : ℝ) {f : C(rectangle A a b, ℂ)}
    (hf : f ∈ tensorAlgebra A a b) : star f ∈ tensorAlgebra A a b := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
      obtain ⟨T, rfl⟩ := hf
      rw [star_restrictTensor]
      exact Algebra.subset_adjoin ⟨T, rfl⟩
  | algebraMap c =>
      simpa only [star_algebraMap] using
        (tensorAlgebra A a b).algebraMap_mem (star c)
  | add f g hf hg ihf ihg =>
      simpa only [star_add] using (tensorAlgebra A a b).add_mem ihf ihg
  | mul f g hf hg ihf ihg =>
      simpa only [star_mul] using (tensorAlgebra A a b).mul_mem ihg ihf

def tensorStarAlgebra (A a b : ℝ) : StarSubalgebra ℂ C(rectangle A a b, ℂ) where
  toSubalgebra := tensorAlgebra A a b
  star_mem' := tensorAlgebra_star_mem A a b

/-- The separating functions are actual compact smooth tensors: the
coordinate is multiplied by the explicit horizontal/vertical cutoffs. -/
theorem tensorStarAlgebra_separatesPoints (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) : (tensorStarAlgebra A a b).SeparatesPoints := by
  intro p q hpq
  let T := cutoffTensor A a b hA ha hab
  by_cases hx : p.1.1 = q.1.1
  · have hy : p.1.2 ≠ q.1.2 := by
      intro hy
      exact hpq (Subtype.ext (Prod.ext hx hy))
    refine ⟨restrictTensor A a b (verticalCoordinateTensor T),
      ⟨_, Algebra.subset_adjoin ⟨verticalCoordinateTensor T, rfl⟩, rfl⟩, ?_⟩
    change restrictTensor A a b (verticalCoordinateTensor T) p ≠
      restrictTensor A a b (verticalCoordinateTensor T) q
    rw [restrict_verticalCoordinateTensor, restrict_verticalCoordinateTensor]
    exact fun h => hy (Complex.ofReal_injective h)
  · refine ⟨restrictTensor A a b (horizontalCoordinateTensor T),
      ⟨_, Algebra.subset_adjoin ⟨horizontalCoordinateTensor T, rfl⟩, rfl⟩, ?_⟩
    change restrictTensor A a b (horizontalCoordinateTensor T) p ≠
      restrictTensor A a b (horizontalCoordinateTensor T) q
    rw [restrict_horizontalCoordinateTensor, restrict_horizontalCoordinateTensor]
    exact fun h => hx (Complex.ofReal_injective h)

/-- Actual finite complex linear combinations of compact C-infinity
positive-height separated tests are uniformly dense on each rectangle. -/
theorem smooth_tensor_span_dense_on_rectangle (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) :
    Dense (Submodule.span ℂ (tensorRestrictions A a b) :
      Set C(rectangle A a b, ℂ)) := by
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (tensorStarAlgebra A a b) (tensorStarAlgebra_separatesPoints A a b hA ha hab)
  have hdense : Dense (tensorStarAlgebra A a b : Set C(rectangle A a b, ℂ)) := by
    rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe, htop]
    rfl
  have hspan := tensorAlgebra_eq_span A a b hA ha hab
  change Dense ((tensorAlgebra A a b).toSubmodule : Set C(rectangle A a b, ℂ)) at hdense
  rwa [hspan] at hdense

theorem exists_smooth_tensor_span_uniform_approx (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b) (F : C(rectangle A a b, ℂ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ G ∈ Submodule.span ℂ (tensorRestrictions A a b),
      ∀ p : rectangle A a b, ‖G p - F p‖ < epsilon := by
  have hd := smooth_tensor_span_dense_on_rectangle A a b hA ha hab
  obtain ⟨G, hG, hdist⟩ := Metric.mem_closure_iff.1 (hd F) epsilon hepsilon
  refine ⟨G, hG, ?_⟩
  intro p
  have hnorm : ‖G - F‖ < epsilon := by simpa only [dist_eq_norm] using hdist
  exact ((G - F).norm_coe_le_norm p).trans_lt hnorm

end
end ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
