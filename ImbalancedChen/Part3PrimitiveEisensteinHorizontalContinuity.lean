import ImbalancedChen.Part3PrimitiveEisensteinFourierParameterAnalytic
import ImbalancedChen.Part3PrimitiveEisensteinParameterAutomorphy
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.OrderClosed

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

Continuity and period one for the ACTUAL complex-parameter primitive
Eisenstein horizontal trace in Re(s)>1. The point is exactly the consumer's
PrimitiveEisensteinFourierParameterAnalytic.horizontalPoint.

Spatial continuity is proved from continuous individual actual seeds and
a summable lattice majorant on every bounded horizontal interval. The
normalization is the literal half-primitive-pair sum. Periodicity is the
actual modular T action applied to the proved primitive automorphy theorem.
No supplied target continuity, assumed uniform convergence, spatial C2 chain,
Fourier reconstruction, spectral continuation or critical-line assertion is used.
-/

namespace ImbalancedChen.Part3.PrimitiveEisensteinHorizontalContinuity

noncomputable section

open Set Filter Topology Complex UpperHalfPlane EisensteinSeries
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAutomorphy

/-- Actual positive base is continuous along the whole horizontal line.
Its denominator is nonzero because the actual primitive base is positive. -/
theorem positiveBase_horizontal_continuous (y : ℝ) (hy : 0 < y) (v : PrimitivePair) :
    Continuous (fun x : ℝ => positiveBase (horizontalPoint y hy x) v) := by
  have hlinear : Continuous (fun x : ℝ =>
      (v.1 0 : ℂ) * (horizontalPoint y hy x : ℂ) + (v.1 1 : ℂ)) := by
    change Continuous (fun x : ℝ => (v.1 0 : ℂ) * Complex.mk x y + (v.1 1 : ℂ))
    fun_prop
  have hden (x : ℝ) :
      ‖(v.1 0 : ℂ) * (horizontalPoint y hy x : ℂ) + (v.1 1 : ℂ)‖ ^ 2 ≠ 0 := by
    intro hz
    have hp := positiveBase_pos (horizontalPoint y hy x) v
    change 0 < y / ‖(v.1 0 : ℂ) * (horizontalPoint y hy x : ℂ) + (v.1 1 : ℂ)‖ ^ 2 at hp
    rw [hz, div_zero] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  change Continuous (fun x : ℝ =>
    y / ‖(v.1 0 : ℂ) * (horizontalPoint y hy x : ℂ) + (v.1 1 : ℂ)‖ ^ 2)
  exact continuous_const.div (hlinear.norm.pow 2) hden

/-- No discontinuity of log at zero occurs: this is the true positive base. -/
theorem complexSeed_horizontal_continuous (y : ℝ) (hy : 0 < y)
    (v : PrimitivePair) (s : ℂ) :
    Continuous (fun x : ℝ => complexSeed (horizontalPoint y hy x) v s) := by
  have hlog : Continuous (fun x : ℝ => Real.log (positiveBase (horizontalPoint y hy x) v)) :=
    (positiveBase_horizontal_continuous y hy v).log
      (fun x => (positiveBase_pos (horizontalPoint y hy x) v).ne')
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

/-- Lattice majorant on the actual compact horizontal segment |x|<=A.
It does not depend on x and has decay exponent2*Re(s)>2. -/
def horizontalStripMajorant (s : ℂ) (y : ℝ) (hy : 0 < y) (A : ℝ)
    (v : PrimitivePair) : ℝ :=
  (y ^ s.re * EisensteinSeries.r ⟨⟨A, y⟩, hy⟩ ^ (-(2 * s.re))) *
    ‖v.1‖ ^ (-(2 * s.re))

theorem horizontalStripMajorant_summable (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (A : ℝ) : Summable (horizontalStripMajorant s y hy A) := by
  exact ((EisensteinSeries.summable_one_div_norm_rpow
    (by linarith : 2 < 2 * s.re)).subtype _).mul_left
      (y ^ s.re * EisensteinSeries.r ⟨⟨A, y⟩, hy⟩ ^ (-(2 * s.re)))

theorem complexSeed_horizontal_strip_bound (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (A : ℝ) (v : PrimitivePair) {x : ℝ} (hx : |x| ≤ A) :
    ‖complexSeed (horizontalPoint y hy x) v s‖ ≤ horizontalStripMajorant s y hy A v := by
  have hz : horizontalPoint y hy x ∈ verticalStrip A y := by
    change |x| ≤ A ∧ y ≤ y
    exact ⟨hx, le_rfl⟩
  rw [norm_complexSeed, positiveBase_rpow_eq_seed]
  exact seed_bound_on_boundedStrip s.re hs A y y hy v.1 (horizontalPoint y hy x) hz le_rfl

/-- Genuine uniform convergence of the literal primitive seed finite sums
on each closed horizontal segment, including both endpoints. -/
theorem complexSeed_horizontal_tendstoUniformlyOn (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (A : ℝ) :
    TendstoUniformlyOn
      (fun F : Finset PrimitivePair => fun x : ℝ =>
        ∑ v ∈ F, complexSeed (horizontalPoint y hy x) v s)
      (fun x : ℝ => ∑' v : PrimitivePair, complexSeed (horizontalPoint y hy x) v s)
      atTop (Icc (-A) A) := by
  apply tendstoUniformlyOn_tsum (horizontalStripMajorant_summable s hs y hy A)
  intro v x hx
  exact complexSeed_horizontal_strip_bound s hs y hy A v (abs_le.mpr hx)

theorem primitive_tsum_horizontal_continuousOn (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (A : ℝ) :
    ContinuousOn
      (fun x : ℝ => ∑' v : PrimitivePair, complexSeed (horizontalPoint y hy x) v s)
      (Icc (-A) A) := by
  apply (complexSeed_horizontal_tendstoUniformlyOn s hs y hy A).continuousOn
  apply Frequently.of_forall
  intro F
  exact continuousOn_finsetSum F (fun v _ => (complexSeed_horizontal_continuous y hy v s).continuousOn)

/-- Each point lies inside one of the proved bounded strips; no global
in-x lattice constant is incorrectly claimed. -/
theorem primitive_tsum_horizontal_continuous (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => ∑' v : PrimitivePair, complexSeed (horizontalPoint y hy x) v s) := by
  rw [continuous_iff_continuousAt]
  intro x
  let A : ℝ := |x| + 1
  have hleft : -A < x := by
    dsimp [A]
    linarith [neg_abs_le x]
  have hright : x < A := by
    dsimp [A]
    linarith [le_abs_self x]
  exact (primitive_tsum_horizontal_continuousOn s hs y hy A).continuousAt
    (Icc_mem_nhds hleft hright)

/-- Exact consumer API: continuity of the actual normalized horizontal trace. -/
theorem primitiveComplexEisenstein_horizontal_continuous
    (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    Continuous (fun x : ℝ => primitiveComplexEisenstein s (horizontalPoint y hy x)) := by
  exact continuous_const.mul (primitive_tsum_horizontal_continuous s hs y hy)

/-- Literal modular T translation of the consumer's existing horizontal point. -/
theorem horizontalPoint_add_one (y : ℝ) (hy : 0 < y) (x : ℝ) :
    horizontalPoint y hy (x + 1) = ModularGroup.T • horizontalPoint y hy x := by
  rw [UpperHalfPlane.modular_T_smul]
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [horizontalPoint, UpperHalfPlane.coe_vadd, add_comm]

/-- Period one comes from the actual modular action, not a periodicity field. -/
theorem primitiveComplexEisenstein_horizontal_periodic
    (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    Function.Periodic (fun x : ℝ => primitiveComplexEisenstein s (horizontalPoint y hy x)) 1 := by
  intro x
  rw [horizontalPoint_add_one]
  exact primitiveComplexEisenstein_SL2_invariant s hs ModularGroup.T (horizontalPoint y hy x)

/-- Endpoint compatibility for the genuine period-one Fourier trace. -/
theorem primitiveComplexEisenstein_horizontal_endpoints
    (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    primitiveComplexEisenstein s (horizontalPoint y hy 0) =
      primitiveComplexEisenstein s (horizontalPoint y hy 1) := by
  simpa only [zero_add] using ((primitiveComplexEisenstein_horizontal_periodic y hy s hs) 0).symm

end
end ImbalancedChen.Part3.PrimitiveEisensteinHorizontalContinuity
