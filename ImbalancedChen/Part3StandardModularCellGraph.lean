import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Actual standard modular-cell lower graph and its vertical Jacobian

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The lower graph is literally sqrt(1-x^2), not an abstract boundary field.
Its positive smooth chart contains [-1/2,1/2]. The vertical interpolation
from this graph to height T has exact oriented Jacobian T-h(x), including
the degenerate T=h(x) fiber, by native affine interval substitution.
-/
namespace ImbalancedChen.Part3.StandardModularCellGraph20261026b
noncomputable section
open Set MeasureTheory
open scoped Topology Interval

def modularBottom (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)
def bottomSlope (x : ℝ) : ℝ := -x / modularBottom x

theorem radicand_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

theorem modularBottom_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < modularBottom x :=
  Real.sqrt_pos.mpr (radicand_pos hx)

theorem modularBottom_continuous : Continuous modularBottom := by unfold modularBottom; fun_prop

theorem modularBottom_contDiffOn : ContDiffOn ℝ ∞ modularBottom (Ioo (-1 : ℝ) 1) :=
  (contDiffOn_const.sub (contDiffOn_id.pow 2)).sqrt (fun _ hx => (radicand_pos hx).ne')

theorem modularBottom_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt modularBottom (bottomSlope x) x := by
  have hp : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1 <;> ring
  convert hp.sqrt (radicand_pos hx).ne' using 1 <;> simp only [modularBottom, bottomSlope]
  <;> field_simp [(modularBottom_pos hx).ne'] <;> ring

theorem bottomSlope_contDiffOn : ContDiffOn ℝ ∞ bottomSlope (Ioo (-1 : ℝ) 1) :=
  contDiffOn_id.neg.div modularBottom_contDiffOn (fun _ hx => (modularBottom_pos hx).ne')

theorem modularBottom_unit_circle {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    x ^ 2 + modularBottom x ^ 2 = 1 := by
  rw [modularBottom, Real.sq_sqrt (radicand_pos hx).le]
  ring

theorem modular_cell_interval_subset : Icc (-(1 / 2 : ℝ)) (1 / 2) ⊆ Ioo (-1 : ℝ) 1 := by
  intro x hx
  constructor <;> linarith [hx.1, hx.2]

theorem modularBottom_le_one (x : ℝ) : modularBottom x ≤ 1 := by
  unfold modularBottom
  exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])

def graphHeight (T x r : ℝ) : ℝ := modularBottom x + (T - modularBottom x) * r

def graphMap (T : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, graphHeight T p.1 p.2)

def graphDomain (T : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < graphHeight T p.1 p.2}

theorem graphHeight_continuous (T : ℝ) : Continuous (fun p : ℝ × ℝ => graphHeight T p.1 p.2) := by
  unfold graphHeight
  exact (modularBottom_continuous.comp continuous_fst).add
    ((continuous_const.sub (modularBottom_continuous.comp continuous_fst)).mul continuous_snd)

theorem graphDomain_isOpen (T : ℝ) : IsOpen (graphDomain T) :=
  (isOpen_Ioo.preimage continuous_fst).inter (isOpen_lt continuous_const (graphHeight_continuous T))

theorem graphMap_contDiffOn (T : ℝ) : ContDiffOn ℝ ∞ (graphMap T) (graphDomain T) := by
  have hh : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => modularBottom p.1) (graphDomain T) :=
    modularBottom_contDiffOn.comp contDiffOn_fst (fun _ hp => hp.1)
  exact contDiffOn_fst.prodMk (hh.add ((contDiffOn_const.sub hh).mul contDiffOn_snd))

theorem modular_rectangle_maps_positive {T : ℝ} (hT : 1 ≤ T)
    {p : ℝ × ℝ} (hp : p ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (0 : ℝ) 1) :
    p ∈ graphDomain T := by
  have hx := modular_cell_interval_subset hp.1
  refine ⟨hx, ?_⟩
  have hh := modularBottom_pos hx
  have hL : 0 ≤ T - modularBottom p.1 := sub_nonneg.mpr ((modularBottom_le_one _).trans hT)
  exact hh.trans_le (le_add_of_nonneg_right (mul_nonneg hL hp.2.1))

/-- Exact original vertical integral, with no missing Jacobian or
nondegenerate-coordinate assumption. -/
theorem graph_vertical_integral (T x : ℝ) (q : ℝ → ℂ) :
    ((T - modularBottom x : ℝ) : ℂ) * (∫ r in (0 : ℝ)..1, q (graphHeight T x r)) =
      ∫ y in modularBottom x..T, q y := by
  simpa [graphHeight, Complex.real_smul] using
    intervalIntegral.smul_integral_comp_add_mul q (a := (0 : ℝ)) (b := 1)
      (T - modularBottom x) (modularBottom x)

end
end ImbalancedChen.Part3.StandardModularCellGraph20261026b

