/-
SPDX-License-Identifier: Apache-2.0

HELD SOURCE CANDIDATE: source review only, with no Lean/Lake execution or
kernel verification. This module proves elementary geometry and continuity
for the manuscript's fixed variable-level pair kernel.

The reserved VariableEnvelope source was unavailable on the inspected head.
The definition below is therefore a separately namespaced literal definition
of the manuscript's two-affine minimum. It does not replace, import, or claim
the reserved envelope comparison theorem. No arithmetic supplier is imported.
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ImbalancedChen.ChenVariablePairKernel

noncomputable section

/-- The fixed lower prime cutoff in the manuscript. -/
def a : ℝ := 100 / 1149

/-- The fixed intermediate prime cutoff in the manuscript. -/
def h : ℝ := 50 / 309

/-- The full upper prime cutoff, equal to `1 / 2 - 3 * a`. -/
def d : ℝ := 183 / 766

/-- A local literal name for the manuscript's two-affine level. No theorem
identifying a more complicated external envelope with this minimum is used. -/
def vLevel (t : ℝ) : ℝ := min ((1 + t) / 2) (57 / 64 - 3 * t / 2)

/-- Symmetric extension of the manuscript's ordered pair argument. -/
def argument (u v : ℝ) : ℝ := (vLevel (max u v) - u - v) / a

def kernel (f : ℝ → ℝ) (u v : ℝ) : ℝ := f (argument u v)

/-- The integration density has its two actual positive coordinates. -/
def weightedKernel (f : ℝ → ℝ) (u v : ℝ) : ℝ := kernel f u v / (u * v)

def R5 : Set (ℝ × ℝ) := Set.Icc a h ×ˢ Set.Icc a h

def R6 : Set (ℝ × ℝ) := Set.Icc a h ×ˢ Set.Icc h d

theorem a_pos : 0 < a := by norm_num [a]

theorem a_lt_h : a < h := by norm_num [a, h]

theorem h_pos : 0 < h := a_pos.trans a_lt_h

theorem h_lt_d : h < d := by norm_num [h, d]

theorem d_le_one : d ≤ 1 := by norm_num [d]

theorem h_le_one : h ≤ 1 := h_lt_d.le.trans d_le_one

theorem d_eq_half_sub_three_a : d = 1 / 2 - 3 * a := by norm_num [a, d]

/-- Subtracting the larger coordinate makes both affine branches decreasing.
This proof uses the literal minimum and does not split off a prime region. -/
theorem vLevel_sub_antitone : Antitone (fun t : ℝ => vLevel t - t) := by
  intro x y hxy
  unfold vLevel
  rcases le_total ((1 + x) / 2) (57 / 64 - 3 * x / 2) with hx | hx
  · rw [min_eq_left hx]
    have hm := min_le_left ((1 + y) / 2) (57 / 64 - 3 * y / 2)
    linarith
  · rw [min_eq_right hx]
    have hm := min_le_right ((1 + y) / 2) (57 / 64 - 3 * y / 2)
    linarith

theorem argument_eq_max_min (u v : ℝ) :
    argument u v = (vLevel (max u v) - max u v - min u v) / a := by
  unfold argument
  rcases le_total u v with huv | hvu
  · rw [max_eq_right huv, min_eq_left huv]
    ring
  · rw [max_eq_left hvu, min_eq_right hvu]

/-- The scalar argument is antitone in the product order on the whole plane. -/
theorem argument_antitone {u₁ u₂ v₁ v₂ : ℝ} (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    argument u₂ v₂ ≤ argument u₁ v₁ := by
  have hmax : max u₁ v₁ ≤ max u₂ v₂ :=
    max_le (hu.trans (le_max_left _ _)) (hv.trans (le_max_right _ _))
  have hmin : min u₁ v₁ ≤ min u₂ v₂ :=
    le_min ((min_le_left _ _).trans hu) ((min_le_right _ _).trans hv)
  rw [argument_eq_max_min, argument_eq_max_min]
  exact div_le_div_of_nonneg_right
    (sub_le_sub (vLevel_sub_antitone hmax) hmin) a_pos.le

theorem argument_symm (u v : ℝ) : argument u v = argument v u := by
  unfold argument
  rw [max_comm u v]
  ring

theorem kernel_symm (f : ℝ → ℝ) (u v : ℝ) : kernel f u v = kernel f v u :=
  congrArg f (argument_symm u v)

theorem weightedKernel_symm (f : ℝ → ℝ) (u v : ℝ) :
    weightedKernel f u v = weightedKernel f v u := by
  unfold weightedKernel
  rw [kernel_symm f u v, mul_comm u v]

/-- On an ordered pair the larger-coordinate level is exactly the manuscript's. -/
theorem argument_of_le {u v : ℝ} (huv : u ≤ v) :
    argument u v = (vLevel v - v - u) / a := by
  unfold argument
  rw [max_eq_right huv]
  ring

theorem kernel_of_le (f : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v) :
    kernel f u v = f ((vLevel v - v - u) / a) :=
  congrArg f (argument_of_le huv)

theorem argument_h_h : argument h h = 60897 / 20600 := by
  norm_num [argument, vLevel, a, h, max_def, min_def]

theorem argument_a_a : argument a a = 849 / 200 := by
  norm_num [argument, vLevel, a, max_def, min_def]

theorem argument_h_d : argument h d = 996419 / 659200 := by
  norm_num [argument, vLevel, a, h, d, max_def, min_def]

theorem argument_a_h : argument a h = 78597 / 20600 := by
  norm_num [argument, vLevel, a, h, max_def, min_def]

/-- Sharp corner bounds on the actual fifth-term square. -/
theorem argument_mem_R5_range {u v : ℝ}
    (hu : u ∈ Set.Icc a h) (hv : v ∈ Set.Icc a h) :
    argument u v ∈ Set.Icc (60897 / 20600 : ℝ) (849 / 200 : ℝ) := by
  constructor
  · rw [← argument_h_h]
    exact argument_antitone hu.2 hv.2
  · rw [← argument_a_a]
    exact argument_antitone hu.1 hv.1

/-- Sharp corner bounds on the full sixth-term rectangle. In particular,
the lower endpoint is below 2; no positivity-of-lower-sieve truncation occurs. -/
theorem argument_mem_R6_range {u v : ℝ}
    (hu : u ∈ Set.Icc a h) (hv : v ∈ Set.Icc h d) :
    argument u v ∈ Set.Icc (996419 / 659200 : ℝ) (78597 / 20600 : ℝ) := by
  constructor
  · rw [← argument_h_d]
    exact argument_antitone hu.2 hv.2
  · rw [← argument_a_h]
    exact argument_antitone hu.1 hv.1

theorem R5_argument_range_subset :
    Set.Icc (60897 / 20600 : ℝ) (849 / 200 : ℝ) ⊆ Set.Icc 1 5 := by
  intro s hs
  constructor <;> linarith [hs.1, hs.2]

theorem R6_argument_range_subset :
    Set.Icc (996419 / 659200 : ℝ) (78597 / 20600 : ℝ) ⊆ Set.Icc 1 5 := by
  intro s hs
  constructor <;> linarith [hs.1, hs.2]

theorem argument_h_d_lt_two : argument h d < 2 := by
  rw [argument_h_d]
  norm_num

theorem continuous_vLevel : Continuous vLevel :=
  ((continuous_const.add continuous_id).div_const 2).min
    (continuous_const.sub ((continuous_const.mul continuous_id).div_const 2))

theorem continuous_argument : Continuous (Function.uncurry argument) :=
  (((continuous_vLevel.comp (continuous_fst.max continuous_snd)).sub
    continuous_fst).sub continuous_snd).div_const a

/-- Only continuity of f on the actual sharp scalar range is needed. -/
theorem continuousOn_kernel_R5_of_range {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (60897 / 20600 : ℝ) (849 / 200 : ℝ))) :
    ContinuousOn (Function.uncurry (kernel f)) R5 :=
  hf.comp continuous_argument.continuousOn
    (fun _ hp => argument_mem_R5_range hp.1 hp.2)

theorem continuousOn_kernel_R6_of_range {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (996419 / 659200 : ℝ) (78597 / 20600 : ℝ))) :
    ContinuousOn (Function.uncurry (kernel f)) R6 :=
  hf.comp continuous_argument.continuousOn
    (fun _ hp => argument_mem_R6_range hp.1 hp.2)

/-- The common scalar continuity interval [1,5] covers the actual square. -/
theorem continuousOn_kernel_R5 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 1 5)) :
    ContinuousOn (Function.uncurry (kernel f)) R5 :=
  continuousOn_kernel_R5_of_range (hf.mono R5_argument_range_subset)

/-- The same interval covers the full mixed rectangle, including arguments <2. -/
theorem continuousOn_kernel_R6 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 1 5)) :
    ContinuousOn (Function.uncurry (kernel f)) R6 :=
  continuousOn_kernel_R6_of_range (hf.mono R6_argument_range_subset)

theorem continuousOn_weightedKernel_R5 {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    ContinuousOn (Function.uncurry (weightedKernel f)) R5 :=
  (continuousOn_kernel_R5 hf).div (continuous_fst.mul continuous_snd).continuousOn
    (fun _ hp => mul_ne_zero (ne_of_gt (a_pos.trans_le hp.1.1))
      (ne_of_gt (a_pos.trans_le hp.2.1)))

theorem continuousOn_weightedKernel_R6 {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    ContinuousOn (Function.uncurry (weightedKernel f)) R6 :=
  (continuousOn_kernel_R6 hf).div (continuous_fst.mul continuous_snd).continuousOn
    (fun _ hp => mul_ne_zero (ne_of_gt (a_pos.trans_le hp.1.1))
      (ne_of_gt (h_pos.trans_le hp.2.1)))

end
end ImbalancedChen.ChenVariablePairKernel
