import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Tactic

/-!
Continuous ramps for the CLOSED spectral interval (-infinity,a]. The ramp
is one at t=a for every n, so an atom at a is included rather than lost.
Every point outside the interval is eventually exactly zero. Dominated
convergence is proved for arbitrary finite measures, not assumed as a
limit or a projection field. SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3.ClosedIntervalSpectralRamps20261025a
noncomputable section
open MeasureTheory Filter
open scoped Topology

def ramp (a : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (1 - ((n : ℝ) + 1) * (t - a)))

theorem continuous_ramp (a : ℝ) (n : ℕ) : Continuous (ramp a n) := by
  unfold ramp
  fun_prop

theorem ramp_bounds (a : ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ ramp a n t ∧ ramp a n t ≤ 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

def closedCut (a t : ℝ) : ℝ := if t ≤ a then 1 else 0

theorem closedCut_bounds (a t : ℝ) : 0 ≤ closedCut a t ∧ closedCut a t ≤ 1 := by
  unfold closedCut
  split_ifs <;> norm_num

theorem ramp_eq_one_of_le {a t : ℝ} (ht : t ≤ a) (n : ℕ) : ramp a n t = 1 := by
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hm := mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.mpr ht)
  have hinner : 1 ≤ 1 - ((n : ℝ) + 1) * (t - a) := by linarith
  simp only [ramp, min_eq_left hinner, max_eq_right zero_le_one]

theorem ramp_eventually_eq_cut (a t : ℝ) :
    (fun n : ℕ => ramp a n t) =ᶠ[atTop] (fun _ => closedCut a t) := by
  by_cases ht : t ≤ a
  · exact Eventually.of_forall (fun n => by simp [closedCut, ht, ramp_eq_one_of_le ht n])
  · have hpos : 0 < t - a := sub_pos.mpr (lt_of_not_ge ht)
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (t - a))
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hquot : 1 / (t - a) ≤ (n : ℝ) + 1 := by linarith
    have hprod : 1 ≤ ((n : ℝ) + 1) * (t - a) := (div_le_iff₀ hpos).mp hquot
    have hinner : 1 - ((n : ℝ) + 1) * (t - a) ≤ 0 := by linarith
    have hmin : min 1 (1 - ((n : ℝ) + 1) * (t - a)) ≤ 0 :=
      (min_le_right _ _).trans hinner
    simp only [ramp, max_eq_left hmin, closedCut, if_neg ht]

theorem ramp_tendsto_cut (a t : ℝ) :
    Tendsto (fun n : ℕ => ramp a n t) atTop (𝓝 (closedCut a t)) :=
  tendsto_const_nhds.congr' (ramp_eventually_eq_cut a t).symm

theorem closedCut_mul (a b t : ℝ) :
    closedCut a t * closedCut b t = closedCut (min a b) t := by
  by_cases ha : t ≤ a <;> by_cases hb : t ≤ b <;>
    simp [closedCut, ha, hb, le_min_iff]

section ScalarMeasure
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable (coordinate : C(X, ℝ)) (μ : Measure X) [IsFiniteMeasure μ]

def rampMap (a : ℝ) (n : ℕ) : C(X, ℝ) :=
  ⟨fun x => ramp a n (coordinate x), (continuous_ramp a n).comp coordinate.continuous⟩

theorem measurable_closedCut (a : ℝ) : Measurable (fun x => closedCut a (coordinate x)) := by
  change Measurable ({x | coordinate x ≤ a}.indicator (fun _ : X => (1 : ℝ)))
  exact measurable_const.indicator (measurableSet_le coordinate.continuous.measurable measurable_const)

/-- A reusable genuine DCT lemma. All limits below are constructed from
bounded measurable scalar functions and pointwise eventual equality. -/
theorem integral_sq_tendsto_zero
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n x, |F n x| ≤ 1)
    (hzero : ∀ x, (fun n => F n x) =ᶠ[atTop] (fun _ => 0)) :
    Tendsto (fun n => ∫ x, (F n x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hd := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => (F n x) ^ 2) (f := fun _ : X => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => ((hF n).pow_const 2).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (fun x => by
      have hb := hbound n x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hm := mul_le_mul hb hb (abs_nonneg (F n x)) zero_le_one
      nlinarith [sq_abs (F n x)]))
    (Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [hzero x] with n hn
      simp only [hn, zero_pow (by decide : 2 ≠ 0)]))
  simpa only [integral_zero] using hd

theorem ramp_error_sq_integral_tendsto_zero (a : ℝ) :
    Tendsto (fun n => ∫ x, (ramp a n (coordinate x) - closedCut a (coordinate x)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply integral_sq_tendsto_zero μ
  · intro n
    exact (rampMap coordinate a n).continuous.measurable.sub (measurable_closedCut coordinate a)
  · intro n x
    have hr := ramp_bounds a n (coordinate x)
    have hc := closedCut_bounds a (coordinate x)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro x
    filter_upwards [ramp_eventually_eq_cut a (coordinate x)] with n hn
    simp only [hn, sub_self]

theorem ramp_product_defect_sq_integral_tendsto_zero (a b : ℝ) :
    Tendsto (fun n => ∫ x,
      (ramp a n (coordinate x) * ramp b n (coordinate x) -
        ramp (min a b) n (coordinate x)) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply integral_sq_tendsto_zero μ
  · intro n
    exact ((rampMap coordinate a n).continuous.measurable.mul
      (rampMap coordinate b n).continuous.measurable).sub
      (rampMap coordinate (min a b) n).continuous.measurable
  · intro n x
    have ha := ramp_bounds a n (coordinate x)
    have hb := ramp_bounds b n (coordinate x)
    have hm := ramp_bounds (min a b) n (coordinate x)
    have hp0 := mul_nonneg ha.1 hb.1
    have hp1 : ramp a n (coordinate x) * ramp b n (coordinate x) ≤ 1 := by
      simpa only [one_mul] using mul_le_mul ha.2 hb.2 hb.1 zero_le_one
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro x
    filter_upwards [ramp_eventually_eq_cut a (coordinate x),
      ramp_eventually_eq_cut b (coordinate x),
      ramp_eventually_eq_cut (min a b) (coordinate x)] with n ha hb hm
    rw [ha, hb, hm, closedCut_mul, sub_self]

end ScalarMeasure
end
end ImbalancedChen.Part3.ClosedIntervalSpectralRamps20261025a
