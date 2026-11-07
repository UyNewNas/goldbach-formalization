import ImbalancedChen.RosserTripleMesh
import ImbalancedChen.LogPrimeBoxIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual inner-mesh sums converge to the first Rosser layer integral

The finite sums are the logarithmic masses of the selected, disjoint,
half-open inner boxes, multiplied by the reciprocal upper endpoint of
their least coordinate. Their integrands converge at every point: selected
cells eventually cover each point of the open region and their endpoints
converge to that point; all selected cells stay inside the region.

The integrands are dominated by 81 times the indicator of the fixed compact
box `[1/3,1]^3`. Dominated convergence therefore identifies the limit with
an actual Lebesgue integral, not a definition by mesh limits. This module
does not identify that integral with an external Suzuki layer supplier.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

def rosserTripleLogDensity (x : Fin 3 → ℝ) : ℝ := ∏ i, 1 / x i

def rosserTripleKernel (x : Fin 3 → ℝ) : ℝ :=
  rosserTripleLogDensity x * (1 / x 2)

/-- The limiting quantity is defined by a genuine Lebesgue set integral. -/
def rosserTripleLayerIntegral : ℝ :=
  ∫ x : Fin 3 → ℝ in rosserTripleRegion, (∏ i, 1 / x i) * (1 / x 2)

def rosserTripleMeshLowerIntegrand (n : ℕ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ j ∈ rosserTripleMeshCells n, (1 / rosserTripleMeshHi n j 2) *
    (rosserTripleMeshCell n j).indicator rosserTripleLogDensity x

def rosserTripleMeshLowerSum (n : ℕ) : ℝ :=
  ∑ j ∈ rosserTripleMeshCells n, (1 / rosserTripleMeshHi n j 2) *
    ∏ i, Real.log (rosserTripleMeshHi n j i / rosserTripleMeshLo n j i)

def rosserTripleMeshAmbient : Set (Fin 3 → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (1 / 3 : ℝ) 1)

@[simp] theorem mem_rosserTripleMeshAmbient {x : Fin 3 → ℝ} :
    x ∈ rosserTripleMeshAmbient ↔ ∀ i, (1 / 3 : ℝ) ≤ x i ∧ x i ≤ 1 := by
  simp only [rosserTripleMeshAmbient, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]

theorem measurableSet_rosserTripleMeshAmbient : MeasurableSet rosserTripleMeshAmbient :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem isCompact_rosserTripleMeshAmbient : IsCompact rosserTripleMeshAmbient :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem measurableSet_rosserTripleRegion : MeasurableSet rosserTripleRegion := by
  unfold rosserTripleRegion
  exact (measurableSet_lt measurable_const (measurable_pi_apply 2)).inter
    ((measurableSet_lt (measurable_pi_apply 2) (measurable_pi_apply 1)).inter
      ((measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 0)).inter
        ((measurableSet_lt (measurable_pi_apply 0) measurable_const).inter
          (measurableSet_lt measurable_const
            (((measurable_pi_apply 0).add (measurable_pi_apply 1)).add
              (measurable_const.mul (measurable_pi_apply 2)))))))

theorem rosserTripleRegion_subset_ambient : rosserTripleRegion ⊆ rosserTripleMeshAmbient := by
  intro x hx
  exact mem_rosserTripleMeshAmbient.mpr (fun i =>
    ⟨(rosserTripleRegion_bounds hx i).1.le, (rosserTripleRegion_bounds hx i).2.le⟩)

theorem rosserTripleMeshCell_subset_ambient (n : ℕ) (j : Fin 3 → Fin (n + 1)) :
    rosserTripleMeshCell n j ⊆ rosserTripleMeshAmbient := by
  intro x hx
  exact mem_rosserTripleMeshAmbient.mpr (fun i =>
    ⟨(rosserTripleMeshLoHi_bounds n j i).1.trans (mem_rosserTripleMeshCell.mp hx i).1,
      (mem_rosserTripleMeshCell.mp hx i).2.le.trans (rosserTripleMeshLoHi_bounds n j i).2.2⟩)

theorem measurableSet_rosserTripleMeshCell (n : ℕ) (j : Fin 3 → Fin (n + 1)) :
    MeasurableSet (rosserTripleMeshCell n j) :=
  measurableSet_logPrimeBox _ _

theorem integrableOn_rosserTripleLogDensity_cell (n : ℕ)
    (j : Fin 3 → Fin (n + 1)) :
    IntegrableOn rosserTripleLogDensity (rosserTripleMeshCell n j) := by
  exact integrableOn_logPrimeBox_one_div _ _ (fun i =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (rosserTripleMeshLoHi_bounds n j i).1)

theorem integrable_rosserTripleMeshLowerIntegrand (n : ℕ) :
    Integrable (rosserTripleMeshLowerIntegrand n) := by
  exact integrable_finsetSum _ (fun j _ =>
    ((integrableOn_rosserTripleLogDensity_cell n j).integrable_indicator
      (measurableSet_rosserTripleMeshCell n j)).const_mul _)

/-- Each finite sum is exactly the integral of the corresponding finite
sum of indicator-weighted densities. -/
theorem rosserTripleMeshLowerSum_eq_integral (n : ℕ) :
    rosserTripleMeshLowerSum n = ∫ x, rosserTripleMeshLowerIntegrand n x := by
  unfold rosserTripleMeshLowerSum rosserTripleMeshLowerIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_indicator (measurableSet_rosserTripleMeshCell n j)]
    congr 1
    exact (integral_logPrimeBox_one_div _ _
      (fun i => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
        (rosserTripleMeshLoHi_bounds n j i).1)
      (fun i => (rosserTripleMeshLoHi_bounds n j i).2.1.le)).symm
  · intro j _
    exact ((integrableOn_rosserTripleLogDensity_cell n j).integrable_indicator
      (measurableSet_rosserTripleMeshCell n j)).const_mul _

theorem rosserTripleMeshLowerIntegrand_eq_of_mem {n : ℕ}
    {j : Fin 3 → Fin (n + 1)} (hj : j ∈ rosserTripleMeshCells n)
    {x : Fin 3 → ℝ} (hx : x ∈ rosserTripleMeshCell n j) :
    rosserTripleMeshLowerIntegrand n x =
      (1 / rosserTripleMeshHi n j 2) * rosserTripleLogDensity x := by
  unfold rosserTripleMeshLowerIntegrand
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hx]
  · intro k _ hkj
    rw [indicator_of_notMem (fun hk => hkj (rosserTripleMeshCell_unique hk hx)), mul_zero]
  · exact fun h => (h hj).elim

theorem rosserTripleMeshLowerIntegrand_eq_zero {n : ℕ} {x : Fin 3 → ℝ}
    (hx : ¬∃ j ∈ rosserTripleMeshCells n, x ∈ rosserTripleMeshCell n j) :
    rosserTripleMeshLowerIntegrand n x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [indicator_of_notMem (fun h => hx ⟨j, hj, h⟩), mul_zero]

theorem rosserTripleMeshLowerIntegrand_eq_zero_of_not_mem_region {n : ℕ}
    {x : Fin 3 → ℝ} (hx : x ∉ rosserTripleRegion) :
    rosserTripleMeshLowerIntegrand n x = 0 := by
  apply rosserTripleMeshLowerIntegrand_eq_zero
  rintro ⟨j, hj, hxj⟩
  exact hx (rosserTripleMeshCell_subset_region hj hxj)

theorem tendsto_rosserTripleMeshHi
    (j : ∀ n : ℕ, Fin 3 → Fin (n + 1)) {x : Fin 3 → ℝ}
    (hx : ∀ n, x ∈ rosserTripleMeshCell n (j n)) (i : Fin 3) :
    Tendsto (fun n => rosserTripleMeshHi n (j n) i) atTop (𝓝 (x i)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  filter_upwards [tendsto_rosserTripleMeshStep.eventually (gt_mem_nhds hepsilon)] with n hn
  have hxi := mem_rosserTripleMeshCell.mp (hx n) i
  have he : rosserTripleMeshHi n (j n) i =
      rosserTripleMeshLo n (j n) i + rosserTripleMeshStep n :=
    rosserTripleMeshPoint_succ n (j n i)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hxi.2], by linarith [hxi.1]⟩

/-- Pointwise convergence holds everywhere, without discarding any
hyperplane or boundary null set. -/
theorem tendsto_rosserTripleMeshLowerIntegrand (x : Fin 3 → ℝ) :
    Tendsto (fun n => rosserTripleMeshLowerIntegrand n x) atTop
      (𝓝 (rosserTripleRegion.indicator rosserTripleKernel x)) := by
  by_cases hx : x ∈ rosserTripleRegion
  · have hb := rosserTripleRegion_bounds hx
    choose j hj using fun n => exists_rosserTripleMeshCell n
      (fun i => ⟨(hb i).1.le, (hb i).2⟩)
    have hselected : ∀ᶠ n : ℕ in atTop, j n ∈ rosserTripleMeshCells n := by
      filter_upwards [rosserTripleRegion_eventually_mem_mesh hx] with n hn
      obtain ⟨r, hr, hxr⟩ := hn
      exact (rosserTripleMeshCell_unique hxr (hj n)) ▸ hr
    have hx2 : x 2 ≠ 0 := ne_of_gt (lt_trans (by norm_num) (hb 2).1)
    have hconst : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hlim := (hconst.div (tendsto_rosserTripleMeshHi j hj 2) hx2).mul_const
      (rosserTripleLogDensity x)
    rw [indicator_of_mem hx]
    change Tendsto _ _ (𝓝 (rosserTripleLogDensity x * (1 / x 2)))
    rw [mul_comm]
    apply hlim.congr'
    filter_upwards [hselected] with n hn
    exact (rosserTripleMeshLowerIntegrand_eq_of_mem hn (hj n)).symm
  · rw [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr (fun _ =>
      (rosserTripleMeshLowerIntegrand_eq_zero_of_not_mem_region hx).symm)

theorem rosserTripleLogDensity_bounds {x : Fin 3 → ℝ}
    (hx : x ∈ rosserTripleMeshAmbient) :
    0 ≤ rosserTripleLogDensity x ∧ rosserTripleLogDensity x ≤ 27 := by
  have hi := mem_rosserTripleMeshAmbient.mp hx
  have hpos (i : Fin 3) : 0 < x i := lt_of_lt_of_le (by norm_num) (hi i).1
  have hle (i : Fin 3) : 1 / x i ≤ (3 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 3) (hi i).1
  refine ⟨Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hpos i)).le), ?_⟩
  calc
    rosserTripleLogDensity x ≤ ∏ _i : Fin 3, (3 : ℝ) :=
      Finset.prod_le_prod (fun i _ => (one_div_pos.mpr (hpos i)).le) (fun i _ => hle i)
    _ = 27 := by norm_num

theorem rosserTripleMeshLowerIntegrand_dominated (n : ℕ) (x : Fin 3 → ℝ) :
    ‖rosserTripleMeshLowerIntegrand n x‖ ≤
      rosserTripleMeshAmbient.indicator (fun _ => (81 : ℝ)) x := by
  by_cases hx : ∃ j ∈ rosserTripleMeshCells n, x ∈ rosserTripleMeshCell n j
  · obtain ⟨j, hj, hxj⟩ := hx
    have hb := rosserTripleMeshCell_subset_ambient n j hxj
    have hd := rosserTripleLogDensity_bounds hb
    have hhi : (1 / 3 : ℝ) ≤ rosserTripleMeshHi n j 2 :=
      (rosserTripleMeshLoHi_bounds n j 2).1.trans (rosserTripleMeshLoHi_bounds n j 2).2.1.le
    have hpos : 0 < rosserTripleMeshHi n j 2 := lt_of_lt_of_le (by norm_num) hhi
    have hcoeff : 1 / rosserTripleMeshHi n j 2 ≤ (3 : ℝ) := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 3) hhi
    rw [rosserTripleMeshLowerIntegrand_eq_of_mem hj hxj, indicator_of_mem hb,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (one_div_pos.mpr hpos).le hd.1)]
    calc
      (1 / rosserTripleMeshHi n j 2) * rosserTripleLogDensity x ≤ 3 * 27 :=
        mul_le_mul hcoeff hd.2 hd.1 (by norm_num)
      _ = 81 := by norm_num
  · rw [rosserTripleMeshLowerIntegrand_eq_zero hx, norm_zero]
    exact indicator_nonneg (fun _ _ => by norm_num) x

theorem continuousOn_rosserTripleKernel_ambient :
    ContinuousOn rosserTripleKernel rosserTripleMeshAmbient := by
  have hrec (i : Fin 3) : ContinuousOn (fun x : Fin 3 → ℝ => 1 / x i)
      rosserTripleMeshAmbient :=
    continuousOn_const.div (continuous_apply i).continuousOn (fun x hx =>
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
        (mem_rosserTripleMeshAmbient.mp hx i).1).ne')
  exact (continuousOn_finsetProd Finset.univ (fun i _ => hrec i)).mul (hrec 2)

theorem integrableOn_rosserTripleKernel_region :
    IntegrableOn rosserTripleKernel rosserTripleRegion :=
  (continuousOn_rosserTripleKernel_ambient.integrableOn_compact
    isCompact_rosserTripleMeshAmbient).mono_set rosserTripleRegion_subset_ambient

/-- The actual finite logarithmic lower sums converge to the actual
first-layer region integral, with no unproved analytic supplier. -/
theorem tendsto_rosserTripleMeshLowerSum :
    Tendsto rosserTripleMeshLowerSum atTop (𝓝 rosserTripleLayerIntegral) := by
  change Tendsto (fun n => rosserTripleMeshLowerSum n) atTop _
  simp only [rosserTripleMeshLowerSum_eq_integral]
  have hbound : Integrable (rosserTripleMeshAmbient.indicator (fun _ => (81 : ℝ))) :=
    (continuousOn_const.integrableOn_compact isCompact_rosserTripleMeshAmbient).integrable_indicator
      measurableSet_rosserTripleMeshAmbient
  have hlim := tendsto_integral_of_dominated_convergence
    (rosserTripleMeshAmbient.indicator (fun _ => (81 : ℝ)))
    (fun n => (integrable_rosserTripleMeshLowerIntegrand n).aestronglyMeasurable)
    hbound (fun n => Eventually.of_forall (rosserTripleMeshLowerIntegrand_dominated n))
    (Eventually.of_forall tendsto_rosserTripleMeshLowerIntegrand)
  rw [integral_indicator measurableSet_rosserTripleRegion] at hlim
  exact hlim

end

end ImbalancedChen
