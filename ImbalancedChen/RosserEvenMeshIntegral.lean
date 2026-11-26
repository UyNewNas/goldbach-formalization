import ImbalancedChen.RosserEvenMesh
import ImbalancedChen.RosserEvenLayerIntegral
import ImbalancedChen.LogPrimeBoxIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual inner-mesh integrals in every fixed even dimension

The logarithmic lower sums converge to the Lebesgue integral on the strict
Rosser region. For each fixed rank and residual level greater than one, all coordinates
lie in a fixed compact box bounded away from zero. The proof uses pointwise mesh coverage and an
explicit integrable dominator, with no assumed integral-limit supplier.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

def rosserEvenMeshLowerIntegrand (k : ℕ) (s : ℝ) (n : ℕ)
    (x : Fin (2 * k + 2) → ℝ) : ℝ :=
  ∑ j ∈ rosserEvenMeshCells k s n, (1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1))) *
    (rosserEvenMeshCell k s n j).indicator (rosserEvenLogDensity k) x

def rosserEvenMeshLowerSum (k : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ rosserEvenMeshCells k s n, (1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1))) *
    ∏ i, Real.log (rosserEvenMeshHi k s n j i / rosserEvenMeshLo k s n j i)

def rosserEvenMeshAmbient (k : ℕ) (s : ℝ) : Set (Fin (2 * k + 2) → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc ((s - 1) / 3 ^ (k + 1)) 1)

@[simp] theorem mem_rosserEvenMeshAmbient {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 2) → ℝ} :
    x ∈ rosserEvenMeshAmbient k s ↔ ∀ i, (s - 1) / 3 ^ (k + 1) ≤ x i ∧ x i ≤ 1 := by
  simp only [rosserEvenMeshAmbient, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]

theorem measurableSet_rosserEvenMeshAmbient (k : ℕ) (s : ℝ) :
    MeasurableSet (rosserEvenMeshAmbient k s) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem isCompact_rosserEvenMeshAmbient (k : ℕ) (s : ℝ) :
    IsCompact (rosserEvenMeshAmbient k s) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem rosserEvenLogRegion_subset_ambient {k : ℕ} {s : ℝ} (hs : 1 < s) :
    rosserEvenLogRegion k s ⊆ rosserEvenMeshAmbient k s := by
  intro x hx
  exact mem_rosserEvenMeshAmbient.mpr (fun i =>
    ⟨(rosserEvenLogRegion_bounds hs hx i).1.le, (rosserEvenLogRegion_bounds hs hx i).2.le⟩)

theorem rosserEvenMeshCell_subset_ambient {k : ℕ} {s : ℝ}
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) :
    rosserEvenMeshCell k s n j ⊆ rosserEvenMeshAmbient k s := by
  intro x hx
  exact mem_rosserEvenMeshAmbient.mpr (fun i =>
    ⟨(rosserEvenMeshLoHi_bounds hcut n j i).1.trans (mem_rosserEvenMeshCell.mp hx i).1,
      (mem_rosserEvenMeshCell.mp hx i).2.le.trans (rosserEvenMeshLoHi_bounds hcut n j i).2.2⟩)

theorem integrableOn_rosserEvenLogDensity_cell {k : ℕ} {s : ℝ} (hs : 1 < s)
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ) (j : Fin (2 * k + 2) → Fin (n + 1)) :
    IntegrableOn (rosserEvenLogDensity k) (rosserEvenMeshCell k s n j) := by
  exact integrableOn_logPrimeBox_one_div _ _ (fun i =>
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (s - 1) / 3 ^ (k + 1))
      (rosserEvenMeshLoHi_bounds hcut n j i).1)

theorem integrable_rosserEvenMeshLowerIntegrand {k : ℕ} {s : ℝ} (hs : 1 < s)
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ) :
    Integrable (rosserEvenMeshLowerIntegrand k s n) := by
  exact integrable_finsetSum _ (fun j _ =>
    ((integrableOn_rosserEvenLogDensity_cell hs hcut n j).integrable_indicator
      (measurableSet_rosserEvenMeshCell k s n j)).const_mul _)

theorem rosserEvenMeshLowerSum_eq_integral {k : ℕ} {s : ℝ} (hs : 1 < s)
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ) :
    rosserEvenMeshLowerSum k s n = ∫ x, rosserEvenMeshLowerIntegrand k s n x := by
  unfold rosserEvenMeshLowerSum rosserEvenMeshLowerIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_indicator (measurableSet_rosserEvenMeshCell k s n j)]
    congr 1
    exact (integral_logPrimeBox_one_div _ _
      (fun i => lt_of_lt_of_le (by positivity : (0 : ℝ) < (s - 1) / 3 ^ (k + 1))
        (rosserEvenMeshLoHi_bounds hcut n j i).1)
      (fun i => (rosserEvenMeshLoHi_bounds hcut n j i).2.1.le)).symm
  · intro j _
    exact ((integrableOn_rosserEvenLogDensity_cell hs hcut n j).integrable_indicator
      (measurableSet_rosserEvenMeshCell k s n j)).const_mul _

theorem rosserEvenMeshLowerIntegrand_eq_of_mem {k n : ℕ} {s : ℝ}
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) {j : Fin (2 * k + 2) → Fin (n + 1)}
    (hj : j ∈ rosserEvenMeshCells k s n) {x : Fin (2 * k + 2) → ℝ}
    (hx : x ∈ rosserEvenMeshCell k s n j) :
    rosserEvenMeshLowerIntegrand k s n x =
      (1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1))) * rosserEvenLogDensity k x := by
  unfold rosserEvenMeshLowerIntegrand
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hx]
  · intro r _ hrj
    rw [indicator_of_notMem (fun hr => hrj (rosserEvenMeshCell_unique hcut.le hr hx)), mul_zero]
  · exact fun h => (h hj).elim

theorem rosserEvenMeshLowerIntegrand_eq_zero {k n : ℕ} {s : ℝ}
    {x : Fin (2 * k + 2) → ℝ}
    (hx : ¬∃ j ∈ rosserEvenMeshCells k s n, x ∈ rosserEvenMeshCell k s n j) :
    rosserEvenMeshLowerIntegrand k s n x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [indicator_of_notMem (fun h => hx ⟨j, hj, h⟩), mul_zero]

theorem rosserEvenMeshLowerIntegrand_eq_zero_of_not_mem_region {k n : ℕ} {s : ℝ}
    (hs : 1 < s) (hcut : (s - 1) / 3 ^ (k + 1) < 1) {x : Fin (2 * k + 2) → ℝ}
    (hx : x ∉ rosserEvenLogRegion k s) : rosserEvenMeshLowerIntegrand k s n x = 0 := by
  apply rosserEvenMeshLowerIntegrand_eq_zero
  rintro ⟨j, hj, hxj⟩
  exact hx (rosserEvenMeshCell_subset_region hs hcut hj hxj)

/-- Pointwise convergence is everywhere on the ambient space; the strict
region has no exceptional hyperplanes in this approximation argument. -/
theorem tendsto_rosserEvenMeshLowerIntegrand {k : ℕ} {s : ℝ} (hs : 1 < s)
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) (x : Fin (2 * k + 2) → ℝ) :
    Tendsto (fun n => rosserEvenMeshLowerIntegrand k s n x) atTop
      (𝓝 ((rosserEvenLogRegion k s).indicator (rosserEvenKernel k) x)) := by
  by_cases hx : x ∈ rosserEvenLogRegion k s
  · have hb := rosserEvenLogRegion_bounds hs hx
    choose j hj using fun n => exists_logPrimeMeshCell ((s - 1) / 3 ^ (k + 1)) 1 n
      (mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩))
    have hselected : ∀ᶠ n : ℕ in atTop, j n ∈ rosserEvenMeshCells k s n := by
      filter_upwards [rosserEvenLogRegion_eventually_mem_mesh hs hx] with n hn
      obtain ⟨r, hr, hxr⟩ := hn
      exact (logPrimeMeshCell_unique hcut.le hxr (hj n)) ▸ hr
    have hxlast : x (Fin.last (2 * k + 1)) ≠ 0 := ne_of_gt
      (lt_trans (by positivity : (0 : ℝ) < (s - 1) / 3 ^ (k + 1)) (hb _).1)
    have hconst : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hlim := (hconst.div
      (tendsto_logPrimeMeshHi_apply ((s - 1) / 3 ^ (k + 1)) 1 j hj (Fin.last (2 * k + 1)))
      hxlast).mul_const (rosserEvenLogDensity k x)
    rw [indicator_of_mem hx]
    change Tendsto _ _ (𝓝 (rosserEvenLogDensity k x * (1 / x (Fin.last (2 * k + 1)))))
    rw [mul_comm]
    apply hlim.congr'
    filter_upwards [hselected] with n hn
    exact (rosserEvenMeshLowerIntegrand_eq_of_mem hcut hn (hj n)).symm
  · rw [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr (fun _ =>
      (rosserEvenMeshLowerIntegrand_eq_zero_of_not_mem_region hs hcut hx).symm)

theorem rosserEvenLogDensity_bounds {k : ℕ} {s : ℝ} (hs : 1 < s)
    {x : Fin (2 * k + 2) → ℝ} (hx : x ∈ rosserEvenMeshAmbient k s) :
    0 ≤ rosserEvenLogDensity k x ∧
      rosserEvenLogDensity k x ≤ (1 / ((s - 1) / 3 ^ (k + 1))) ^ (2 * k + 2) := by
  have hi := mem_rosserEvenMeshAmbient.mp hx
  have hpos (i : Fin (2 * k + 2)) : 0 < x i :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (s - 1) / 3 ^ (k + 1)) (hi i).1
  have hle (i : Fin (2 * k + 2)) : 1 / x i ≤ 1 / ((s - 1) / 3 ^ (k + 1)) :=
    one_div_le_one_div_of_le (by positivity) (hi i).1
  refine ⟨Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hpos i)).le), ?_⟩
  calc
    rosserEvenLogDensity k x ≤ ∏ _i : Fin (2 * k + 2), (1 / ((s - 1) / 3 ^ (k + 1))) :=
      Finset.prod_le_prod (fun i _ => (one_div_pos.mpr (hpos i)).le) (fun i _ => hle i)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem rosserEvenMeshLowerIntegrand_dominated {k : ℕ} {s : ℝ} (hs : 1 < s)
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ) (x : Fin (2 * k + 2) → ℝ) :
    ‖rosserEvenMeshLowerIntegrand k s n x‖ ≤
      (rosserEvenMeshAmbient k s).indicator
        (fun _ => (1 / ((s - 1) / 3 ^ (k + 1))) * (1 / ((s - 1) / 3 ^ (k + 1))) ^ (2 * k + 2)) x := by
  by_cases hx : ∃ j ∈ rosserEvenMeshCells k s n, x ∈ rosserEvenMeshCell k s n j
  · obtain ⟨j, hj, hxj⟩ := hx
    have hb := rosserEvenMeshCell_subset_ambient hcut n j hxj
    have hd := rosserEvenLogDensity_bounds hs hb
    have hhi : (s - 1) / 3 ^ (k + 1) ≤ rosserEvenMeshHi k s n j (Fin.last (2 * k + 1)) :=
      (rosserEvenMeshLoHi_bounds hcut n j _).1.trans (rosserEvenMeshLoHi_bounds hcut n j _).2.1.le
    have hpos : 0 < rosserEvenMeshHi k s n j (Fin.last (2 * k + 1)) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < (s - 1) / 3 ^ (k + 1)) hhi
    have hcoeff : 1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1)) ≤
        1 / ((s - 1) / 3 ^ (k + 1)) := one_div_le_one_div_of_le (by positivity) hhi
    rw [rosserEvenMeshLowerIntegrand_eq_of_mem hcut hj hxj, indicator_of_mem hb,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (one_div_pos.mpr hpos).le hd.1)]
    exact mul_le_mul hcoeff hd.2 hd.1 (by positivity)
  · rw [rosserEvenMeshLowerIntegrand_eq_zero hx, norm_zero]
    exact indicator_nonneg (fun _ _ => by positivity) x

theorem continuousOn_rosserEvenKernel_ambient {k : ℕ} {s : ℝ} (hs : 1 < s) :
    ContinuousOn (rosserEvenKernel k) (rosserEvenMeshAmbient k s) := by
  have hrec (i : Fin (2 * k + 2)) : ContinuousOn
      (fun x : Fin (2 * k + 2) → ℝ => 1 / x i) (rosserEvenMeshAmbient k s) :=
    continuousOn_const.div (continuous_apply i).continuousOn (fun x hx =>
      (lt_of_lt_of_le (by positivity : (0 : ℝ) < (s - 1) / 3 ^ (k + 1))
        (mem_rosserEvenMeshAmbient.mp hx i).1).ne')
  exact (continuousOn_finsetProd Finset.univ (fun i _ => hrec i)).mul (hrec _)

/-- Every fixed even rank has a proved mesh limit equal to its actual
Lebesgue region integral. The cutoff hypothesis only says the ambient
interval is nonempty; all analytic convergence is proved here. -/
theorem tendsto_rosserEvenMeshLowerSum {k : ℕ} {s : ℝ} (hs : 1 < s)
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) :
    Tendsto (rosserEvenMeshLowerSum k s) atTop (𝓝 (rosserEvenLayerIntegral k s)) := by
  change Tendsto (fun n => rosserEvenMeshLowerSum k s n) atTop _
  simp only [rosserEvenMeshLowerSum_eq_integral hs hcut]
  have hbound : Integrable ((rosserEvenMeshAmbient k s).indicator
      (fun _ => (1 / ((s - 1) / 3 ^ (k + 1))) * (1 / ((s - 1) / 3 ^ (k + 1))) ^ (2 * k + 2))) :=
    (continuousOn_const.integrableOn_compact (isCompact_rosserEvenMeshAmbient k s)).integrable_indicator
      (measurableSet_rosserEvenMeshAmbient k s)
  have hlim := tendsto_integral_of_dominated_convergence _
    (fun n => (integrable_rosserEvenMeshLowerIntegrand hs hcut n).aestronglyMeasurable)
    hbound (fun n => Eventually.of_forall (rosserEvenMeshLowerIntegrand_dominated hs hcut n))
    (Eventually.of_forall (tendsto_rosserEvenMeshLowerIntegrand hs hcut))
  rw [integral_indicator (measurableSet_rosserEvenLogRegion k s)] at hlim
  exact hlim

end

end ImbalancedChen
