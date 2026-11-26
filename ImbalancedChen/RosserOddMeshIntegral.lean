import ImbalancedChen.RosserOddMesh
import ImbalancedChen.LogPrimeBoxIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual inner-mesh integrals in every fixed odd dimension

The logarithmic lower sums converge to the Lebesgue integral on the strict
Rosser region. For each fixed rank, all coordinates lie in a fixed compact
box bounded away from zero. The proof uses pointwise mesh coverage and an
explicit integrable dominator, with no assumed integral-limit supplier.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

def rosserOddLogDensity (k : ℕ) (x : Fin (2 * k + 1) → ℝ) : ℝ := ∏ i, 1 / x i

def rosserOddKernel (k : ℕ) (x : Fin (2 * k + 1) → ℝ) : ℝ :=
  rosserOddLogDensity k x * (1 / x (Fin.last (2 * k)))

def rosserOddLayerIntegral (k : ℕ) (s : ℝ) : ℝ :=
  ∫ x : Fin (2 * k + 1) → ℝ in rosserOddLogRegion k s, rosserOddKernel k x

def rosserOddMeshLowerIntegrand (k : ℕ) (s : ℝ) (n : ℕ)
    (x : Fin (2 * k + 1) → ℝ) : ℝ :=
  ∑ j ∈ rosserOddMeshCells k s n, (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) *
    (rosserOddMeshCell k s n j).indicator (rosserOddLogDensity k) x

def rosserOddMeshLowerSum (k : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ rosserOddMeshCells k s n, (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) *
    ∏ i, Real.log (rosserOddMeshHi k s n j i / rosserOddMeshLo k s n j i)

def rosserOddMeshAmbient (k : ℕ) (s : ℝ) : Set (Fin (2 * k + 1) → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (s / 3 ^ (k + 1)) 1)

@[simp] theorem mem_rosserOddMeshAmbient {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} :
    x ∈ rosserOddMeshAmbient k s ↔ ∀ i, s / 3 ^ (k + 1) ≤ x i ∧ x i ≤ 1 := by
  simp only [rosserOddMeshAmbient, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]

theorem measurableSet_rosserOddMeshAmbient (k : ℕ) (s : ℝ) :
    MeasurableSet (rosserOddMeshAmbient k s) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem isCompact_rosserOddMeshAmbient (k : ℕ) (s : ℝ) :
    IsCompact (rosserOddMeshAmbient k s) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem rosserOddLogRegion_subset_ambient {k : ℕ} {s : ℝ} (hs : 0 < s) :
    rosserOddLogRegion k s ⊆ rosserOddMeshAmbient k s := by
  intro x hx
  exact mem_rosserOddMeshAmbient.mpr (fun i =>
    ⟨(rosserOddLogRegion_bounds hs hx i).1.le, (rosserOddLogRegion_bounds hs hx i).2.le⟩)

theorem rosserOddMeshCell_subset_ambient {k : ℕ} {s : ℝ}
    (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) :
    rosserOddMeshCell k s n j ⊆ rosserOddMeshAmbient k s := by
  intro x hx
  exact mem_rosserOddMeshAmbient.mpr (fun i =>
    ⟨(rosserOddMeshLoHi_bounds hcut n j i).1.trans (mem_rosserOddMeshCell.mp hx i).1,
      (mem_rosserOddMeshCell.mp hx i).2.le.trans (rosserOddMeshLoHi_bounds hcut n j i).2.2⟩)

theorem integrableOn_rosserOddLogDensity_cell {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) :
    IntegrableOn (rosserOddLogDensity k) (rosserOddMeshCell k s n j) := by
  exact integrableOn_logPrimeBox_one_div _ _ (fun i =>
    lt_of_lt_of_le (by positivity : (0 : ℝ) < s / 3 ^ (k + 1))
      (rosserOddMeshLoHi_bounds hcut n j i).1)

theorem integrable_rosserOddMeshLowerIntegrand {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ) :
    Integrable (rosserOddMeshLowerIntegrand k s n) := by
  exact integrable_finsetSum _ (fun j _ =>
    ((integrableOn_rosserOddLogDensity_cell hs hcut n j).integrable_indicator
      (measurableSet_rosserOddMeshCell k s n j)).const_mul _)

theorem rosserOddMeshLowerSum_eq_integral {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ) :
    rosserOddMeshLowerSum k s n = ∫ x, rosserOddMeshLowerIntegrand k s n x := by
  unfold rosserOddMeshLowerSum rosserOddMeshLowerIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_indicator (measurableSet_rosserOddMeshCell k s n j)]
    congr 1
    exact (integral_logPrimeBox_one_div _ _
      (fun i => lt_of_lt_of_le (by positivity : (0 : ℝ) < s / 3 ^ (k + 1))
        (rosserOddMeshLoHi_bounds hcut n j i).1)
      (fun i => (rosserOddMeshLoHi_bounds hcut n j i).2.1.le)).symm
  · intro j _
    exact ((integrableOn_rosserOddLogDensity_cell hs hcut n j).integrable_indicator
      (measurableSet_rosserOddMeshCell k s n j)).const_mul _

theorem rosserOddMeshLowerIntegrand_eq_of_mem {k n : ℕ} {s : ℝ}
    (hcut : s / 3 ^ (k + 1) < 1) {j : Fin (2 * k + 1) → Fin (n + 1)}
    (hj : j ∈ rosserOddMeshCells k s n) {x : Fin (2 * k + 1) → ℝ}
    (hx : x ∈ rosserOddMeshCell k s n j) :
    rosserOddMeshLowerIntegrand k s n x =
      (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) * rosserOddLogDensity k x := by
  unfold rosserOddMeshLowerIntegrand
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hx]
  · intro r _ hrj
    rw [indicator_of_notMem (fun hr => hrj (rosserOddMeshCell_unique hcut.le hr hx)), mul_zero]
  · exact fun h => (h hj).elim

theorem rosserOddMeshLowerIntegrand_eq_zero {k n : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ}
    (hx : ¬∃ j ∈ rosserOddMeshCells k s n, x ∈ rosserOddMeshCell k s n j) :
    rosserOddMeshLowerIntegrand k s n x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [indicator_of_notMem (fun h => hx ⟨j, hj, h⟩), mul_zero]

theorem rosserOddMeshLowerIntegrand_eq_zero_of_not_mem_region {k n : ℕ} {s : ℝ}
    (hs : 0 < s) (hcut : s / 3 ^ (k + 1) < 1) {x : Fin (2 * k + 1) → ℝ}
    (hx : x ∉ rosserOddLogRegion k s) : rosserOddMeshLowerIntegrand k s n x = 0 := by
  apply rosserOddMeshLowerIntegrand_eq_zero
  rintro ⟨j, hj, hxj⟩
  exact hx (rosserOddMeshCell_subset_region hs hcut hj hxj)

/-- Pointwise convergence is everywhere on the ambient space; the strict
region has no exceptional hyperplanes in this approximation argument. -/
theorem tendsto_rosserOddMeshLowerIntegrand {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hcut : s / 3 ^ (k + 1) < 1) (x : Fin (2 * k + 1) → ℝ) :
    Tendsto (fun n => rosserOddMeshLowerIntegrand k s n x) atTop
      (𝓝 ((rosserOddLogRegion k s).indicator (rosserOddKernel k) x)) := by
  by_cases hx : x ∈ rosserOddLogRegion k s
  · have hb := rosserOddLogRegion_bounds hs hx
    choose j hj using fun n => exists_logPrimeMeshCell (s / 3 ^ (k + 1)) 1 n
      (mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩))
    have hselected : ∀ᶠ n : ℕ in atTop, j n ∈ rosserOddMeshCells k s n := by
      filter_upwards [rosserOddLogRegion_eventually_mem_mesh hs hx] with n hn
      obtain ⟨r, hr, hxr⟩ := hn
      exact (logPrimeMeshCell_unique hcut.le hxr (hj n)) ▸ hr
    have hxlast : x (Fin.last (2 * k)) ≠ 0 := ne_of_gt
      (lt_trans (by positivity : (0 : ℝ) < s / 3 ^ (k + 1)) (hb _).1)
    have hconst : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hlim := (hconst.div
      (tendsto_logPrimeMeshHi_apply (s / 3 ^ (k + 1)) 1 j hj (Fin.last (2 * k)))
      hxlast).mul_const (rosserOddLogDensity k x)
    rw [indicator_of_mem hx]
    change Tendsto _ _ (𝓝 (rosserOddLogDensity k x * (1 / x (Fin.last (2 * k)))))
    rw [mul_comm]
    apply hlim.congr'
    filter_upwards [hselected] with n hn
    exact (rosserOddMeshLowerIntegrand_eq_of_mem hcut hn (hj n)).symm
  · rw [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr (fun _ =>
      (rosserOddMeshLowerIntegrand_eq_zero_of_not_mem_region hs hcut hx).symm)

theorem rosserOddLogDensity_bounds {k : ℕ} {s : ℝ} (hs : 0 < s)
    {x : Fin (2 * k + 1) → ℝ} (hx : x ∈ rosserOddMeshAmbient k s) :
    0 ≤ rosserOddLogDensity k x ∧
      rosserOddLogDensity k x ≤ (1 / (s / 3 ^ (k + 1))) ^ (2 * k + 1) := by
  have hi := mem_rosserOddMeshAmbient.mp hx
  have hpos (i : Fin (2 * k + 1)) : 0 < x i :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < s / 3 ^ (k + 1)) (hi i).1
  have hle (i : Fin (2 * k + 1)) : 1 / x i ≤ 1 / (s / 3 ^ (k + 1)) :=
    one_div_le_one_div_of_le (by positivity) (hi i).1
  refine ⟨Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hpos i)).le), ?_⟩
  calc
    rosserOddLogDensity k x ≤ ∏ _i : Fin (2 * k + 1), (1 / (s / 3 ^ (k + 1))) :=
      Finset.prod_le_prod (fun i _ => (one_div_pos.mpr (hpos i)).le) (fun i _ => hle i)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem rosserOddMeshLowerIntegrand_dominated {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ) (x : Fin (2 * k + 1) → ℝ) :
    ‖rosserOddMeshLowerIntegrand k s n x‖ ≤
      (rosserOddMeshAmbient k s).indicator
        (fun _ => (1 / (s / 3 ^ (k + 1))) * (1 / (s / 3 ^ (k + 1))) ^ (2 * k + 1)) x := by
  by_cases hx : ∃ j ∈ rosserOddMeshCells k s n, x ∈ rosserOddMeshCell k s n j
  · obtain ⟨j, hj, hxj⟩ := hx
    have hb := rosserOddMeshCell_subset_ambient hcut n j hxj
    have hd := rosserOddLogDensity_bounds hs hb
    have hhi : s / 3 ^ (k + 1) ≤ rosserOddMeshHi k s n j (Fin.last (2 * k)) :=
      (rosserOddMeshLoHi_bounds hcut n j _).1.trans (rosserOddMeshLoHi_bounds hcut n j _).2.1.le
    have hpos : 0 < rosserOddMeshHi k s n j (Fin.last (2 * k)) :=
      lt_of_lt_of_le (by positivity : (0 : ℝ) < s / 3 ^ (k + 1)) hhi
    have hcoeff : 1 / rosserOddMeshHi k s n j (Fin.last (2 * k)) ≤
        1 / (s / 3 ^ (k + 1)) := one_div_le_one_div_of_le (by positivity) hhi
    rw [rosserOddMeshLowerIntegrand_eq_of_mem hcut hj hxj, indicator_of_mem hb,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (one_div_pos.mpr hpos).le hd.1)]
    exact mul_le_mul hcoeff hd.2 hd.1 (by positivity)
  · rw [rosserOddMeshLowerIntegrand_eq_zero hx, norm_zero]
    exact indicator_nonneg (fun _ _ => by positivity) x

theorem continuousOn_rosserOddKernel_ambient {k : ℕ} {s : ℝ} (hs : 0 < s) :
    ContinuousOn (rosserOddKernel k) (rosserOddMeshAmbient k s) := by
  have hrec (i : Fin (2 * k + 1)) : ContinuousOn
      (fun x : Fin (2 * k + 1) → ℝ => 1 / x i) (rosserOddMeshAmbient k s) :=
    continuousOn_const.div (continuous_apply i).continuousOn (fun x hx =>
      (lt_of_lt_of_le (by positivity : (0 : ℝ) < s / 3 ^ (k + 1))
        (mem_rosserOddMeshAmbient.mp hx i).1).ne')
  exact (continuousOn_finsetProd Finset.univ (fun i _ => hrec i)).mul (hrec _)

theorem integrableOn_rosserOddKernel_region {k : ℕ} {s : ℝ} (hs : 0 < s) :
    IntegrableOn (rosserOddKernel k) (rosserOddLogRegion k s) :=
  ((continuousOn_rosserOddKernel_ambient hs).integrableOn_compact
    (isCompact_rosserOddMeshAmbient k s)).mono_set (rosserOddLogRegion_subset_ambient hs)

/-- Every fixed odd rank has a proved mesh limit equal to its actual
Lebesgue region integral. The cutoff hypothesis only says the ambient
interval is nonempty; all analytic convergence is proved here. -/
theorem tendsto_rosserOddMeshLowerSum {k : ℕ} {s : ℝ} (hs : 0 < s)
    (hcut : s / 3 ^ (k + 1) < 1) :
    Tendsto (rosserOddMeshLowerSum k s) atTop (𝓝 (rosserOddLayerIntegral k s)) := by
  change Tendsto (fun n => rosserOddMeshLowerSum k s n) atTop _
  simp only [rosserOddMeshLowerSum_eq_integral hs hcut]
  have hbound : Integrable ((rosserOddMeshAmbient k s).indicator
      (fun _ => (1 / (s / 3 ^ (k + 1))) * (1 / (s / 3 ^ (k + 1))) ^ (2 * k + 1))) :=
    (continuousOn_const.integrableOn_compact (isCompact_rosserOddMeshAmbient k s)).integrable_indicator
      (measurableSet_rosserOddMeshAmbient k s)
  have hlim := tendsto_integral_of_dominated_convergence _
    (fun n => (integrable_rosserOddMeshLowerIntegrand hs hcut n).aestronglyMeasurable)
    hbound (fun n => Eventually.of_forall (rosserOddMeshLowerIntegrand_dominated hs hcut n))
    (Eventually.of_forall (tendsto_rosserOddMeshLowerIntegrand hs hcut))
  rw [integral_indicator (measurableSet_rosserOddLogRegion k s)] at hlim
  exact hlim

end

end ImbalancedChen
