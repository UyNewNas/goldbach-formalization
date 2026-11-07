import ImbalancedChen.RosserOddMeshIntegral
import ImbalancedChen.RosserEvenMeshIntegral

/-!
# Meshes with a strict upper face for both Rosser parities

Filtering by `Hi 0 < 1` supplies a strict outer-cutoff margin without
changing the limiting actual integral. Pointwise eventual coverage and
dominated convergence are proved for each fixed rank and residual level.
No parameter-uniform conclusion is inferred from these pointwise limits.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

/-- Existing selected cells with a strict top endpoint, leaving a margin for
variation of the outer cutoff exponent. -/
def rosserOddTopStrictMeshCells (k : ℕ) (s : ℝ) (n : ℕ) :
    Finset (Fin (2 * k + 1) → Fin (n + 1)) :=
  (rosserOddMeshCells k s n).filter (fun j => rosserOddMeshHi k s n j 0 < 1)

@[simp] theorem mem_rosserOddTopStrictMeshCells {k n : ℕ} {s : ℝ}
    {j : Fin (2 * k + 1) → Fin (n + 1)} :
    j ∈ rosserOddTopStrictMeshCells k s n ↔
      j ∈ rosserOddMeshCells k s n ∧ rosserOddMeshHi k s n j 0 < 1 := by
  simp only [rosserOddTopStrictMeshCells, Finset.mem_filter]

theorem rosserOddTopStrictMeshCells_subset (k : ℕ) (s : ℝ) (n : ℕ) :
    rosserOddTopStrictMeshCells k s n ⊆ rosserOddMeshCells k s n :=
  Finset.filter_subset _ _

def rosserOddTopStrictMeshLowerIntegrand (k : ℕ) (s : ℝ) (n : ℕ)
    (x : Fin (2 * k + 1) → ℝ) : ℝ :=
  ∑ j ∈ rosserOddTopStrictMeshCells k s n,
    (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) *
      (rosserOddMeshCell k s n j).indicator (rosserOddLogDensity k) x

def rosserOddTopStrictMeshLowerSum (k : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ rosserOddTopStrictMeshCells k s n,
    (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) *
      ∏ i, Real.log (rosserOddMeshHi k s n j i / rosserOddMeshLo k s n j i)

/-- Strict top selection still eventually contains every point of the
actual open region. The endpoint margin comes from `x 0 < 1`. -/
theorem rosserOddLogRegion_eventually_mem_topStrictMesh {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 < s) (hx : x ∈ rosserOddLogRegion k s) :
    ∀ᶠ n : ℕ in atTop, ∃ j ∈ rosserOddTopStrictMeshCells k s n,
      x ∈ rosserOddMeshCell k s n j := by
  have hb := rosserOddLogRegion_bounds hs hx
  have hcut : s / 3 ^ (k + 1) < 1 := (hb 0).1.trans (hb 0).2
  choose j hj using fun n => exists_logPrimeMeshCell (s / 3 ^ (k + 1)) 1 n
    (mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩))
  have hselected : ∀ᶠ n : ℕ in atTop, j n ∈ rosserOddMeshCells k s n := by
    filter_upwards [rosserOddLogRegion_eventually_mem_mesh hs hx] with n hn
    obtain ⟨r, hr, hxr⟩ := hn
    exact (logPrimeMeshCell_unique hcut.le hxr (hj n)) ▸ hr
  have htop : ∀ᶠ n : ℕ in atTop, rosserOddMeshHi k s n (j n) 0 < 1 :=
    (tendsto_logPrimeMeshHi_apply (s / 3 ^ (k + 1)) 1 j hj 0).eventually
      (gt_mem_nhds (hb 0).2)
  filter_upwards [hselected, htop] with n hn ht
  exact ⟨j n, mem_rosserOddTopStrictMeshCells.mpr ⟨hn, ht⟩, hj n⟩

theorem integrable_rosserOddTopStrictMeshLowerIntegrand {k : ℕ} {s : ℝ}
    (hs : 0 < s) (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ) :
    Integrable (rosserOddTopStrictMeshLowerIntegrand k s n) := by
  exact integrable_finsetSum _ (fun j _ =>
    ((integrableOn_rosserOddLogDensity_cell hs hcut n j).integrable_indicator
      (measurableSet_rosserOddMeshCell k s n j)).const_mul _)

theorem rosserOddTopStrictMeshLowerSum_eq_integral {k : ℕ} {s : ℝ}
    (hs : 0 < s) (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ) :
    rosserOddTopStrictMeshLowerSum k s n =
      ∫ x, rosserOddTopStrictMeshLowerIntegrand k s n x := by
  unfold rosserOddTopStrictMeshLowerSum rosserOddTopStrictMeshLowerIntegrand
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

theorem rosserOddTopStrictMeshLowerIntegrand_eq_of_mem {k n : ℕ} {s : ℝ}
    (hcut : s / 3 ^ (k + 1) < 1) {j : Fin (2 * k + 1) → Fin (n + 1)}
    (hj : j ∈ rosserOddTopStrictMeshCells k s n) {x : Fin (2 * k + 1) → ℝ}
    (hx : x ∈ rosserOddMeshCell k s n j) :
    rosserOddTopStrictMeshLowerIntegrand k s n x =
      (1 / rosserOddMeshHi k s n j (Fin.last (2 * k))) * rosserOddLogDensity k x := by
  unfold rosserOddTopStrictMeshLowerIntegrand
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hx]
  · intro r _ hrj
    rw [indicator_of_notMem (fun hr => hrj (rosserOddMeshCell_unique hcut.le hr hx)), mul_zero]
  · exact fun h => (h hj).elim

theorem rosserOddTopStrictMeshLowerIntegrand_eq_zero {k n : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ}
    (hx : ¬∃ j ∈ rosserOddTopStrictMeshCells k s n, x ∈ rosserOddMeshCell k s n j) :
    rosserOddTopStrictMeshLowerIntegrand k s n x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [indicator_of_notMem (fun h => hx ⟨j, hj, h⟩), mul_zero]

theorem rosserOddTopStrictMeshLowerIntegrand_eq_zero_of_not_mem_region
    {k n : ℕ} {s : ℝ} (hs : 0 < s) (hcut : s / 3 ^ (k + 1) < 1)
    {x : Fin (2 * k + 1) → ℝ} (hx : x ∉ rosserOddLogRegion k s) :
    rosserOddTopStrictMeshLowerIntegrand k s n x = 0 := by
  apply rosserOddTopStrictMeshLowerIntegrand_eq_zero
  rintro ⟨j, hj, hxj⟩
  exact hx (rosserOddMeshCell_subset_region hs hcut
    (mem_rosserOddTopStrictMeshCells.mp hj).1 hxj)

theorem tendsto_rosserOddTopStrictMeshLowerIntegrand {k : ℕ} {s : ℝ}
    (hs : 0 < s) (hcut : s / 3 ^ (k + 1) < 1) (x : Fin (2 * k + 1) → ℝ) :
    Tendsto (fun n => rosserOddTopStrictMeshLowerIntegrand k s n x) atTop
      (𝓝 ((rosserOddLogRegion k s).indicator (rosserOddKernel k) x)) := by
  by_cases hx : x ∈ rosserOddLogRegion k s
  · have hb := rosserOddLogRegion_bounds hs hx
    choose j hj using fun n => exists_logPrimeMeshCell (s / 3 ^ (k + 1)) 1 n
      (mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩))
    have hselected : ∀ᶠ n : ℕ in atTop, j n ∈ rosserOddTopStrictMeshCells k s n := by
      filter_upwards [rosserOddLogRegion_eventually_mem_topStrictMesh hs hx] with n hn
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
    exact (rosserOddTopStrictMeshLowerIntegrand_eq_of_mem hcut hn (hj n)).symm
  · rw [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr (fun _ =>
      (rosserOddTopStrictMeshLowerIntegrand_eq_zero_of_not_mem_region hs hcut hx).symm)

/-- A selected top-strict contribution equals the old integrand at its
unique cell; otherwise it is zero. The old compact majorant still applies. -/
theorem rosserOddTopStrictMeshLowerIntegrand_dominated {k : ℕ} {s : ℝ}
    (hs : 0 < s) (hcut : s / 3 ^ (k + 1) < 1) (n : ℕ)
    (x : Fin (2 * k + 1) → ℝ) :
    ‖rosserOddTopStrictMeshLowerIntegrand k s n x‖ ≤
      (rosserOddMeshAmbient k s).indicator
        (fun _ => (1 / (s / 3 ^ (k + 1))) * (1 / (s / 3 ^ (k + 1))) ^ (2 * k + 1)) x := by
  by_cases hx : ∃ j ∈ rosserOddTopStrictMeshCells k s n, x ∈ rosserOddMeshCell k s n j
  · obtain ⟨j, hj, hxj⟩ := hx
    rw [rosserOddTopStrictMeshLowerIntegrand_eq_of_mem hcut hj hxj,
      ← rosserOddMeshLowerIntegrand_eq_of_mem hcut (mem_rosserOddTopStrictMeshCells.mp hj).1 hxj]
    exact rosserOddMeshLowerIntegrand_dominated hs hcut n x
  · rw [rosserOddTopStrictMeshLowerIntegrand_eq_zero hx, norm_zero]
    exact indicator_nonneg (fun _ _ => by positivity) x

/-- Discarding cells that touch the upper face does not change the limit. -/
theorem tendsto_rosserOddTopStrictMeshLowerSum {k : ℕ} {s : ℝ}
    (hs : 0 < s) (hcut : s / 3 ^ (k + 1) < 1) :
    Tendsto (rosserOddTopStrictMeshLowerSum k s) atTop
      (𝓝 (rosserOddLayerIntegral k s)) := by
  change Tendsto (fun n => rosserOddTopStrictMeshLowerSum k s n) atTop _
  simp only [rosserOddTopStrictMeshLowerSum_eq_integral hs hcut]
  have hbound : Integrable ((rosserOddMeshAmbient k s).indicator
      (fun _ => (1 / (s / 3 ^ (k + 1))) * (1 / (s / 3 ^ (k + 1))) ^ (2 * k + 1))) :=
    (continuousOn_const.integrableOn_compact (isCompact_rosserOddMeshAmbient k s)).integrable_indicator
      (measurableSet_rosserOddMeshAmbient k s)
  have hlim := tendsto_integral_of_dominated_convergence _
    (fun n => (integrable_rosserOddTopStrictMeshLowerIntegrand hs hcut n).aestronglyMeasurable)
    hbound (fun n => Eventually.of_forall (rosserOddTopStrictMeshLowerIntegrand_dominated hs hcut n))
    (Eventually.of_forall (tendsto_rosserOddTopStrictMeshLowerIntegrand hs hcut))
  rw [integral_indicator (measurableSet_rosserOddLogRegion k s)] at hlim
  exact hlim

/-- Existing selected cells with a strict top endpoint, leaving a margin for
variation of the outer cutoff exponent. -/
def rosserEvenTopStrictMeshCells (k : ℕ) (s : ℝ) (n : ℕ) :
    Finset (Fin (2 * k + 2) → Fin (n + 1)) :=
  (rosserEvenMeshCells k s n).filter (fun j => rosserEvenMeshHi k s n j 0 < 1)

@[simp] theorem mem_rosserEvenTopStrictMeshCells {k n : ℕ} {s : ℝ}
    {j : Fin (2 * k + 2) → Fin (n + 1)} :
    j ∈ rosserEvenTopStrictMeshCells k s n ↔
      j ∈ rosserEvenMeshCells k s n ∧ rosserEvenMeshHi k s n j 0 < 1 := by
  simp only [rosserEvenTopStrictMeshCells, Finset.mem_filter]

theorem rosserEvenTopStrictMeshCells_subset (k : ℕ) (s : ℝ) (n : ℕ) :
    rosserEvenTopStrictMeshCells k s n ⊆ rosserEvenMeshCells k s n :=
  Finset.filter_subset _ _

def rosserEvenTopStrictMeshLowerIntegrand (k : ℕ) (s : ℝ) (n : ℕ)
    (x : Fin (2 * k + 2) → ℝ) : ℝ :=
  ∑ j ∈ rosserEvenTopStrictMeshCells k s n,
    (1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1))) *
      (rosserEvenMeshCell k s n j).indicator (rosserEvenLogDensity k) x

def rosserEvenTopStrictMeshLowerSum (k : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ rosserEvenTopStrictMeshCells k s n,
    (1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1))) *
      ∏ i, Real.log (rosserEvenMeshHi k s n j i / rosserEvenMeshLo k s n j i)

/-- Strict top selection still eventually contains every point of the
actual open region. The endpoint margin comes from `x 0 < 1`. -/
theorem rosserEvenLogRegion_eventually_mem_topStrictMesh {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 2) → ℝ} (hs : 1 < s) (hx : x ∈ rosserEvenLogRegion k s) :
    ∀ᶠ n : ℕ in atTop, ∃ j ∈ rosserEvenTopStrictMeshCells k s n,
      x ∈ rosserEvenMeshCell k s n j := by
  have hb := rosserEvenLogRegion_bounds hs hx
  have hcut : (s - 1) / 3 ^ (k + 1) < 1 := (hb 0).1.trans (hb 0).2
  choose j hj using fun n => exists_logPrimeMeshCell ((s - 1) / 3 ^ (k + 1)) 1 n
    (mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩))
  have hselected : ∀ᶠ n : ℕ in atTop, j n ∈ rosserEvenMeshCells k s n := by
    filter_upwards [rosserEvenLogRegion_eventually_mem_mesh hs hx] with n hn
    obtain ⟨r, hr, hxr⟩ := hn
    exact (logPrimeMeshCell_unique hcut.le hxr (hj n)) ▸ hr
  have htop : ∀ᶠ n : ℕ in atTop, rosserEvenMeshHi k s n (j n) 0 < 1 :=
    (tendsto_logPrimeMeshHi_apply ((s - 1) / 3 ^ (k + 1)) 1 j hj 0).eventually
      (gt_mem_nhds (hb 0).2)
  filter_upwards [hselected, htop] with n hn ht
  exact ⟨j n, mem_rosserEvenTopStrictMeshCells.mpr ⟨hn, ht⟩, hj n⟩

theorem integrable_rosserEvenTopStrictMeshLowerIntegrand {k : ℕ} {s : ℝ}
    (hs : 1 < s) (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ) :
    Integrable (rosserEvenTopStrictMeshLowerIntegrand k s n) := by
  exact integrable_finsetSum _ (fun j _ =>
    ((integrableOn_rosserEvenLogDensity_cell hs hcut n j).integrable_indicator
      (measurableSet_rosserEvenMeshCell k s n j)).const_mul _)

theorem rosserEvenTopStrictMeshLowerSum_eq_integral {k : ℕ} {s : ℝ}
    (hs : 1 < s) (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ) :
    rosserEvenTopStrictMeshLowerSum k s n =
      ∫ x, rosserEvenTopStrictMeshLowerIntegrand k s n x := by
  unfold rosserEvenTopStrictMeshLowerSum rosserEvenTopStrictMeshLowerIntegrand
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

theorem rosserEvenTopStrictMeshLowerIntegrand_eq_of_mem {k n : ℕ} {s : ℝ}
    (hcut : (s - 1) / 3 ^ (k + 1) < 1) {j : Fin (2 * k + 2) → Fin (n + 1)}
    (hj : j ∈ rosserEvenTopStrictMeshCells k s n) {x : Fin (2 * k + 2) → ℝ}
    (hx : x ∈ rosserEvenMeshCell k s n j) :
    rosserEvenTopStrictMeshLowerIntegrand k s n x =
      (1 / rosserEvenMeshHi k s n j (Fin.last (2 * k + 1))) * rosserEvenLogDensity k x := by
  unfold rosserEvenTopStrictMeshLowerIntegrand
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hx]
  · intro r _ hrj
    rw [indicator_of_notMem (fun hr => hrj (rosserEvenMeshCell_unique hcut.le hr hx)), mul_zero]
  · exact fun h => (h hj).elim

theorem rosserEvenTopStrictMeshLowerIntegrand_eq_zero {k n : ℕ} {s : ℝ}
    {x : Fin (2 * k + 2) → ℝ}
    (hx : ¬∃ j ∈ rosserEvenTopStrictMeshCells k s n, x ∈ rosserEvenMeshCell k s n j) :
    rosserEvenTopStrictMeshLowerIntegrand k s n x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [indicator_of_notMem (fun h => hx ⟨j, hj, h⟩), mul_zero]

theorem rosserEvenTopStrictMeshLowerIntegrand_eq_zero_of_not_mem_region
    {k n : ℕ} {s : ℝ} (hs : 1 < s) (hcut : (s - 1) / 3 ^ (k + 1) < 1)
    {x : Fin (2 * k + 2) → ℝ} (hx : x ∉ rosserEvenLogRegion k s) :
    rosserEvenTopStrictMeshLowerIntegrand k s n x = 0 := by
  apply rosserEvenTopStrictMeshLowerIntegrand_eq_zero
  rintro ⟨j, hj, hxj⟩
  exact hx (rosserEvenMeshCell_subset_region hs hcut
    (mem_rosserEvenTopStrictMeshCells.mp hj).1 hxj)

theorem tendsto_rosserEvenTopStrictMeshLowerIntegrand {k : ℕ} {s : ℝ}
    (hs : 1 < s) (hcut : (s - 1) / 3 ^ (k + 1) < 1) (x : Fin (2 * k + 2) → ℝ) :
    Tendsto (fun n => rosserEvenTopStrictMeshLowerIntegrand k s n x) atTop
      (𝓝 ((rosserEvenLogRegion k s).indicator (rosserEvenKernel k) x)) := by
  by_cases hx : x ∈ rosserEvenLogRegion k s
  · have hb := rosserEvenLogRegion_bounds hs hx
    choose j hj using fun n => exists_logPrimeMeshCell ((s - 1) / 3 ^ (k + 1)) 1 n
      (mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩))
    have hselected : ∀ᶠ n : ℕ in atTop, j n ∈ rosserEvenTopStrictMeshCells k s n := by
      filter_upwards [rosserEvenLogRegion_eventually_mem_topStrictMesh hs hx] with n hn
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
    exact (rosserEvenTopStrictMeshLowerIntegrand_eq_of_mem hcut hn (hj n)).symm
  · rw [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr (fun _ =>
      (rosserEvenTopStrictMeshLowerIntegrand_eq_zero_of_not_mem_region hs hcut hx).symm)

/-- A selected top-strict contribution equals the old integrand at its
unique cell; otherwise it is zero. The old compact majorant still applies. -/
theorem rosserEvenTopStrictMeshLowerIntegrand_dominated {k : ℕ} {s : ℝ}
    (hs : 1 < s) (hcut : (s - 1) / 3 ^ (k + 1) < 1) (n : ℕ)
    (x : Fin (2 * k + 2) → ℝ) :
    ‖rosserEvenTopStrictMeshLowerIntegrand k s n x‖ ≤
      (rosserEvenMeshAmbient k s).indicator
        (fun _ => (1 / ((s - 1) / 3 ^ (k + 1))) * (1 / ((s - 1) / 3 ^ (k + 1))) ^ (2 * k + 2)) x := by
  by_cases hx : ∃ j ∈ rosserEvenTopStrictMeshCells k s n, x ∈ rosserEvenMeshCell k s n j
  · obtain ⟨j, hj, hxj⟩ := hx
    rw [rosserEvenTopStrictMeshLowerIntegrand_eq_of_mem hcut hj hxj,
      ← rosserEvenMeshLowerIntegrand_eq_of_mem hcut (mem_rosserEvenTopStrictMeshCells.mp hj).1 hxj]
    exact rosserEvenMeshLowerIntegrand_dominated hs hcut n x
  · rw [rosserEvenTopStrictMeshLowerIntegrand_eq_zero hx, norm_zero]
    exact indicator_nonneg (fun _ _ => by positivity) x

/-- Discarding cells that touch the upper face does not change the limit. -/
theorem tendsto_rosserEvenTopStrictMeshLowerSum {k : ℕ} {s : ℝ}
    (hs : 1 < s) (hcut : (s - 1) / 3 ^ (k + 1) < 1) :
    Tendsto (rosserEvenTopStrictMeshLowerSum k s) atTop
      (𝓝 (rosserEvenLayerIntegral k s)) := by
  change Tendsto (fun n => rosserEvenTopStrictMeshLowerSum k s n) atTop _
  simp only [rosserEvenTopStrictMeshLowerSum_eq_integral hs hcut]
  have hbound : Integrable ((rosserEvenMeshAmbient k s).indicator
      (fun _ => (1 / ((s - 1) / 3 ^ (k + 1))) * (1 / ((s - 1) / 3 ^ (k + 1))) ^ (2 * k + 2))) :=
    (continuousOn_const.integrableOn_compact (isCompact_rosserEvenMeshAmbient k s)).integrable_indicator
      (measurableSet_rosserEvenMeshAmbient k s)
  have hlim := tendsto_integral_of_dominated_convergence _
    (fun n => (integrable_rosserEvenTopStrictMeshLowerIntegrand hs hcut n).aestronglyMeasurable)
    hbound (fun n => Eventually.of_forall (rosserEvenTopStrictMeshLowerIntegrand_dominated hs hcut n))
    (Eventually.of_forall (tendsto_rosserEvenTopStrictMeshLowerIntegrand hs hcut))
  rw [integral_indicator (measurableSet_rosserEvenLogRegion k s)] at hlim
  exact hlim

end

end ImbalancedChen
