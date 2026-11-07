import ImbalancedChen.RosserOddLogRegion
import ImbalancedChen.LogPrimeBoxMesh

/-!
# Strict inner meshes for every fixed odd Rosser region

The ambient interval is the proved positive support interval
`[s / 3^(k+1), 1)`. A selected cell satisfies all upper prefix tests at its
upper endpoints and the terminal shell at its lower endpoints. Adjacent
intervals may meet at an endpoint because cell ownership is half-open.

Every selected cell lies in the strict region. Conversely, every point of
the strict region eventually lies in a selected cell. This follows from
convergence of both endpoint vectors and the finitely many strict tests;
no explicit margin estimates or boundary-null-set assumption are needed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open Filter Set

def rosserOddMeshLo (k : ℕ) (s : ℝ) (n : ℕ)
    (j : Fin (2 * k + 1) → Fin (n + 1)) : Fin (2 * k + 1) → ℝ :=
  logPrimeMeshLo (s / 3 ^ (k + 1)) 1 n j

def rosserOddMeshHi (k : ℕ) (s : ℝ) (n : ℕ)
    (j : Fin (2 * k + 1) → Fin (n + 1)) : Fin (2 * k + 1) → ℝ :=
  logPrimeMeshHi (s / 3 ^ (k + 1)) 1 n j

def rosserOddMeshCell (k : ℕ) (s : ℝ) (n : ℕ)
    (j : Fin (2 * k + 1) → Fin (n + 1)) : Set (Fin (2 * k + 1) → ℝ) :=
  logPrimeMeshCell (s / 3 ^ (k + 1)) 1 n j

/-- The filter includes the strict total-tail-product gate used by the
actual finite boundary supplier, even though it is redundant pointwise
in the continuous region. -/
def rosserOddMeshCells (k : ℕ) (s : ℝ) (n : ℕ) :
    Finset (Fin (2 * k + 1) → Fin (n + 1)) :=
  Finset.univ.filter fun j =>
    (∀ i : Fin (2 * k), rosserOddMeshHi k s n j i.succ ≤
      rosserOddMeshLo k s n j i.castSucc) ∧
    rosserOddMeshHi k s n j 0 ≤ 1 ∧
    (∑ i : Fin (2 * k), rosserOddMeshHi k s n j i.castSucc) < s ∧
    (∀ i : Fin (2 * k), Even i.val →
      rosserOddLogPrefix k (rosserOddMeshHi k s n j) i +
        3 * rosserOddMeshHi k s n j i.castSucc < s) ∧
    s < (∑ i : Fin (2 * k), rosserOddMeshLo k s n j i.castSucc) +
      3 * rosserOddMeshLo k s n j (Fin.last (2 * k))

@[simp] theorem mem_rosserOddMeshCell {k n : ℕ} {s : ℝ}
    {j : Fin (2 * k + 1) → Fin (n + 1)} {x : Fin (2 * k + 1) → ℝ} :
    x ∈ rosserOddMeshCell k s n j ↔
      ∀ i, rosserOddMeshLo k s n j i ≤ x i ∧ x i < rosserOddMeshHi k s n j i :=
  mem_logPrimeMeshCell

@[simp] theorem mem_rosserOddMeshCells {k n : ℕ} {s : ℝ}
    {j : Fin (2 * k + 1) → Fin (n + 1)} :
    j ∈ rosserOddMeshCells k s n ↔
      (∀ i : Fin (2 * k), rosserOddMeshHi k s n j i.succ ≤
        rosserOddMeshLo k s n j i.castSucc) ∧
      rosserOddMeshHi k s n j 0 ≤ 1 ∧
      (∑ i : Fin (2 * k), rosserOddMeshHi k s n j i.castSucc) < s ∧
      (∀ i : Fin (2 * k), Even i.val →
        rosserOddLogPrefix k (rosserOddMeshHi k s n j) i +
          3 * rosserOddMeshHi k s n j i.castSucc < s) ∧
      s < (∑ i : Fin (2 * k), rosserOddMeshLo k s n j i.castSucc) +
        3 * rosserOddMeshLo k s n j (Fin.last (2 * k)) := by
  simp only [rosserOddMeshCells, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rosserOddMeshLoHi_bounds {k : ℕ} {s : ℝ} (hcut : s / 3 ^ (k + 1) < 1)
    (n : ℕ) (j : Fin (2 * k + 1) → Fin (n + 1)) (i : Fin (2 * k + 1)) :
    s / 3 ^ (k + 1) ≤ rosserOddMeshLo k s n j i ∧
      rosserOddMeshLo k s n j i < rosserOddMeshHi k s n j i ∧
      rosserOddMeshHi k s n j i ≤ 1 :=
  logPrimeMeshLoHi_bounds hcut n j i

theorem measurableSet_rosserOddMeshCell (k : ℕ) (s : ℝ) (n : ℕ)
    (j : Fin (2 * k + 1) → Fin (n + 1)) :
    MeasurableSet (rosserOddMeshCell k s n j) :=
  measurableSet_logPrimeMeshCell _ _ n j

theorem rosserOddMesh_separated {k n : ℕ} {s : ℝ} (hcut : s / 3 ^ (k + 1) ≤ 1)
    {j r : Fin (2 * k + 1) → Fin (n + 1)} (hjr : j ≠ r) : ∃ i,
      rosserOddMeshHi k s n j i ≤ rosserOddMeshLo k s n r i ∨
      rosserOddMeshHi k s n r i ≤ rosserOddMeshLo k s n j i :=
  logPrimeMesh_separated hcut hjr

theorem rosserOddMeshCell_unique {k n : ℕ} {s : ℝ} (hcut : s / 3 ^ (k + 1) ≤ 1)
    {j r : Fin (2 * k + 1) → Fin (n + 1)} {x : Fin (2 * k + 1) → ℝ}
    (hj : x ∈ rosserOddMeshCell k s n j) (hr : x ∈ rosserOddMeshCell k s n r) : j = r :=
  logPrimeMeshCell_unique hcut hj hr

/-- Endpoint tests are sufficient for the whole half-open cell, with no
unproved geometric inclusion premise. -/
theorem rosserOddMeshCell_subset_region {k n : ℕ} {s : ℝ}
    {j : Fin (2 * k + 1) → Fin (n + 1)} (hs : 0 < s)
    (hcut : s / 3 ^ (k + 1) < 1) (hj : j ∈ rosserOddMeshCells k s n) :
    rosserOddMeshCell k s n j ⊆ rosserOddLogRegion k s := by
  intro x hx
  have hm := mem_rosserOddMeshCell.mp hx
  have hg := mem_rosserOddMeshCells.mp hj
  refine ⟨?_, ?_, (hm 0).2.trans_le hg.2.1, ?_, ?_⟩
  · exact (show 0 < s / 3 ^ (k + 1) by positivity).trans_le
      ((rosserOddMeshLoHi_bounds hcut n j (Fin.last (2 * k))).1.trans
        (hm (Fin.last (2 * k))).1)
  · apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    exact (hm i.succ).2.trans_le ((hg.1 i).trans (hm i.castSucc).1)
  · intro i hi
    have hprefix : rosserOddLogPrefix k x i ≤
        rosserOddLogPrefix k (rosserOddMeshHi k s n j) i := by
      exact Finset.sum_le_sum (fun r _ => (hm r.castSucc).2.le)
    have hlast := (hm i.castSucc).2.le
    have hgate := hg.2.2.2.1 i hi
    linarith
  · have hsum : (∑ i : Fin (2 * k), rosserOddMeshLo k s n j i.castSucc) ≤
        ∑ i : Fin (2 * k), x i.castSucc :=
      Finset.sum_le_sum (fun i _ => (hm i.castSucc).1)
    have hterminal := (hm (Fin.last (2 * k))).1
    linarith [hg.2.2.2.2]

theorem tendsto_rosserOddMeshLo {k : ℕ} (s : ℝ)
    (j : ∀ n : ℕ, Fin (2 * k + 1) → Fin (n + 1)) {x : Fin (2 * k + 1) → ℝ}
    (hx : ∀ n, x ∈ rosserOddMeshCell k s n (j n)) :
    Tendsto (fun n => rosserOddMeshLo k s n (j n)) atTop (𝓝 x) :=
  tendsto_logPrimeMeshLo _ _ j hx

theorem tendsto_rosserOddMeshHi {k : ℕ} (s : ℝ)
    (j : ∀ n : ℕ, Fin (2 * k + 1) → Fin (n + 1)) {x : Fin (2 * k + 1) → ℝ}
    (hx : ∀ n, x ∈ rosserOddMeshCell k s n (j n)) :
    Tendsto (fun n => rosserOddMeshHi k s n (j n)) atTop (𝓝 x) :=
  tendsto_logPrimeMeshHi _ _ j hx

/-- Every strict region point eventually belongs to a selected inner box.
The proof also covers the depth-zero region and derives the nonempty
ambient interval from the point, rather than assuming it separately. -/
theorem rosserOddLogRegion_eventually_mem_mesh {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 < s) (hx : x ∈ rosserOddLogRegion k s) :
    ∀ᶠ n : ℕ in atTop, ∃ j ∈ rosserOddMeshCells k s n,
      x ∈ rosserOddMeshCell k s n j := by
  have hb := rosserOddLogRegion_bounds hs hx
  have hcut : s / 3 ^ (k + 1) < 1 := (hb 0).1.trans (hb 0).2
  have hbox : x ∈ logPrimeBox (fun _ => s / 3 ^ (k + 1)) (fun _ => (1 : ℝ)) :=
    mem_logPrimeBox.mpr (fun i => ⟨(hb i).1.le, (hb i).2⟩)
  choose j hj using fun n => exists_logPrimeMeshCell _ _ n hbox
  have hlo := tendsto_rosserOddMeshLo s j hj
  have hhi := tendsto_rosserOddMeshHi s j hj
  have hsep : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 * k),
      rosserOddMeshHi k s n (j n) i.succ ≤ rosserOddMeshLo k s n (j n) i.castSucc := by
    rw [Filter.eventually_all]
    intro i
    have hlim := ((continuous_apply i.succ).tendsto x |>.comp hhi).sub
      ((continuous_apply i.castSucc).tendsto x |>.comp hlo)
    have hlt : x i.succ - x i.castSucc < 0 :=
      sub_neg.mpr (hx.2.1 Fin.castSucc_lt_succ)
    filter_upwards [hlim.eventually (gt_mem_nhds hlt)] with n hn
    exact sub_nonpos.mp hn.le
  have hsumcont : Continuous (fun y : Fin (2 * k + 1) → ℝ =>
      ∑ i : Fin (2 * k), y i.castSucc) := by fun_prop
  have hsum : ∀ᶠ n : ℕ in atTop,
      (∑ i : Fin (2 * k), rosserOddMeshHi k s n (j n) i.castSucc) < s :=
    ((hsumcont.tendsto x).comp hhi).eventually
      (gt_mem_nhds (rosserOddLogRegion_tail_sum_lt hs hx))
  have hprefix : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 * k), Even i.val →
      rosserOddLogPrefix k (rosserOddMeshHi k s n (j n)) i +
        3 * rosserOddMeshHi k s n (j n) i.castSucc < s := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : Even i.val
    · have hcont : Continuous (fun y : Fin (2 * k + 1) → ℝ =>
          rosserOddLogPrefix k y i + 3 * y i.castSucc) :=
        (continuous_rosserOddLogPrefix k i).add
          (continuous_const.mul (continuous_apply i.castSucc))
      filter_upwards [((hcont.tendsto x).comp hhi).eventually
        (gt_mem_nhds (hx.2.2.2.1 i hi))] with n hn
      exact fun _ => hn
    · exact Eventually.of_forall (fun _ hn => (hi hn).elim)
  have hshellcont : Continuous (fun y : Fin (2 * k + 1) → ℝ =>
      (∑ i : Fin (2 * k), y i.castSucc) + 3 * y (Fin.last (2 * k))) := by fun_prop
  have hshell : ∀ᶠ n : ℕ in atTop,
      s < (∑ i : Fin (2 * k), rosserOddMeshLo k s n (j n) i.castSucc) +
        3 * rosserOddMeshLo k s n (j n) (Fin.last (2 * k)) :=
    ((hshellcont.tendsto x).comp hlo).eventually (lt_mem_nhds hx.2.2.2.2)
  filter_upwards [hsep, hsum, hprefix, hshell] with n hnsep hnsum hnprefix hnshell
  exact ⟨j n, mem_rosserOddMeshCells.mpr
    ⟨hnsep, (rosserOddMeshLoHi_bounds hcut n (j n) 0).2.2, hnsum, hnprefix, hnshell⟩, hj n⟩

end

end ImbalancedChen
