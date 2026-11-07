import ImbalancedChen.LogPrimeBoxIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Union
import Mathlib.Tactic

/-!
# Half-open logarithmic meshes in arbitrary finite dimension

The same finite mesh works in any fixed dimension and on any real interval.
It retains exact Ico ownership, explicit coordinate separation between cells,
and convergence of both endpoint vectors to every point in their cells.
These are geometric suppliers for fixed-rank Rosser boundary integrals.
-/

namespace ImbalancedChen

noncomputable section

open Filter Set
open scoped Classical Topology

def logPrimeMeshStep (a b : ℝ) (n : ℕ) : ℝ := (b - a) / (n + 1)

def logPrimeMeshPoint (a b : ℝ) (n i : ℕ) : ℝ :=
  a + (i : ℝ) * logPrimeMeshStep a b n

def logPrimeMeshLo {d : ℕ} (a b : ℝ) (n : ℕ)
    (j : Fin d → Fin (n + 1)) : Fin d → ℝ :=
  fun i => logPrimeMeshPoint a b n (j i)

def logPrimeMeshHi {d : ℕ} (a b : ℝ) (n : ℕ)
    (j : Fin d → Fin (n + 1)) : Fin d → ℝ :=
  fun i => logPrimeMeshPoint a b n ((j i).val + 1)

def logPrimeMeshCell {d : ℕ} (a b : ℝ) (n : ℕ)
    (j : Fin d → Fin (n + 1)) : Set (Fin d → ℝ) :=
  logPrimeBox (logPrimeMeshLo a b n j) (logPrimeMeshHi a b n j)

@[simp] theorem mem_logPrimeMeshCell {d n : ℕ} {a b : ℝ}
    {j : Fin d → Fin (n + 1)} {x : Fin d → ℝ} :
    x ∈ logPrimeMeshCell a b n j ↔
      ∀ i, logPrimeMeshLo a b n j i ≤ x i ∧ x i < logPrimeMeshHi a b n j i :=
  mem_logPrimeBox

theorem measurableSet_logPrimeMeshCell {d : ℕ} (a b : ℝ) (n : ℕ)
    (j : Fin d → Fin (n + 1)) : MeasurableSet (logPrimeMeshCell a b n j) :=
  measurableSet_logPrimeBox _ _

theorem logPrimeMeshStep_pos {a b : ℝ} (hab : a < b) (n : ℕ) :
    0 < logPrimeMeshStep a b n := div_pos (sub_pos.mpr hab) (by positivity)

theorem logPrimeMeshPoint_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    Monotone (logPrimeMeshPoint a b n) := by
  intro i j hij
  change a + (i : ℝ) * logPrimeMeshStep a b n ≤ a + (j : ℝ) * logPrimeMeshStep a b n
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij)
    (div_nonneg (sub_nonneg.mpr hab) (by positivity))

@[simp] theorem logPrimeMeshPoint_zero (a b : ℝ) (n : ℕ) :
    logPrimeMeshPoint a b n 0 = a := by simp [logPrimeMeshPoint]

@[simp] theorem logPrimeMeshPoint_last (a b : ℝ) (n : ℕ) :
    logPrimeMeshPoint a b n (n + 1) = b := by
  unfold logPrimeMeshPoint logPrimeMeshStep
  push_cast
  field_simp
  ring

theorem logPrimeMeshPoint_succ (a b : ℝ) (n i : ℕ) :
    logPrimeMeshPoint a b n (i + 1) =
      logPrimeMeshPoint a b n i + logPrimeMeshStep a b n := by
  simp only [logPrimeMeshPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem logPrimeMeshHi_eq_lo_add_step {d : ℕ} (a b : ℝ) (n : ℕ)
    (j : Fin d → Fin (n + 1)) (i : Fin d) :
    logPrimeMeshHi a b n j i = logPrimeMeshLo a b n j i + logPrimeMeshStep a b n :=
  logPrimeMeshPoint_succ a b n (j i)

theorem logPrimeMeshLoHi_bounds {d : ℕ} {a b : ℝ} (hab : a < b) (n : ℕ)
    (j : Fin d → Fin (n + 1)) (i : Fin d) :
    a ≤ logPrimeMeshLo a b n j i ∧
      logPrimeMeshLo a b n j i < logPrimeMeshHi a b n j i ∧
      logPrimeMeshHi a b n j i ≤ b := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [logPrimeMeshLo] using logPrimeMeshPoint_mono hab.le n (Nat.zero_le (j i).val)
  · rw [logPrimeMeshHi_eq_lo_add_step]
    exact lt_add_of_pos_right _ (logPrimeMeshStep_pos hab n)
  · simpa [logPrimeMeshHi] using
      logPrimeMeshPoint_mono hab.le n (Nat.succ_le_of_lt (j i).isLt)

/-- Distinct grid labels have a separating coordinate, including when the
two half-open intervals meet at their common endpoint. -/
theorem logPrimeMesh_separated {d n : ℕ} {a b : ℝ} (hab : a ≤ b)
    {j k : Fin d → Fin (n + 1)} (hjk : j ≠ k) : ∃ i,
      logPrimeMeshHi a b n j i ≤ logPrimeMeshLo a b n k i ∨
      logPrimeMeshHi a b n k i ≤ logPrimeMeshLo a b n j i := by
  obtain ⟨i, hi⟩ : ∃ i, j i ≠ k i := by
    by_contra h
    push Not at h
    exact hjk (funext h)
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne hi with h | h
  · exact Or.inl (logPrimeMeshPoint_mono hab n (show (j i).val + 1 ≤ (k i).val from h))
  · exact Or.inr (logPrimeMeshPoint_mono hab n (show (k i).val + 1 ≤ (j i).val from h))

theorem logPrimeMeshCell_unique {d n : ℕ} {a b : ℝ} (hab : a ≤ b)
    {j k : Fin d → Fin (n + 1)} {x : Fin d → ℝ}
    (hj : x ∈ logPrimeMeshCell a b n j) (hk : x ∈ logPrimeMeshCell a b n k) : j = k := by
  by_contra h
  obtain ⟨i, hi | hi⟩ := logPrimeMesh_separated hab h
  · exact (not_lt_of_ge hi) (((mem_logPrimeMeshCell.mp hk) i).1.trans_lt
      ((mem_logPrimeMeshCell.mp hj) i).2)
  · exact (not_lt_of_ge hi) (((mem_logPrimeMeshCell.mp hj) i).1.trans_lt
      ((mem_logPrimeMeshCell.mp hk) i).2)

theorem logPrimeMeshCell_pairwiseDisjoint {d : ℕ} {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (Set.univ : Set (Fin d → Fin (n + 1))).PairwiseDisjoint (logPrimeMeshCell a b n) := by
  intro j _ k _ hjk
  change Disjoint (logPrimeMeshCell a b n j) (logPrimeMeshCell a b n k)
  rw [Set.disjoint_left]
  intro x hxj hxk
  exact hjk (logPrimeMeshCell_unique hab hxj hxk)

theorem logPrimeMeshCell_subset_box {d : ℕ} {a b : ℝ} (hab : a < b)
    (n : ℕ) (j : Fin d → Fin (n + 1)) :
    logPrimeMeshCell a b n j ⊆ logPrimeBox (fun _ => a) (fun _ => b) := by
  intro x hx
  refine mem_logPrimeBox.mpr (fun i => ?_)
  have hi := mem_logPrimeMeshCell.mp hx i
  exact ⟨(logPrimeMeshLoHi_bounds hab n j i).1.trans hi.1,
    hi.2.trans_le (logPrimeMeshLoHi_bounds hab n j i).2.2⟩

theorem exists_logPrimeMeshInterval (a b : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico a b) :
    ∃ i : Fin (n + 1), x ∈ Set.Ico
      (logPrimeMeshPoint a b n i) (logPrimeMeshPoint a b n (i.val + 1)) := by
  have hx' : x ∈ Set.Ico (logPrimeMeshPoint a b n 0)
      (logPrimeMeshPoint a b n (n + 1)) := by simpa using hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp
    (Ico_subset_biUnion_Ico (n + 1) (logPrimeMeshPoint a b n) hx')
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, hxi⟩

theorem exists_logPrimeMeshCell {d : ℕ} (a b : ℝ) (n : ℕ) {x : Fin d → ℝ}
    (hx : x ∈ logPrimeBox (fun _ => a) (fun _ => b)) :
    ∃ j : Fin d → Fin (n + 1), x ∈ logPrimeMeshCell a b n j := by
  choose j hj using fun i => exists_logPrimeMeshInterval a b n (mem_logPrimeBox.mp hx i)
  exact ⟨j, mem_logPrimeMeshCell.mpr hj⟩

theorem logPrimeMeshCells_union {d : ℕ} {a b : ℝ} (hab : a < b) (n : ℕ) :
    (⋃ j : Fin d → Fin (n + 1), logPrimeMeshCell a b n j) =
      logPrimeBox (fun _ => a) (fun _ => b) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact logPrimeMeshCell_subset_box hab n j hj
  · intro hx
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell a b n hx
    exact Set.mem_iUnion.mpr ⟨j, hj⟩

theorem tendsto_logPrimeMeshStep (a b : ℝ) :
    Tendsto (logPrimeMeshStep a b) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 1)) atTop (nhds 0)
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b - a)

theorem tendsto_logPrimeMeshHi_apply {d : ℕ} (a b : ℝ)
    (j : ∀ n : ℕ, Fin d → Fin (n + 1)) {x : Fin d → ℝ}
    (hx : ∀ n, x ∈ logPrimeMeshCell a b n (j n)) (i : Fin d) :
    Tendsto (fun n => logPrimeMeshHi a b n (j n) i) atTop (nhds (x i)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  filter_upwards [(tendsto_logPrimeMeshStep a b).eventually (gt_mem_nhds hepsilon)] with n hn
  have hxi := mem_logPrimeMeshCell.mp (hx n) i
  have he := logPrimeMeshHi_eq_lo_add_step a b n (j n) i
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hxi.2], by linarith [hxi.1]⟩

theorem tendsto_logPrimeMeshLo_apply {d : ℕ} (a b : ℝ)
    (j : ∀ n : ℕ, Fin d → Fin (n + 1)) {x : Fin d → ℝ}
    (hx : ∀ n, x ∈ logPrimeMeshCell a b n (j n)) (i : Fin d) :
    Tendsto (fun n => logPrimeMeshLo a b n (j n) i) atTop (nhds (x i)) := by
  have h := (tendsto_logPrimeMeshHi_apply a b j hx i).sub (tendsto_logPrimeMeshStep a b)
  simpa only [sub_zero, logPrimeMeshHi_eq_lo_add_step, add_sub_cancel_right] using h

/-- Both endpoint vectors converge, so every finite family of strict
continuous endpoint tests eventually holds without choosing a new mesh
for each coordinate. -/
theorem tendsto_logPrimeMeshLo {d : ℕ} (a b : ℝ)
    (j : ∀ n : ℕ, Fin d → Fin (n + 1)) {x : Fin d → ℝ}
    (hx : ∀ n, x ∈ logPrimeMeshCell a b n (j n)) :
    Tendsto (fun n => logPrimeMeshLo a b n (j n)) atTop (nhds x) :=
  tendsto_pi_nhds.mpr (fun i => tendsto_logPrimeMeshLo_apply a b j hx i)

theorem tendsto_logPrimeMeshHi {d : ℕ} (a b : ℝ)
    (j : ∀ n : ℕ, Fin d → Fin (n + 1)) {x : Fin d → ℝ}
    (hx : ∀ n, x ∈ logPrimeMeshCell a b n (j n)) :
    Tendsto (fun n => logPrimeMeshHi a b n (j n)) atTop (nhds x) :=
  tendsto_pi_nhds.mpr (fun i => tendsto_logPrimeMeshHi_apply a b j hx i)

end

end ImbalancedChen
