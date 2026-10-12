import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Set.Union
import Mathlib.Tactic

/-!
# Strict inner boxes for the continuous three-prime Rosser layer

Coordinates are logarithms relative to the outer prime cutoff, in decreasing
order. At residual coordinate three the open boundary region stays above
1/3 in every coordinate. The finite half-open mesh below lies inside this
region and eventually covers every one of its points. Cross-cell coordinate
separation is explicit for use with actual prime-tuple box sums.
-/

namespace ImbalancedChen

noncomputable section

open Filter Set
open scoped Classical Topology

def rosserTripleRegion : Set (Fin 3 → ℝ) :=
  {x | 0 < x 2 ∧ x 2 < x 1 ∧ x 1 < x 0 ∧ x 0 < 1 ∧
    3 < x 0 + x 1 + 3 * x 2}

def rosserTripleMeshStep (n : ℕ) : ℝ := (2 / 3 : ℝ) / (n + 1)

def rosserTripleMeshPoint (n i : ℕ) : ℝ :=
  (1 / 3 : ℝ) + (i : ℝ) * rosserTripleMeshStep n

def rosserTripleMeshLo (n : ℕ) (j : Fin 3 → Fin (n + 1)) : Fin 3 → ℝ :=
  fun i => rosserTripleMeshPoint n (j i)

def rosserTripleMeshHi (n : ℕ) (j : Fin 3 → Fin (n + 1)) : Fin 3 → ℝ :=
  fun i => rosserTripleMeshPoint n ((j i).val + 1)

def rosserTripleMeshCell (n : ℕ) (j : Fin 3 → Fin (n + 1)) : Set (Fin 3 → ℝ) :=
  Set.univ.pi fun i => Set.Ico (rosserTripleMeshLo n j i) (rosserTripleMeshHi n j i)

def rosserTripleMeshCells (n : ℕ) : Finset (Fin 3 → Fin (n + 1)) :=
  Finset.univ.filter fun j =>
    rosserTripleMeshHi n j 1 ≤ rosserTripleMeshLo n j 0 ∧
    rosserTripleMeshHi n j 2 ≤ rosserTripleMeshLo n j 1 ∧
    3 < rosserTripleMeshLo n j 0 + rosserTripleMeshLo n j 1 +
      3 * rosserTripleMeshLo n j 2

@[simp] theorem mem_rosserTripleMeshCell {n : ℕ} {j : Fin 3 → Fin (n + 1)}
    {x : Fin 3 → ℝ} :
    x ∈ rosserTripleMeshCell n j ↔
      ∀ i, rosserTripleMeshLo n j i ≤ x i ∧ x i < rosserTripleMeshHi n j i := by
  simp [rosserTripleMeshCell, Set.mem_pi]

@[simp] theorem mem_rosserTripleMeshCells {n : ℕ} {j : Fin 3 → Fin (n + 1)} :
    j ∈ rosserTripleMeshCells n ↔
      rosserTripleMeshHi n j 1 ≤ rosserTripleMeshLo n j 0 ∧
      rosserTripleMeshHi n j 2 ≤ rosserTripleMeshLo n j 1 ∧
      3 < rosserTripleMeshLo n j 0 + rosserTripleMeshLo n j 1 +
        3 * rosserTripleMeshLo n j 2 := by
  simp [rosserTripleMeshCells]

theorem rosserTripleMeshStep_pos (n : ℕ) : 0 < rosserTripleMeshStep n := by
  unfold rosserTripleMeshStep
  positivity

theorem rosserTripleMeshPoint_mono (n : ℕ) : Monotone (rosserTripleMeshPoint n) := by
  intro i j hij
  change (1 / 3 : ℝ) + (i : ℝ) * rosserTripleMeshStep n ≤
    (1 / 3 : ℝ) + (j : ℝ) * rosserTripleMeshStep n
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij)
      (rosserTripleMeshStep_pos n).le) _

@[simp] theorem rosserTripleMeshPoint_zero (n : ℕ) :
    rosserTripleMeshPoint n 0 = 1 / 3 := by simp [rosserTripleMeshPoint]

@[simp] theorem rosserTripleMeshPoint_last (n : ℕ) :
    rosserTripleMeshPoint n (n + 1) = 1 := by
  unfold rosserTripleMeshPoint rosserTripleMeshStep
  push_cast
  field_simp
  ring

theorem rosserTripleMeshPoint_succ (n i : ℕ) :
    rosserTripleMeshPoint n (i + 1) =
      rosserTripleMeshPoint n i + rosserTripleMeshStep n := by
  simp only [rosserTripleMeshPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem rosserTripleMeshLoHi_bounds (n : ℕ) (j : Fin 3 → Fin (n + 1)) (i : Fin 3) :
    (1 / 3 : ℝ) ≤ rosserTripleMeshLo n j i ∧
      rosserTripleMeshLo n j i < rosserTripleMeshHi n j i ∧
      rosserTripleMeshHi n j i ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [rosserTripleMeshLo] using
      rosserTripleMeshPoint_mono n (Nat.zero_le (j i).val)
  · dsimp [rosserTripleMeshLo, rosserTripleMeshHi]
    rw [rosserTripleMeshPoint_succ]
    exact lt_add_of_pos_right _ (rosserTripleMeshStep_pos n)
  · simpa [rosserTripleMeshHi] using
      rosserTripleMeshPoint_mono n (Nat.succ_le_of_lt (j i).isLt)

theorem rosserTripleMesh_separated {n : ℕ} {j k : Fin 3 → Fin (n + 1)}
    (hjk : j ≠ k) : ∃ i,
      rosserTripleMeshHi n j i ≤ rosserTripleMeshLo n k i ∨
      rosserTripleMeshHi n k i ≤ rosserTripleMeshLo n j i := by
  obtain ⟨i, hi⟩ : ∃ i, j i ≠ k i := by
    by_contra h
    push Not at h
    exact hjk (funext h)
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne hi with h | h
  · exact Or.inl (rosserTripleMeshPoint_mono n (show (j i).val + 1 ≤ (k i).val from h))
  · exact Or.inr (rosserTripleMeshPoint_mono n (show (k i).val + 1 ≤ (j i).val from h))

theorem rosserTripleMeshCell_unique {n : ℕ} {j k : Fin 3 → Fin (n + 1)}
    {x : Fin 3 → ℝ} (hj : x ∈ rosserTripleMeshCell n j)
    (hk : x ∈ rosserTripleMeshCell n k) : j = k := by
  by_contra h
  obtain ⟨i, hi | hi⟩ := rosserTripleMesh_separated h
  · exact (not_lt_of_ge hi) (((mem_rosserTripleMeshCell.mp hk) i).1.trans_lt
      ((mem_rosserTripleMeshCell.mp hj) i).2)
  · exact (not_lt_of_ge hi) (((mem_rosserTripleMeshCell.mp hj) i).1.trans_lt
      ((mem_rosserTripleMeshCell.mp hk) i).2)

theorem rosserTripleMeshCell_subset_region {n : ℕ} {j : Fin 3 → Fin (n + 1)}
    (hj : j ∈ rosserTripleMeshCells n) : rosserTripleMeshCell n j ⊆ rosserTripleRegion := by
  intro x hx
  have hx' := mem_rosserTripleMeshCell.mp hx
  have hj' := mem_rosserTripleMeshCells.mp hj
  refine ⟨?_, (hx' 2).2.trans_le (hj'.2.1.trans (hx' 1).1),
    (hx' 1).2.trans_le (hj'.1.trans (hx' 0).1),
    (hx' 0).2.trans_le (rosserTripleMeshLoHi_bounds n j 0).2.2, ?_⟩
  · have h := (rosserTripleMeshLoHi_bounds n j 2).1.trans (hx' 2).1
    linarith
  · have h0 := (hx' 0).1
    have h1 := (hx' 1).1
    have h2 := (hx' 2).1
    linarith [hj'.2.2]

theorem rosserTripleRegion_bounds {x : Fin 3 → ℝ} (hx : x ∈ rosserTripleRegion) :
    ∀ i, (1 / 3 : ℝ) < x i ∧ x i < 1 := by
  rcases hx with ⟨h2, h21, h10, h0, hs⟩
  have h2lo : (1 / 3 : ℝ) < x 2 := by linarith
  intro i
  fin_cases i
  · exact ⟨h2lo.trans (h21.trans h10), h0⟩
  · exact ⟨h2lo.trans h21, h10.trans h0⟩
  · exact ⟨h2lo, h21.trans (h10.trans h0)⟩

theorem exists_rosserTripleMeshInterval (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico (1 / 3 : ℝ) 1) :
    ∃ i : Fin (n + 1), x ∈ Set.Ico
      (rosserTripleMeshPoint n i) (rosserTripleMeshPoint n (i.val + 1)) := by
  have hx' : x ∈ Set.Ico (rosserTripleMeshPoint n 0)
      (rosserTripleMeshPoint n (n + 1)) := by simpa using hx
  have hmem := Ico_subset_biUnion_Ico (n + 1) (rosserTripleMeshPoint n) hx'
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hmem
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, hxi⟩

theorem exists_rosserTripleMeshCell (n : ℕ) {x : Fin 3 → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico (1 / 3 : ℝ) 1) :
    ∃ j : Fin 3 → Fin (n + 1), x ∈ rosserTripleMeshCell n j := by
  choose j hj using fun i => exists_rosserTripleMeshInterval n (hx i)
  exact ⟨j, mem_rosserTripleMeshCell.mpr hj⟩

theorem tendsto_rosserTripleMeshStep :
    Tendsto rosserTripleMeshStep atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (2 / 3 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0)
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 / 3 : ℝ)

/-- Every point of the strict continuous boundary eventually belongs to
one selected inner cell. No almost-everywhere boundary exception is used. -/
theorem rosserTripleRegion_eventually_mem_mesh {x : Fin 3 → ℝ}
    (hx : x ∈ rosserTripleRegion) :
    ∀ᶠ n : ℕ in atTop, ∃ j ∈ rosserTripleMeshCells n, x ∈ rosserTripleMeshCell n j := by
  have hb := rosserTripleRegion_bounds hx
  choose j hj using fun n => exists_rosserTripleMeshCell n (fun i => ⟨(hb i).1.le, (hb i).2⟩)
  rcases hx with ⟨_, h21, h10, _, hs⟩
  have hgap21 : 0 < (x 1 - x 2) / 2 := by linarith
  have hgap10 : 0 < (x 0 - x 1) / 2 := by linarith
  have hgapS : 0 < (x 0 + x 1 + 3 * x 2 - 3) / 5 := by linarith
  filter_upwards [tendsto_rosserTripleMeshStep.eventually (gt_mem_nhds hgap21),
    tendsto_rosserTripleMeshStep.eventually (gt_mem_nhds hgap10),
    tendsto_rosserTripleMeshStep.eventually (gt_mem_nhds hgapS)] with n hn21 hn10 hnS
  refine ⟨j n, mem_rosserTripleMeshCells.mpr ?_, hj n⟩
  have hm := mem_rosserTripleMeshCell.mp (hj n)
  have he (i : Fin 3) : rosserTripleMeshHi n (j n) i =
      rosserTripleMeshLo n (j n) i + rosserTripleMeshStep n :=
    rosserTripleMeshPoint_succ n (j n i)
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  rw [he 0] at h0
  rw [he 1] at h1
  rw [he 2] at h2
  refine ⟨?_, ?_, ?_⟩
  · rw [he 1]
    linarith
  · rw [he 2]
    linarith
  · linarith

end

end ImbalancedChen
