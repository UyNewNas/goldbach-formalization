import MathlibNt.SieveTheory.LinearSieve.BoundaryIntegrals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Strict logarithmic boundary regions in every fixed odd dimension

The last of `2*k+1` decreasing coordinates is the terminal prime coordinate.
The preceding `2*k` coordinates satisfy the strict alternating cubic-prefix
tests, and the terminal coordinate crosses the strict continuous shell.

No total-tail-sum inequality is assumed: the proved geometric residual
budget makes it redundant for positive levels. The region embeds in the
provider's actual continuous Rosser region. Its terminal coordinate, hence
every coordinate, lies above `s / 3^(k+1)`. All defining inequalities are
strict and finite in number, so the region is open and measurable.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set MeasureTheory
open MathlibNt.SieveTheory.LinearSieve

/-- The ordered list of nonterminal coordinates. -/
def rosserOddLogTail (k : ℕ) (x : Fin (2 * k + 1) → ℝ) : List ℝ :=
  List.ofFn (fun i : Fin (2 * k) => x i.castSucc)

/-- The preceding-coordinate sum at a tail index. -/
def rosserOddLogPrefix (k : ℕ) (x : Fin (2 * k + 1) → ℝ) (i : Fin (2 * k)) : ℝ :=
  ∑ j : Fin (2 * k) with j.val < i.val, x j.castSucc

/-- The actual strict continuous boundary region. The total-tail-sum
constraint is a theorem for positive levels, not an extra hypothesis. -/
def rosserOddLogRegion (k : ℕ) (s : ℝ) : Set (Fin (2 * k + 1) → ℝ) :=
  {x | 0 < x (Fin.last (2 * k)) ∧ StrictAnti x ∧ x 0 < 1 ∧
    (∀ i : Fin (2 * k), Even i.val →
      rosserOddLogPrefix k x i + 3 * x i.castSucc < s) ∧
    s < (∑ i : Fin (2 * k), x i.castSucc) + 3 * x (Fin.last (2 * k))}

@[simp] theorem rosserOddLogTail_length (k : ℕ) (x : Fin (2 * k + 1) → ℝ) :
    (rosserOddLogTail k x).length = 2 * k := by
  simp [rosserOddLogTail]

@[simp] theorem rosserOddLogTail_sum (k : ℕ) (x : Fin (2 * k + 1) → ℝ) :
    (rosserOddLogTail k x).sum = ∑ i : Fin (2 * k), x i.castSucc := by
  simp [rosserOddLogTail, List.sum_ofFn]

theorem rosserOddLogTail_take_sum (k : ℕ) (x : Fin (2 * k + 1) → ℝ)
    (i : Fin (2 * k)) :
    ((rosserOddLogTail k x).take i.val).sum = rosserOddLogPrefix k x i := by
  exact List.sum_take_ofFn (fun j : Fin (2 * k) => x j.castSucc) i.val

theorem rosserOddLogRegion_tail_sorted {k : ℕ} {s : ℝ} {x : Fin (2 * k + 1) → ℝ}
    (hx : x ∈ rosserOddLogRegion k s) : (rosserOddLogTail k x).SortedGT := by
  apply List.sortedGT_ofFn_iff.mpr
  intro i j hij
  exact hx.2.1 (show i.castSucc < j.castSucc from hij)

/-- Translation of the strict coordinate-prefix tests to the provider's
list-indexed tests, retaining the strict inequality. -/
theorem rosserOddLogRegion_tail_prefix_lt {k : ℕ} {s : ℝ} {x : Fin (2 * k + 1) → ℝ}
    (hx : x ∈ rosserOddLogRegion k s) :
    ∀ i (hi : i < (rosserOddLogTail k x).length), Even i →
      ((rosserOddLogTail k x).take i).sum + 3 * (rosserOddLogTail k x)[i] < s := by
  intro i hi heven
  have hi' : i < 2 * k := by simpa using hi
  have h := hx.2.2.2.1 ⟨i, hi'⟩ heven
  simpa [rosserOddLogTail, rosserOddLogPrefix, List.sum_take_ofFn] using h

/-- The unused logarithmic budget after all selected pairs is at least
the geometric residual supplied by the genuine alternating-prefix theorem. -/
theorem rosserOddLogRegion_tail_sum_add_geometric_le {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 ≤ s) (hx : x ∈ rosserOddLogRegion k s) :
    (∑ i : Fin (2 * k), x i.castSucc) + s / 3 ^ k ≤ s := by
  have h := sum_add_geometric_le_of_sortedGT_even_prefix hs
    (rosserOddLogTail_length k x) (rosserOddLogRegion_tail_sorted hx)
    (fun i hi heven => (rosserOddLogRegion_tail_prefix_lt hx i hi heven).le)
  simpa using h

/-- For a positive level the total-tail-sum constraint is strictly
satisfied, including the empty tail at pair depth zero. -/
theorem rosserOddLogRegion_tail_sum_lt {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 < s) (hx : x ∈ rosserOddLogRegion k s) :
    (∑ i : Fin (2 * k), x i.castSucc) < s := by
  have h := rosserOddLogRegion_tail_sum_add_geometric_le hs.le hx
  have hpos : (0 : ℝ) < s / 3 ^ k := by positivity
  linarith

/-- The strict region supplies the exact provider region with its closed
prefix tests. The list sum inequality is derived rather than assumed. -/
theorem rosserOddLogRegion_to_upperRosserLogRegion {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 ≤ s) (hx : x ∈ rosserOddLogRegion k s) :
    UpperRosserLogRegion s (x (Fin.last (2 * k))) (rosserOddLogTail k x) := by
  refine ⟨rosserOddLogRegion_tail_sorted hx, ?_, ?_, ?_, ?_⟩
  · rw [rosserOddLogTail_length]
    exact even_two_mul k
  · have h := rosserOddLogRegion_tail_sum_add_geometric_le hs hx
    have hnonneg : (0 : ℝ) ≤ s / 3 ^ k := by positivity
    rw [rosserOddLogTail_sum]
    linarith
  · intro i hi heven
    exact (rosserOddLogRegion_tail_prefix_lt hx i hi heven).le
  · simpa using hx.2.2.2.2

/-- The inherited top cutoff is one and every selected coordinate lies
strictly above the same terminal coordinate. -/
theorem rosserOddLogRegion_to_upperRosserLogRegionBelow {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 ≤ s) (hx : x ∈ rosserOddLogRegion k s) :
    UpperRosserLogRegionBelow s (x (Fin.last (2 * k))) 1 (rosserOddLogTail k x) := by
  refine ⟨rosserOddLogRegion_to_upperRosserLogRegion hs hx, ?_⟩
  intro y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  refine ⟨hx.2.1 (Fin.castSucc_lt_last i), ?_⟩
  exact (hx.2.1.antitone (Fin.zero_le i.castSucc)).trans_lt hx.2.2.1

/-- The exact fixed-depth positive cutoff, directly supplied by the
provider's proved continuous-region theorem. -/
theorem rosserOddLogRegion_terminal_lower {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 ≤ s) (hx : x ∈ rosserOddLogRegion k s) :
    s / 3 ^ (k + 1) < x (Fin.last (2 * k)) :=
  (rosserOddLogRegion_to_upperRosserLogRegion hs hx).outer_lower hs
    (rosserOddLogTail_length k x)

/-- Every coordinate of a positive-level fixed-depth region is uniformly
bounded away from zero, with the strict global top cutoff unchanged. -/
theorem rosserOddLogRegion_bounds {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 1) → ℝ} (hs : 0 < s) (hx : x ∈ rosserOddLogRegion k s) :
    ∀ i, s / 3 ^ (k + 1) < x i ∧ x i < 1 := by
  intro i
  exact ⟨(rosserOddLogRegion_terminal_lower hs.le hx).trans_le
      (hx.2.1.antitone (Fin.le_last i)),
    (hx.2.1.antitone (Fin.zero_le i)).trans_lt hx.2.2.1⟩

theorem rosserOddLogRegion_subset_positive_box {k : ℕ} {s : ℝ} (hs : 0 < s) :
    rosserOddLogRegion k s ⊆ Set.univ.pi (fun _ => Set.Ioo (s / 3 ^ (k + 1)) 1) := by
  intro x hx
  exact Set.mem_pi.mpr (fun i _ => rosserOddLogRegion_bounds hs hx i)

theorem continuous_rosserOddLogPrefix (k : ℕ) (i : Fin (2 * k)) :
    Continuous (fun x : Fin (2 * k + 1) → ℝ => rosserOddLogPrefix k x i) := by
  unfold rosserOddLogPrefix
  fun_prop

/-- Strict antitonicity on a finite coordinate space is an open condition. -/
theorem isOpen_strictAnti_fin (d : ℕ) :
    IsOpen {x : Fin d → ℝ | StrictAnti x} := by
  change IsOpen {x : Fin d → ℝ | ∀ i j, i < j → x j < x i}
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _hij
  exact isOpen_lt (continuous_apply j) (continuous_apply i)

/-- All inequalities defining the odd region are strict and indexed by
finite sets, so the region is open without deleting any hyperplanes. -/
theorem isOpen_rosserOddLogRegion (k : ℕ) (s : ℝ) : IsOpen (rosserOddLogRegion k s) := by
  have hprefix : IsOpen {x : Fin (2 * k + 1) → ℝ |
      ∀ i : Fin (2 * k), Even i.val → rosserOddLogPrefix k x i + 3 * x i.castSucc < s} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _hi
    exact isOpen_lt ((continuous_rosserOddLogPrefix k i).add
      (continuous_const.mul (continuous_apply i.castSucc))) continuous_const
  have hsum : Continuous (fun x : Fin (2 * k + 1) → ℝ =>
      (∑ i : Fin (2 * k), x i.castSucc) + 3 * x (Fin.last (2 * k))) := by fun_prop
  exact (isOpen_lt continuous_const (continuous_apply (Fin.last (2 * k)))).inter
    ((isOpen_strictAnti_fin (2 * k + 1)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        (hprefix.inter (isOpen_lt continuous_const hsum))))

theorem measurableSet_rosserOddLogRegion (k : ℕ) (s : ℝ) :
    MeasurableSet (rosserOddLogRegion k s) := (isOpen_rosserOddLogRegion k s).measurableSet

end

end ImbalancedChen
