import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A finite dyadic cover for the primitive Shiu window gate

NEW RECONSTRUCTION, 2026-11-26. This source is a new implementation of the
elementary subdivision in the frozen 1106 manuscript, `ana:shifted-divisor`.
It is compatible with the observed WindowGate API. It is not a recovery of
either historically registered FiniteCover file or its unobserved proofs.

For the positive closed interval [A,B], assume B-A <= T and T > 0. On the
shell [2^j,2^(j+1)), use H = min(T,2^j) and translated starts
max(A,2^j)+k*H. Two windows suffice, including the closed right endpoint;
the eight-window index set is retained for the existing caller. Every
window has H <= X, polynomial location, and the required active-scale
lower bound. Active shells have an actual large source-point witness.

The cover, nonnegative sum comparison and total length payment are proved
below. No Shiu estimate, prime reciprocal estimate, gcd reduction, small
range estimate, or final shifted-divisor estimate is asserted here.
-/

namespace ImbalancedChen.Part3.MediumPrimitiveShiuCover20261028

noncomputable section
open Classical Finset
open scoped BigOperators

/-- The positive dyadic scale. -/
def shellBase (j : ℕ) : ℕ := 2 ^ j

/-- The exact smaller of the quotient length and the shell scale. -/
def windowLength (T j : ℕ) : ℕ := min T (shellBase j)

/-- The translated start keeps both the original lower endpoint and the shell. -/
def windowStart (A T j k : ℕ) : ℕ :=
  max A (shellBase j) + k * windowLength T j

/-- The interval form is definitionally the one expected by primitive Shiu. -/
def window (A T j k : ℕ) : Finset ℕ :=
  Ico (windowStart A T j k) (windowStart A T j k + windowLength T j)

theorem shellBase_pos (j : ℕ) : 0 < shellBase j := by
  exact pow_pos (by norm_num) j

theorem windowLength_pos (T j : ℕ) (hT : 0 < T) : 0 < windowLength T j := by
  exact lt_min hT (shellBase_pos j)

theorem windowLength_le_T (T j : ℕ) : windowLength T j ≤ T := min_le_left _ _

theorem windowLength_le_shellBase (T j : ℕ) : windowLength T j ≤ shellBase j :=
  min_le_right _ _

theorem shellBase_le_windowStart (A T j k : ℕ) :
    shellBase j ≤ windowStart A T j k := by
  exact (le_max_right A (shellBase j)).trans (Nat.le_add_right _ _)

theorem windowLength_le_start (A T j k : ℕ) (_hT : 0 < T) :
    windowLength T j ≤ windowStart A T j k :=
  (windowLength_le_shellBase T j).trans (shellBase_le_windowStart A T j k)

theorem shellBase_le_B (B j : ℕ) (hB : B ≠ 0)
    (hj : j < Nat.log 2 B + 1) : shellBase j ≤ B := by
  have hlog : j ≤ Nat.log 2 B := by omega
  exact (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hlog).trans
    (Nat.pow_log_le_self 2 hB)

/-- The bound is independent of T, including windows past the original endpoint. -/
theorem windowStart_le_eight_B (A B T j k : ℕ) (hAB : A ≤ B) (hB : B ≠ 0)
    (hj : j < Nat.log 2 B + 1) (hk : k < 8) :
    windowStart A T j k ≤ 8 * B := by
  have hs : shellBase j ≤ B := shellBase_le_B B j hB hj
  have hmax : max A (shellBase j) ≤ B := max_le hAB hs
  have hH : windowLength T j ≤ B := (windowLength_le_shellBase T j).trans hs
  have hmul : k * windowLength T j ≤ 7 * B :=
    Nat.mul_le_mul (by omega : k ≤ 7) hH
  unfold windowStart
  omega

/-- A source-point witness supplies the scale lower bound used by WindowGate. -/
theorem active_window_length_lower (T j n : ℕ) (R : ℝ)
    (hT : R / 16 ≤ (T : ℝ)) (hpoint : R ≤ (n : ℝ))
    (hshell : n < 2 * shellBase j) :
    R / 16 ≤ (windowLength T j : ℝ) := by
  have hns : (n : ℝ) < 2 * (shellBase j : ℝ) := by exact_mod_cast hshell
  have hs : (0 : ℝ) ≤ shellBase j := Nat.cast_nonneg _
  have hR : R / 16 ≤ (shellBase j : ℝ) := by linarith
  rw [windowLength, Nat.cast_min]
  exact le_min hT hR

/-- The second window retains n=B=A+T when that closed endpoint is in the shell. -/
theorem point_mem_window_zero_or_one {A B T j n : ℕ}
    (hT : 0 < T) (hspan : B - A ≤ T)
    (hn : n ∈ Icc A B) (hshell : n ∈ Ico (shellBase j) (2 * shellBase j)) :
    n ∈ window A T j 0 ∨ n ∈ window A T j 1 := by
  have hABT : B ≤ A + T := by omega
  have hmax : max A (shellBase j) ≤ n :=
    max_le (mem_Icc.mp hn).1 (mem_Ico.mp hshell).1
  have hnT : n ≤ max A (shellBase j) + T :=
    (mem_Icc.mp hn).2.trans (hABT.trans
      (Nat.add_le_add_right (le_max_left A (shellBase j)) T))
  have hnS : n < max A (shellBase j) + shellBase j :=
    (mem_Ico.mp hshell).2.trans_le (by
      have h := le_max_right A (shellBase j)
      omega)
  by_cases hTS : T ≤ shellBase j
  · simp only [window, windowStart, windowLength, min_eq_left hTS,
      zero_mul, one_mul, add_zero, mem_Ico]
    omega
  · have hST : shellBase j ≤ T := le_of_not_ge hTS
    left
    simpa only [window, windowStart, windowLength, min_eq_right hST,
      zero_mul, add_zero, mem_Ico] using And.intro hmax hnS

/-- Each positive original integer has a legal shell and one of the eight windows. -/
theorem positive_point_mem_window {A B T n : ℕ}
    (hT : 0 < T) (hspan : B - A ≤ T) (hn : n ∈ Icc A B) (hnpos : 0 < n) :
    ∃ j ∈ range (Nat.log 2 B + 1), ∃ k ∈ range 8,
      n ∈ window A T j k ∧ n ∈ Ico (shellBase j) (2 * shellBase j) := by
  let j := Nat.log 2 n
  have hj : j ∈ range (Nat.log 2 B + 1) := by
    apply mem_range.mpr
    have h := Nat.log_mono_right (b := 2) (mem_Icc.mp hn).2
    omega
  have hslo : shellBase j ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
  have hshi : n < 2 * shellBase j := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
    simpa only [j, shellBase, pow_succ, Nat.mul_comm] using h
  have hshell : n ∈ Ico (shellBase j) (2 * shellBase j) := mem_Ico.mpr ⟨hslo, hshi⟩
  rcases point_mem_window_zero_or_one hT hspan hn hshell with h | h
  · exact ⟨j, hj, 0, by simp, h, hshell⟩
  · exact ⟨j, hj, 1, by simp, h, hshell⟩

/-- The positive part above the manuscript's separately treated small range. -/
def largeSource (A B : ℕ) (R : ℝ) : Finset ℕ :=
  (Icc A B).filter (fun n => 0 < n ∧ R ≤ (n : ℝ))

/-- Only shells containing an actual retained source point are active. -/
def activeShells (A B : ℕ) (R : ℝ) : Finset ℕ :=
  (range (Nat.log 2 B + 1)).filter
    (fun j => ∃ n ∈ largeSource A B R, n ∈ Ico (shellBase j) (2 * shellBase j))

theorem activeShell_witness {A B j : ℕ} {R : ℝ} (hj : j ∈ activeShells A B R) :
    j < Nat.log 2 B + 1 ∧
      ∃ n ∈ Icc A B, 0 < n ∧ R ≤ (n : ℝ) ∧
        shellBase j ≤ n ∧ n < 2 * shellBase j := by
  obtain ⟨hj, n, hn, hshell⟩ := mem_filter.mp hj
  obtain ⟨hn, hnpos, hR⟩ := mem_filter.mp hn
  exact ⟨mem_range.mp hj, n, hn, hnpos, hR,
    (mem_Ico.mp hshell).1, (mem_Ico.mp hshell).2⟩

theorem largeSource_mem_active_window {A B T n : ℕ} {R : ℝ}
    (hT : 0 < T) (hspan : B - A ≤ T) (hn : n ∈ largeSource A B R) :
    ∃ j ∈ activeShells A B R, ∃ k ∈ range 8, n ∈ window A T j k := by
  have hdata := mem_filter.mp hn
  obtain ⟨j, hj, k, hk, hw, hshell⟩ :=
    positive_point_mem_window hT hspan hdata.1 hdata.2.1
  exact ⟨j, mem_filter.mpr ⟨hj, n, hn, hshell⟩, k, hk, hw⟩

/-- A genuine nonnegative-sum majorization on the original retained source. -/
theorem sum_largeSource_le_active_windows (A B T : ℕ) (R : ℝ)
    (hT : 0 < T) (hspan : B - A ≤ T) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ n ∈ largeSource A B R, F n) ≤
      ∑ j ∈ activeShells A B R, ∑ k ∈ range 8, ∑ n ∈ window A T j k, F n := by
  have hpoint (n : ℕ) (hn : n ∈ largeSource A B R) :
      F n ≤ ∑ j ∈ activeShells A B R, ∑ k ∈ range 8,
        if n ∈ window A T j k then F n else 0 := by
    obtain ⟨j, hj, k, hk, hw⟩ := largeSource_mem_active_window hT hspan hn
    have hkbound : F n ≤ ∑ k' ∈ range 8,
        if n ∈ window A T j k' then F n else 0 := by
      have h := single_le_sum
        (f := fun k' => if n ∈ window A T j k' then F n else 0)
        (fun k' _ => by
          split_ifs
          · exact hF n
          · exact le_rfl) hk
      simpa only [if_pos hw] using h
    have hjbound := single_le_sum
      (f := fun j' => ∑ k' ∈ range 8,
        if n ∈ window A T j' k' then F n else 0)
      (fun j' _ => sum_nonneg (fun k' _ => by
        split_ifs
        · exact hF n
        · exact le_rfl)) hj
    exact hkbound.trans hjbound
  calc
    (∑ n ∈ largeSource A B R, F n) ≤
        ∑ n ∈ largeSource A B R, ∑ j ∈ activeShells A B R, ∑ k ∈ range 8,
          if n ∈ window A T j k then F n else 0 := sum_le_sum hpoint
    _ = ∑ j ∈ activeShells A B R, ∑ k ∈ range 8, ∑ n ∈ largeSource A B R,
          if n ∈ window A T j k then F n else 0 := by
      rw [sum_comm (s := largeSource A B R) (t := activeShells A B R)]
      apply sum_congr rfl
      intro j _
      rw [sum_comm (s := largeSource A B R) (t := range 8)]
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro k _
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact (mem_filter.mp hn).2
      · intro n _ _
        exact hF n

theorem window_card (A T j k : ℕ) : (window A T j k).card = windowLength T j := by
  simp only [window, Nat.card_Ico, Nat.add_sub_cancel_left]

theorem shell_window_lengths_le (T j : ℕ) :
    (∑ _k ∈ range 8, windowLength T j) ≤ 8 * T := by
  calc
    (∑ _k ∈ range 8, windowLength T j) = 8 * windowLength T j := by simp
    _ ≤ 8 * T := Nat.mul_le_mul_left 8 (windowLength_le_T T j)

theorem activeShells_card_le (A B : ℕ) (R : ℝ) :
    (activeShells A B R).card ≤ Nat.log 2 B + 1 := by
  exact (card_le_card (filter_subset _ _)).trans_eq (card_range _)

/-- All window lengths together cost at most one logarithmic shell count. -/
theorem total_window_lengths_le (A B T : ℕ) (R : ℝ) :
    (∑ j ∈ activeShells A B R, ∑ _k ∈ range 8, windowLength T j) ≤
      8 * T * (Nat.log 2 B + 1) := by
  calc
    (∑ j ∈ activeShells A B R, ∑ _k ∈ range 8, windowLength T j) ≤
        ∑ _j ∈ activeShells A B R, 8 * T :=
      sum_le_sum (fun j _ => shell_window_lengths_le T j)
    _ = (activeShells A B R).card * (8 * T) := by simp
    _ ≤ (Nat.log 2 B + 1) * (8 * T) :=
      Nat.mul_le_mul_right (8 * T) (activeShells_card_le A B R)
    _ = 8 * T * (Nat.log 2 B + 1) := Nat.mul_comm _ _

end
end ImbalancedChen.Part3.MediumPrimitiveShiuCover20261028
