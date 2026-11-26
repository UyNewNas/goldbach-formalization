import ImbalancedChen.RosserOddLogRegion

/-!
# Strict Rosser tail regions and exact pair removal

The inherited top cutoff is retained explicitly, and every alternating
prefix inequality is strict. The empty tail imposes only the residual
shell, with no artificial comparison of the terminal and top cutoffs.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set MeasureTheory

/-- The strict even-dimensional tail preceding a fixed terminal coordinate. -/
def rosserOddTailRegion (k : ℕ) (s q b : ℝ) : Set (Fin (2 * k) → ℝ) :=
  {v | 0 ≤ s ∧ StrictAnti v ∧ (∀ i, q < v i ∧ v i < b) ∧
    (∀ i : Fin (2 * k), Even i.val →
      (∑ j : Fin (2 * k) with j.val < i.val, v j) + 3 * v i < s) ∧
    s < (∑ i, v i) + 3 * q}

@[simp] theorem mem_rosserOddTailRegion {k : ℕ} {s q b : ℝ} {v : Fin (2 * k) → ℝ} :
    v ∈ rosserOddTailRegion k s q b ↔
      0 ≤ s ∧ StrictAnti v ∧ (∀ i, q < v i ∧ v i < b) ∧
        (∀ i : Fin (2 * k), Even i.val →
          (∑ j : Fin (2 * k) with j.val < i.val, v j) + 3 * v i < s) ∧
        s < (∑ i, v i) + 3 * q := Iff.rfl

@[simp] theorem mem_rosserOddTailRegion_zero (s q b : ℝ) (v : Fin (2 * 0) → ℝ) :
    v ∈ rosserOddTailRegion 0 s q b ↔ 0 ≤ s ∧ s < 3 * q := by
  simp [rosserOddTailRegion, StrictAnti]

/-- List form used solely for the exact two-coordinate reindexing. -/
def rosserStrictTailListRegion (s q b : ℝ) (v : List ℝ) : Prop :=
  0 ≤ s ∧ v.SortedGT ∧ (∀ x ∈ v, q < x ∧ x < b) ∧
    (∀ i (hi : i < v.length), Even i → (v.take i).sum + 3 * v[i] < s) ∧
    s < v.sum + 3 * q

theorem mem_rosserOddTailRegion_iff_list {k : ℕ} {s q b : ℝ} {v : Fin (2 * k) → ℝ} :
    v ∈ rosserOddTailRegion k s q b ↔ rosserStrictTailListRegion s q b (List.ofFn v) := by
  constructor
  · rintro ⟨hs, hanti, hb, hp, ht⟩
    refine ⟨hs, List.sortedGT_ofFn_iff.mpr hanti, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hb i
    · intro i hi heven
      have hi' : i < 2 * k := by simpa using hi
      simpa [List.sum_take_ofFn] using hp ⟨i, hi'⟩ heven
    · simpa only [List.sum_ofFn] using ht
  · rintro ⟨hs, hanti, hb, hp, ht⟩
    refine ⟨hs, List.sortedGT_ofFn_iff.mp hanti, ?_, ?_, ?_⟩
    · intro i
      exact hb (v i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · intro i heven
      simpa [List.sum_take_ofFn] using hp i.val (by simp) heven
    · simpa only [List.sum_ofFn] using ht

/-- The strict pair recursion has the same open endpoints as the actual
continuous boundary-mass supplier. -/
theorem rosserStrictTailListRegion_cons_cons_iff {s q b x₀ x₁ : ℝ} {v : List ℝ}
    (hq : 0 < q) :
    rosserStrictTailListRegion s q b (x₀ :: x₁ :: v) ↔
      q < x₁ ∧ x₁ < x₀ ∧ x₀ < min b (s / 3) ∧
        rosserStrictTailListRegion (s - x₀ - x₁) q x₁ v := by
  constructor
  · rintro ⟨_hs, hsorted, hb, hp, ht⟩
    have hpair := List.sortedGT_iff_pairwise.mp hsorted
    simp only [List.pairwise_cons] at hpair
    have hq1 := (hb x₁ (by simp)).1
    have h10 := hpair.1 x₁ (by simp)
    have h0b := (hb x₀ (by simp)).2
    have hhead := hp 0 (by simp) (by simp)
    norm_num at hhead
    refine ⟨hq1, h10, lt_min h0b (by linarith), ?_⟩
    refine ⟨by linarith, List.sortedGT_iff_pairwise.mpr hpair.2.2, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨(hb x (by simp [hx])).1, hpair.2.1 x hx⟩
    · intro i hi heven
      have heven' : Even (i + 2) := heven.add (by norm_num)
      have h := hp (i + 2) (by simp; omega) heven'
      simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ] at h
      linarith
    · simp only [List.sum_cons] at ht
      linarith
  · rintro ⟨hq1, h10, h0, hs, hsorted, hb, hp, ht⟩
    have h0b := (lt_min_iff.mp h0).1
    have hhead : 3 * x₀ < s := by linarith [(lt_min_iff.mp h0).2]
    refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
    · rw [List.sortedGT_iff_pairwise, List.pairwise_cons, List.pairwise_cons,
        ← List.sortedGT_iff_pairwise]
      refine ⟨?_, ?_, hsorted⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h10
        · exact (hb x hx).2.trans h10
      · intro x hx
        exact (hb x hx).2
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ⟨hq1.trans h10, h0b⟩
      · exact ⟨hq1, h10.trans h0b⟩
      · exact ⟨(hb x hx).1, (hb x hx).2.trans (h10.trans h0b)⟩
    · intro i hi heven
      cases i with
      | zero => simpa using hhead
      | succ i =>
        cases i with
        | zero => simp at heven
        | succ i =>
          have heven' : Even i := by simpa [Nat.even_add] using heven
          have h := hp i (by simp at hi ⊢; omega) heven'
          simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
          linarith
    · simp only [List.sum_cons]
      linarith

/-- Removing the first pair preserves the strict terminal and inherited
upper endpoints exactly, including the empty residual tail. -/
theorem mem_rosserOddTailRegion_cons_cons {k : ℕ} {s q b x₀ x₁ : ℝ}
    {v : Fin (2 * k) → ℝ} (hq : 0 < q) :
    Fin.cons x₀ (Fin.cons x₁ v) ∈ rosserOddTailRegion (k + 1) s q b ↔
      q < x₁ ∧ x₁ < x₀ ∧ x₀ < min b (s / 3) ∧
        v ∈ rosserOddTailRegion k (s - x₀ - x₁) q x₁ := by
  rw [mem_rosserOddTailRegion_iff_list]
  simp only [List.ofFn_cons]
  rw [rosserStrictTailListRegion_cons_cons_iff hq, mem_rosserOddTailRegion_iff_list]

/-- Inserting the least coordinate identifies the existing strict odd
region with its actual tail slice. At rank zero the outer cutoff remains. -/
theorem mem_rosserOddLogRegion_snoc {k : ℕ} {s q : ℝ}
    {v : Fin (2 * k) → ℝ} (hs : 0 < s) :
    Fin.snoc v q ∈ rosserOddLogRegion k s ↔
      0 < q ∧ q < 1 ∧ v ∈ rosserOddTailRegion k s q 1 := by
  constructor
  · intro hx
    have hq : 0 < q := by simpa using hx.1
    have hq1 : q < 1 := by
      have h := (hx.2.1.antitone (Fin.zero_le (Fin.last (2 * k)))).trans_lt hx.2.2.1
      simpa using h
    refine ⟨hq, hq1, hs.le, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      simpa using hx.2.1 (show i.castSucc < j.castSucc from hij)
    · intro i
      constructor
      · simpa using hx.2.1 (Fin.castSucc_lt_last i)
      · have h := (hx.2.1.antitone (Fin.zero_le i.castSucc)).trans_lt hx.2.2.1
        simpa using h
    · intro i hi
      simpa [rosserOddLogPrefix] using hx.2.2.2.1 i hi
    · simpa using hx.2.2.2.2
  · rintro ⟨hq, hq1, _hs, hanti, hb, hp, ht⟩
    refine ⟨by simpa using hq, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simpa using hanti (show i < j from hij)
        · simpa using (hb i).1
      · exact False.elim (not_lt_of_ge (Fin.le_last j) hij)
    · rcases Fin.eq_castSucc_or_eq_last (0 : Fin (2 * k + 1)) with ⟨i, hi⟩ | hi
      · rw [hi, Fin.snoc_castSucc]
        exact (hb i).2
      · rw [hi, Fin.snoc_last]
        exact hq1
    · intro i hi
      simpa [rosserOddLogPrefix] using hp i hi
    · simpa using ht

/-- Fixed-parameter tail regions are open, even though the constant
residual-level check is weak. -/
theorem isOpen_rosserOddTailRegion (k : ℕ) (s q b : ℝ) :
    IsOpen (rosserOddTailRegion k s q b) := by
  by_cases hs : 0 ≤ s
  · have hb : IsOpen {v : Fin (2 * k) → ℝ | ∀ i, q < v i ∧ v i < b} := by
      simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact (isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i) continuous_const)
    have hp : IsOpen {v : Fin (2 * k) → ℝ | ∀ i : Fin (2 * k), Even i.val →
        (∑ j : Fin (2 * k) with j.val < i.val, v j) + 3 * v i < s} := by
      simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro _hi
      apply isOpen_lt _ continuous_const
      fun_prop
    have ht : IsOpen {v : Fin (2 * k) → ℝ | s < (∑ i, v i) + 3 * q} := by
      apply isOpen_lt continuous_const
      fun_prop
    simpa only [rosserOddTailRegion, hs, true_and, Set.ofPred_and] using
      (isOpen_strictAnti_fin (2 * k)).inter (hb.inter (hp.inter ht))
  · simp [rosserOddTailRegion, hs]

theorem measurableSet_rosserOddTailRegion (k : ℕ) (s q b : ℝ) :
    MeasurableSet (rosserOddTailRegion k s q b) :=
  (isOpen_rosserOddTailRegion k s q b).measurableSet

/-- The fixed terminal coordinate bounds every reciprocal away from its
singular point whenever it is positive. -/
theorem rosserOddTailRegion_subset_Icc (k : ℕ) (s q b : ℝ) :
    rosserOddTailRegion k s q b ⊆ Set.univ.pi (fun _ => Set.Icc q b) := by
  intro v hv
  exact Set.mem_pi.mpr (fun i _ => ⟨(hv.2.2.1 i).1.le, (hv.2.2.1 i).2.le⟩)

theorem isCompact_rosserOddTailBox (k : ℕ) (q b : ℝ) :
    IsCompact (Set.univ.pi (fun _ : Fin (2 * k) => Set.Icc q b)) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

end

end ImbalancedChen
