import ImbalancedChen.RosserOddTailRegion

/-!
# Strict even-dimensional Rosser boundary regions

The largest coordinate is peeled off before applying the existing odd
region at the residual level. The equivalent literal description has
strict cubic-prefix tests at odd indices and a strict terminal crossing.
The total nonterminal budget is derived, not imposed. At a fixed level
`s>1`, every coordinate lies in a compact box bounded away from zero.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set MeasureTheory

def rosserEvenLogPrefix (k : ℕ) (x : Fin (2 * k + 2) → ℝ)
    (i : Fin (2 * k + 1)) : ℝ :=
  ∑ j : Fin (2 * k + 1) with j.val < i.val, x j.castSucc

/-- Removing the largest coordinate gives the odd residual region. Its
upper-one condition is redundant under the full strict ordering. -/
def rosserEvenLogRegion (k : ℕ) (s : ℝ) : Set (Fin (2 * k + 2) → ℝ) :=
  {x | StrictAnti x ∧ x 0 < 1 ∧ Fin.tail x ∈ rosserOddLogRegion k (s - x 0)}

theorem rosserEvenLogPrefix_cons_succ (k : ℕ) (t : ℝ)
    (v : Fin (2 * k + 1) → ℝ) (i : Fin (2 * k)) :
    rosserEvenLogPrefix k (Fin.cons t v) i.succ = t + rosserOddLogPrefix k v i := by
  simp [rosserEvenLogPrefix, rosserOddLogPrefix, Finset.sum_filter, Fin.sum_univ_succ]

theorem rosserEvenLogTail_sum_cons (k : ℕ) (t : ℝ)
    (v : Fin (2 * k + 1) → ℝ) :
    (∑ i : Fin (2 * k + 1), ((Fin.cons t v : Fin (2 * k + 2) → ℝ) i.castSucc)) =
      t + ∑ i : Fin (2 * k), v i.castSucc := by
  simp [Fin.sum_univ_succ]

/-- Literal strict lower-boundary geometry: tests occur at odd indices of
the nonterminal coordinates. No total-sum gate is included as a premise. -/
theorem mem_rosserEvenLogRegion_iff {k : ℕ} {s : ℝ} {x : Fin (2 * k + 2) → ℝ} :
    x ∈ rosserEvenLogRegion k s ↔
      0 < x (Fin.last (2 * k + 1)) ∧ StrictAnti x ∧ x 0 < 1 ∧
        (∀ i : Fin (2 * k + 1), Odd i.val →
          rosserEvenLogPrefix k x i + 3 * x i.castSucc < s) ∧
        s < (∑ i : Fin (2 * k + 1), x i.castSucc) + 3 * x (Fin.last (2 * k + 1)) := by
  have hpref (i : Fin (2 * k)) :
      rosserEvenLogPrefix k x i.succ = x 0 + rosserOddLogPrefix k (Fin.tail x) i := by
    simpa only [Fin.cons_self_tail] using
      rosserEvenLogPrefix_cons_succ k (x 0) (Fin.tail x) i
  have hsum : (∑ i : Fin (2 * k + 1), x i.castSucc) =
      x 0 + ∑ i : Fin (2 * k), Fin.tail x i.castSucc := by
    simpa only [Fin.cons_self_tail] using rosserEvenLogTail_sum_cons k (x 0) (Fin.tail x)
  constructor
  · rintro ⟨hanti, ht, hq, _hantiRest, _htRest, hp, hterm⟩
    refine ⟨by simpa [Fin.tail] using hq, hanti, ht, ?_, ?_⟩
    · intro i hi
      cases i using Fin.cases with
      | zero => simp at hi
      | succ i =>
          have heven : Even i.val := by
            simp only [Fin.val_succ] at hi
            have := Nat.odd_iff.mp hi
            exact Nat.even_iff.mpr (by omega)
          have h := hp i heven
          rw [hpref]
          change rosserOddLogPrefix k (Fin.tail x) i + 3 * x i.castSucc.succ < s - x 0 at h
          have hidx : i.succ.castSucc = i.castSucc.succ := by ext; rfl
          rw [hidx]
          linarith
    · rw [hsum]
      change s - x 0 < (∑ i : Fin (2 * k), Fin.tail x i.castSucc) +
        3 * x (Fin.last (2 * k + 1)) at hterm
      linarith
  · rintro ⟨hq, hanti, ht, hp, hterm⟩
    refine ⟨hanti, ht, by simpa [Fin.tail] using hq, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact hanti (Fin.succ_lt_succ_iff.mpr hij)
    · exact (hanti (show (0 : Fin (2 * k + 2)) < (0 : Fin (2 * k + 1)).succ by simp)).trans ht
    · intro i hi
      have hodd : Odd i.succ.val := by
        change Odd (i.val + 1)
        have := Nat.even_iff.mp hi
        exact Nat.odd_iff.mpr (by omega)
      have h := hp i.succ hodd
      rw [hpref] at h
      change rosserOddLogPrefix k (Fin.tail x) i + 3 * x i.castSucc.succ < s - x 0
      have hidx : i.succ.castSucc = i.castSucc.succ := by ext; rfl
      rw [hidx] at h
      linarith
    · rw [hsum] at hterm
      change s - x 0 < (∑ i : Fin (2 * k), Fin.tail x i.castSucc) +
        3 * x (Fin.last (2 * k + 1))
      linarith

/-- Peeling the greatest coordinate and retaining the least coordinate
gives the exact strict odd tail slice, including an empty middle tail. -/
theorem mem_rosserEvenLogRegion_cons_snoc {k : ℕ} {s t q : ℝ}
    {v : Fin (2 * k) → ℝ} (hs : 1 < s) :
    Fin.cons t (Fin.snoc v q) ∈ rosserEvenLogRegion k s ↔
      0 < q ∧ q < t ∧ t < 1 ∧ v ∈ rosserOddTailRegion k (s - t) q t := by
  constructor
  · rintro ⟨hanti, ht, hrest⟩
    have ht1 : t < 1 := by simpa using ht
    have hres : 0 < s - t := by linarith
    have hrest' : Fin.snoc v q ∈ rosserOddLogRegion k (s - t) := by simpa using hrest
    obtain ⟨hq, _hq1, hv⟩ := (mem_rosserOddLogRegion_snoc hres).mp hrest'
    have hqt : q < t := by
      simpa using hanti (show (0 : Fin (2 * k + 2)) < Fin.last (2 * k + 1) by
        change 0 < 2 * k + 1
        omega)
    refine ⟨hq, hqt, ht1, hv.1, hv.2.1, ?_, hv.2.2.2⟩
    intro i
    refine ⟨(hv.2.2.1 i).1, ?_⟩
    simpa using hanti (show (0 : Fin (2 * k + 2)) < i.castSucc.succ by simp)
  · rintro ⟨hq, hqt, ht1, hv⟩
    have hres : 0 < s - t := by linarith
    have hv1 : v ∈ rosserOddTailRegion k (s - t) q 1 :=
      ⟨hv.1, hv.2.1, fun i => ⟨(hv.2.2.1 i).1, (hv.2.2.1 i).2.trans ht1⟩,
        hv.2.2.2⟩
    have hrest : Fin.snoc v q ∈ rosserOddLogRegion k (s - t) :=
      (mem_rosserOddLogRegion_snoc hres).mpr ⟨hq, hqt.trans ht1, hv1⟩
    refine ⟨?_, by simpa using ht1, by simpa using hrest⟩
    intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (lt_irrefl _ hij).elim
        | succ j =>
            rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
            · simpa using (hv.2.2.1 j).2
            · simpa using hqt
    | succ i =>
        cases j using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
        | succ j =>
            simpa using hrest.2.1 (Fin.succ_lt_succ_iff.mp hij)

/-- The nonterminal sum is strictly below the level; the geometric
residual of the odd tail supplies this gate rather than assuming it. -/
theorem rosserEvenLogRegion_tail_sum_lt {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 2) → ℝ} (hs : 1 < s) (hx : x ∈ rosserEvenLogRegion k s) :
    (∑ i : Fin (2 * k + 1), x i.castSucc) < s := by
  have hres : 0 < s - x 0 := by linarith [hx.2.1]
  have h := rosserOddLogRegion_tail_sum_lt hres hx.2.2
  have hsum := rosserEvenLogTail_sum_cons k (x 0) (Fin.tail x)
  rw [Fin.cons_self_tail] at hsum
  rw [hsum]
  linarith

theorem rosserEvenLogRegion_terminal_lower {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 2) → ℝ} (hs : 1 < s) (hx : x ∈ rosserEvenLogRegion k s) :
    (s - 1) / 3 ^ (k + 1) < x (Fin.last (2 * k + 1)) := by
  have hres : 0 < s - x 0 := by linarith [hx.2.1]
  have h := rosserOddLogRegion_terminal_lower hres.le hx.2.2
  have hcmp : (s - 1) / 3 ^ (k + 1) < (s - x 0) / 3 ^ (k + 1) :=
    (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith [hx.2.1])
  exact hcmp.trans (by simpa [Fin.tail] using h)

theorem rosserEvenLogRegion_bounds {k : ℕ} {s : ℝ}
    {x : Fin (2 * k + 2) → ℝ} (hs : 1 < s) (hx : x ∈ rosserEvenLogRegion k s) :
    ∀ i, (s - 1) / 3 ^ (k + 1) < x i ∧ x i < 1 := by
  intro i
  exact ⟨(rosserEvenLogRegion_terminal_lower hs hx).trans_le (hx.1.antitone (Fin.le_last i)),
    (hx.1.antitone (Fin.zero_le i)).trans_lt hx.2.1⟩

/-- A fixed compact positive box contains the entire even region. -/
theorem rosserEvenLogRegion_subset_positive_box (k : ℕ) (s : ℝ) (hs : 1 < s) :
    rosserEvenLogRegion k s ⊆
      Set.univ.pi (fun _ => Set.Icc ((s - 1) / 3 ^ (k + 1)) 1) := by
  intro x hx
  exact Set.mem_pi.mpr (fun i _ =>
    ⟨(rosserEvenLogRegion_bounds hs hx i).1.le, (rosserEvenLogRegion_bounds hs hx i).2.le⟩)

theorem isCompact_rosserEvenLogBox (k : ℕ) (s : ℝ) :
    IsCompact (Set.univ.pi (fun _ : Fin (2 * k + 2) =>
      Set.Icc ((s - 1) / 3 ^ (k + 1)) 1)) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem continuous_rosserEvenLogPrefix (k : ℕ) (i : Fin (2 * k + 1)) :
    Continuous (fun x : Fin (2 * k + 2) → ℝ => rosserEvenLogPrefix k x i) := by
  unfold rosserEvenLogPrefix
  fun_prop

/-- The literal geometry has only finitely many strict inequalities. -/
theorem isOpen_rosserEvenLogRegion (k : ℕ) (s : ℝ) : IsOpen (rosserEvenLogRegion k s) := by
  have hprefix : IsOpen {x : Fin (2 * k + 2) → ℝ |
      ∀ i : Fin (2 * k + 1), Odd i.val → rosserEvenLogPrefix k x i + 3 * x i.castSucc < s} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _hi
    exact isOpen_lt ((continuous_rosserEvenLogPrefix k i).add
      (continuous_const.mul (continuous_apply i.castSucc))) continuous_const
  have hsum : Continuous (fun x : Fin (2 * k + 2) → ℝ =>
      (∑ i : Fin (2 * k + 1), x i.castSucc) + 3 * x (Fin.last (2 * k + 1))) := by fun_prop
  have heq : rosserEvenLogRegion k s =
      {x | 0 < x (Fin.last (2 * k + 1)) ∧ StrictAnti x ∧ x 0 < 1 ∧
        (∀ i : Fin (2 * k + 1), Odd i.val → rosserEvenLogPrefix k x i + 3 * x i.castSucc < s) ∧
        s < (∑ i : Fin (2 * k + 1), x i.castSucc) + 3 * x (Fin.last (2 * k + 1))} :=
    Set.ext (fun _ => mem_rosserEvenLogRegion_iff)
  rw [heq]
  exact (isOpen_lt continuous_const (continuous_apply (Fin.last (2 * k + 1)))).inter
    ((isOpen_strictAnti_fin (2 * k + 2)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        (hprefix.inter (isOpen_lt continuous_const hsum))))

theorem measurableSet_rosserEvenLogRegion (k : ℕ) (s : ℝ) :
    MeasurableSet (rosserEvenLogRegion k s) := (isOpen_rosserEvenLogRegion k s).measurableSet

end

end ImbalancedChen
