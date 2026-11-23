import ImbalancedChen.P2WuProductInnerUnsiftedLoss
import ImbalancedChen.P4BSmoothGateUpperStep

/-!
Source only, uncompiled.

On an original Wu convolution slot the mask is V/Δ ≤ p < V. Remove
only its upper inequality in the native label construction, then recover
the original family by testing the same slot of the complete prime word.
The strengthened fibre, ordered prefix and canonical tail all stay in
the construction. The smooth outer factor equals one at p = V.
-/
namespace ImbalancedChen.P2WuOriginalWindowUpperWall

noncomputable section
open Classical Finset Wu2008DoubleSieve
open scoped ContDiff
open P2NativeOmega3ExpandedPrimeWords P2NativeOmega3RankTupleReceiver
open P4B

/-- On a word with positive prime slots and product at most N, the
new finite upper endpoint is strictly above the physical coordinate. -/
def openedWindows {i : ℕ} (N : ℕ) (Δ : ℝ) (V : Fin i → ℝ) (j l : Fin i) :
    Finset ℕ :=
  primeWindow N (V l / Δ) (if l = j then max (V l) ((N : ℝ) + 1) else V l)

def openedFamily (δ : ℝ) (r N : ℕ) (b : BoxIndex) (j : Fin b.1) :
    Finset (Fin r → Fin (N+1)) :=
  family N δ 3 (16/5) (openedWindows N b.2.1 b.2.2 j) r

private theorem opened_prime {i N : ℕ} {Δ : ℝ} {V : Fin i → ℝ}
    (j l : Fin i) (p : ℕ) (hp : p ∈ openedWindows N Δ V j l) : p.Prime :=
  (mem_primeWindow.mp hp).1

theorem opened_product_cap {δ : ℝ} {r N : ℕ} (b : BoxIndex) (j : Fin b.1) :
    ∀ u ∈ openedFamily δ r N b j, Part3.labelledProduct u ≤ N :=
  family_product_cap (opened_prime j)

/-- Read an old coordinate of the encoded tuple, without decoding the
product. In particular equal prime values at distinct slots remain distinct
positions. A rank too short to contain this coordinate has no such label. -/
theorem read_prefix_slot {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    (hW : ∀ l p, p ∈ W l → p.Prime) {a : ExpandedLabel i}
    (ha : a ∈ rankLabels N δ s t W r) (j : Fin i) :
    ∃ h : j.val < r, (tuple N r a ⟨j.val,h⟩).val = a.1 j := by
  have hlen := (rank_data ha).2
  simp only [primeWord, List.length_append, List.length_ofFn, List.length_cons,
    List.length_nil] at hlen
  have hj := j.isLt
  have hr : j.val < r := by omega
  refine ⟨hr,?_⟩
  have hread := congrArg (fun w : List ℕ => w[j.val]?) (tuple_word hW ha)
  have hpre : j.val < (List.ofFn a.1).length := by simpa only [List.length_ofFn] using hj
  simpa only [primeWord, List.append_assoc, List.getElem?_append_left hpre,
    List.getElem?_ofFn, dif_pos hr, dif_pos hj, Option.some.injEq] using hread

/-- The rank, complete tail and its strengthened native membership do not
change when the same ordered prefix belongs to a second set of windows. -/
private theorem change_windows {i N r : ℕ} {δ s t : ℝ} {W W' : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (ha : a ∈ rankLabels N δ s t W r)
    (hv : ∀ l, a.1 l ∈ W' l) : a ∈ rankLabels N δ s t W' r := by
  obtain ⟨he,hlen⟩ := rank_data ha
  exact mem_filter.mpr ⟨mem_sigma.mpr
    ⟨Fintype.mem_piFinset.mpr hv,(mem_sigma.mp he).2⟩,hlen⟩

theorem indexed_subset_opened {k r N : ℕ} {δ : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (j : Fin b.1) :
    indexedFamily k δ r N b ⊆ openedFamily δ r N b j := by
  rw [indexedFamily, if_pos hb]
  intro u hu
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  refine mem_image.mpr ⟨a,change_windows ha ?_,rfl⟩
  intro l
  obtain ⟨hp,hcop,hlo,hhi⟩ := old_window_geometry (rank_data ha).1 l
  apply mem_primeWindow.mpr
  refine ⟨hp,hcop,hlo,?_⟩
  by_cases hl : l = j
  · simpa only [if_pos hl] using hhi.trans_le (le_max_left _ ((N : ℝ)+1))
  · simpa only [if_neg hl] using hhi

/-- Reverse membership on the opened physical grid. The witness kept on
the right-to-left implication is the very same expanded label, with the
same distinguished p1,p2,p3, integer tail and the same original rank. -/
theorem indexed_iff_slot {k r N : ℕ} {δ : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (j : Fin b.1)
    {u : Fin r → Fin (N+1)} (hu : u ∈ openedFamily δ r N b j) :
    u ∈ indexedFamily k δ r N b ↔
      ∃ h : j.val < r, ((u ⟨j.val,h⟩).val : ℝ) < b.2.2 j := by
  rw [indexedFamily, if_pos hb]
  constructor
  · intro hs
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hs
    obtain ⟨h,he⟩ := read_prefix_slot
      (fun l p hp => (mem_convolutionWuWindows.mp hp).1) ha j
    refine ⟨h,?_⟩
    rw [he]
    exact (old_window_geometry (rank_data ha).1 j).2.2.2
  · rintro ⟨h,hupper⟩
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
    obtain ⟨_,he⟩ := read_prefix_slot (opened_prime j) ha j
    rw [he] at hupper
    refine mem_image.mpr ⟨a,change_windows ha ?_,rfl⟩
    intro l
    have hm := Fintype.mem_piFinset.mp (expanded_data (rank_data ha).1).1 l
    obtain ⟨hp,hcop,hlo,hhi⟩ := mem_primeWindow.mp hm
    apply mem_convolutionWuWindows.mpr
    refine ⟨hp,hcop,hlo,?_⟩
    by_cases hl : l = j
    · subst l
      exact hupper
    · simpa only [if_neg hl] using hhi

/-- Relative-width C-infinity outer approximation to the wall log p < log V.
It is a smooth physical-coordinate function, also across p = 0. -/
def upperProfile {r : ℕ} (V w : ℝ) (l : Fin r) (x : Fin r → ℝ) : ℝ :=
  smoothGateUpperStep (V*w) (V - x l)

theorem upperProfile_smooth {r : ℕ} (V w : ℝ) (l : Fin r) :
    ContDiff ℝ ∞ (upperProfile V w l) :=
  (contDiff_smoothGateUpperStep (V*w)).comp
    (contDiff_const.sub (contDiff_apply ℝ ℝ l))

theorem upperProfile_one {r : ℕ} {V w : ℝ} (hV : 0 < V) (hw : 0 < w)
    (l : Fin r) (x : Fin r → ℝ) (hx : x l ≤ V) : upperProfile V w l x = 1 :=
  smoothGateUpperStep_eq_one (mul_pos hV hw) (sub_nonneg.mpr hx)

theorem upperProfile_zero {r : ℕ} {V w : ℝ} (hV : 0 < V) (hw : 0 < w)
    (l : Fin r) (x : Fin r → ℝ) (hx : V*(1+w) ≤ x l) : upperProfile V w l x = 0 :=
  smoothGateUpperStep_eq_zero (mul_pos hV hw) (by nlinarith only [hx])

theorem upperProfile_transition {r : ℕ} {V w : ℝ} (hV : 0 < V) (hw : 0 < w)
    (l : Fin r) (x : Fin r → ℝ) (hlo : V < x l) (hhi : x l < V*(1+w)) :
    0 < upperProfile V w l x ∧ upperProfile V w l x < 1 := by
  have hb := smoothGateUpperStep_bounds (V*w) (V-x l)
  constructor
  · apply lt_of_le_of_ne hb.1
    intro hz
    have h := (smoothGateUpperStep_eq_zero_iff (mul_pos hV hw)).mp hz.symm
    nlinarith only [hhi,h]
  · apply lt_of_le_of_ne hb.2
    intro ho
    have h := (smoothGateUpperStep_eq_one_iff (mul_pos hV hw)).mp ho
    linarith only [hlo,h]

/-- All other masks are exactly the original ones. The sole new real
factor is sampled at the physical prime in the chosen old slot. -/
def wallWeight (δ w : ℝ) (r N : ℕ) (b : BoxIndex) (j : Fin b.1) :
    (Fin r → Fin (N+1)) → ℝ :=
  p5z_markedPhysicalWeight (openedFamily δ r N b j) (fun u =>
    if h : j.val < r then
      upperProfile (b.2.2 j) w ⟨j.val,h⟩ (fun l => ((u l).val : ℝ))
    else 0)

theorem wallWeight_bounds (δ w : ℝ) (r N : ℕ) (b : BoxIndex) (j : Fin b.1)
    (u : Fin r → Fin (N+1)) :
    0 ≤ wallWeight δ w r N b j u ∧ wallWeight δ w r N b j u ≤ 1 := by
  unfold wallWeight p5z_markedPhysicalWeight
  split_ifs
  · exact smoothGateUpperStep_bounds _ _
  all_goals norm_num

theorem wallWeight_one {k r N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (j : Fin b.1)
    (hV : 0 < b.2.2 j) (hw : 0 < w) {u : Fin r → Fin (N+1)}
    (hu : u ∈ indexedFamily k δ r N b) : wallWeight δ w r N b j u = 1 := by
  have ho := indexed_subset_opened hb j hu
  obtain ⟨h,hi⟩ := (indexed_iff_slot hb j ho).mp hu
  simp only [wallWeight, p5z_markedPhysicalWeight, if_pos ho, dif_pos h]
  exact upperProfile_one hV hw _ _ hi.le

/-- The discarded strict endpoint p = V is inside the leakage collar,
and the far endpoint p = V(1+w) has zero weight. -/
theorem outside_nonzero {k r N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (j : Fin b.1)
    (hV : 0 < b.2.2 j) (hw : 0 < w) {u : Fin r → Fin (N+1)}
    (hs : u ∉ indexedFamily k δ r N b) (hn : wallWeight δ w r N b j u ≠ 0) :
    Part3.labelledProduct u ≤ N ∧ ∃ h : j.val < r,
      b.2.2 j ≤ ((u ⟨j.val,h⟩).val : ℝ) ∧
        ((u ⟨j.val,h⟩).val : ℝ) < b.2.2 j * (1+w) := by
  have ho : u ∈ openedFamily δ r N b j := by
    by_contra hh
    exact hn (by simp only [wallWeight, p5z_markedPhysicalWeight, if_neg hh])
  have hr : j.val < r := by
    by_contra hh
    exact hn (by simp only [wallWeight, p5z_markedPhysicalWeight, if_pos ho, dif_neg hh])
  refine ⟨opened_product_cap b j u ho,hr,?_,?_⟩
  · exact le_of_not_gt (fun ht => hs ((indexed_iff_slot hb j ho).mpr ⟨hr,ht⟩))
  · by_contra hh
    apply hn
    simp only [wallWeight, p5z_markedPhysicalWeight, if_pos ho, dif_pos hr]
    exact upperProfile_zero hV hw _ _ (le_of_not_gt hh)

end
end ImbalancedChen.P2WuOriginalWindowUpperWall
