import ImbalancedChen.ActualFrozenSelectedPairSlots

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Whole-box allocation with an arbitrary ORIGINAL selected list. The two
branches are chosen from endpoint products once, before the actual tuple
or an arithmetic test. This extends the selected-pair algorithm to the
actual upper fifth masks, whose selected set need not have two elements.
It is a numerical helper; the companion source theorem derives both square
supports and the critical interval from the original upper policy5 leaf.
-/
namespace ImbalancedChen.P4BUpperSelectedBoxCapacity
noncomputable section
open scoped Classical
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def endpoint {α : Type*} (upper : α → ℕ) (slots : List α) : ℝ :=
  (slots.map (fun i => (upper i : ℝ))).prod

theorem endpoint_eq_cast {α : Type*} (upper : α → ℕ) (slots : List α) :
    endpoint upper slots = ((slots.map upper).prod : ℝ) := by
  simpa only [endpoint,List.map_map,Function.comp_def] using
    actualNatList_cast_prod (slots.map upper)

def groups {α : Type*} (D A : ℝ) (upper : α → ℕ)
    (selected remainder whole : List α) : List α × List α × List α :=
  if 1 ≤ D / (A * endpoint upper selected) then
    let ac := actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A remainder
    (ac.1, selected, ac.2)
  else
    let ab := actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A whole
    (ab.1, ab.2, [])

def endpoints {α : Type*} (D A : ℝ) (upper : α → ℕ)
    (selected remainder whole : List α) : ℝ × ℝ × ℝ :=
  let g := groups D A upper selected remainder whole
  (endpoint upper g.1, endpoint upper g.2.1, endpoint upper g.2.2)

theorem groups_partition {α : Type*} (D A : ℝ) (upper : α → ℕ)
    (selected remainder whole : List α) (hp : (selected ++ remainder).Perm whole) :
    let g := groups D A upper selected remainder whole
    (g.1 ++ (g.2.1 ++ g.2.2)).Perm whole := by
  unfold groups
  split_ifs with hc
  · let ac := actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A remainder
    have hm : (ac.1 ++ selected ++ ac.2).Perm (selected ++ (ac.1 ++ ac.2)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := ac.1) (l₂ := selected)).append_right ac.2
    simpa only [List.append_assoc] using hm.trans (((actualTwoCapacityGreedy_partition
      (fun i => (upper i : ℝ)) A remainder).perm.append_left selected).trans hp)
  · simpa only [List.append_nil] using
      (actualTwoCapacityGreedy_partition (fun i => (upper i : ℝ)) A whole).perm

/-- Every coordinatewise smaller actual tuple uses these SAME slot lists.
No assumption that a tuple-dependent decision fibre is a box is made. -/
theorem actual_products {α : Type*} (D A : ℝ) (upper actual : α → ℕ)
    (selected remainder whole : List α) (hp : (selected ++ remainder).Perm whole)
    (hs : ∀ i ∈ whole, actual i ≤ upper i) :
    let g := groups D A upper selected remainder whole
    let abc := endpoints D A upper selected remainder whole
    (g.1.map actual).prod * (g.2.1.map actual).prod * (g.2.2.map actual).prod =
      (whole.map actual).prod ∧
    ((g.1.map actual).prod : ℝ) ≤ abc.1 ∧
    ((g.2.1.map actual).prod : ℝ) ≤ abc.2.1 ∧
    ((g.2.2.map actual).prod : ℝ) ≤ abc.2.2 := by
  let g := groups D A upper selected remainder whole
  have hg := groups_partition D A upper selected remainder whole hp
  have hbound (l : List α) (hl : ∀ i ∈ l, i ∈ whole) :
      ((l.map actual).prod : ℝ) ≤ endpoint upper l := by
    have h := List.prod_map_le_prod_map₀ (fun i => (actual i : ℝ))
      (fun i => (upper i : ℝ)) (fun i _ => Nat.cast_nonneg _)
      (fun i hi => by exact_mod_cast hs i (hl i hi))
    simpa only [endpoint, ← actualNatList_cast_prod (l.map actual),
      List.map_map, Function.comp_def] using h
  refine ⟨?_, hbound g.1 ?_, hbound g.2.1 ?_, hbound g.2.2 ?_⟩
  · simpa only [List.map_append, List.prod_append, mul_assoc] using (hg.map actual).prod_eq
  · intro i hi
    exact hg.mem_iff.mp (by simp only [List.mem_append]; exact Or.inl hi)
  · intro i hi
    exact hg.mem_iff.mp (by simp only [List.mem_append]; exact Or.inr (Or.inl hi))
  · intro i hi
    exact hg.mem_iff.mp (by simp only [List.mem_append]; exact Or.inr (Or.inr hi))

private theorem endpoint_support {α : Type*} (upper : α → ℕ) (D : ℝ) (l : List α)
    (h : actualDwellSupport D (l.map upper)) :
    PrefixSquareBound (fun i => (upper i : ℝ)) D l := by
  intro i hi
  have hh := h i (by simpa only [List.length_map] using hi)
  simpa only [← List.map_take, List.map_map, List.getElem_map, Function.comp_def] using hh

theorem endpoint_positive {α : Type*} (upper : α → ℕ) (l : List α)
    (h : ∀ i ∈ l, 0 < upper i) : 0 < endpoint upper l := by
  rw [endpoint_eq_cast]
  exact_mod_cast (List.prod_pos (by simpa only [List.forall_mem_map] using h))

/-- Both capacity cases are proved from the two ORIGINAL endpoint square
families. In the below-one case the whole vector is rerun and group3 is empty. -/
theorem capacities {α : Type*} {D A : ℝ} (upper : α → ℕ)
    (selected remainder whole : List α)
    (hS : 0 < endpoint upper selected) (hA : 1 ≤ A) (hAD : A ≤ D)
    (hfull : actualDwellSupport D (whole.map upper))
    (hselected : actualDwellSupport (D / endpoint upper selected) (remainder.map upper)) :
    let abc := endpoints D A upper selected remainder whole
    abc.1 ≤ A ∧
      (if 1 ≤ D / (A * endpoint upper selected) then
        abc.2.1 = endpoint upper selected ∧ abc.2.2 ≤ D / (A * endpoint upper selected)
      else abc.2.2 = 1 ∧ abc.2.1 ≤ D / A ∧ D / A < endpoint upper selected) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  unfold endpoints groups
  split_ifs with hc
  · have hsplit : A * (D / (A * endpoint upper selected)) = D / endpoint upper selected := by
      field_simp [hAp.ne', hS.ne']
      <;> ring
    have hs : PrefixSquareBound (fun i => (upper i : ℝ))
        (A * (D / (A * endpoint upper selected))) remainder := by
      rw [hsplit]
      exact endpoint_support upper _ remainder hselected
    have hg := actualTwoCapacityGreedy_correct (fun i => (upper i : ℝ)) hA hc remainder hs
    exact ⟨hg.2.1, rfl, hg.2.2⟩
  · have hB : 1 ≤ D / A := (le_div_iff₀ hAp).mpr (by simpa using hAD)
    have hsplit : A * (D / A) = D := by
      field_simp [hAp.ne']
      <;> ring
    have hs : PrefixSquareBound (fun i => (upper i : ℝ)) (A * (D / A)) whole := by
      rw [hsplit]
      exact endpoint_support upper _ whole hfull
    have hg := actualTwoCapacityGreedy_correct (fun i => (upper i : ℝ)) hA hB whole hs
    refine ⟨hg.2.1, rfl, hg.2.2, ?_⟩
    have h := (div_lt_one (mul_pos hAp hS)).mp (lt_of_not_ge hc)
    exact (div_lt_iff₀ hAp).mpr (by nlinarith)

/-- The three real endpoint monomials, for arbitrary selected masks.
All coordinates are whole-slot products. The original selected factor is
kept only in the successful capacity branch. -/
theorem monomials {α : Type*} {x d theta alpha A : ℝ}
    (hx : 1 < x) (hd : 0 < d) (hdsmall : d ≤ 1/12)
    (hthlo : 1/2 ≤ theta) (hthhi : theta ≤ 5/8)
    (upper : α → ℕ) (selected remainder whole : List α)
    (hp : (selected ++ remainder).Perm whole) (hpositive : ∀ i ∈ whole, 0 < upper i)
    (hA : 1 ≤ A) (hAu : A ≤ x^(1/3-d/2))
    (hfull : actualDwellSupport (x^(theta-2*d)) (whole.map upper))
    (hselected : actualDwellSupport (x^(theta-2*d) / endpoint upper selected) (remainder.map upper))
    (hlo : x^(2*theta-1) ≤ endpoint upper selected)
    (hhi : endpoint upper selected ≤ x^actualSelectedSubproductUpper alpha theta) :
    let abc := endpoints (x^(theta-2*d)) A upper selected remainder whole
    abc.1 ≤ A ∧ A^2*abc.2.1*abc.2.2^2 ≤ x^(1-3*d) ∧
      x^(7*alpha/32)*A*abc.1*abc.2.1^5*abc.2.2^2 ≤ x^(2-4*d) ∧
      (A*abc.2.2/abc.2.1)^(7/16 : ℝ)*A*abc.1*abc.2.1^5*abc.2.2^2 ≤ x^(2-39*d/8) := by
  let D := x^(theta-2*d)
  let abc := endpoints D A upper selected remainder whole
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hSp : 0 < endpoint upper selected := endpoint_positive upper selected
    (fun i hi => hpositive i (hp.mem_iff.mp (List.mem_append_left _ hi)))
  have hAD : A ≤ D := hAu.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  have hcaps := capacities upper selected remainder whole hSp hA hAD hfull hselected
  have hg := groups_partition D A upper selected remainder whole hp
  have hpos (l : List α) (hl : ∀ i ∈ l, i ∈ whole) : 0 < endpoint upper l :=
    endpoint_positive upper l (fun i hi => hpositive i (hl i hi))
  have hap : 0 < abc.1 := hpos _ (fun i hi => hg.mem_iff.mp (by
    simp only [List.mem_append]; exact Or.inl hi))
  have hbp : 0 < abc.2.1 := hpos _ (fun i hi => hg.mem_iff.mp (by
    simp only [List.mem_append]; exact Or.inr (Or.inl hi)))
  have hcp : 0 < abc.2.2 := hpos _ (fun i hi => hg.mem_iff.mp (by
    simp only [List.mem_append]; exact Or.inr (Or.inr hi)))
  by_cases hc : 1 ≤ D / (A * endpoint upper selected)
  · have hb := hcaps.2
    rw [if_pos hc] at hb
    have hcap : A*abc.2.1*abc.2.2 ≤ x^(theta-2*d) := by
      rw [hb.1]
      have hh := (le_div_iff₀ (mul_pos hAp hSp)).mp hb.2
      simpa only [D, mul_comm, mul_left_comm, mul_assoc] using hh
    have hm := selectedPair_monomials hx hAp hap hbp hcp hcap
      (by simpa only [hb.1] using hlo) (by simpa only [hb.1] using hhi) hcaps.1
    exact ⟨hcaps.1, hm.1.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)), hm.2⟩
  · have hb := hcaps.2
    rw [if_neg hc] at hb
    have hAB : A*(D/A) = x^(theta-2*d) := by
      dsimp [D]
      field_simp [hAp.ne']
      <;> ring
    have hm := twoFactorRepair_monomials hx hdsmall hthhi hAp
      (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) hAp) hap hbp hAB
      hAu (hb.2.2.le.trans hhi) hcaps.1 hb.2.1
    refine ⟨hcaps.1, ?_⟩
    simpa only [hb.1, one_pow, mul_one] using hm

end
end ImbalancedChen.P4BUpperSelectedBoxCapacity
