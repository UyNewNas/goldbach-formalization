import ImbalancedChen.P3OriginalU5WarmMixedReusedCore

/-!
# Literal warm-cap alphabet and coarse-code stability

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

The finite alphabet is the image of the ACTUAL CapPlan.choose domain,
together with the original seed. Inheritance retains the previous cap.
No later coordinate is read at an earlier prefix, and no acceptance
condition is added to the plan. The cardinal bound is independent of
the real values of the seed and all chosen caps.
-/

namespace ImbalancedChen.P3OriginalU5WarmCapCodeStability

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention

abbrev CapAddress (depth mesh : ℕ) :=
  Unit ⊕ (Fin (depth + 1) × (Fin depth → CellCode mesh × Bool))

def addressedCap {depth mesh : ℕ} (P : CapPlan depth mesh) (seed : ℝ) :
    CapAddress depth mesh → ℝ
  | .inl _ => seed
  | .inr a => (P.choose a.1 a.2).freeze seed

def capAlphabet {depth mesh : ℕ} (P : CapPlan depth mesh) (seed : ℝ) : Finset ℝ :=
  Finset.univ.image (addressedCap P seed)

theorem capAlphabet_card_le {depth mesh : ℕ} (P : CapPlan depth mesh) (seed : ℝ) :
    (capAlphabet P seed).card ≤ Fintype.card (CapAddress depth mesh) := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

theorem seed_mem_capAlphabet {depth mesh : ℕ} (P : CapPlan depth mesh) (seed : ℝ) :
    seed ∈ capAlphabet P seed := by
  exact Finset.mem_image.mpr ⟨Sum.inl (), Finset.mem_univ _, rfl⟩

theorem chosen_freeze_mem_capAlphabet {depth mesh : ℕ} (P : CapPlan depth mesh)
    (seed incoming : ℝ) (hi : incoming ∈ capAlphabet P seed)
    (rank : Fin (depth + 1)) (code : Fin depth → CellCode mesh × Bool) :
    (P.choose rank code).freeze incoming ∈ capAlphabet P seed := by
  cases hc : P.choose rank code with
  | inherit argument => simpa only [hc, CapChoice.freeze] using hi
  | fresh cap argument =>
      apply Finset.mem_image.mpr
      refine ⟨Sum.inr (rank, code), Finset.mem_univ _, ?_⟩
      simp only [addressedCap, hc, CapChoice.freeze]

theorem step_cap_mem_capAlphabet {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seed : ℝ) (H : Trace) (x : ℝ) (hH : H.cap ∈ capAlphabet P seed) :
    (step P a b H x).cap ∈ capAlphabet P seed := by
  change (planChoice P a b (H.word ++ [x])).freeze H.cap ∈ capAlphabet P seed
  unfold planChoice
  split_ifs with hr
  · exact chosen_freeze_mem_capAlphabet P seed H.cap hH _ _
  · exact hH

theorem run_cap_mem_capAlphabet {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seed : ℝ) (H : Trace) (xs : List ℝ)
    (hH : H.cap ∈ capAlphabet P seed) :
    (run P a b H xs).cap ∈ capAlphabet P seed := by
  induction xs generalizing H with
  | nil => exact hH
  | cons x xs ih =>
      exact ih (step P a b H x) (step_cap_mem_capAlphabet P a b seed H x hH)

def coarseWord (a b : ℝ) (mesh : ℕ) (xs : List ℝ) : List (CellCode mesh) :=
  xs.map (exponentCode a b mesh)

private theorem coarseWord_length {a b : ℝ} {mesh : ℕ} {xs ys : List ℝ}
    (h : coarseWord a b mesh xs = coarseWord a b mesh ys) : xs.length = ys.length := by
  simpa only [coarseWord, List.length_map] using congrArg List.length h

/-- The unused padding is exactly the existing top code, with false mark. -/
theorem physicalCode_marked_eq (a b : ℝ) (depth mesh : ℕ) (xs : List ℝ)
    (i : Fin depth) :
    physicalCode a b depth mesh (marked xs) i =
      ((coarseWord a b mesh xs).getD i.val none, false) := by
  simp only [physicalCode, marked, coarseWord, List.getD, List.getElem?_map]
  cases h : xs[i.val]? with
  | none => simp [h, exponentCode, Set.mem_Ico]
  | some x => simp [h]

theorem physicalCode_eq_of_coarseWord {a b : ℝ} {depth mesh : ℕ}
    {xs ys : List ℝ} (h : coarseWord a b mesh xs = coarseWord a b mesh ys) :
    physicalCode a b depth mesh (marked xs) = physicalCode a b depth mesh (marked ys) := by
  funext i
  rw [physicalCode_marked_eq, physicalCode_marked_eq, h]

theorem planChoice_eq_of_coarseWord {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (xs ys : List ℝ)
    (h : coarseWord a b mesh xs = coarseWord a b mesh ys) :
    planChoice P a b xs = planChoice P a b ys := by
  have hlen := coarseWord_length h
  have hx : (marked xs).take xs.length = marked xs := by simp [marked]
  have hy : (marked ys).take ys.length = marked ys := by simp [marked]
  have hc : incomingChoice P a b xs.length (marked xs) =
      incomingChoice P a b ys.length (marked ys) := by
    unfold incomingChoice incomingCode
    rw [hx, hy, hlen, physicalCode_eq_of_coarseWord h]
  by_cases hr : xs.length = 3 ∨ xs.length = 4 ∨ xs.length = 5
  · have hr' : ys.length = 3 ∨ ys.length = 4 ∨ ys.length = 5 := by
      simpa only [hlen] using hr
    simpa only [planChoice, if_pos hr, if_pos hr'] using hc
  · have hr' : ¬(ys.length = 3 ∨ ys.length = 4 ∨ ys.length = 5) := by
      simpa only [hlen] using hr
    simp only [planChoice, if_neg hr, if_neg hr']

/-- Actual cap evolution depends on the actual prefix codes. Accepted
flags and frames are not erased or changed; this theorem only compares caps. -/
theorem run_cap_eq_of_coarseWord {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (xs ys : List ℝ) (H K : Trace)
    (hcap : H.cap = K.cap)
    (hword : coarseWord a b mesh H.word = coarseWord a b mesh K.word)
    (hxy : coarseWord a b mesh xs = coarseWord a b mesh ys) :
    (run P a b H xs).cap = (run P a b K ys).cap := by
  induction xs generalizing ys H K with
  | nil =>
      have hy : ys = [] := by simpa only [coarseWord, List.map_nil, List.map_eq_nil_iff] using hxy.symm
      subst ys
      exact hcap
  | cons x xs ih =>
      cases ys with
      | nil => simp [coarseWord] at hxy
      | cons y ys =>
          have hhead : exponentCode a b mesh x = exponentCode a b mesh y :=
            (List.cons.inj hxy).1
          have htail : coarseWord a b mesh xs = coarseWord a b mesh ys :=
            (List.cons.inj hxy).2
          have hnew : coarseWord a b mesh (H.word ++ [x]) =
              coarseWord a b mesh (K.word ++ [y]) := by
            change H.word.map _ = K.word.map _ at hword
            simp only [coarseWord, List.map_append, List.map_cons, List.map_nil, hword, hhead]
          have hc := planChoice_eq_of_coarseWord P a b (H.word ++ [x]) (K.word ++ [y]) hnew
          have hnextcap : (step P a b H x).cap = (step P a b K y).cap := by
            change (planChoice P a b (H.word ++ [x])).freeze H.cap =
              (planChoice P a b (K.word ++ [y])).freeze K.cap
            rw [hc, hcap]
          have hnextword : coarseWord a b mesh (step P a b H x).word =
              coarseWord a b mesh (step P a b K y).word := hnew
          exact ih ys (step P a b H x) (step P a b K y) hnextcap hnextword htail

theorem run_prefix_cap_eq_of_coarseWord {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (H : Trace) (xs ys : List ℝ)
    (hxy : coarseWord a b mesh xs = coarseWord a b mesh ys) (k : ℕ) :
    (run P a b H (xs.take k)).cap = (run P a b H (ys.take k)).cap := by
  apply run_cap_eq_of_coarseWord P a b _ _ H H rfl rfl
  simpa only [coarseWord, List.map_take] using congrArg (List.take k) hxy

end
end ImbalancedChen.P3OriginalU5WarmCapCodeStability
