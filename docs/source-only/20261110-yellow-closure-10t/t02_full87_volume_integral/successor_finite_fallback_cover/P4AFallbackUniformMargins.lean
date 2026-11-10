import ImbalancedChen.P4AFallbackOriginalCompactTrims

/-! SOURCE_ONLY / UNCOMPILED.
One positive rational margin for BOTH finite original banks. Every value
is an original rational corner or cap slack; no gain or distribution
field is inserted. The same margin precedes omega, compiler width and N.
-/
namespace ImbalancedChen.P4AFallbackUniformMargins
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AFallbackCanonicalBanks P4AFallbackCompactEndpointCover P4AFallbackOriginalCompactTrims
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (secondMask thirdMask)

def rowValues {a : ℕ} (s : Fin a → ℚ) (lower upper : ℚ) : Finset ℚ :=
  insert 1 (insert lower (insert upper (Finset.univ.image s)))
def rowMargin {a : ℕ} (s : Fin a → ℚ) (lower upper : ℚ) : ℚ :=
  (rowValues s lower upper).min' ⟨1,by simp [rowValues]⟩

theorem rowMargin_pos {a : ℕ} (s : Fin a → ℚ) (lower upper : ℚ)
    (hs : ∀ i,0<s i) (hl : 0<lower) (hu : 0<upper) : 0<rowMargin s lower upper := by
  have h := Finset.min'_mem (rowValues s lower upper) ⟨1,by simp [rowValues]⟩
  rcases Finset.mem_insert.mp h with he | h
  · change rowMargin s lower upper=1 at he
    rw [he];norm_num
  · rcases Finset.mem_insert.mp h with he | h
    · change rowMargin s lower upper=lower at he
      rwa [he]
    · rcases Finset.mem_insert.mp h with he | h
      · change rowMargin s lower upper=upper at he
        rwa [he]
      · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
        change s i=rowMargin s lower upper at hi
        rw [←hi]
        exact hs i

theorem rowMargin_le_lower {a : ℕ} (s : Fin a → ℚ) (l u : ℚ) : rowMargin s l u≤l :=
  Finset.min'_le _ _ (by simp [rowValues])
theorem rowMargin_le_upper {a : ℕ} (s : Fin a → ℚ) (l u : ℚ) : rowMargin s l u≤u :=
  Finset.min'_le _ _ (by simp [rowValues])
theorem rowMargin_le_slack {a : ℕ} (s : Fin a → ℚ) (l u : ℚ) (i : Fin a) : rowMargin s l u≤s i :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))))

def margin2 (m : ℕ) (j : Label 2 m) : ℚ :=
  rowMargin (qSlacks2 (lo m j) (hi m j))
    (level2 m j-selectedCapLower secondMask (qC (lo m j 0)) (hi m j))
    (selectedCapUpper secondMask (299/500) (lo m j) (hi m j)-level2 m j)
def margin3 (m : ℕ) (j : Label 3 m) : ℚ :=
  rowMargin (qSlacks3 (lo m j) (hi m j))
    (level3 m j-selectedCapLower thirdMask (qC (lo m j 0)) (hi m j))
    (selectedCapUpper thirdMask (299/500) (lo m j) (hi m j)-level3 m j)

theorem margin2_pos (m : ℕ) (j : Label 2 m) (h : good2 m j) : 0<margin2 m j :=
  rowMargin_pos _ _ _ ((corners2_iff _ _).mp h.1) (sub_pos.mpr h.2.1) (sub_pos.mpr h.2.2)
theorem margin3_pos (m : ℕ) (j : Label 3 m) (h : good3 m j) : 0<margin3 m j :=
  rowMargin_pos _ _ _ ((corners3_iff _ _).mp h.1) (sub_pos.mpr h.2.1) (sub_pos.mpr h.2.2)

def bankValues (m : ℕ) : Finset ℚ :=
  insert 1 (((Finset.univ.filter (good2 m)).image (margin2 m)) ∪
    ((Finset.univ.filter (good3 m)).image (margin3 m)))
def uniformMargin (m : ℕ) : ℚ :=
  (bankValues m).min' ⟨1,by simp [bankValues]⟩

theorem uniformMargin_pos (m : ℕ) : 0<uniformMargin m := by
  have h := Finset.min'_mem (bankValues m) ⟨1,by simp [bankValues]⟩
  rcases Finset.mem_insert.mp h with he | h
  · change uniformMargin m=1 at he
    rw [he];norm_num
  · rcases Finset.mem_union.mp h with h | h
    · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      change margin2 m j=uniformMargin m at he
      rw [←he]
      exact margin2_pos m j (Finset.mem_filter.mp hj).2
    · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      change margin3 m j=uniformMargin m at he
      rw [←he]
      exact margin3_pos m j (Finset.mem_filter.mp hj).2

theorem uniformMargin_le_second (m : ℕ) (j : Label 2 m) (h : good2 m j) : uniformMargin m≤margin2 m j :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩)))
theorem uniformMargin_le_third (m : ℕ) (j : Label 3 m) (h : good3 m j) : uniformMargin m≤margin3 m j :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩)))

theorem second_corner_margin (m : ℕ) (j : Label 2 m) (h : good2 m j) (i : Fin 5) :
    uniformMargin m≤qSlacks2 (lo m j) (hi m j) i :=
  (uniformMargin_le_second m j h).trans (rowMargin_le_slack _ _ _ i)
theorem third_corner_margin (m : ℕ) (j : Label 3 m) (h : good3 m j) (i : Fin 11) :
    uniformMargin m≤qSlacks3 (lo m j) (hi m j) i :=
  (uniformMargin_le_third m j h).trans (rowMargin_le_slack _ _ _ i)

/-- Quantitative whole-CLOSED-box cap/mask bounds from the same exact
rational lower/max and upper/min test. -/
theorem cap_corner_margin_sound {k : ℕ} [NeZero k] (I : Finset (Fin k))
    (l u : QPoint k) (c sigma : ℚ)
    (hl : sigma≤c-selectedCapLower I (qC (l 0)) u)
    (hu : sigma≤selectedCapUpper I (299/500) l u-c)
    (t : Point k) (ht : t∈Icc (realPoint l) (realPoint u)) :
    v (t 0)+(sigma : ℝ)≤c ∧ (1/2 : ℝ)+sigma≤c ∧
      (∀ i,prefixSquareExpr t i+sigma≤c) ∧
      (∀ i∉I,selectedSquareExpr I t i+sigma≤c) ∧
      (c : ℝ)+sigma≤v (∑ i∈I,t i) ∧ (c : ℝ)+sigma≤299/500 := by
  have hL : (selectedCapLower I (qC (l 0)) u : ℝ)+sigma≤c := by exact_mod_cast (by linarith : selectedCapLower I (qC (l 0)) u+sigma≤c)
  have hU : (c : ℝ)+sigma≤selectedCapUpper I (299/500) l u := by exact_mod_cast (by linarith : c+sigma≤selectedCapUpper I (299/500) l u)
  have hOld : v (t 0)≤(qC (l 0) : ℝ) := by
    rw [cast_qC]
    have hv : v (t 0)≤C (t 0) := by rw [v_eq_min];exact min_le_right _ _
    dsimp only [C] at hv ⊢
    linarith [ht.1 0]
  have hOldL : (qC (l 0) : ℝ)≤selectedCapLower I (qC (l 0)) u := by exact_mod_cast selectedCapLower_old_le I (qC (l 0)) u
  have hhalf : (1/2 : ℝ)≤selectedCapLower I (qC (l 0)) u := by exact_mod_cast selectedCapLower_half_le I (qC (l 0)) u
  have htop : (selectedCapUpper I (299/500) l u : ℝ)=
      min (299/500 : ℝ) (qVLo (∑ i∈I,l i) (∑ i∈I,u i) : ℝ) := by simp [selectedCapUpper]
  rw [htop] at hU
  refine ⟨by linarith,by linarith,?_,?_,?_,hU.trans (min_le_left _ _)⟩
  · intro i
    have hp : (prefixSquareExpr u i : ℝ)≤selectedCapLower I (qC (l 0)) u := by exact_mod_cast selectedCapLower_prefix_le I (qC (l 0)) u i
    rw [cast_prefixSquareExpr] at hp
    have hm := prefixSquareExpr_mono ht.2 i
    linarith
  · intro i hi
    have hp : (selectedSquareExpr I u i : ℝ)≤selectedCapLower I (qC (l 0)) u := by exact_mod_cast selectedCapLower_selected_le I (qC (l 0)) u i hi
    rw [cast_selectedSquareExpr] at hp
    have hm := selectedSquareExpr_mono I ht.2 i
    linarith
  · have hls : ((∑ i∈I,l i : ℚ) : ℝ)≤∑ i∈I,t i := by push_cast;exact Finset.sum_le_sum (fun i _ => ht.1 i)
    have hus : (∑ i∈I,t i)≤((∑ i∈I,u i : ℚ) : ℝ) := by push_cast;exact Finset.sum_le_sum (fun i _ => ht.2 i)
    exact (hU.trans (min_le_right _ _)).trans (qVLo_le_v hls hus)

theorem second_uniform_cap_margin (m : ℕ) (j : Label 2 m) (h : good2 m j) (t : Point 2)
    (ht : t∈closedBox m j) :
    v (t 0)+(uniformMargin m : ℝ)≤level2 m j ∧
      (1/2 : ℝ)+uniformMargin m≤level2 m j ∧
      (∀ i,prefixSquareExpr t i+uniformMargin m≤level2 m j) ∧
      (∀ i∉secondMask,selectedSquareExpr secondMask t i+uniformMargin m≤level2 m j) ∧
      (level2 m j : ℝ)+uniformMargin m≤v (t 1) ∧
      (level2 m j : ℝ)+uniformMargin m≤299/500 := by
  have hm := uniformMargin_le_second m j h
  have hl := hm.trans (rowMargin_le_lower _ _ _)
  have hu := hm.trans (rowMargin_le_upper _ _ _)
  simpa [secondMask] using cap_corner_margin_sound secondMask _ _ _ _ hl hu t ht

theorem third_uniform_cap_margin (m : ℕ) (j : Label 3 m) (h : good3 m j) (t : Point 3)
    (ht : t∈closedBox m j) :
    v (t 0)+(uniformMargin m : ℝ)≤level3 m j ∧
      (1/2 : ℝ)+uniformMargin m≤level3 m j ∧
      (∀ i,prefixSquareExpr t i+uniformMargin m≤level3 m j) ∧
      (∀ i∉thirdMask,selectedSquareExpr thirdMask t i+uniformMargin m≤level3 m j) ∧
      (level3 m j : ℝ)+uniformMargin m≤v (t 1+t 2) ∧
      (level3 m j : ℝ)+uniformMargin m≤299/500 := by
  have hm := uniformMargin_le_third m j h
  have hl := hm.trans (rowMargin_le_lower _ _ _)
  have hu := hm.trans (rowMargin_le_upper _ _ _)
  simpa [thirdMask] using cap_corner_margin_sound thirdMask _ _ _ _ hl hu t ht

/-- The old first cube has the SAME positive bank margin, throughout
the closed physical box. -/
theorem second_old_cube_margin (m : ℕ) (j : Label 2 m) (h : good2 m j)
    (t : Point 2) (ht : t∈closedBox m j) :
    3*t 0+(uniformMargin m : ℝ)≤v (t 0) := by
  have hs := second_corner_margin m j h 4
  have hsCast : (uniformMargin m : ℝ)≤(qSlacks2 (lo m j) (hi m j) 4 : ℝ) := by
    exact_mod_cast hs
  rw [←slacks2_cast] at hsCast
  have hsR : (uniformMargin m : ℝ)≤C (hi m j 0 : ℝ)-3*(hi m j 0 : ℝ) := by
    simpa [slacks2,realPoint] using hsCast
  have hv := v_eq_C (good2_sound m j h t ht).1.1.le
  rw [hv]
  dsimp only [C] at hsR ⊢
  linarith [ht.2 0]

/-- Both old history cubes retain one uniform margin on every third
box, before any error buffer or physical rough cutoff is chosen. -/
theorem third_old_cube_margins (m : ℕ) (j : Label 3 m) (h : good3 m j)
    (t : Point 3) (ht : t∈closedBox m j) :
    3*t 0+(uniformMargin m : ℝ)≤v (t 0) ∧
      t 0+t 1+3*t 2+(uniformMargin m : ℝ)≤v (t 0) := by
  have hfirst := third_corner_margin m j h 9
  have hthird := third_corner_margin m j h 10
  have hfirstCast : (uniformMargin m : ℝ)≤(qSlacks3 (lo m j) (hi m j) 9 : ℝ) := by
    exact_mod_cast hfirst
  have hthirdCast : (uniformMargin m : ℝ)≤(qSlacks3 (lo m j) (hi m j) 10 : ℝ) := by
    exact_mod_cast hthird
  rw [←slacks3_cast] at hfirstCast hthirdCast
  have hfirstR : (uniformMargin m : ℝ)≤C (hi m j 0 : ℝ)-3*(hi m j 0 : ℝ) := by
    simpa [slacks3,realPoint] using hfirstCast
  have hthirdR : (uniformMargin m : ℝ)≤C (hi m j 0 : ℝ)-
      (hi m j 0 : ℝ)-(hi m j 1 : ℝ)-3*(hi m j 2 : ℝ) := by
    simpa [slacks3,realPoint] using hthirdCast
  have hv := v_eq_C (good3_sound m j h t ht).1.1.le
  rw [hv]
  dsimp only [C] at hfirstR hthirdR ⊢
  constructor <;> linarith [ht.2 0,ht.2 1,ht.2 2]

end
end ImbalancedChen.P4AFallbackUniformMargins
