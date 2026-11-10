import ImbalancedChen.P4AOriginalFiniteFallbackBank
import ImbalancedChen.P4AOriginalBufferedFallbackCaps
import ImbalancedChen.SelectedPrefixRationalMesh

/-! SOURCE_ONLY / UNCOMPILED.
Canonical physical rational boxes for the ORIGINAL second and third
fallback masks. The cap is the existing qVLo table MINUS a positive
rational width. It approaches the original endpoint rather than a
midpoint between a gate and that endpoint. Every accepted row has
explicit rational whole-corner tests on its actual closed box.
-/
namespace ImbalancedChen.P4AFallbackCanonicalBanks
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (SecondRegion ThirdRegion secondMask thirdMask)
open P4AOriginalFiniteFallbackBank (Bank)

abbrev Label (k m : ℕ) := Fin k → Fin (m+1)
abbrev QPoint (k : ℕ) := Fin k → ℚ
abbrev Point (k : ℕ) := Fin k → ℝ

def lo {k : ℕ} (m : ℕ) (j : Label k m) : QPoint k := qLogPrimeMeshLo 0 (19/96) m j
def hi {k : ℕ} (m : ℕ) (j : Label k m) : QPoint k := qLogPrimeMeshHi 0 (19/96) m j
def realPoint {k : ℕ} (x : QPoint k) : Point k := fun i => (x i : ℝ)
def closedBox {k : ℕ} (m : ℕ) (j : Label k m) : Set (Point k) :=
  Icc (realPoint (lo m j)) (realPoint (hi m j))

def buffer (m : ℕ) : ℚ := 1 / ((m : ℚ)+1)
def level2 (m : ℕ) (j : Label 2 m) : ℚ := P4AOriginalBufferedFallbackCaps.table2 m j-buffer m
def level3 (m : ℕ) (j : Label 3 m) : ℚ := P4AOriginalBufferedFallbackCaps.table3 m j-buffer m

theorem buffer_pos (m : ℕ) : 0 < buffer m := by unfold buffer; positivity
theorem buffer_cast (m : ℕ) : (buffer m : ℝ) = 1 / ((m : ℝ)+1) := by simp [buffer]

/-- Explicit strict rational corner rows for the TRUE second region,
including the original first cube at the old endpoint. -/
def corners2 (l u : QPoint 2) : Prop :=
  (25/128 : ℚ)<l 0 ∧ u 0<(19/96 : ℚ) ∧
    2*qC (l 0)-1<l 1 ∧ u 1<l 0 ∧ 3*u 0<qC (u 0)

/-- The strict inner third region. Its two weak original chart faces
are trimmed inward; all recorded rows imply the original ThirdRegion.
The original third cube is retained at the same old endpoint. -/
def corners3 (l u : QPoint 3) : Prop :=
  (25/128 : ℚ)<l 0 ∧ u 0<(19/96 : ℚ) ∧ 0<l 2 ∧ u 2<l 1 ∧
    2*qC (l 0)-1<l 1+l 2 ∧ u 1+u 2<l 0 ∧
    5*(u 1+u 2)<18*l 2 ∧ (5/96 : ℚ)<l 2 ∧ u 1<(3/16 : ℚ) ∧
    3*u 0<qC (u 0) ∧ u 0+u 1+3*u 2<qC (u 0)

def capRows {k : ℕ} [NeZero k] (I : Finset (Fin k)) (l u : QPoint k) (c : ℚ) : Prop :=
  selectedCapLower I (qC (l 0)) u<c ∧ c<selectedCapUpper I (299/500) l u

def good2 (m : ℕ) (j : Label 2 m) : Prop :=
  corners2 (lo m j) (hi m j) ∧ capRows secondMask (lo m j) (hi m j) (level2 m j)
def good3 (m : ℕ) (j : Label 3 m) : Prop :=
  corners3 (lo m j) (hi m j) ∧ capRows thirdMask (lo m j) (hi m j) (level3 m j)

def bank (m : ℕ) : Bank :=
  ⟨m,fun j => if good2 m j then some (level2 m j) else none,
    fun j => if good3 m j then some (level3 m j) else none⟩

theorem second_some_iff (m : ℕ) (j : Label 2 m) (c : ℚ) :
    (bank m).second j=some c ↔ good2 m j ∧ c=level2 m j := by
  simp only [bank]
  split_ifs with h <;> simp [h,eq_comm]

theorem third_some_iff (m : ℕ) (j : Label 3 m) (c : ℚ) :
    (bank m).third j=some c ↔ good3 m j ∧ c=level3 m j := by
  simp only [bank]
  split_ifs with h <;> simp [h,eq_comm]

theorem closedBox_compact {k : ℕ} (m : ℕ) (j : Label k m) : IsCompact (closedBox m j) := isCompact_Icc

theorem meshCell_subset_closedBox {k : ℕ} (m : ℕ) (j : Label k m) :
    logPrimeMeshCell 0 (19/96) m j ⊆ closedBox m j := by
  intro t ht
  have hl := congrFun (cast_qLogPrimeMeshLo 0 (19/96) m j)
  have hu := congrFun (cast_qLogPrimeMeshHi 0 (19/96) m j)
  refine ⟨fun i => ?_,fun i => ?_⟩
  · simpa only [lo,realPoint,Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using
      (hl i).trans_le (mem_logPrimeMeshCell.mp ht i).1
  · simpa only [hi,realPoint,Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using
      (mem_logPrimeMeshCell.mp ht i).2.le.trans_eq (hu i).symm

theorem closedBox_nonempty {k : ℕ} (m : ℕ) (j : Label k m) : (closedBox m j).Nonempty := by
  refine ⟨realPoint (lo m j),le_rfl,?_⟩
  intro i
  have h := (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ)<19/96) m j i).2.1.le
  simpa only [lo,hi,realPoint,Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using
    ((congrFun (cast_qLogPrimeMeshLo 0 (19/96) m j) i).trans_le
      (h.trans_eq (congrFun (cast_qLogPrimeMeshHi 0 (19/96) m j) i).symm))

private theorem old_bounds {k : ℕ} [NeZero k] (l u : QPoint k) (t : Point k)
    (hmu : (25/128 : ℚ)<l 0) (ht : t ∈ Icc (realPoint l) (realPoint u)) :
    (qC (u 0) : ℝ) ≤ v (t 0) ∧ v (t 0) ≤ (qC (l 0) : ℝ) := by
  have hm : mu<t 0 := by
    have hh : (25/128 : ℝ)<(l 0 : ℝ) := by exact_mod_cast hmu
    dsimp only [mu]
    linarith [ht.1 0]
  rw [v_eq_C hm.le,cast_qC,cast_qC]
  dsimp only [C]
  constructor <;> linarith [ht.1 0,ht.2 0]

theorem corners2_sound (l u : QPoint 2) (h : corners2 l u) (t : Point 2)
    (ht : t ∈ Icc (realPoint l) (realPoint u)) :
    SecondRegion (t 0) (t 1) ∧ 3*t 0<v (t 0) := by
  obtain ⟨hm,hr,hb,ho,hcube⟩ := h
  have hbounds := old_bounds l u t hm ht
  have hmR : (25/128 : ℝ)<(l 0 : ℝ) := by exact_mod_cast hm
  have hrR : (u 0 : ℝ)<(19/96 : ℝ) := by exact_mod_cast hr
  have hbR : 2*(qC (l 0) : ℝ)-1<(l 1 : ℝ) := by exact_mod_cast hb
  have hoR : (u 1 : ℝ)<(l 0 : ℝ) := by exact_mod_cast ho
  have hcR : 3*(u 0 : ℝ)<(qC (u 0) : ℝ) := by exact_mod_cast hcube
  change (mu<t 0 ∧ t 0<P5OriginalAboveMuThirdLowerPhysicalCoefficient.rho ∧
    2*v (t 0)-1<t 1 ∧ t 1<t 0) ∧ _
  dsimp only [mu,P5OriginalAboveMuThirdLowerPhysicalCoefficient.rho]
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩ <;> linarith [ht.1 0,ht.2 0,ht.1 1,ht.2 1]

theorem corners3_sound (l u : QPoint 3) (h : corners3 l u) (t : Point 3)
    (ht : t ∈ Icc (realPoint l) (realPoint u)) :
    ThirdRegion (t 0) (t 1) (t 2) ∧ 3*t 0<v (t 0) ∧
      t 0+t 1+3*t 2<v (t 0) := by
  obtain ⟨hm,hr,hz,ho,hb,hs,hw,hcut,hy,hcube,hthird⟩ := h
  have hbds := old_bounds l u t hm ht
  have hmR : (25/128 : ℝ)<(l 0 : ℝ) := by exact_mod_cast hm
  have hrR : (u 0 : ℝ)<(19/96 : ℝ) := by exact_mod_cast hr
  have hzR : (0 : ℝ)<(l 2 : ℝ) := by exact_mod_cast hz
  have hoR : (u 2 : ℝ)<(l 1 : ℝ) := by exact_mod_cast ho
  have hbR : 2*(qC (l 0) : ℝ)-1<(l 1 : ℝ)+(l 2 : ℝ) := by exact_mod_cast hb
  have hsR : (u 1 : ℝ)+(u 2 : ℝ)<(l 0 : ℝ) := by exact_mod_cast hs
  have hwR : 5*((u 1 : ℝ)+(u 2 : ℝ))<18*(l 2 : ℝ) := by exact_mod_cast hw
  have hcR : (5/96 : ℝ)<(l 2 : ℝ) := by exact_mod_cast hcut
  have hyR : (u 1 : ℝ)<(3/16 : ℝ) := by exact_mod_cast hy
  have hcubeR : 3*(u 0 : ℝ)<(qC (u 0) : ℝ) := by exact_mod_cast hcube
  have hthirdR : (u 0 : ℝ)+(u 1 : ℝ)+3*(u 2 : ℝ)<(qC (u 0) : ℝ) := by exact_mod_cast hthird
  have hz0 : 0<t 2 := by linarith [ht.1 2]
  have hzy : t 2<t 1 := by linarith [ht.2 2,ht.1 1]
  have hs0 : 0<t 1+t 2 := by linarith
  have hlo : (5/9 : ℝ)≤2*t 2/(t 1+t 2) := by
    apply (le_div_iff₀ hs0).mpr
    linarith [ht.2 1,ht.2 2,ht.1 2]
  have hhi : 2*t 2/(t 1+t 2)≤1 := (div_le_one hs0).mpr (by linarith)
  refine ⟨?_,?_,?_⟩
  · change mu<t 0 ∧ t 0<P5OriginalAboveMuThirdLowerPhysicalCoefficient.rho ∧ _
    dsimp only [mu,P5OriginalAboveMuThirdLowerPhysicalCoefficient.rho]
    refine ⟨?_,?_,hz0,hzy,?_,?_,hlo,hhi,?_,?_⟩ <;>
      linarith [ht.1 0,ht.2 0,ht.1 1,ht.2 1,ht.1 2,ht.2 2]
  · linarith [ht.2 0]
  · linarith [ht.2 0,ht.2 1,ht.2 2]

/-- Reuse the original rational lower/max and tent/min bounding lemmas
for a chosen rational level c, rather than the old midpoint level. -/
theorem capRows_sound {k : ℕ} [NeZero k] (I : Finset (Fin k)) (l u : QPoint k) (c : ℚ)
    (h : capRows I l u c) (t : Point k) (ht : t ∈ Icc (realPoint l) (realPoint u)) :
    (qC (l 0) : ℝ)<(c : ℝ) ∧ (c : ℝ)<299/500 ∧ (1/2 : ℝ)<c ∧
      (∀ j,prefixSquareExpr t j<c) ∧
      (∀ j∉I,selectedSquareExpr I t j<c) ∧ (c : ℝ)<v (∑ j∈I,t j) := by
  have hlow : (selectedCapLower I (qC (l 0)) u : ℝ)<c := by exact_mod_cast h.1
  have hhigh : (c : ℝ)<selectedCapUpper I (299/500) l u := by exact_mod_cast h.2
  have hold : (qC (l 0) : ℝ)≤selectedCapLower I (qC (l 0)) u := by
    exact_mod_cast selectedCapLower_old_le I (qC (l 0)) u
  have hhalf : (1/2 : ℝ)≤selectedCapLower I (qC (l 0)) u := by
    exact_mod_cast selectedCapLower_half_le I (qC (l 0)) u
  have hup : (selectedCapUpper I (299/500) l u : ℝ) =
      min (299/500 : ℝ) (qVLo (∑ j∈I,l j) (∑ j∈I,u j) : ℝ) := by simp [selectedCapUpper]
  rw [hup] at hhigh
  refine ⟨hold.trans_lt hlow,hhigh.trans_le (min_le_left _ _),hhalf.trans_lt hlow,?_,?_,?_⟩
  · intro j
    have hh : (prefixSquareExpr u j : ℝ)≤selectedCapLower I (qC (l 0)) u := by
      exact_mod_cast selectedCapLower_prefix_le I (qC (l 0)) u j
    rw [cast_prefixSquareExpr] at hh
    exact (prefixSquareExpr_mono ht.2 j).trans_lt (hh.trans_lt hlow)
  · intro j hj
    have hh : (selectedSquareExpr I u j : ℝ)≤selectedCapLower I (qC (l 0)) u := by
      exact_mod_cast selectedCapLower_selected_le I (qC (l 0)) u j hj
    rw [cast_selectedSquareExpr] at hh
    exact (selectedSquareExpr_mono I ht.2 j).trans_lt (hh.trans_lt hlow)
  · have hls : ((∑ j∈I,l j : ℚ) : ℝ)≤∑ j∈I,t j := by
      push_cast
      exact Finset.sum_le_sum (fun j _ => ht.1 j)
    have hus : (∑ j∈I,t j)≤((∑ j∈I,u j : ℚ) : ℝ) := by
      push_cast
      exact Finset.sum_le_sum (fun j _ => ht.2 j)
    exact (hhigh.trans_le (min_le_right _ _)).trans_le (qVLo_le_v hls hus)

theorem capRows_original_check {k : ℕ} [NeZero k] (I : Finset (Fin k)) (l u : QPoint k) (c : ℚ)
    (h : capRows I l u c) : selectedBoxCapCheck I (qC (l 0)) (299/500) l u=true :=
  decide_eq_true (h.1.trans h.2)

theorem good2_sound (m : ℕ) (j : Label 2 m) (h : good2 m j) (t : Point 2)
    (ht : t ∈ closedBox m j) :
    SecondRegion (t 0) (t 1) ∧ 3*t 0<v (t 0) ∧
      v (t 0)<(level2 m j : ℝ) ∧ (level2 m j : ℝ)<299/500 ∧
      (1/2 : ℝ)<level2 m j ∧ (∀ i,prefixSquareExpr t i<level2 m j) ∧
      (∀ i∉secondMask,selectedSquareExpr secondMask t i<level2 m j) ∧
      (level2 m j : ℝ)<v (t 1) := by
  have hr := corners2_sound _ _ h.1 t ht
  have hc := capRows_sound secondMask _ _ _ h.2 t ht
  have ho := (old_bounds _ _ t h.1.1 ht).2
  exact ⟨hr.1,hr.2,ho.trans_lt hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,
    by simpa [secondMask] using hc.2.2.2.2.2⟩

theorem good3_sound (m : ℕ) (j : Label 3 m) (h : good3 m j) (t : Point 3)
    (ht : t ∈ closedBox m j) :
    ThirdRegion (t 0) (t 1) (t 2) ∧ 3*t 0<v (t 0) ∧
      t 0+t 1+3*t 2<v (t 0) ∧
      v (t 0)<(level3 m j : ℝ) ∧ (level3 m j : ℝ)<299/500 ∧
      (1/2 : ℝ)<level3 m j ∧ (∀ i,prefixSquareExpr t i<level3 m j) ∧
      (∀ i∉thirdMask,selectedSquareExpr thirdMask t i<level3 m j) ∧
      (level3 m j : ℝ)<v (t 1+t 2) := by
  have hr := corners3_sound _ _ h.1 t ht
  have hc := capRows_sound thirdMask _ _ _ h.2 t ht
  have ho := (old_bounds _ _ t h.1.1 ht).2
  exact ⟨hr.1,hr.2.1,hr.2.2,ho.trans_lt hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,
    by simpa [thirdMask] using hc.2.2.2.2.2⟩

end
end ImbalancedChen.P4AFallbackCanonicalBanks
