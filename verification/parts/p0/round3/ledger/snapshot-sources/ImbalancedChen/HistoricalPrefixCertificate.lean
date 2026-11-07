import ImbalancedChen.ActualSelectedPrefixCapSelector
import ImbalancedChen.FirstExitHistoricalLevels

/-!
# Finite inherited cap tables on one historical mesh

The cell data below are fixed before the target `N`.  The same half-open
mesh is used at ranks three, four and five; an ancestor cell is the literal
initial coordinate projection.  An unselected fourth or fifth cell keeps
its inherited cap, including outside the ambient cube.

The Boolean check in this file checks only finite level comparisons.  It
does not assert square/envelope licensing, certificate integral values,
physical support, distribution, or the final manuscript constants.  The
actual third-to-fifth identity follows from these finite comparisons and
the already proved historical-tree theorem.  Both old and new own-cube
indicators remain in that theorem's fifth saving.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- Initial processing-order coordinates, also used for mesh cell labels. -/
def historicalPrefixProject {α : Type*} {r d : ℕ} (hrd : r ≤ d)
    (t : Fin d → α) : Fin r → α :=
  fun i => t (i.castLE hrd)

theorem historicalPrefixProject_comp {α : Type*} {r d e : ℕ}
    (hrd : r ≤ d) (hde : d ≤ e) (t : Fin e → α) :
    historicalPrefixProject hrd (historicalPrefixProject hde t) =
      historicalPrefixProject (hrd.trans hde) t := by
  funext i
  rfl

/-- The projected label owns precisely the projected ancestor point. -/
theorem mem_logPrimeMeshCell_historicalPrefixProject {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} {j : Fin d → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j) :
    historicalPrefixProject hrd t ∈
      logPrimeMeshCell a b m (historicalPrefixProject hrd j) := by
  apply mem_logPrimeMeshCell.mpr
  intro i
  simpa only [historicalPrefixProject, logPrimeMeshLo, logPrimeMeshHi]
    using mem_logPrimeMeshCell.mp ht (i.castLE hrd)

/-- Half-open ownership identifies the ancestor cell uniquely, including
points on internal grid faces. -/
theorem historicalPrefixAncestorCell_unique {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} (hab : a ≤ b)
    {j : Fin d → Fin (m + 1)} {q : Fin r → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j)
    (hq : historicalPrefixProject hrd t ∈ logPrimeMeshCell a b m q) :
    q = historicalPrefixProject hrd j :=
  logPrimeMeshCell_unique hab hq (mem_logPrimeMeshCell_historicalPrefixProject hrd ht)

theorem primeHistoryLogCoordinates_eq_historicalPrefixProject (N : ℝ)
    {r d : ℕ} (hrd : r ≤ d) {history : List ℕ} (hlen : history.length = d) :
    primeHistoryLogCoordinates N r (rosserAncestor r history) =
      historicalPrefixProject hrd (primeHistoryLogCoordinates N d history) := by
  funext i
  exact primeHistoryLogCoordinates_ancestor N hlen hrd i

/-- A finite cap lookup with an explicit, possibly inherited, fallback. -/
def historicalPrefixLookup {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ) : ℚ :=
  fallback + ∑ j ∈ J,
    if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then cap j - fallback else 0

theorem historicalPrefixLookup_on_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1)) (hj : j ∈ J)
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = cap j := by
  unfold historicalPrefixLookup
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [if_pos ht]
    ring
  · intro q _hq hqj
    apply if_neg
    intro hq
    exact hqj (logPrimeMeshCell_unique (by exact_mod_cast hab) hq ht)

theorem historicalPrefixLookup_outside {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (ht : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = fallback := by
  unfold historicalPrefixLookup
  rw [Finset.sum_eq_zero (fun j hj => if_neg (ht j hj)), add_zero]

/-- On every mesh cell, including an unselected one, the effective value
is the stored cap or the exact inherited fallback. -/
theorem historicalPrefixLookup_on_any_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1))
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t =
      if j ∈ J then cap j else fallback := by
  by_cases hj : j ∈ J
  · rw [if_pos hj]
    exact historicalPrefixLookup_on_cell a b hab m J cap fallback t j hj ht
  · rw [if_neg hj]
    apply historicalPrefixLookup_outside
    intro q hq hqt
    have heq : q = j := logPrimeMeshCell_unique (by exact_mod_cast hab) hqt ht
    subst q
    exact hj hq

/-- Finite cell comparisons imply monotonicity once the inherited value
has been identified on the selected cell. -/
theorem historicalPrefixLookup_ge_fallback {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (old cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (hlevel : ∀ j ∈ J, old j ≤ cap j)
    (hinherit : ∀ j ∈ J,
      t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j → fallback = old j) :
    fallback ≤ historicalPrefixLookup a b m J cap fallback t := by
  unfold historicalPrefixLookup
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with ht
  · rw [hinherit j hj ht]
    exact sub_nonneg.mpr (hlevel j hj)
  · exact le_rfl

/-- Exact finite decomposition for any function of the cap.  No
continuity, level ordering or own-cube admission is required. -/
theorem historicalPrefixLookup_apply_sub {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (f : ℚ → ℝ) :
    f (historicalPrefixLookup a b m J cap fallback t) - f fallback =
      ∑ j ∈ J, if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then
        f (cap j) - f fallback else 0 := by
  by_cases hex : ∃ j ∈ J, t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j
  · obtain ⟨j, hj, ht⟩ := hex
    have hsum : (∑ q ∈ J,
        if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m q then
          f (cap q) - f fallback else 0) = f (cap j) - f fallback := by
      calc
        _ = (if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then
            f (cap j) - f fallback else 0) := by
          apply Finset.sum_eq_single_of_mem j hj
          intro q _hq hqj
          apply if_neg
          intro hq
          exact hqj (logPrimeMeshCell_unique (by exact_mod_cast hab) hq ht)
        _ = _ := if_pos ht
    rw [historicalPrefixLookup_on_cell a b hab m J cap fallback t j hj ht, hsum]
  · have hout : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j := by
      simpa only [not_exists, not_and] using hex
    rw [historicalPrefixLookup_outside a b m J cap fallback t hout, sub_self]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hout j hj))

/-- Every field is finite data independent of the target or tested
integer.  `cap4` and `cap5` are new values only on their adopted cells. -/
structure HistoricalPrefixCapData where
  a : ℚ
  b : ℚ
  m : ℕ
  old : ℚ
  cells3 : Finset (Fin 3 → Fin (m + 1))
  cap3 : (Fin 3 → Fin (m + 1)) → ℚ
  cells4 : Finset (Fin 4 → Fin (m + 1))
  cap4 : (Fin 4 → Fin (m + 1)) → ℚ
  cells5 : Finset (Fin 5 → Fin (m + 1))
  cap5 : (Fin 5 → Fin (m + 1)) → ℚ

namespace HistoricalPrefixCapData

def cell3 (D : HistoricalPrefixCapData) (j : Fin 3 → Fin (D.m + 1)) : ℚ :=
  if j ∈ D.cells3 then D.cap3 j else D.old

def old4 (D : HistoricalPrefixCapData) (j : Fin 4 → Fin (D.m + 1)) : ℚ :=
  D.cell3 (historicalPrefixProject (by omega : 3 ≤ 4) j)

def cell4 (D : HistoricalPrefixCapData) (j : Fin 4 → Fin (D.m + 1)) : ℚ :=
  if j ∈ D.cells4 then D.cap4 j else D.old4 j

def old5 (D : HistoricalPrefixCapData) (j : Fin 5 → Fin (D.m + 1)) : ℚ :=
  D.cell4 (historicalPrefixProject (by omega : 4 ≤ 5) j)

def cell5 (D : HistoricalPrefixCapData) (j : Fin 5 → Fin (D.m + 1)) : ℚ :=
  if j ∈ D.cells5 then D.cap5 j else D.old5 j

/-- Only level comparisons are checked here.  The bounded deciders
explicitly traverse the selected finsets, not the full cell-label types.
Square/envelope licenses and numerical integral bounds remain separate
obligations. -/
def levelCheck (D : HistoricalPrefixCapData) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := D.cells3)
    (p := fun j _ => D.old ≤ D.cap3 j)) &&
    (@decide _ (Finset.decidableDforallFinset (s := D.cells4)
      (p := fun j _ => D.old4 j ≤ D.cap4 j)) &&
    @decide _ (Finset.decidableDforallFinset (s := D.cells5)
      (p := fun j _ => D.old5 j ≤ D.cap5 j)))

theorem levelCheck_sound (D : HistoricalPrefixCapData) (h : D.levelCheck = true) :
    (∀ j ∈ D.cells3, D.old ≤ D.cap3 j) ∧
      (∀ j ∈ D.cells4, D.old4 j ≤ D.cap4 j) ∧
      (∀ j ∈ D.cells5, D.old5 j ≤ D.cap5 j) := by
  simpa only [levelCheck, Bool.and_eq_true, decide_eq_true_eq] using h

/-- Existing whole-box checks supply the finite historical comparisons
when each stored new cap is identified with its checked midpoint cap.
The fourth and fifth checks use their actual inherited cell values. -/
theorem levelCheck_of_selectedBoxCapChecks (D : HistoricalPrefixCapData)
    (I3 : (Fin 3 → Fin (D.m + 1)) → Finset (Fin 3))
    (I4 : (Fin 4 → Fin (D.m + 1)) → Finset (Fin 4))
    (I5 : (Fin 5 → Fin (D.m + 1)) → Finset (Fin 5))
    (nu3 : (Fin 3 → Fin (D.m + 1)) → ℚ)
    (nu4 : (Fin 4 → Fin (D.m + 1)) → ℚ)
    (nu5 : (Fin 5 → Fin (D.m + 1)) → ℚ)
    (h3 : ∀ j ∈ D.cells3,
      D.cap3 j = selectedBoxCap (I3 j) D.old (nu3 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I3 j) D.old (nu3 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true)
    (h4 : ∀ j ∈ D.cells4,
      D.cap4 j = selectedBoxCap (I4 j) (D.old4 j) (nu4 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I4 j) (D.old4 j) (nu4 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true)
    (h5 : ∀ j ∈ D.cells5,
      D.cap5 j = selectedBoxCap (I5 j) (D.old5 j) (nu5 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I5 j) (D.old5 j) (nu5 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true) :
    D.levelCheck = true := by
  simp only [levelCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hcap, hcheck⟩ := h3 j hj
    rw [hcap]
    exact (selectedCapLower_old_le (I3 j) D.old _).trans
      (selectedBoxCap_between (I3 j) D.old (nu3 j) _ _ hcheck).1.le
  · intro j hj
    obtain ⟨hcap, hcheck⟩ := h4 j hj
    rw [hcap]
    exact (selectedCapLower_old_le (I4 j) (D.old4 j) _).trans
      (selectedBoxCap_between (I4 j) (D.old4 j) (nu4 j) _ _ hcheck).1.le
  · intro j hj
    obtain ⟨hcap, hcheck⟩ := h5 j hj
    rw [hcap]
    exact (selectedCapLower_old_le (I5 j) (D.old5 j) _).trans
      (selectedBoxCap_between (I5 j) (D.old5 j) (nu5 j) _ _ hcheck).1.le

def exponent3 (D : HistoricalPrefixCapData) (t : Fin 3 → ℝ) : ℚ :=
  historicalPrefixLookup D.a D.b D.m D.cells3 D.cap3 D.old t

def exponent4 (D : HistoricalPrefixCapData) (t : Fin 4 → ℝ) : ℚ :=
  historicalPrefixLookup D.a D.b D.m D.cells4 D.cap4
    (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)) t

def exponent5 (D : HistoricalPrefixCapData) (t : Fin 5 → ℝ) : ℚ :=
  historicalPrefixLookup D.a D.b D.m D.cells5 D.cap5
    (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) t

theorem exponent3_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 3 → ℝ) (j : Fin 3 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 t = D.cell3 j :=
  historicalPrefixLookup_on_any_cell D.a D.b hab D.m D.cells3 D.cap3 D.old t j ht

theorem exponent4_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 4 → ℝ) (j : Fin 4 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent4 t = D.cell4 j := by
  change historicalPrefixLookup D.a D.b D.m D.cells4 D.cap4
      (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)) t =
    if j ∈ D.cells4 then D.cap4 j else
      D.cell3 (historicalPrefixProject (by omega : 3 ≤ 4) j)
  rw [historicalPrefixLookup_on_any_cell D.a D.b hab D.m D.cells4 D.cap4 _ t j ht]
  rw [D.exponent3_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)]

theorem exponent5_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent5 t = D.cell5 j := by
  change historicalPrefixLookup D.a D.b D.m D.cells5 D.cap5
      (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) t =
    if j ∈ D.cells5 then D.cap5 j else
      D.cell4 (historicalPrefixProject (by omega : 4 ≤ 5) j)
  rw [historicalPrefixLookup_on_any_cell D.a D.b hab D.m D.cells5 D.cap5 _ t j ht]
  rw [D.exponent4_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)]

theorem exponent3_outside (D : HistoricalPrefixCapData) (t : Fin 3 → ℝ)
    (ht : ∀ j ∈ D.cells3,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 t = D.old :=
  historicalPrefixLookup_outside D.a D.b D.m D.cells3 D.cap3 D.old t ht

theorem exponent4_outside (D : HistoricalPrefixCapData) (t : Fin 4 → ℝ)
    (ht : ∀ j ∈ D.cells4,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent4 t = D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t) :=
  historicalPrefixLookup_outside D.a D.b D.m D.cells4 D.cap4 _ t ht

theorem exponent5_outside (D : HistoricalPrefixCapData) (t : Fin 5 → ℝ)
    (ht : ∀ j ∈ D.cells5,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent5 t = D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) :=
  historicalPrefixLookup_outside D.a D.b D.m D.cells5 D.cap5 _ t ht

/-- The old cap is constant on the same fourth cell as its replacement,
because its third ancestor has exactly the projected owner. -/
theorem exponent4_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 4 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent4 t) -
        f (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)) =
      ∑ j ∈ D.cells4,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap4 j) - f (D.old4 j) else 0 := by
  rw [exponent4, historicalPrefixLookup_apply_sub D.a D.b hab]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · have hinherit :
        D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t) = D.old4 j :=
      D.exponent3_on_cell hab _ _
        (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)
    simp only [if_pos ht, hinherit]
  · simp only [if_neg ht]

/-- Both functions of the old and new fifth caps are evaluated on one
joint cell.  This includes every old-rejected candidate. -/
theorem exponent5_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent5 t) -
        f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) =
      ∑ j ∈ D.cells5,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0 := by
  rw [exponent5, historicalPrefixLookup_apply_sub D.a D.b hab]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · have hinherit :
        D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) = D.old5 j :=
      D.exponent4_on_cell hab _ _
        (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)
    simp only [if_pos ht, hinherit]
  · simp only [if_neg ht]

theorem old_le_exponent3 (D : HistoricalPrefixCapData) (hcheck : D.levelCheck = true)
    (t : Fin 3 → ℝ) : D.old ≤ D.exponent3 t := by
  exact historicalPrefixLookup_ge_fallback D.a D.b D.m D.cells3
    (fun _ => D.old) D.cap3 D.old t (D.levelCheck_sound hcheck).1 (by intros; rfl)

theorem exponent3_le_exponent4 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (t : Fin 4 → ℝ) :
    D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t) ≤ D.exponent4 t := by
  apply historicalPrefixLookup_ge_fallback D.a D.b D.m D.cells4 D.old4 D.cap4
    _ t (D.levelCheck_sound hcheck).2.1
  intro j _hj ht
  exact D.exponent3_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)

theorem exponent4_le_exponent5 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (t : Fin 5 → ℝ) :
    D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) ≤ D.exponent5 t := by
  apply historicalPrefixLookup_ge_fallback D.a D.b D.m D.cells5 D.old5 D.cap5
    _ t (D.levelCheck_sound hcheck).2.2
  intro j _hj ht
  exact D.exponent4_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)

/-- The target is introduced only after the finite mesh and cap tables. -/
def level3 (D : HistoricalPrefixCapData) (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ (D.exponent3 (primeHistoryLogCoordinates N 3 history) : ℝ)

def level4 (D : HistoricalPrefixCapData) (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ (D.exponent4 (primeHistoryLogCoordinates N 4 history) : ℝ)

def level5 (D : HistoricalPrefixCapData) (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ (D.exponent5 (primeHistoryLogCoordinates N 5 history) : ℝ)

theorem level3_outside (D : HistoricalPrefixCapData) (N : ℝ) (history : List ℕ)
    (hout : ∀ j ∈ D.cells3, primeHistoryLogCoordinates N 3 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 N history = N ^ (D.old : ℝ) := by
  unfold level3
  rw [D.exponent3_outside _ hout]

/-- Outside adopted fourth cells the old level is the selected third
ancestor's level, rather than the original global constant. -/
theorem level4_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 4)
    (hout : ∀ j ∈ D.cells4, primeHistoryLogCoordinates N 4 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level4 N history = D.level3 N (rosserAncestor 3 history) := by
  unfold level4 level3
  rw [D.exponent4_outside _ hout,
    primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 4) hlen]

/-- The fifth fallback keeps the complete fourth history, including the
third selection inherited by that fourth history. -/
theorem level5_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates N 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = D.level4 N (rosserAncestor 4 history) := by
  unfold level5 level4
  rw [D.exponent5_outside _ hout,
    primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 4 ≤ 5) hlen]

theorem level3_ancestor_le_level4 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 4) :
    D.level3 N (rosserAncestor 3 history) ≤ D.level4 N history := by
  unfold level3 level4
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 4) hlen]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  exact_mod_cast D.exponent3_le_exponent4 hab hcheck (primeHistoryLogCoordinates N 4 history)

theorem level4_ancestor_le_level5 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 5) :
    D.level4 N (rosserAncestor 4 history) ≤ D.level5 N history := by
  unfold level4 level5
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 4 ≤ 5) hlen]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  exact_mod_cast D.exponent4_le_exponent5 hab hcheck (primeHistoryLogCoordinates N 5 history)

/-- The concrete upper policy after selecting the third cap, starting
from the ordinary upper policy at the stored original level. -/
def upperThirdPolicy (D : HistoricalPrefixCapData) (N : ℝ) : Bool → List ℕ → Bool :=
  thirdCappedUpperPolicy (ordinaryParityRosserPolicy false (N ^ (D.old : ℝ))) (D.level3 N)

def upperFourthPolicy (D : HistoricalPrefixCapData) (N : ℝ) : Bool → List ℕ → Bool :=
  fourthCappedUpperPolicy (ordinaryParityRosserPolicy false (N ^ (D.old : ℝ)))
    (D.level3 N) (D.level4 N)

def upperFifthPolicy (D : HistoricalPrefixCapData) (N : ℝ) : Bool → List ℕ → Bool :=
  fifthCappedUpperPolicy (ordinaryParityRosserPolicy false (N ^ (D.old : ℝ)))
    (D.level3 N) (D.level5 N)

/-- The concrete historical updates retain the inactive upper parity.
This structural fact supplies the odd-first-exit attachment interface; it
does not imply a support exponent or a factorization license. -/
theorem upperThirdPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperThirdPolicy N true pre = true := by
  simp [upperThirdPolicy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem upperFourthPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperFourthPolicy N true pre = true := by
  simp [upperFourthPolicy, fourthCappedUpperPolicy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem upperFifthPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperFifthPolicy N true pre = true := by
  simp [upperFifthPolicy, fifthCappedUpperPolicy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem upperFifthPolicy_eq_oddFirstExitPolicy (D : HistoricalPrefixCapData) (N : ℝ) :
    D.upperFifthPolicy N = oddFirstExitPolicy (fun pre => D.upperFifthPolicy N false pre) := by
  funext positive pre
  cases positive <;> simp [oddFirstExitPolicy, upperFifthPolicy_even]

/-- The original historical finite identity now receives its two level
comparisons from a finite rational check.  No prefix-admissibility or
own-cube-admission hypothesis is supplied by the caller. -/
theorem actual_thirdToFifthSaving_eq (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (base : Bool → List ℕ → Bool)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (thirdCappedUpperPolicy base (D.level3 (N : ℝ)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (fifthCappedUpperPolicy base (D.level3 (N : ℝ)) (D.level5 (N : ℝ)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving base (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving base (D.level3 (N : ℝ))
          (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z := by
  apply actualHistoricalThirdToFifthSaving_eq
  · intro state hstate
    apply D.level3_ancestor_le_level4 hab hcheck (N : ℝ) hN
    exact firstExitDepthFrontier_selected_length 4 _ _ [] _ true 1 (by simp) state hstate
  · intro frontier hfrontier candidate hcandidate
    have hlen := firstExitDepthFrontier_selected_length 4
      (thirdCappedUpperPolicy base (D.level3 (N : ℝ)))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z)
      true 1 (by simp) frontier hfrontier
    obtain ⟨_before, q, _after, _hremaining, rfl⟩ :=
      (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ candidate).mp hcandidate
    have hnext : (q :: frontier.selectedPrefix).length = 5 := by
      simp only [List.length_cons, hlen]
    have h := D.level4_ancestor_le_level5 hab hcheck (N : ℝ) hN
      (q :: frontier.selectedPrefix) hnext
    rw [rosserAncestor_cons 4 q frontier.selectedPrefix (by omega),
      rosserAncestor_self_of_length 4 frontier.selectedPrefix hlen] at h
    exact h

/-- Actual reciprocal-prime densities of the concrete ordinary-base
historical policies telescope with the two inherited savings. -/
theorem upperThirdToFifthSaving_eq (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z :=
  D.actual_thirdToFifthSaving_eq hab hcheck
    (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ))) N cap hN z

end HistoricalPrefixCapData

end

end ImbalancedChen
