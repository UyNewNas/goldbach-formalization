import ImbalancedChen.P1OriginalCoarseContinuationCells
import ImbalancedChen.HistoricalPrefixCertificate

/-!
# Actual fifth continuation cells after the original coarse fourth lookup

Source-only candidate. This file consumes the original coarse fourth selector,
not `HistoricalPrefixCapData.old_le_exponent3`. The inherited fifth fallback
is the full fourth effective exponent at the projected four-coordinate point.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical List BigOperators
open Set

namespace HistoricalThirdCoarse.P1OriginalFifthCells

abbrev FifthCell (m : ℕ) := Fin 5 → Fin (m + 1)

/-- A real-valued lookup is required: the actual buffered coarse exponent
contains the real loss 2e and may be below the initial Theta fallback. -/
def fifthLookup (m : ℕ) (J : Finset (FifthCell m)) (cap : FifthCell m → ℝ)
    (fallback : ℝ) (t : Fin 5 → ℝ) : ℝ :=
  fallback + ∑ j ∈ J,
    if t ∈ logPrimeMeshCell 0 (19 / 96) m j then cap j - fallback else 0

theorem fifthLookup_on_cell (m : ℕ) (J : Finset (FifthCell m))
    (cap : FifthCell m → ℝ) (fallback : ℝ) (t : Fin 5 → ℝ)
    (j : FifthCell m) (hj : j ∈ J)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    fifthLookup m J cap fallback t = cap j := by
  unfold fifthLookup
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [if_pos ht]
    ring
  · intro q _hq hqj
    apply if_neg
    intro hq
    exact hqj (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hq ht)

theorem fifthLookup_outside (m : ℕ) (J : Finset (FifthCell m))
    (cap : FifthCell m → ℝ) (fallback : ℝ) (t : Fin 5 → ℝ)
    (hout : ∀ j ∈ J, t ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    fifthLookup m J cap fallback t = fallback := by
  unfold fifthLookup
  rw [Finset.sum_eq_zero (fun j hj => if_neg (hout j hj)), add_zero]

theorem fifthLookup_on_any_cell (m : ℕ) (J : Finset (FifthCell m))
    (cap : FifthCell m → ℝ) (fallback : ℝ) (t : Fin 5 → ℝ)
    (j : FifthCell m) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    fifthLookup m J cap fallback t = if j ∈ J then cap j else fallback := by
  by_cases hj : j ∈ J
  · rw [if_pos hj]
    exact fifthLookup_on_cell m J cap fallback t j hj ht
  · rw [if_neg hj]
    apply fifthLookup_outside
    intro q hq hqt
    have heq : q = j :=
      logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hqt ht
    subst q
    exact hj hq

theorem fifthLookup_ge_fallback (m : ℕ) (J : Finset (FifthCell m))
    (old cap : FifthCell m → ℝ) (fallback : ℝ) (t : Fin 5 → ℝ)
    (hcheck : ∀ j ∈ J, old j ≤ cap j)
    (hinherit : ∀ j ∈ J, t ∈ logPrimeMeshCell 0 (19 / 96) m j → fallback = old j) :
    fallback ≤ fifthLookup m J cap fallback t := by
  unfold fifthLookup
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with ht
  · rw [hinherit j hj ht]
    exact sub_nonneg.mpr (hcheck j hj)
  · exact le_rfl

theorem fifthLookup_apply_sub (m : ℕ) (J : Finset (FifthCell m))
    (cap : FifthCell m → ℝ) (fallback : ℝ) (t : Fin 5 → ℝ) (f : ℝ → ℝ) :
    f (fifthLookup m J cap fallback t) - f fallback =
      ∑ j ∈ J, if t ∈ logPrimeMeshCell 0 (19 / 96) m j then
        f (cap j) - f fallback else 0 := by
  by_cases hex : ∃ j ∈ J, t ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [fifthLookup_on_cell m J cap fallback t j hj ht]
    symm
    calc
      _ = (if t ∈ logPrimeMeshCell 0 (19 / 96) m j then
          f (cap j) - f fallback else 0) := by
        apply Finset.sum_eq_single_of_mem j hj
        intro q _hq hqj
        apply if_neg
        intro hq
        exact hqj (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hq ht)
      _ = _ := if_pos ht
  · have hout : ∀ j ∈ J, t ∉ logPrimeMeshCell 0 (19 / 96) m j := by
      simpa only [not_exists, not_and] using hex
    rw [fifthLookup_outside m J cap fallback t hout, sub_self]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hout j hj))

end HistoricalThirdCoarse.P1OriginalFifthCells

namespace P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse

abbrev Label4 (m : ℕ) := Fin 4 → Fin (m + 1)
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

/-- Fifth tables are fixed before N. Whole-cell activation is checked at the
projected third lower endpoint, retaining equality at the rough boundary. -/
def selectedFifthCells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) : Finset (Label5 m) :=
  J5.filter fun j =>
    historicalPrefixProject (by omega : 3 ≤ 5) j ∈ cells (e : ℝ) chi m ∧
      omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 5) j) 2 : ℝ)

theorem mem_selectedFifthCells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m) :
    j ∈ selectedFifthCells e chi m omega J5 ↔
      j ∈ J5 ∧ historicalPrefixProject (by omega : 3 ≤ 5) j ∈ cells (e : ℝ) chi m ∧
        omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
          (historicalPrefixProject (by omega : 3 ≤ 5) j) 2 : ℝ) := by
  simp only [selectedFifthCells, Finset.mem_filter]

/-- This is the effective fourth owner, including its true coarse fallback. -/
def old5 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ) (j : Label5 m) : ℚ :=
  let q := historicalPrefixProject (by omega : 4 ≤ 5) j
  if q ∈ P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4 then cap4 q
  else P1OriginalCoarseContinuation.thirdCellExponent e m q

/-- The fifth check compares only with the actual inherited fourth value.
No initial <= third comparison is present. -/
def h45Check (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := selectedFifthCells e chi m omega J5)
    (p := fun j _ => old5 e chi m omega J4 cap4 j ≤ cap5 j))

theorem h45Check_sound (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (hcheck : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    ∀ j ∈ selectedFifthCells e chi m omega J5, old5 e chi m omega J4 cap4 j ≤ cap5 j := by
  simpa only [h45Check, decide_eq_true_eq] using hcheck

theorem h45Check_of_selectedBoxCapChecks
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (I5 : Label5 m → Finset (Fin 5)) (nu5 : Label5 m → ℚ)
    (htables : ∀ j ∈ selectedFifthCells e chi m omega J5,
      cap5 j = selectedBoxCap (I5 j) (old5 e chi m omega J4 cap4 j) (nu5 j)
        (qLogPrimeMeshLo 0 (19 / 96) m j) (qLogPrimeMeshHi 0 (19 / 96) m j) ∧
      selectedBoxCapCheck (I5 j) (old5 e chi m omega J4 cap4 j) (nu5 j)
        (qLogPrimeMeshLo 0 (19 / 96) m j) (qLogPrimeMeshHi 0 (19 / 96) m j) = true) :
    h45Check e chi m omega J4 cap4 J5 cap5 = true := by
  simp only [h45Check, decide_eq_true_eq]
  intro j hj
  obtain ⟨hcap, hcheck⟩ := htables j hj
  rw [hcap]
  exact (selectedCapLower_old_le (I5 j) (old5 e chi m omega J4 cap4 j) _).trans
    (selectedBoxCap_between (I5 j) (old5 e chi m omega J4 cap4 j) (nu5 j) _ _ hcheck).1.le

/-- Outside selected fifth cells, including outside the mesh, the fallback is
the original fourth effective lookup on the exact fourth ancestor. -/
def effectiveExponent5Q (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) : ℚ :=
  let inherited := P1OriginalCoarseContinuation.effectiveExponent4Q
    e chi m omega J4 cap4 N (rosserAncestor 4 pre)
  if pre.length = 5 then historicalPrefixLookup 0 (19 / 96) m
    (selectedFifthCells e chi m omega J5) cap5 inherited (primeHistoryLogCoordinates N 5 pre)
  else inherited

def effectiveExponent5 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) : ℝ :=
  (effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre : ℝ)

def level5 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) : ℝ :=
  N ^ effectiveExponent5 e chi m omega J4 cap4 J5 cap5 N pre

def frozenLevel5 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) : ℝ :=
  level5 e chi m omega J4 cap4 J5 cap5 N (rosserAncestor 5 pre)

def policy5 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N : ℝ) : Bool → List ℕ → Bool :=
  fifthCappedUpperPolicy (initialPolicy (e : ℝ) m N) (rawLevel (e : ℝ) chi m omega N)
    (level5 e chi m omega J4 cap4 J5 cap5 N)

theorem effectiveExponent5Q_on_selected_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre = cap5 j := by
  have ht' : primeHistoryLogCoordinates N 5 pre ∈
      logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using ht
  unfold effectiveExponent5Q
  rw [if_pos hlen]
  exact historicalPrefixLookup_on_cell 0 (19 / 96) (by norm_num) m
    (selectedFifthCells e chi m omega J5) cap5 _ _ j hj ht'

theorem effectiveExponent5Q_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ)
    (hout : ∀ j ∈ selectedFifthCells e chi m omega J5,
      primeHistoryLogCoordinates N 5 pre ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre =
      P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 N
        (rosserAncestor 4 pre) := by
  have hout' : ∀ j ∈ selectedFifthCells e chi m omega J5,
      primeHistoryLogCoordinates N 5 pre ∉
        logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using hout
  unfold effectiveExponent5Q
  split_ifs
  · exact historicalPrefixLookup_outside 0 (19 / 96) m _ _ _ _ hout'
  · rfl

theorem level5_on_selected_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    level5 e chi m omega J4 cap4 J5 cap5 N pre = N ^ (cap5 j : ℝ) := by
  unfold level5 effectiveExponent5
  rw [effectiveExponent5Q_on_selected_cell e chi m omega J4 cap4 J5 cap5 N pre hlen j hj ht]

/-- The selected fifth owner reads the same projected-fourth effective cell,
whether fourth selection supplied cap4 or the original active coarse Gamma. -/
theorem inherited_fourth_on_selected_fifth_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (N : ℝ) (pre : List ℕ) (hN : 1 < N)
    (hlen : pre.length = 5) (hpos : ∀ p ∈ pre, 0 < p)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 N
        (rosserAncestor 4 pre) = old5 e chi m omega J4 cap4 j := by
  have hmem := (mem_selectedFifthCells e chi m omega J5 j).mp hj
  have hlen4 : (rosserAncestor 4 pre).length = 4 := by rw [rosserAncestor_length]; omega
  have hpos4 : ∀ p ∈ rosserAncestor 4 pre, 0 < p := by
    intro p hp
    exact hpos p (List.mem_of_mem_drop hp)
  have ht4 : primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) ∈
      logPrimeMeshCell 0 (19 / 96) m (historicalPrefixProject (by omega : 4 ≤ 5) j) := by
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 4 ≤ 5) hlen]
    exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht
  have hc : historicalPrefixProject (by omega : 3 ≤ 4)
      (historicalPrefixProject (by omega : 4 ≤ 5) j) ∈ cells (e : ℝ) chi m := by
    simpa only [historicalPrefixProject_comp] using hmem.2.1
  have hr : omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 4)
        (historicalPrefixProject (by omega : 4 ≤ 5) j)) 2 : ℝ) := by
    simpa only [historicalPrefixProject_comp] using hmem.2.2
  exact P1OriginalCoarseContinuation.effectiveExponent4Q_on_wholeActive_cell
    e chi m omega J4 cap4 N (rosserAncestor 4 pre) hN hlen4 hpos4
    (historicalPrefixProject (by omega : 4 ≤ 5) j) hc hr ht4

theorem effectiveExponent4Q_ancestor_le_effectiveExponent5Q
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hcheck : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (hN : 1 < N) (hlen : pre.length = 5) (hpos : ∀ p ∈ pre, 0 < p) :
    P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 N
        (rosserAncestor 4 pre) ≤ effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre := by
  unfold effectiveExponent5Q
  rw [if_pos hlen]
  apply historicalPrefixLookup_ge_fallback 0 (19 / 96) m
    (selectedFifthCells e chi m omega J5) (old5 e chi m omega J4 cap4) cap5 _ _
    (h45Check_sound e chi m omega J4 cap4 J5 cap5 hcheck)
  intro j hj ht
  apply inherited_fourth_on_selected_fifth_cell e chi m omega J4 cap4 J5 N pre hN hlen hpos j hj
  simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using ht

/-- Exact cell decomposition for any function of the new and inherited caps;
the old value in every summand is that same owner's actual old5. -/
theorem effectiveExponent5Q_apply_sub
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hN : 1 < N) (hlen : pre.length = 5)
    (hpos : ∀ p ∈ pre, 0 < p) (f : ℚ → ℝ) :
    f (effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre) -
      f (P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 N
        (rosserAncestor 4 pre)) =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        if primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) m j then
          f (cap5 j) - f (old5 e chi m omega J4 cap4 j) else 0 := by
  unfold effectiveExponent5Q
  rw [if_pos hlen, historicalPrefixLookup_apply_sub 0 (19 / 96) (by norm_num)]
  simp only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) m j
  · have hinherit := inherited_fourth_on_selected_fifth_cell
      e chi m omega J4 cap4 J5 N pre hN hlen hpos j hj ht
    simp only [if_pos ht, hinherit]
  · simp only [if_neg ht]

theorem level4_ancestor_le_level5
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hcheck : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (hN : 1 < N) (hlen : pre.length = 5) (hpos : ∀ p ∈ pre, 0 < p) :
    P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 N (rosserAncestor 4 pre) ≤
      level5 e chi m omega J4 cap4 J5 cap5 N pre := by
  change N ^ (P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 N
      (rosserAncestor 4 pre) : ℝ) ≤
    N ^ (effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre : ℝ)
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  exact_mod_cast effectiveExponent4Q_ancestor_le_effectiveExponent5Q
    e chi m omega J4 cap4 J5 cap5 N pre hcheck hN hlen hpos

theorem level5_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N : ℝ) (pre : List ℕ)
    (hout : ∀ j ∈ selectedFifthCells e chi m omega J5,
      primeHistoryLogCoordinates N 5 pre ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    level5 e chi m omega J4 cap4 J5 cap5 N pre =
      P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 N (rosserAncestor 4 pre) := by
  change N ^ (effectiveExponent5Q e chi m omega J4 cap4 J5 cap5 N pre : ℝ) = _
  rw [effectiveExponent5Q_outside e chi m omega J4 cap4 J5 cap5 N pre hout]
  rfl

theorem frozenLevel5_append (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (later pre : List ℕ) (hlen : 5 ≤ pre.length) :
    frozenLevel5 e chi m omega J4 cap4 J5 cap5 N (later ++ pre) =
      frozenLevel5 e chi m omega J4 cap4 J5 cap5 N pre := by
  unfold frozenLevel5
  rw [rosserAncestor_append 5 later pre hlen]

theorem frozenLevel5_on_length_five (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 5) :
    frozenLevel5 e chi m omega J4 cap4 J5 cap5 N pre =
      level5 e chi m omega J4 cap4 J5 cap5 N pre := by
  unfold frozenLevel5
  rw [rosserAncestor_self_of_length 5 pre hlen]

theorem policy5_through_four (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    policy5 e chi m omega J4 cap4 J5 cap5 N positive pre =
      HistoricalThirdCoarse.policy (e : ℝ) chi m omega N positive pre := by
  simp only [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy, if_pos hlen]
  rfl

/-- The successful finite check gives the actual h45 on every original coarse
rank-four frontier and every next candidate, including old-rejected candidates. -/
theorem h45_actual
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (hcheck : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hc : candidate ∈ firstExitNextSelectionCandidates (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining) :
    P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ) frontier.selectedPrefix ≤
      level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ) candidate.selectedPrefix := by
  obtain ⟨hlen, _, _, _, _, _, _, hprime⟩ :=
    actualPrimeNextSelection_geometry 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      N cap z frontier hf candidate hc
  have hfrontlen := firstExitDepthFrontier_selected_length 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1 (by simp) frontier hf
  obtain ⟨before, q, after, hremaining, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.remaining frontier.positive frontier.mass candidate).mp hc
  have ha : rosserAncestor 4 candidate.selectedPrefix = frontier.selectedPrefix := by
    rw [hstate]
    calc
      rosserAncestor 4 (q :: frontier.selectedPrefix) = rosserAncestor 4 frontier.selectedPrefix :=
        rosserAncestor_cons 4 q frontier.selectedPrefix (by omega)
      _ = frontier.selectedPrefix := rosserAncestor_self_of_length 4 frontier.selectedPrefix hfrontlen
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hh := level4_ancestor_le_level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)
    candidate.selectedPrefix hcheck hNr hlen (fun p hp => (hprime p hp).pos)
  simpa only [ha] using hh

/-- The sibling fourth checker discharges the original coarse h34 on this
same actual frontier, preserving the original firstStop base and raw Q3. -/
theorem h34_actual
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (hcheck : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) :
    rawLevel (e : ℝ) chi m omega (N : ℝ) (rosserAncestor 3 state.selectedPrefix) ≤
      P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ) state.selectedPrefix := by
  have hlen := firstExitDepthFrontier_selected_length 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1 (by simp) state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) state hs
  have hpos : ∀ p ∈ state.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  exact P1OriginalCoarseContinuation.frozenLevel_le_level4
    e chi m omega J4 cap4 (N : ℝ) state.selectedPrefix hcheck hNr hlen hpos

/-- Actual fourth-to-fifth saving for the original coarse policy. Neither
checker compares the initial Theta cap with the possibly smaller third cap. -/
theorem actualFourthToFifthSaving_eq
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    firstExitRetainedPolynomial
        (fourthCappedUpperPolicy (initialPolicy (e : ℝ) m (N : ℝ))
          (rawLevel (e : ℝ) chi m omega (N : ℝ))
          (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (policy5 e chi m omega J4 cap4 J5 cap5 (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFifthSaving (initialPolicy (e : ℝ) m (N : ℝ))
        (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap z := by
  apply actualHistoricalFifthSaving_eq
  · intro state hs
    exact h34_actual e chi m omega J4 cap4 h34 N cap hN z state hs
  · intro frontier hf candidate hc
    exact h45_actual e chi m omega J4 cap4 J5 cap5 h45 N cap hN z frontier hf candidate hc

/-- The two concrete finite checks assemble the original third-to-fifth
telescoping identity, with actual separately gated fifth residuals. -/
theorem actualThirdToFifthSaving_eq
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    firstExitRetainedPolynomial (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (policy5 e chi m omega J4 cap4 J5 cap5 (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving (initialPolicy (e : ℝ) m (N : ℝ))
        (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)) N cap z +
      actualHistoricalFifthSaving (initialPolicy (e : ℝ) m (N : ℝ))
        (rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
        (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ)) N cap z := by
  apply actualHistoricalThirdToFifthSaving_eq
  · intro state hs
    exact h34_actual e chi m omega J4 cap4 h34 N cap hN z state hs
  · intro frontier hf candidate hc
    exact h45_actual e chi m omega J4 cap4 J5 cap5 h45 N cap hN z frontier hf candidate hc

end P1OriginalCoarseFifthContinuation
end
end ImbalancedChen
