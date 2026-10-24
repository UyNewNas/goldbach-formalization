import ImbalancedChen.P1CoarseFirstCubeFallbackMargin
import ImbalancedChen.FirstExitHistoricalLevels

/-!
Concrete fourth continuation of the ORIGINAL third coarse policy.

The third fallback is the literal effective exponent of rawLevel, frozen at
the third ancestor. It is never replaced by a constant D.old. The fourth
family is a finite filter of supplied fourth labels: its third ancestor must
be an adopted coarse cell, and its entire last-coordinate interval starts
at or above omega. The real coarse parameters are unchanged; rational e
merely permits an exact rational representation of Gamma-2e and Theta-2e.

Only later third-to-fourth comparisons are checked. No initial<=Gamma
comparison, original-table adoption, density limit or integral is asserted.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace P1OriginalCoarseContinuation

abbrev FourthCell (m : ℕ) := Fin 4 → Fin (m + 1)

def thirdCellExponent (e : ℚ) (m : ℕ) (j : FourthCell m) : ℚ :=
  HistoricalThirdCoarse.gamma (e : ℝ)
      (HistoricalThirdCoarse.box m (historicalPrefixProject (by omega : 3 ≤ 4) j)) -
    2 * e

theorem cast_thirdCellExponent (e : ℚ) (m : ℕ) (j : FourthCell m) :
    (thirdCellExponent e m j : ℝ) = HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (historicalPrefixProject (by omega : 3 ≤ 4) j)) := by
  simp [thirdCellExponent, HistoricalThirdCoarse.levelExponent]

/-- Finite selection fixed before N; no partial rough-activation cell is used. -/
def selectedFourthCells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) : Finset (FourthCell m) :=
  J4.filter (fun j =>
    historicalPrefixProject (by omega : 3 ≤ 4) j ∈
        HistoricalThirdCoarse.cells (e : ℝ) chi m ∧
      omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ))

theorem mem_selectedFourthCells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (j : FourthCell m) :
    j ∈ selectedFourthCells e chi m omega J4 ↔ j ∈ J4 ∧
      historicalPrefixProject (by omega : 3 ≤ 4) j ∈
        HistoricalThirdCoarse.cells (e : ℝ) chi m ∧
      omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ) := by
  simp only [selectedFourthCells, Finset.mem_filter]

/-- An exact rational representation of the EXISTING actual Q3 exponent. -/
def effectiveExponent3Q (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) : ℚ :=
  if P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N history then
    historicalPrefixLookup 0 (19 / 96) m
      (HistoricalThirdCoarse.cells (e : ℝ) chi m)
      (fun j => HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m j))
      (299 / 500) (primeHistoryLogCoordinates N 3 history) - 2 * e
  else (299 / 500) - 2 * e

theorem cast_effectiveExponent3Q (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    (effectiveExponent3Q e chi m omega N history : ℝ) =
      P1CoarseFirstCubeFallbackMargin.effectiveExponent (e : ℝ) chi m omega N history := by
  by_cases hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N history <;>
    simp [effectiveExponent3Q, P1CoarseFirstCubeFallbackMargin.effectiveExponent,
      hs, HistoricalThirdCoarse.exponent, HistoricalThirdCoarse.initial,
      VariableEnvelope.extendedDistributionCap]

theorem effectiveExponent3Q_fallback (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N history) :
    effectiveExponent3Q e chi m omega N history = (299 / 500) - 2 * e := by
  exact if_neg hs

theorem rawLevel_eq_rpow_effectiveExponent3Q (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (history : List ℕ) :
    HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega N history =
      N ^ (effectiveExponent3Q e chi m omega N history : ℝ) := by
  rw [cast_effectiveExponent3Q]
  exact P1CoarseFirstCubeFallbackMargin.rawLevel_eq_rpow_effectiveExponent
    (e : ℝ) chi m omega N history

theorem frozenLevel_eq_rpow_effectiveExponent3Q (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (history : List ℕ) :
    HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega N history =
      N ^ (effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) : ℝ) := by
  exact rawLevel_eq_rpow_effectiveExponent3Q e chi m omega N (rosserAncestor 3 history)

/-- The lookup uses the literal third ancestor even outside every selected
fourth cell. The length guard excludes total-dictionary padding artefacts. -/
def effectiveExponent4Q (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) : ℚ :=
  if history.length = 4 then
    historicalPrefixLookup 0 (19 / 96) m (selectedFourthCells e chi m omega J4) cap4
      (effectiveExponent3Q e chi m omega N (rosserAncestor 3 history))
      (primeHistoryLogCoordinates N 4 history)
  else effectiveExponent3Q e chi m omega N (rosserAncestor 3 history)

def effectiveExponent4 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) : ℝ :=
  (effectiveExponent4Q e chi m omega J4 cap4 N history : ℝ)

def level4 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) : ℝ :=
  N ^ effectiveExponent4 e chi m omega J4 cap4 N history

def frozenLevel4 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) : ℝ :=
  level4 e chi m omega J4 cap4 N (rosserAncestor 4 history)

/-- The actual fourth policy starts from the original first-stop initial
policy and the original raw Q3. No constant ordinary D policy is substituted. -/
def policy4 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) (N : ℝ) :
    Bool → List ℕ → Bool :=
  fourthCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) m N)
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega N)
    (level4 e chi m omega J4 cap4 N)

theorem policy4_frontier_four (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) (N : ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4 (policy4 e chi m omega J4 cap4 N) h pre positive mass carrier =
      firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
        h pre positive mass carrier := by
  exact fourthCappedUpperPolicy_frontier_four
    (HistoricalThirdCoarse.initialPolicy (e : ℝ) m N)
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega N)
    (level4 e chi m omega J4 cap4 N) h pre carrier positive mass

theorem effectiveExponent4Q_on_selected_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 4)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (ht : primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    effectiveExponent4Q e chi m omega J4 cap4 N history = cap4 j := by
  have ht' : primeHistoryLogCoordinates N 4 history ∈
      logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using ht
  unfold effectiveExponent4Q
  rw [if_pos hlen]
  exact historicalPrefixLookup_on_cell 0 (19 / 96) (by norm_num) m
    (selectedFourthCells e chi m omega J4) cap4 _ _ j hj ht'

theorem level4_on_selected_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 4)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (ht : primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    level4 e chi m omega J4 cap4 N history = N ^ (cap4 j : ℝ) := by
  unfold level4 effectiveExponent4
  rw [effectiveExponent4Q_on_selected_cell e chi m omega J4 cap4 N history hlen j hj ht]

theorem effectiveExponent4Q_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ)
    (hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
      primeHistoryLogCoordinates N 4 history ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    effectiveExponent4Q e chi m omega J4 cap4 N history =
      effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) := by
  by_cases hlen : history.length = 4
  · have hout' : ∀ j ∈ selectedFourthCells e chi m omega J4,
        primeHistoryLogCoordinates N 4 history ∉
          logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
      simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using hout
    unfold effectiveExponent4Q
    rw [if_pos hlen]
    exact historicalPrefixLookup_outside 0 (19 / 96) m
      (selectedFourthCells e chi m omega J4) cap4 _ _ hout'
  · simp only [effectiveExponent4Q, if_neg hlen]

theorem level4_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ)
    (hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
      primeHistoryLogCoordinates N 4 history ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    level4 e chi m omega J4 cap4 N history =
      HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega N history := by
  unfold level4 effectiveExponent4
  rw [effectiveExponent4Q_outside e chi m omega J4 cap4 N history hout]
  exact (frozenLevel_eq_rpow_effectiveExponent3Q e chi m omega N history).symm

/-- Whole-cell rough licensing proves the ACTUAL natural-prime activation,
including equality at omega; it is not an activation hypothesis field. -/
theorem active_ancestor3_of_wholeActive_cell (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (history : List ℕ) (hN : 1 < N) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p) (j : FourthCell m)
    (hrough : omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ))
    (ht : primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    HistoricalThirdCoarse.active omega N (rosserAncestor 3 history) := by
  have hlen3 : (rosserAncestor 3 history).length = 3 := by
    simp only [rosserAncestor_length, hlen, Nat.min_eq_left (by omega : 3 ≤ 4)]
  have hpos3 : ∀ p ∈ rosserAncestor 3 history, 0 < p := by
    intro p hp
    exact hpos p (List.mem_of_mem_drop hp)
  have ht3 : primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
      logPrimeMeshCell 0 (19 / 96) m (historicalPrefixProject (by omega : 3 ≤ 4) j) := by
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 4) hlen]
    exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht
  have hcast : (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 4) j)) 2
  have hcoord : omega ≤ primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) 2 := by
    rw [hcast] at hrough
    exact hrough.trans (mem_logPrimeMeshCell.mp ht3 2).1
  refine ⟨hlen3, ?_⟩
  have hp := Real.rpow_le_rpow_of_exponent_le hN.le hcoord
  rw [rpow_primeHistoryLogCoordinates N hN hlen3 hpos3 (2 : Fin 3)] at hp
  exact hp

theorem effectiveExponent3Q_ancestor_on_wholeActive_cell (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (history : List ℕ) (hN : 1 < N) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p) (j : FourthCell m)
    (hcoarse : historicalPrefixProject (by omega : 3 ≤ 4) j ∈
      HistoricalThirdCoarse.cells (e : ℝ) chi m)
    (hrough : omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ))
    (ht : primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) = thirdCellExponent e m j := by
  have ha := active_ancestor3_of_wholeActive_cell e chi m omega N history hN hlen hpos j hrough ht
  have ht3 : primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
      logPrimeMeshCell 0 (19 / 96) m (historicalPrefixProject (by omega : 3 ≤ 4) j) := by
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 4) hlen]
    exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht
  have hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 history) :=
    ⟨ha, historicalPrefixProject (by omega : 3 ≤ 4) j, hcoarse, ht3⟩
  have ht3' : primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
      logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m
        (historicalPrefixProject (by omega : 3 ≤ 4) j) := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using ht3
  unfold effectiveExponent3Q
  rw [if_pos hs, historicalPrefixLookup_on_cell 0 (19 / 96) (by norm_num) m
    (HistoricalThirdCoarse.cells (e : ℝ) chi m) _ (299 / 500) _
    (historicalPrefixProject (by omega : 3 ≤ 4) j) hcoarse ht3']

theorem effectiveExponent4Q_on_wholeActive_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hN : 1 < N) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p) (j : FourthCell m)
    (hcoarse : historicalPrefixProject (by omega : 3 ≤ 4) j ∈
      HistoricalThirdCoarse.cells (e : ℝ) chi m)
    (hrough : omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ))
    (ht : primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    effectiveExponent4Q e chi m omega J4 cap4 N history =
      if j ∈ selectedFourthCells e chi m omega J4 then cap4 j else thirdCellExponent e m j := by
  have ht' : primeHistoryLogCoordinates N 4 history ∈
      logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using ht
  unfold effectiveExponent4Q
  rw [if_pos hlen, historicalPrefixLookup_on_any_cell 0 (19 / 96) (by norm_num) m
    (selectedFourthCells e chi m omega J4) cap4 _ _ j ht',
    effectiveExponent3Q_ancestor_on_wholeActive_cell e chi m omega N history hN hlen hpos
      j hcoarse hrough ht]

/-- Only Q3<=Q4 on actually selected fully active fourth cells is checked. -/
def h34Check (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := selectedFourthCells e chi m omega J4)
    (p := fun j _ => thirdCellExponent e m j ≤ cap4 j))

theorem h34Check_sound (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∀ j ∈ selectedFourthCells e chi m omega J4, thirdCellExponent e m j ≤ cap4 j := by
  simpa only [h34Check, decide_eq_true_eq] using hcheck

theorem effectiveExponent3Q_ancestor_le_effectiveExponent4Q
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hcheck : h34Check e chi m omega J4 cap4 = true)
    (hN : 1 < N) (hlen : history.length = 4) (hpos : ∀ p ∈ history, 0 < p) :
    effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) ≤
      effectiveExponent4Q e chi m omega J4 cap4 N history := by
  by_cases hex : ∃ j ∈ selectedFourthCells e chi m omega J4,
      primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj, ht⟩ := hex
    have hlic := (mem_selectedFourthCells e chi m omega J4 j).mp hj
    rw [effectiveExponent4Q_on_selected_cell e chi m omega J4 cap4 N history hlen j hj ht,
      effectiveExponent3Q_ancestor_on_wholeActive_cell e chi m omega N history hN hlen hpos
        j hlic.2.1 hlic.2.2 ht]
    exact h34Check_sound e chi m omega J4 cap4 hcheck j hj
  · have hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
        primeHistoryLogCoordinates N 4 history ∉ logPrimeMeshCell 0 (19 / 96) m j := by
      simpa only [not_exists, not_and] using hex
    exact le_of_eq (effectiveExponent4Q_outside e chi m omega J4 cap4 N history hout).symm

theorem frozenLevel_le_level4 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hcheck : h34Check e chi m omega J4 cap4 = true)
    (hN : 1 < N) (hlen : history.length = 4) (hpos : ∀ p ∈ history, 0 < p) :
    HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega N history ≤
      level4 e chi m omega J4 cap4 N history := by
  rw [frozenLevel_eq_rpow_effectiveExponent3Q]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  change (effectiveExponent3Q e chi m omega N (rosserAncestor 3 history) : ℝ) ≤
    (effectiveExponent4Q e chi m omega J4 cap4 N history : ℝ)
  exact_mod_cast effectiveExponent3Q_ancestor_le_effectiveExponent4Q e chi m omega J4 cap4
    N history hcheck hN hlen hpos

theorem frozenLevel4_on_length_four (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 4) :
    frozenLevel4 e chi m omega J4 cap4 N history = level4 e chi m omega J4 cap4 N history := by
  unfold frozenLevel4
  rw [rosserAncestor_self_of_length 4 history hlen]

theorem frozenLevel4_append (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (later history : List ℕ) (hlen : 4 ≤ history.length) :
    frozenLevel4 e chi m omega J4 cap4 N (later ++ history) =
      frozenLevel4 e chi m omega J4 cap4 N history := by
  unfold frozenLevel4
  rw [rosserAncestor_append 4 later history hlen]

theorem frozenLevel4_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ)
    (hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 history) ∉
        logPrimeMeshCell 0 (19 / 96) m j) :
    frozenLevel4 e chi m omega J4 cap4 N history =
      HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega N history := by
  unfold frozenLevel4
  rw [level4_outside e chi m omega J4 cap4 N (rosserAncestor 4 history) hout]
  unfold HistoricalThirdCoarse.frozenLevel
  rw [rosserAncestor_nested 3 4 (by omega)]

/-- Failed coarse support implies no selected fourth hit, by the actual
whole-cell activation license and positivity of the original prime history. -/
theorem outside_selectedFourth_of_not_supported_ancestor
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J4 : Finset (FourthCell m))
    (N : ℝ) (history : List ℕ) (hN : 1 < N) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 history)) :
    ∀ j ∈ selectedFourthCells e chi m omega J4,
      primeHistoryLogCoordinates N 4 history ∉ logPrimeMeshCell 0 (19 / 96) m j := by
  intro j hj ht
  have hlic := (mem_selectedFourthCells e chi m omega J4 j).mp hj
  have ha := active_ancestor3_of_wholeActive_cell e chi m omega N history hN hlen hpos j hlic.2.2 ht
  apply hs
  refine ⟨ha, historicalPrefixProject (by omega : 3 ≤ 4) j, hlic.2.1, ?_⟩
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 4) hlen]
  exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht

theorem effectiveExponent4Q_fallback_of_not_supported_ancestor
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hN : 1 < N) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 history)) :
    effectiveExponent4Q e chi m omega J4 cap4 N history = (299 / 500) - 2 * e := by
  rw [effectiveExponent4Q_outside e chi m omega J4 cap4 N history
    (outside_selectedFourth_of_not_supported_ancestor e chi m omega J4 N history hN hlen hpos hs)]
  exact effectiveExponent3Q_fallback e chi m omega N (rosserAncestor 3 history) hs

theorem level4_fallback_of_not_supported_ancestor
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) (hN : 1 < N) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 history)) :
    level4 e chi m omega J4 cap4 N history = N ^ HistoricalThirdCoarse.initial (e : ℝ) := by
  rw [level4_outside e chi m omega J4 cap4 N history
    (outside_selectedFourth_of_not_supported_ancestor e chi m omega J4 N history hN hlen hpos hs)]
  exact P1ThirdFallbackSupport.frozenLevel_fallback (e : ℝ) chi m omega N history hs

/-- A literal finite range of the ORIGINAL Q3 exponent, including Theta. -/
def thirdExponentValues (e : ℚ) (chi : ℝ) (m : ℕ) : Finset ℚ :=
  insert ((299 / 500) - 2 * e)
    ((HistoricalThirdCoarse.cells (e : ℝ) chi m).image
      (fun j => HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m j) - 2 * e))

theorem effectiveExponent3Q_mem_values (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) : effectiveExponent3Q e chi m omega N history ∈ thirdExponentValues e chi m := by
  by_cases hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N history
  · have hs' := hs
    obtain ⟨_, j, hj, ht⟩ := hs'
    have ht' : primeHistoryLogCoordinates N 3 history ∈
        logPrimeMeshCell ((0 : ℚ) : ℝ) ((19 / 96 : ℚ) : ℝ) m j := by
      simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using ht
    have he : effectiveExponent3Q e chi m omega N history =
        HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m j) - 2 * e := by
      unfold effectiveExponent3Q
      rw [if_pos hs, historicalPrefixLookup_on_cell 0 (19 / 96) (by norm_num) m
        (HistoricalThirdCoarse.cells (e : ℝ) chi m) _ (299 / 500) _ j hj ht']
    rw [he]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  · rw [effectiveExponent3Q_fallback e chi m omega N history hs]
    exact Finset.mem_insert_self _ _

def fourthExponentValues (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) : Finset ℚ :=
  thirdExponentValues e chi m ∪ (selectedFourthCells e chi m omega J4).image cap4

/-- The actual fourth lookup has a finite range without any N, history,
coverage or analytic hypothesis. -/
theorem effectiveExponent4Q_mem_values (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N : ℝ) (history : List ℕ) :
    effectiveExponent4Q e chi m omega J4 cap4 N history ∈ fourthExponentValues e chi m omega J4 cap4 := by
  by_cases hlen : history.length = 4
  · by_cases hex : ∃ j ∈ selectedFourthCells e chi m omega J4,
        primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j
    · obtain ⟨j, hj, ht⟩ := hex
      rw [effectiveExponent4Q_on_selected_cell e chi m omega J4 cap4 N history hlen j hj ht]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    · have hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
          primeHistoryLogCoordinates N 4 history ∉ logPrimeMeshCell 0 (19 / 96) m j := by
        simpa only [not_exists, not_and] using hex
      rw [effectiveExponent4Q_outside e chi m omega J4 cap4 N history hout]
      exact Finset.mem_union_left _ (effectiveExponent3Q_mem_values e chi m omega N _)
  · rw [effectiveExponent4Q, if_neg hlen]
    exact Finset.mem_union_left _ (effectiveExponent3Q_mem_values e chi m omega N _)

end P1OriginalCoarseContinuation

end

end ImbalancedChen
