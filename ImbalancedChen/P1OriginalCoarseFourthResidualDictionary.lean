import ImbalancedChen.P1OriginalCoarseContinuationCells
import ImbalancedChen.ActualHistoricalFourthResidualDictionaryP1

/-!
Exact admitted-fourth residual dictionaries for the original coarse policy.
No finite signed residual sign or arithmetic mean is used.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace P1OriginalCoarseFourthResidual

open P1OriginalCoarseContinuation

def tupleHistory (p : Fin 4 → ℕ) : List ℕ := (List.ofFn p).reverse

theorem tupleHistory_primeHistoryTuple (history : List ℕ) (hlen : history.length = 4) :
    tupleHistory (primeHistoryTuple 4 history) = history := by
  unfold tupleHistory
  rw [primeHistoryTuple_ofFn hlen, List.reverse_reverse]

theorem primeHistoryTuple_tupleHistory (p : Fin 4 → ℕ) :
    primeHistoryTuple 4 (tupleHistory p) = p := by
  apply List.ofFn_injective
  rw [primeHistoryTuple_ofFn (show (tupleHistory p).length = 4 by simp [tupleHistory])]
  simp only [tupleHistory, List.reverse_reverse]

theorem tupleHistory_log (N : ℕ) (p : Fin 4 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 4 (tupleHistory p) = actualPrimeTupleLog N p := by
  rw [primeHistoryLogCoordinates_eq_actualPrimeTupleLog, primeHistoryTuple_tupleHistory]

theorem tupleHistory_pos (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) :
    ∀ q ∈ tupleHistory p, 0 < q := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hq)
  exact hp i

/-- Literal actual quotient levels are used here, before any logarithmic
cell identity. In particular Q3 is allowed to be the original rawLevel. -/
def literalTupleResidualDifference (Q3 Q4 : List ℕ → ℝ)
    (N cap : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  (actualSmallRosserPlusDensity N cap (p (Fin.last 3) : ℝ)
      (Q3 (rosserAncestor 3 (tupleHistory p)) / (∏ i, p i : ℕ)) -
    actualSmallRosserPlusDensity N cap (p (Fin.last 3) : ℝ)
      (Q4 (tupleHistory p) / (∏ i, p i : ℕ))) *
    Real.log (N : ℝ) / singularSeries N

theorem literalTupleResidualDifference_history (Q3 Q4 : List ℕ → ℝ)
    (N cap : ℕ) (history : List ℕ) (hlen : history.length = 4) :
    literalTupleResidualDifference Q3 Q4 N cap (primeHistoryTuple 4 history) =
      (actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
          (Q3 (rosserAncestor 3 history) / (history.prod : ℝ)) -
        actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ)
          (Q4 history / (history.prod : ℝ))) *
        Real.log (N : ℝ) / singularSeries N := by
  unfold literalTupleResidualDifference
  rw [tupleHistory_primeHistoryTuple history hlen,
    primeHistoryTuple_last (k := 3) hlen, primeHistoryTuple_prod hlen]

/-- The primitive history-to-admitted-tuple theorem is valid for the
literal initial first-stop policy as well as ordinary policies. -/
theorem actualHistoricalFourthSaving_eq_literalTupleSum
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFourthSaving base Q3 Q4 N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitAdmittedTuples 4 (thirdCappedUpperPolicy base Q3)
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) * literalTupleResidualDifference Q3 Q4 N cap p := by
  let parent := thirdCappedUpperPolicy base Q3
  let h (q : ℕ) := 1 / ((q : ℝ) - 1)
  let states := firstExitDepthFrontier 4 parent h [] true 1 (roughPrimeUniverse N cap 0 z)
  have hn : actualHistoricalFourthSaving base Q3 Q4 N cap z *
      Real.log (N : ℝ) / singularSeries N =
      (states.map (fun s =>
        (actualFrozenFrontierDensityTerm false N cap
            (fun pre => Q3 (rosserAncestor 3 pre)) s.selectedPrefix -
          actualFrozenFrontierDensityTerm false N cap Q4 s.selectedPrefix) *
          (Real.log (N : ℝ) / singularSeries N))).sum := by
    simp only [List.sum_map_mul_right]
    change _ * Real.log (N : ℝ) / singularSeries N =
      actualHistoricalFourthSaving base Q3 Q4 N cap z *
        (Real.log (N : ℝ) / singularSeries N)
    ring
  rw [hn]
  have heq : (states.map (fun s =>
      (actualFrozenFrontierDensityTerm false N cap
          (fun pre => Q3 (rosserAncestor 3 pre)) s.selectedPrefix -
        actualFrozenFrontierDensityTerm false N cap Q4 s.selectedPrefix) *
        (Real.log (N : ℝ) / singularSeries N))).sum =
      (states.map (fun s => (s.selectedPrefix.map h).prod *
        literalTupleResidualDifference Q3 Q4 N cap
          (primeHistoryTuple 4 s.selectedPrefix))).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    have hlen : s.selectedPrefix.length = 4 :=
      firstExitDepthFrontier_selected_length 4 parent h []
        (roughPrimeUniverse N cap 0 z) true 1 (by simp) s hs
    rw [actualFrozenFrontierDensityTerm_four_eq_plusP1 N cap _ _ hlen,
      actualFrozenFrontierDensityTerm_four_eq_plusP1 N cap _ _ hlen,
      literalTupleResidualDifference_history Q3 Q4 N cap _ hlen]
    dsimp [h]
    ring
  rw [heq]
  exact firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 4 parent h
    (roughPrimeUniverse N cap 0 z) (roughPrimeUniverse_nodup N cap 0 z)
    (literalTupleResidualDifference Q3 Q4 N cap)

def coarseTupleResidualDifference (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  literalTupleResidualDifference
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
    (level4 e chi m omega J4 cap4 (N : ℝ)) N cap p

def coarseCellPrimeCorrection (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (z : ℝ) (j : FourthCell m) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 z),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
        then coarseTupleResidualDifference e chi m omega J4 cap4 N cap p else 0)

/-- Globally, the old exponent remains the exact original Gamma/Theta
lookup with rough activation, including its original outside fallback. -/
theorem coarseTupleResidualDifference_eq_effectiveExponents
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (p : Fin 4 → ℕ) :
    coarseTupleResidualDifference e chi m omega J4 cap4 N cap p =
      fourthTuplePlusResidualP1 N cap
          (effectiveExponent3Q e chi m omega (N : ℝ)
            (rosserAncestor 3 (tupleHistory p)) : ℝ) p -
        fourthTuplePlusResidualP1 N cap
          (effectiveExponent4Q e chi m omega J4 cap4 (N : ℝ) (tupleHistory p) : ℝ) p := by
  unfold coarseTupleResidualDifference literalTupleResidualDifference
  rw [rawLevel_eq_rpow_effectiveExponent3Q]
  unfold level4 effectiveExponent4 fourthTuplePlusResidualP1
  ring

theorem coarseTupleResidualDifference_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (p : Fin 4 → ℕ)
    (hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
      actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    coarseTupleResidualDifference e chi m omega J4 cap4 N cap p = 0 := by
  have hlevel := level4_outside e chi m omega J4 cap4 (N : ℝ) (tupleHistory p)
    (by simpa only [tupleHistory_log] using hout)
  unfold coarseTupleResidualDifference literalTupleResidualDifference
  rw [hlevel]
  simp only [HistoricalThirdCoarse.frozenLevel, sub_self, zero_mul, zero_div]

theorem coarseTupleResidualDifference_on_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    coarseTupleResidualDifference e chi m omega J4 cap4 N cap p =
      fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
        fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p := by
  have hlen : (tupleHistory p).length = 4 := by simp [tupleHistory]
  have ht' : primeHistoryLogCoordinates (N : ℝ) 4 (tupleHistory p) ∈
      logPrimeMeshCell 0 (19 / 96) m j := by simpa only [tupleHistory_log] using ht
  have hlic := (mem_selectedFourthCells e chi m omega J4 j).mp hj
  have hexp := effectiveExponent3Q_ancestor_on_wholeActive_cell e chi m omega (N : ℝ)
    (tupleHistory p) (by exact_mod_cast hN) hlen (tupleHistory_pos p hp)
    j hlic.2.1 hlic.2.2 ht'
  have hold := rawLevel_eq_rpow_effectiveExponent3Q e chi m omega (N : ℝ)
    (rosserAncestor 3 (tupleHistory p))
  rw [hexp] at hold
  have hnew := level4_on_selected_cell e chi m omega J4 cap4 (N : ℝ)
    (tupleHistory p) hlen j hj ht'
  unfold coarseTupleResidualDifference literalTupleResidualDifference
  rw [hold, hnew]
  unfold fourthTuplePlusResidualP1
  ring

/-- An unselected owned cell cancels against its original raw Q3 fallback. -/
theorem coarseTupleResidualDifference_on_unselected_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (p : Fin 4 → ℕ) (j : FourthCell m)
    (hj : j ∉ selectedFourthCells e chi m omega J4)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    coarseTupleResidualDifference e chi m omega J4 cap4 N cap p = 0 := by
  apply coarseTupleResidualDifference_outside e chi m omega J4 cap4 N cap p
  intro q hq htq
  have hqj : q = j :=
    logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) htq ht
  exact hj (hqj ▸ hq)

theorem coarseTupleResidualDifference_eq_cell_indicators
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (p : Fin 4 → ℕ) :
    coarseTupleResidualDifference e chi m omega J4 cap4 N cap p =
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
          then coarseTupleResidualDifference e chi m omega J4 cap4 N cap p else 0 := by
  by_cases hex : ∃ j ∈ selectedFourthCells e chi m omega J4,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [if_pos ht]
    · intro q _hq hqj
      apply if_neg
      intro htq
      exact hqj (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) htq ht)
  · have hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
        actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) m j := by
      simpa only [not_exists, not_and] using hex
    rw [coarseTupleResidualDifference_outside e chi m omega J4 cap4 N cap p hout]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hout j hj))

/-- This is the actual original first-stop/coarse-policy admitted carrier. -/
theorem actualSaving_eq_tupleSum (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (level4 e chi m omega J4 cap4 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitAdmittedTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          coarseTupleResidualDifference e chi m omega J4 cap4 N cap p := by
  exact actualHistoricalFourthSaving_eq_literalTupleSum
    (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
    (level4 e chi m omega J4 cap4 (N : ℝ)) N cap z

theorem actualSaving_eq_cells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (level4 e chi m omega J4 cap4 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        coarseCellPrimeCorrection e chi m omega J4 cap4 N cap z j := by
  rw [actualSaving_eq_tupleSum]
  calc
    _ = ∑ p ∈ firstExitAdmittedTuples 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          ∑ j ∈ selectedFourthCells e chi m omega J4,
            if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
              then coarseTupleResidualDifference e chi m omega J4 cap4 N cap p else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact congrArg (fun x : ℝ => (∏ i, 1 / ((p i : ℝ) - 1)) * x)
        (coarseTupleResidualDifference_eq_cell_indicators e chi m omega J4 cap4 N cap p)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl

theorem admittedTuple_pos (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) (p : Fin 4 → ℕ)
    (hp : p ∈ firstExitAdmittedTuples 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 z)) : ∀ i, 0 < p i := by
  have hsub := (mem_firstExitAdmittedTuples_iff 4 _ _ p).mp hp
  intro i
  exact (mem_roughPrimeUniverse_prime
    (hsub.1.subset (List.mem_ofFn.mpr ⟨i, rfl⟩))).pos

/-- Old lambda is the true Gamma-2e coarse owner, not a substitute D.old. -/
theorem cellCorrection_eq_capResidualSum (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4) :
    coarseCellPrimeCorrection e chi m omega J4 cap4 N cap z j =
      ∑ p ∈ firstExitAdmittedTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
              fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p else 0) := by
  unfold coarseCellPrimeCorrection
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · rw [if_pos ht, if_pos ht,
      coarseTupleResidualDifference_on_cell e chi m omega J4 cap4 N cap hN p
        (admittedTuple_pos e chi m omega N cap z p hp) j hj ht]
  · rw [if_neg ht, if_neg ht]

theorem coarseCellPrimeCorrection_eq_zero_of_unselected
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (z : ℝ) (j : FourthCell m)
    (hj : j ∉ selectedFourthCells e chi m omega J4) :
    coarseCellPrimeCorrection e chi m omega J4 cap4 N cap z j = 0 := by
  unfold coarseCellPrimeCorrection
  apply Finset.sum_eq_zero
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · rw [if_pos ht,
      coarseTupleResidualDifference_on_unselected_cell e chi m omega J4 cap4 N cap p j hj ht,
      mul_zero]
  · rw [if_neg ht, mul_zero]

theorem actualSaving_eq_capResidualCells (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    actualHistoricalFourthSaving (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (level4 e chi m omega J4 cap4 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        ∑ p ∈ firstExitAdmittedTuples 4
            (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
            (roughPrimeUniverse N cap 0 z),
          (∏ i, 1 / ((p i : ℝ) - 1)) *
            (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
              fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
                fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p else 0) := by
  rw [actualSaving_eq_cells]
  apply Finset.sum_congr rfl
  intro j hj
  exact cellCorrection_eq_capResidualSum e chi m omega J4 cap4 N cap hN z j hj

/-- Exact compact truncation plus its explicit small-coordinate remainder.
There is no deletion or asymptotic assertion about that remainder. -/
theorem cellCorrection_eq_positiveTruncation_add_smallRemainder
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (z a : ℝ) (j : FourthCell m)
    (hj : j ∈ selectedFourthCells e chi m omega J4) :
    coarseCellPrimeCorrection e chi m omega J4 cap4 N cap z j =
      (∑ p ∈ (firstExitAdmittedTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z)).filter
            (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
              fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p else 0)) +
      ∑ p ∈ (firstExitAdmittedTuples 4
          (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z)).filter
            (fun p => ∃ i, actualPrimeTupleLog N p i < a),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
              fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p else 0) := by
  rw [cellCorrection_eq_capResidualSum e chi m omega J4 cap4 N cap hN z j hj]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hlarge : ∀ i, a ≤ actualPrimeTupleLog N p i
  · have hsmall : ¬∃ i, actualPrimeTupleLog N p i < a := by
      rintro ⟨i, hi⟩
      exact not_lt_of_ge (hlarge i) hi
    rw [if_pos hlarge, if_neg hsmall, add_zero]
  · have hsmall : ∃ i, actualPrimeTupleLog N p i < a := by
      simpa only [not_forall, not_le] using hlarge
    rw [if_neg hlarge, if_pos hsmall, zero_add]

end P1OriginalCoarseFourthResidual

end

end ImbalancedChen
