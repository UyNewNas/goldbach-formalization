import ImbalancedChen.P1HistoricalFourthArithmeticWallStrip
import ImbalancedChen.P1HistoricalUpperFourthPhysicalGates
import ImbalancedChen.ActualHistoricalFourthResidualDictionaryP1
import ImbalancedChen.P1ActualUpperNearOneBound

/-!
# Actual fourth residual payment on the near-s=1 strip

The old and new PLUS residuals have the same actual natural tuple product,
the same last-prime cutoff, and the original log(N)/singularSeries(N)
normalization.  The arithmetic strip is the literal admitted rank-four
strip on the SAME historical T3 cell used in the original correction.

The uniform residual bound below is obtained from the source-only proved
endpoint supplier `exists_p1_fourthTuplePlusResidual_uniform_bound`.
It is not a hypothesis of the final payment theorems.  The two residuals
cost the same constant twice.  The actual wall mass then supplies any
requested finite-family reserve with width chosen before the threshold.

Source-only sibling imports must be installed under their proposed module
names.  This candidate has not been compiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set
open P1HistoricalFourthArithmeticWallStrip

namespace P1HistoricalFourthResidualWallPayment

def tupleWeight (p : Fin 4 → ℕ) : ℝ := ∏ i, 1 / ((p i : ℝ) - 1)

/-- The complete old/new absolute payment on the old near-wall carrier. -/
def wallResidualPairAbsSum (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : ℝ :=
  ∑ p ∈ admittedWallTuples D N cap j delta,
    tupleWeight p * (|fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p| +
      |fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p|)

/-- The near-wall part of the literal original normalized correction. -/
def wallCellCorrection (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : ℝ :=
  ∑ p ∈ admittedWallTuples D N cap j delta,
    tupleWeight p * D.fourthTupleResidualDifferenceP1 N cap p

/-- Its complementary actual finite sum, with every original predicate kept. -/
def awayCellCorrection (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    tupleWeight p *
      (if actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
          ¬inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p)
        then D.fourthTupleResidualDifferenceP1 N cap p else 0)

/-- The directly usable strict clipped sum, with the same normalized residual. -/
def strictClipCellCorrection (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    tupleWeight p *
      (if actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
          delta < (D.old4 j : ℝ) - (∑ i, actualPrimeTupleLog N p i) -
            actualPrimeTupleLog N p 3
        then D.fourthTupleResidualDifferenceP1 N cap p else 0)

/-- Closed clipping matches the geometric region oldGap>=delta exactly. -/
def closedClipCellCorrection (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    tupleWeight p *
      (if actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
          delta ≤ (D.old4 j : ℝ) - (∑ i, actualPrimeTupleLog N p i) -
            actualPrimeTupleLog N p 3
        then D.fourthTupleResidualDifferenceP1 N cap p else 0)

/-- Exact finite splitting, prior to any asymptotic or positivity estimate. -/
theorem cellCorrection_eq_wall_add_away (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    D.fourthCellPrimeCorrectionP1 N cap j =
      wallCellCorrection D N cap j delta + awayCellCorrection D N cap j delta := by
  unfold HistoricalPrefixCapData.fourthCellPrimeCorrectionP1
    wallCellCorrection admittedWallTuples awayCellCorrection tupleWeight
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j <;>
    by_cases hs : inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p) <;>
    simp [ht, hs]

/-- The cell identity also covers unselected owners via their inherited cell4. -/
theorem tupleDifference_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (j : Fin 4 → Fin (D.m + 1)) (p : Fin 4 → ℕ)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fourthTupleResidualDifferenceP1 N cap p =
      fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p -
        fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p := by
  unfold HistoricalPrefixCapData.fourthTupleResidualDifferenceP1
  rw [D.exponent4_on_cell hab _ j ht,
    D.exponent3_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht)]
  rfl

/-- On adopted cells the new residual is exactly the original cap4 residual. -/
theorem wallResidualPairAbsSum_eq_cap4 (D : HistoricalPrefixCapData) (N cap : ℕ)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) (delta : ℝ) :
    wallResidualPairAbsSum D N cap j delta =
      ∑ p ∈ admittedWallTuples D N cap j delta,
        tupleWeight p * (|fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p| +
          |fourthTuplePlusResidualP1 N cap (D.cap4 j : ℝ) p|) := by
  simp only [wallResidualPairAbsSum, HistoricalPrefixCapData.cell4, if_pos hj]

/-- The exact finite dictionary gives positivity without assumptions on weights. -/
theorem wall_tupleWeight_nonneg
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) {p : Fin 4 → ℕ}
    (hp : p ∈ admittedWallTuples D N cap j delta) :
    0 ≤ tupleWeight p := by
  rw [admittedWallTuples_eq_cube_filter D hab hcheck N cap hN hcap j delta] at hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- These are literally the two absolute sums of the weighted residuals. -/
theorem wallResidualPairAbsSum_eq_two_abs_sums
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    wallResidualPairAbsSum D N cap j delta =
      (∑ p ∈ admittedWallTuples D N cap j delta,
        |tupleWeight p * fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p|) +
      (∑ p ∈ admittedWallTuples D N cap j delta,
        |tupleWeight p * fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p|) := by
  unfold wallResidualPairAbsSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hw := wall_tupleWeight_nonneg D hab hcheck N cap hN hcap j delta hp
  simp only [abs_mul, abs_of_nonneg hw]
  ring

/-- The original correction's wall part is paid by those same two sums. -/
theorem abs_wallCellCorrection_le_pair
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    |wallCellCorrection D N cap j delta| ≤ wallResidualPairAbsSum D N cap j delta := by
  unfold wallCellCorrection wallResidualPairAbsSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hw := wall_tupleWeight_nonneg D hab hcheck N cap hN hcap j delta hp
  have ht := (Finset.mem_filter.mp hp).2.1
  rw [tupleDifference_on_cell D hab.le N cap j p ht, abs_mul, abs_of_nonneg hw]
  apply mul_le_mul_of_nonneg_left _ hw
  simpa only [sub_zero, zero_sub, abs_neg] using
    (abs_sub_le (fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p) 0
      (fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p))

/-- If either new residual is near its wall, the original old strip pays it.
Both legality and old<=new are conclusions about the actual T3 tuple. -/
theorem new_near_wall_implies_old
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) (p : Fin 4 → ℕ)
    (hp : p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (hs : inOldWallStrip (D.cell4 j : ℝ) delta (actualPrimeTupleLog N p)) :
    inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p) := by
  have hlegal := p1_admittedFourth_plusLegality_on_cell D hab hcheck N cap hN hcap p j hp ht
  have hlevels : (D.old4 j : ℝ) ≤ D.cell4 j := by
    exact_mod_cast D.p1_old4_le_cell4 hcheck j
  exact ⟨by linarith [hlegal.2.1], by linarith [hs.2]⟩

/-- Actual T3 legality identifies the complement exactly with gap>delta.
No tuple at the original s=1 wall has been silently discarded. -/
theorem awayCellCorrection_eq_strictClip
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    awayCellCorrection D N cap j delta = strictClipCellCorrection D N cap j delta := by
  unfold awayCellCorrection strictClipCellCorrection
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · have hlegal := p1_admittedFourth_plusLegality_on_cell D hab hcheck N cap hN hcap p j hp ht
    have hpos : 0 < (D.old4 j : ℝ) - (∑ i, actualPrimeTupleLog N p i) -
        actualPrimeTupleLog N p 3 := by linarith [hlegal.2.1]
    have hiff : ¬inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p) ↔
        delta < (D.old4 j : ℝ) - (∑ i, actualPrimeTupleLog N p i) -
          actualPrimeTupleLog N p 3 := by
      constructor
      · intro hn
        exact lt_of_not_ge (fun hh => hn ⟨hpos, hh⟩)
      · intro hh hs
        linarith [hs.2]
    simp only [ht, true_and, hiff]
  · simp only [ht, false_and, if_false, mul_zero]

/-- The closed clip removes only 0<oldGap<delta, which is contained in
the already-budgeted strip 0<oldGap<=delta, including all endpoint cases. -/
theorem abs_cellCorrection_sub_closedClip_le_pair
    (D : HistoricalPrefixCapData) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ) :
    |D.fourthCellPrimeCorrectionP1 N cap j - closedClipCellCorrection D N cap j delta| ≤
      wallResidualPairAbsSum D N cap j delta := by
  unfold HistoricalPrefixCapData.fourthCellPrimeCorrectionP1 closedClipCellCorrection
    wallResidualPairAbsSum admittedWallTuples
  simp only [tupleWeight]
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
  · by_cases hs : inOldWallStrip (D.old4 j : ℝ) delta (actualPrimeTupleLog N p)
    · have hpstrip : p ∈ admittedWallTuples D N cap j delta :=
        Finset.mem_filter.mpr ⟨hp, ht, hs⟩
      have hw := wall_tupleWeight_nonneg D hab hcheck N cap hN hcap j delta hpstrip
      by_cases hdelta : delta ≤ (D.old4 j : ℝ) - (∑ i, actualPrimeTupleLog N p i) -
          actualPrimeTupleLog N p 3
      · simp only [ht, hs, hdelta, true_and, and_self, if_true, sub_self, abs_zero]
        exact mul_nonneg hw (add_nonneg (abs_nonneg _) (abs_nonneg _))
      · simp only [ht, hs, hdelta, true_and, and_self, if_true, if_false, mul_zero, sub_zero]
        rw [tupleDifference_on_cell D hab.le N cap j p ht, abs_mul, abs_of_nonneg hw]
        apply mul_le_mul_of_nonneg_left _ hw
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p) 0
            (fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p))
    · have hlegal := p1_admittedFourth_plusLegality_on_cell
        D hab.le hcheck N cap hN hcap p j hp ht
      have hpos : 0 < (D.old4 j : ℝ) - (∑ i, actualPrimeTupleLog N p i) -
          actualPrimeTupleLog N p 3 := by linarith [hlegal.2.1]
      have hdelta : delta ≤ (D.old4 j : ℝ) - (∑ i, actualPrimeTupleLog N p i) -
          actualPrimeTupleLog N p 3 :=
        (lt_of_not_ge (fun hh => hs ⟨hpos, hh⟩)).le
      simp only [ht, hs, hdelta, true_and, and_self, if_true, if_false, sub_self, abs_zero,
        le_refl]
  · simp only [ht, false_and, if_false, mul_zero, sub_self, abs_zero, le_refl]

/-- The endpoint supplier is instantiated, rather than passed as a hypothesis.
The two residuals use the same M, for every width and every actual owner. -/
theorem exists_wallResidualPayment_bound
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → Even N →
        (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        ∀ (j : Fin 4 → Fin (D.m + 1)) (delta : ℝ),
          wallResidualPairAbsSum D N cap j delta ≤ C * admittedWallMass D N cap j delta ∧
          |wallCellCorrection D N cap j delta| ≤ C * admittedWallMass D N cap j delta := by
  obtain ⟨M, hM, N₀, hN₀, hbound⟩ :=
    exists_p1_fourthTuplePlusResidual_uniform_bound (D.a : ℝ) (by exact_mod_cast ha)
  refine ⟨2 * M, by positivity, N₀, hN₀, ?_⟩
  intro N cap hN hEven hcap j delta
  have hn : 1 < N := by omega
  have hpair : wallResidualPairAbsSum D N cap j delta ≤
      (2 * M) * admittedWallMass D N cap j delta := by
    unfold wallResidualPairAbsSum admittedWallMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have haTuple := (Finset.mem_filter.mp hp).1
    have ht := (Finset.mem_filter.mp hp).2.1
    have hpCube := hp
    rw [admittedWallTuples_eq_cube_filter D hab hcheck N cap hn hcap j delta] at hpCube
    have hcube := mem_actualPrimeBoxTuples_iff.mp (Finset.mem_filter.mp hpCube).1
    have hcut : (N : ℝ) ^ (D.a : ℝ) ≤ (p (Fin.last 3) : ℝ) := (hcube _).2.2.1
    have hpcap : (p (Fin.last 3) : ℝ) ≤ (cap : ℝ) := (hcube _).2.2.2.le.trans hcap
    have hlevels := p1_admittedFourth_physical_levels_on_cell
      D hab.le hcheck N cap hn hcap p j haTuple ht
    have hold : |fourthTuplePlusResidualP1 N cap (D.old4 j : ℝ) p| ≤ M :=
      hbound N hN hEven cap p (D.old4 j : ℝ) hcut hlevels.2.2.1.le hpcap
    have hnew : |fourthTuplePlusResidualP1 N cap (D.cell4 j : ℝ) p| ≤ M :=
      hbound N hN hEven cap p (D.cell4 j : ℝ) hcut hlevels.2.2.2.le hpcap
    have hw := wall_tupleWeight_nonneg D hab hcheck N cap hn hcap j delta hp
    have h := mul_le_mul_of_nonneg_left (add_le_add hold hnew) hw
    change tupleWeight p * _ ≤ (2 * M) * tupleWeight p
    nlinarith only [h]
  exact ⟨hpair,
    (abs_wallCellCorrection_le_pair D hab hcheck N cap hn hcap j delta).trans hpair⟩

/-- Arbitrarily small actual old/new wall payment for one fixed finite family.
Width is selected before the common target threshold, including the threshold
of the actual endpoint residual supplier. -/
theorem exists_sum_wallResidualPayment_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (J : Finset (Fin 4 → Fin (D.m + 1)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → Even N →
        (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
          (∑ j ∈ J, wallResidualPairAbsSum D N cap j delta) < epsilon ∧
          (∑ j ∈ J, |wallCellCorrection D N cap j delta|) < epsilon ∧
          |∑ j ∈ J, wallCellCorrection D N cap j delta| < epsilon := by
  obtain ⟨C, hC, NB, hNB, hbound⟩ := exists_wallResidualPayment_bound D ha hab hcheck
  obtain ⟨delta, hd, NM, hNM, hmass⟩ :=
    exists_sum_admittedWallMass_lt D ha hab hcheck J (epsilon / C) (div_pos hepsilon hC)
  refine ⟨delta, hd, max NB NM, hNB.trans (le_max_left _ _), ?_⟩
  intro N cap hN hEven hcap
  have hNB' : NB ≤ N := (le_max_left _ _).trans hN
  have hNM' : NM ≤ N := (le_max_right _ _).trans hN
  have hsmall : C * (∑ j ∈ J, admittedWallMass D N cap j delta) < epsilon := by
    calc
      _ < C * (epsilon / C) := mul_lt_mul_of_pos_left (hmass N cap hNM' hcap) hC
      _ = epsilon := by rw [mul_comm, div_mul_cancel₀ _ hC.ne']
  have hpair : (∑ j ∈ J, wallResidualPairAbsSum D N cap j delta) < epsilon := by
    apply lt_of_le_of_lt _ hsmall
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _hj => (hbound N cap hNB' hEven hcap j delta).1)
  have herr : (∑ j ∈ J, |wallCellCorrection D N cap j delta|) < epsilon := by
    apply lt_of_le_of_lt _ hsmall
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _hj => (hbound N cap hNB' hEven hcap j delta).2)
  exact ⟨hpair, herr, (Finset.abs_sum_le_sum_abs _ _).trans_lt herr⟩

/-- Scalar form for a single fixed cell, ready for the cell-limit assembly. -/
theorem exists_single_cell_strictClip_remainder_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → Even N →
        (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
          wallResidualPairAbsSum D N cap j delta < epsilon ∧
          |D.fourthCellPrimeCorrectionP1 N cap j -
            strictClipCellCorrection D N cap j delta| < epsilon := by
  obtain ⟨delta, hd, N₀, hN₀, hsmall⟩ :=
    exists_sum_wallResidualPayment_lt D ha hab hcheck {j} epsilon hepsilon
  refine ⟨delta, hd, N₀, hN₀, ?_⟩
  intro N cap hN hEven hcap
  have hn : 1 < N := by omega
  obtain ⟨hpair, _herr, htotal⟩ := hsmall N cap hN hEven hcap
  refine ⟨by simpa only [Finset.sum_singleton] using hpair, ?_⟩
  rw [← awayCellCorrection_eq_strictClip D hab.le hcheck N cap hn hcap j delta,
    cellCorrection_eq_wall_add_away, add_sub_cancel_right]
  simpa only [Finset.sum_singleton] using htotal

/-- The actual threshold is uniform over every smaller positive clipping width.
This permits a later continuous-side choice of delta without reordering limits. -/
theorem exists_sum_closedClip_small_widths_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (J : Finset (Fin 4 → Fin (D.m + 1)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → Even N →
        (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          (∑ j ∈ J, wallResidualPairAbsSum D N cap j delta) < epsilon ∧
          (∑ j ∈ J, |D.fourthCellPrimeCorrectionP1 N cap j -
            closedClipCellCorrection D N cap j delta|) < epsilon ∧
          |∑ j ∈ J, (D.fourthCellPrimeCorrectionP1 N cap j -
            closedClipCellCorrection D N cap j delta)| < epsilon := by
  obtain ⟨C, hC, NB, hNB, hbound⟩ := exists_wallResidualPayment_bound D ha hab hcheck
  obtain ⟨delta₀, hd₀, NM, hNM, hmass⟩ :=
    exists_sum_admittedWallMass_lt D ha hab hcheck J (epsilon / C) (div_pos hepsilon hC)
  refine ⟨delta₀, hd₀, max NB NM, hNB.trans (le_max_left _ _), ?_⟩
  intro N cap hN hEven hcap delta _hd hdd₀
  have hNB' : NB ≤ N := (le_max_left _ _).trans hN
  have hNM' : NM ≤ N := (le_max_right _ _).trans hN
  have hn : 1 < N := by omega
  have hsmall : C * (∑ j ∈ J, admittedWallMass D N cap j delta₀) < epsilon := by
    calc
      _ < C * (epsilon / C) := mul_lt_mul_of_pos_left (hmass N cap hNM' hcap) hC
      _ = epsilon := by rw [mul_comm, div_mul_cancel₀ _ hC.ne']
  have hpair : (∑ j ∈ J, wallResidualPairAbsSum D N cap j delta) < epsilon := by
    apply lt_of_le_of_lt _ hsmall
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _hj
    exact ((hbound N cap hNB' hEven hcap j delta).1).trans
      (mul_le_mul_of_nonneg_left
        (admittedWallMass_mono D hab hcheck N cap hn hcap j hdd₀) hC.le)
  have herr : (∑ j ∈ J, |D.fourthCellPrimeCorrectionP1 N cap j -
      closedClipCellCorrection D N cap j delta|) < epsilon := by
    apply lt_of_le_of_lt _ hpair
    exact Finset.sum_le_sum (fun j _hj =>
      abs_cellCorrection_sub_closedClip_le_pair D hab hcheck N cap hn hcap j delta)
  exact ⟨hpair, herr, (Finset.abs_sum_le_sum_abs _ _).trans_lt herr⟩

/-- Scalar closed-clip API: one common N₀ works for every delta in (0,delta₀]. -/
theorem exists_single_cell_closedClip_small_widths_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (j : Fin 4 → Fin (D.m + 1))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → Even N →
        (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          wallResidualPairAbsSum D N cap j delta < epsilon ∧
          |D.fourthCellPrimeCorrectionP1 N cap j -
            closedClipCellCorrection D N cap j delta| < epsilon := by
  obtain ⟨delta₀, hd₀, N₀, hN₀, hsmall⟩ :=
    exists_sum_closedClip_small_widths_lt D ha hab hcheck {j} epsilon hepsilon
  refine ⟨delta₀, hd₀, N₀, hN₀, ?_⟩
  intro N cap hN hEven hcap delta hd hdd₀
  obtain ⟨hpair, herr, _htotal⟩ := hsmall N cap hN hEven hcap delta hd hdd₀
  exact ⟨by simpa only [Finset.sum_singleton] using hpair,
    by simpa only [Finset.sum_singleton] using herr⟩

/-- Direct original-correction endpoint: the sum of actual selected cell
corrections differs from its away part by less than any prescribed reserve. -/
theorem exists_fourthCellPrimeCorrection_wall_remainder_lt
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b)
    (hcheck : D.levelCheck = true) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N cap : ℕ, N₀ ≤ N → Even N →
        (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ) →
          (∑ j ∈ D.cells4, wallResidualPairAbsSum D N cap j delta) < epsilon ∧
          |∑ j ∈ D.cells4,
            (D.fourthCellPrimeCorrectionP1 N cap j - awayCellCorrection D N cap j delta)| < epsilon := by
  obtain ⟨delta, hd, N₀, hN₀, hsmall⟩ :=
    exists_sum_wallResidualPayment_lt D ha hab hcheck D.cells4 epsilon hepsilon
  refine ⟨delta, hd, N₀, hN₀, ?_⟩
  intro N cap hN hEven hcap
  obtain ⟨hpair, _herr, htotal⟩ := hsmall N cap hN hEven hcap
  refine ⟨hpair, ?_⟩
  have heq : (∑ j ∈ D.cells4,
      (D.fourthCellPrimeCorrectionP1 N cap j - awayCellCorrection D N cap j delta)) =
      ∑ j ∈ D.cells4, wallCellCorrection D N cap j delta := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [cellCorrection_eq_wall_add_away]
    ring
  rw [heq]
  exact htotal

end P1HistoricalFourthResidualWallPayment

end

end ImbalancedChen
