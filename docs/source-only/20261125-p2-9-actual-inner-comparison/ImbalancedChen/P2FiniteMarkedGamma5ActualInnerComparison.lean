import ImbalancedChen.P2FiniteMarkedGamma5InnerComparison
import ImbalancedChen.P2FiniteMarkedGamma5ActualHistoryScale

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Multiply the fixed-word inner comparison by the original positive
levelMark and sum over the original root prime and dependent B p.
The exact root-cell partition supplies a common Q; the existing
nonzero-prefix history-scale helper supplies the actual positive scale.

The ordinaryBad term keeps coefficient one and all original history
marks. The noncoprime error is exactly selectedNoncoprimeMass. The new
proper-strip error is a literal marked count, with an exact cell
dictionary for its separate arithmetic payment consumer.

No shape/root/rank multiplier is applied to the ordinaryBad term.
This file does not pay the proper strips or construct a global smooth
selected-history mask, identify J, or apply a prime-product licence.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualInnerComparison

noncomputable section
open Finset Real
open Part5OriginalH430FrozenRootRefinement (RootCode)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430RequestedHistory
open Part5OriginalH430SeedHistoryMass (wordProduct)
open Part5OriginalH430SameQHistoryCells (cellQ)
open P2EnhancedBadGamma5ArithmeticGeometry (ordinaryBad)
open P2FiniteMarkedGamma5ActualRootCells
open P2FiniteMarkedGamma5ActualRadialAggregate
  (Split admissibleSplit prefixWeight boundedInnerSlice selectedInnerMass
    allDepthSelectedInnerMass)
open P2FiniteMarkedGamma5ActualTargetExclusion
  (noncoprimeSlice selectedNoncoprimeMass selectedNoncoprimeMass_eq_cells
    allDepthSelectedNoncoprimeMass)
open P2FiniteMarkedGamma5InnerComparison
  (properStripTuples inner_sum_le_ordinaryBad_add_errors)
open P2FiniteMarkedGamma5ActualHistoryScale (of_prefixWeight_ne_zero)
open scoped Classical BigOperators

/-- An original selected position gives a strictly positive contribution
to its complete old-word coefficient. This uses positive marks, with no
cancellation or collapse of repeated path occurrences. -/
theorem prefixWeight_pos_of_mem {N n p dep : ℕ} {t : ℝ} {c : RootCode n}
    {B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)}
    (hp : p ∈ originalRootCellBand N n .U4 t c)
    {l : LevelIndex N n .U4 t p dep} (hl : l ∈ B p) :
    0 < prefixWeight N n dep t c B (levelOccurrence l).current.old := by
  have hterm (q : ℕ) (j : LevelIndex N n .U4 t q dep) :
      0 ≤ (if (levelOccurrence j).current.old = (levelOccurrence l).current.old
        then levelMark j else 0) := by
    split_ifs
    · exact (mark_pos (levelOccurrence j)).le
    · exact le_rfl
  have hinner : levelMark l ≤
      ∑ j ∈ B p, if (levelOccurrence j).current.old = (levelOccurrence l).current.old
        then levelMark j else 0 := by
    simpa only [if_pos (rfl :
      (levelOccurrence l).current.old = (levelOccurrence l).current.old)] using
      (single_le_sum (fun j _ => hterm p j) hl)
  have houter :
      (∑ j ∈ B p, if (levelOccurrence j).current.old = (levelOccurrence l).current.old
        then levelMark j else 0) ≤
      prefixWeight N n dep t c B (levelOccurrence l).current.old := by
    unfold prefixWeight
    exact single_le_sum (fun q _ => sum_nonneg (fun j _ => hterm q j)) hp
  exact (mark_pos (levelOccurrence l)).trans_le (hinner.trans houter)

/-- The exact original inner mass at the same Q on each original root
cell. The root prime p and dependent B p remain unchanged. -/
theorem selectedInnerMass_eq_cells (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedInnerMass N n dep t h B =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
        levelMark l * ∑ s : Split, if admissibleSplit s then
          boundedInnerSlice N s.1.val s.2.val (log (cellQ N n c)) h
            (levelOccurrence l).current.old
        else 0 := by
  calc
    _ = ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
        levelMark l * ∑ s : Split, if admissibleSplit s then
          boundedInnerSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h
            (levelOccurrence l).current.old
        else 0 := by
      symm
      simp only [originalRootCellBand, sum_filter]
      rw [sum_comm]
      simp [selectedInnerMass]
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro p hp
      rw [originalRootCellBand_Q hp]

/-- Literal weighted proper-strip count on the original selected
history. Split admission is already inside properStripTuples. -/
def selectedProperStripMass (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) : ℝ :=
  ∑ p ∈ originalBand N .U4, ∑ l ∈ B p, levelMark l *
    ∑ s : Split, ((properStripTuples N (rootQ N n .U4 t p) h
      (levelOccurrence l).current.old s).card : ℝ)

/-- Exact input to the separate proper-wall payment: all original
positive marks, p-dependent positions and old-word occurrences survive.
There is no additional outer split-admission factor. -/
theorem selectedProperStripMass_eq_cells (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedProperStripMass N n dep t h B =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
        levelMark l * ∑ s : Split,
          ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ) := by
  calc
    _ = ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
        levelMark l * ∑ s : Split,
          ((properStripTuples N (rootQ N n .U4 t p) h
            (levelOccurrence l).current.old s).card : ℝ) := by
      symm
      simp only [originalRootCellBand, sum_filter]
      rw [sum_comm]
      simp [selectedProperStripMass]
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro p hp
      rw [originalRootCellBand_Q hp]

/-- Actual selected-history inner comparison. The ordinary bad mass is
the original marked sum with coefficient one. Only the two positive
errors remain for their separate uniform payment consumers. -/
theorem selectedInnerMass_le_original_add_errors (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep))
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hN : 2 ≤ N)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 12) (hh : 0 < h) :
    selectedInnerMass N n dep t h B ≤
      (∑ p ∈ originalBand N .U4, ∑ l ∈ B p,
        levelMark l * ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)) +
      selectedNoncoprimeMass N n dep t h B +
      selectedProperStripMass N n dep t h B := by
  rw [selectedInnerMass_eq_cells, ordinaryBad_original_cells N n dep .U4 t B,
    selectedNoncoprimeMass_eq_cells, selectedProperStripMass_eq_cells]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro c hc
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro l hl
  have hscale := of_prefixWeight_ne_zero hn hN ht ht'
    (prefixWeight_pos_of_mem hp hl).ne'
  have hinner := inner_sum_le_ordinaryBad_add_errors N (cellQ N n c) h
    (levelOccurrence l).current.old (by omega) hscale.1 hscale.2.2.1 hh
  have hweighted := mul_le_mul_of_nonneg_left hinner (mark_pos (levelOccurrence l)).le
  simpa only [mul_add, wordProduct, P2EnhancedLowerPrimeChildCarriers.parentProduct] using hweighted

/-- The same fixed 431 remaining-depth budget as the existing raw
profile and noncoprime sums, retaining every original B dep p. -/
def allDepthSelectedProperStripMass (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) : ℝ :=
  ∑ dep : Fin 431, selectedProperStripMass N n dep.val t h (B dep)

theorem allDepthSelectedProperStripMass_eq_cells (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) :
    allDepthSelectedProperStripMass N n t h B =
      ∑ dep : Fin 431, ∑ c : RootCode n,
        ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B dep p,
          levelMark l * ∑ s : Split,
            ((properStripTuples N (cellQ N n c) h (levelOccurrence l).current.old s).card : ℝ) := by
  simp only [allDepthSelectedProperStripMass, selectedProperStripMass_eq_cells]

/-- Summing the actual comparison over the existing finite depth budget
keeps the literal marked ordinaryBad sum, still with coefficient one. -/
theorem allDepthSelectedInnerMass_le_original_add_errors (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val))
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hN : 2 ≤ N)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 12) (hh : 0 < h) :
    allDepthSelectedInnerMass N n t h B ≤
      (∑ dep : Fin 431, ∑ p ∈ originalBand N .U4, ∑ l ∈ B dep p,
        levelMark l * ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)) +
      allDepthSelectedNoncoprimeMass N n t h B +
      allDepthSelectedProperStripMass N n t h B := by
  calc
    _ ≤ ∑ dep : Fin 431,
        ((∑ p ∈ originalBand N .U4, ∑ l ∈ B dep p,
          levelMark l * ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)) +
        selectedNoncoprimeMass N n dep.val t h (B dep) +
        selectedProperStripMass N n dep.val t h (B dep)) :=
      sum_le_sum (fun dep _ =>
        selectedInnerMass_le_original_add_errors N n dep.val t h (B dep) hn hN ht ht' hh)
    _ = _ := by
      simp only [allDepthSelectedNoncoprimeMass, allDepthSelectedProperStripMass,
        sum_add_distrib]

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualInnerComparison
