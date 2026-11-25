import ImbalancedChen.P2FiniteMarkedGamma5ActualRadialAggregate
import ImbalancedChen.Part5OriginalH430HistoryScaleCore
import ImbalancedChen.P2EnhancedUnitSourceMass

namespace ImbalancedChen.P2FiniteMarkedGamma5ActualHistoryScale
noncomputable section
open Finset Real
open Part5OriginalH430RequestedHistory
open Part5OriginalH430FrozenRootRefinement (RootCode frozenResidualFloor)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430SeedHistoryMass (wordProduct scale_and_alpha)
open P2FiniteMarkedGamma5ActualRootCells
open P2FiniteMarkedGamma5ActualRadialAggregate (prefixWeight)
open scoped Classical BigOperators

/-- The scale of a word with nonzero total mark comes from a position in
the original selected band and its exact root cell. -/
theorem of_prefixWeight_ne_zero {N n dep : ℕ} {t : ℝ} {c : RootCode n}
    {B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)} {w : List ℕ}
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hN : 2 ≤ N)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 12)
    (hw : prefixWeight N n dep t c B w ≠ 0) :
    0 < w.prod ∧ (N : ℝ) ^ frozenResidualFloor ≤ cellQ N n c / w.prod ∧
    1 < cellQ N n c / w.prod ∧ (cellQ N n c / w.prod)^2 ≤ (N : ℝ) / w.prod := by
  classical
  have hex : ∃ p ∈ originalRootCellBand N n .U4 t c, ∃ l ∈ B p,
      (levelOccurrence l).current.old = w := by
    by_contra! h
    apply hw
    unfold prefixWeight
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro l hl
    simp [h p hp l hl]
  obtain ⟨p, hp, l, _, hl⟩ := hex
  have hd : wordProduct l = w.prod := by
    change (levelOccurrence l).current.old.prod = w.prod
    rw [hl]
  obtain ⟨hpos, _, _, hfloor, halpha⟩ :=
    scale_and_alpha hN ht ht' hn (mem_originalRootCellBand.mp hp).1 l
  rw [originalRootCellBand_Q hp, hd] at hfloor halpha
  rw [hd] at hpos
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have heta : 0 < frozenResidualFloor := by unfold frozenResidualFloor; positivity
  have hR := (Real.one_lt_rpow hN' heta).trans_le hfloor
  refine ⟨hpos, hfloor, hR, ?_⟩
  rw [← P2EnhancedUnitSourceMass.scale_identity (by omega : 0 < N) hpos hR,
      ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hR.le (by exact_mod_cast halpha)

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualHistoryScale
