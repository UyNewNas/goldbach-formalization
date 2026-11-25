import ImbalancedChen.Part5OriginalH430SameQHistoryCells
import ImbalancedChen.Part5OriginalH430SeedSameCarrierPP

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Partition the original root-prime sum by its existing cumulative RootCode.
The original p and every dependent LevelIndex position remain in the sum.
No position is mapped to the all-Programs catalog, and equal products do
not merge their original path marks.

The public mass identities use ordinaryBad, markedConverted and
markedTheta themselves. The existing codeLevel_rootCode supplies the
same Q throughout one root cell; the existing converted_eq_untested and
weighted_fiber_sum supply the inclusive marked ordinary source.

This is an exact finite source dictionary. It does not construct the
smooth masks for selected histories, estimate their ordinary excess,
identify a PP mass constant J, or apply distribution separately at each p.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualRootCells

noncomputable section
open Finset
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedBadGamma5ArithmeticGeometry (ordinaryBad)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2OriginalW2CentreThetaPayment (weighted_fiber_sum)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement (RootCode rootCode)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430SameQHistoryCells (cellQ codeLevel_rootCode)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430RequestedHistory (LevelIndex levelMark)
open Part5OriginalH430SeedHistoryMass (wordProduct markedConverted markedTheta)
open Part5OriginalH430SeedPurifiedPrimeFibres (switchedFibre)
open Part5OriginalH430SeedSameCarrierPP (converted_eq_untested)
open scoped Classical BigOperators

/-- Filter the original root-prime band by its original cumulative code.
The finite code type depends on n, not on N or the selected root prime. -/
def originalRootCellBand (N n : ℕ) (root : Root) (t : ℝ)
    (c : RootCode n) : Finset ℕ :=
  (originalBand N root).filter fun p =>
    rootCode n (sourceRoot root t (physicalPrime N p)).physical.total = c

theorem mem_originalRootCellBand {N n p : ℕ} {root : Root} {t : ℝ}
    {c : RootCode n} :
    p ∈ originalRootCellBand N n root t c ↔
      p ∈ originalBand N root ∧
      rootCode n (sourceRoot root t (physicalPrime N p)).physical.total = c := by
  simp only [originalRootCellBand, Finset.mem_filter]

/-- The old cell level, rather than a newly chosen representative p,
is the exact original frozen Q on this whole root-prime cell. -/
theorem originalRootCellBand_Q {N n p : ℕ} {root : Root} {t : ℝ}
    {c : RootCode n} (hp : p ∈ originalRootCellBand N n root t c) :
    rootQ N n root t p = cellQ N n c := by
  have hc := (mem_originalRootCellBand.mp hp).2
  rw [← hc, cellQ, codeLevel_rootCode]
  rfl

/-- Internal finite algebra. Public consumers below retain the actual
mass functions and the original dependent history index. -/
private theorem sum_sameQ_cells (N n : ℕ) (root : Root) (t : ℝ)
    (F : ℕ → ℝ → ℝ) :
    (∑ p ∈ originalBand N root, F p (rootQ N n root t p)) =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n root t c,
        F p (cellQ N n c) := by
  calc
    _ = ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n root t c,
        F p (rootQ N n root t p) := by
      symm
      simp only [originalRootCellBand, Finset.sum_filter]
      rw [Finset.sum_comm]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro p hp
      rw [originalRootCellBand_Q hp]

/-- Literal bad-Gamma5 ordinary mass on the actual selected positions,
now at one common original Q per root cell. B p is kept unchanged:
all old-slot orders, repeated products and path occurrences are retained. -/
theorem ordinaryBad_original_cells (N n dep : ℕ) (root : Root) (t : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n root t p dep)) :
    (∑ p ∈ originalBand N root, ∑ l ∈ B p,
      levelMark l * ordinaryBad N (rootQ N n root t p) (wordProduct l)) =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n root t c,
        ∑ l ∈ B p, levelMark l * ordinaryBad N (cellQ N n c) (wordProduct l) := by
  exact sum_sameQ_cells N n root t
    (fun p Q => ∑ l ∈ B p, levelMark l * ordinaryBad N Q (wordProduct l))

/-- The original inclusive converted seed mass, including Gamma5 and
every Gamma9--21 word-list occurrence, is the same marked untested
source at cellQ. The original d-dependent thetaConversion is retained. -/
theorem markedConverted_original_cells (N n dep : ℕ) (root : Root) (t : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n root t p dep)) :
    (∑ p ∈ originalBand N root, markedConverted (B p)) =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n root t c,
        ∑ l ∈ B p, levelMark l *
          (thetaConversion N (wordProduct l) *
            switchedFibre false N (cellQ N n c) (wordProduct l)) := by
  have hsource (p : ℕ) :
      markedConverted (B p) =
        ∑ l ∈ B p, levelMark l *
          (thetaConversion N (wordProduct l) *
            switchedFibre false N (rootQ N n root t p) (wordProduct l)) := by
    rw [markedConverted, converted_eq_untested, weighted_fiber_sum]
  calc
    _ = ∑ p ∈ originalBand N root, ∑ l ∈ B p, levelMark l *
        (thetaConversion N (wordProduct l) *
          switchedFibre false N (rootQ N n root t p) (wordProduct l)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hsource p
    _ = _ := sum_sameQ_cells N n root t
      (fun p Q => ∑ l ∈ B p, levelMark l *
        (thetaConversion N (wordProduct l) *
          switchedFibre false N Q (wordProduct l)))

/-- The original marked Theta is partitioned with precisely the same
root cells and dependent history positions as the ordinary seed charge. -/
theorem markedTheta_original_cells (N n dep : ℕ) (root : Root) (t : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n root t p dep)) :
    (∑ p ∈ originalBand N root, markedTheta (B p)) =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n root t c,
        ∑ l ∈ B p, levelMark l * thetaAtom N (cellQ N n c) (wordProduct l) := by
  simpa only [markedTheta] using sum_sameQ_cells N n root t
    (fun p Q => ∑ l ∈ B p, levelMark l * thetaAtom N Q (wordProduct l))

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualRootCells
