import ImbalancedChen.Part5OriginalH430OriginalRootQBound
import ImbalancedChen.Part5OriginalH430BuchstabCutoffCancellation
import ImbalancedChen.P5OriginalU5FrozenSource
import ImbalancedChen.Part5OriginalH430HistoryRoughnessCore

/-! Arithmetic count at the cutoff of each actual history occurrence.
The old integer word consists of genuine prime factors of its product.
In a pair the added word is [large,small] and the small exponent becomes
the new ceiling. These facts give both primitive roughness gates at the
same fixed power, beginning at the original U3/U4 root. -/

namespace ImbalancedChen.Part5OriginalH430HistoryQuotientCounts

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry P2FrozenReceiverCountActions
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430CutoffCoherence
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430ActualMarkedRootConsumer Part5OriginalH430OriginalRootQBound

/-- On every finite history request the old prime mask can be removed.
The receiver remains the original centre-coprime additive prime. This
identifies a count before making any asymptotic or selected-floor claim. -/
theorem history_frozen_count_eq_true_quotient {N n p : ℕ} {k : Root} {t : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384)
    (hp : p ∈ originalBand N k) (ho : o ∈ rootHistory N n k t p) :
    let d := parentProduct o.current.old
    let z := cutoff (rootQ N n k t p) d o.current.node.physical.argument
    (frozenCount N d (receiver N) z : ℝ) =
      ((chenSiftedQuotientPrimeSource N d z).card : ℝ) :=
  frozenCount_eq_original_count _ _ _ (history_integer_roughness hN ht ht' hn hp ho).1

/-- The earlier original U3+U4 marked entrance no longer needs any
prime-factor roughness or 227/50 cutoff gate from its caller. Its positive
q-to-5-Phi discrepancy at arbitrary inspected depth remains in the budget. -/
theorem original_U34_actual_marked_entrance {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (n : ℕ) (t : ℝ) (depth : Root → ℕ → Fin 430),
      0 ≤ t → t ≤ 1/12 → 1 / ((n : ℝ) + 1) ≤ 11/384 →
      currentChenUpsilon3 N + currentChenUpsilon4 N ≤
        (∑ p ∈ originalBand N .U3, actualMarkedRootBudget N n .U3 t p (depth .U3 p) ε) +
        (∑ p ∈ originalBand N .U4, actualMarkedRootBudget N n .U4 t p (depth .U4 p) ε) := by
  obtain ⟨T, hT4, hT⟩ := original_U34_le_actual_budgets_without_Q_gate frozenLeafCutoffFloor_pos hε
  refine ⟨T, hT4, ?_⟩
  intro N hNT he n t depth ht ht' hn
  apply hT N hNT he n t depth ht ht' hn
  intro k p hp
  constructor
  · intro l _
    exact (history_integer_roughness (by omega : 2 ≤ N) ht ht' hn hp
      (levelOccurrence_source l).1).2.2.1
  · intro l _
    exact (history_integer_roughness (by omega : 2 ≤ N) ht ht' hn hp
      (levelOccurrence_source l).1).2.2.2

end
end ImbalancedChen.Part5OriginalH430HistoryQuotientCounts

