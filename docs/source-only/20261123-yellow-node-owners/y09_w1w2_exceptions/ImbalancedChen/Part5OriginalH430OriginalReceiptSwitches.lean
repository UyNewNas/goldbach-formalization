import ImbalancedChen.Part5OriginalH430SelectedReceiptPlateau
import ImbalancedChen.Part5OriginalH430ReceiptTwoBounds

/-! The signed predecessor identity summed on the original occupied fibre,
with all 106 selected actions, multiplicities and levels. -/
namespace ImbalancedChen.Part5OriginalH430OriginalReceiptSwitches
noncomputable section
open Finset Wu2008DoubleSieve
open P5OriginalActionMassBound P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (quotientCount)
open P2AllW1FrozenReceiverFiniteAction (rawTripleCount)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SeedHistoryMass Part5OriginalH430BankSlotTargets
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430ReceiptFourBand
open Part5OriginalH430MaskedSievePlateau Part5OriginalH430SelectedReceiptPlateau
open Part5OriginalH430OwnedReceiptNet Part5OriginalH430ReceiptSignedPredecessors
open Part5OriginalH430ReceiptTwoBounds
open scoped Classical BigOperators

/-- Retain the complete selected owner, multiplicity and signed predecessor
charges. This equality on the original occupied fibre holds at each generation,
without a threshold or a rounding loss on this route. -/
theorem owned_106_exact_net {N n m : ℕ} {k : Root} {t : ℝ} (hN : 2≤N) (ht : 0≤t)
    (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (c : RootKey n m) (g : Fin 430) :
    let P := rootFibre N n m k t c
    let Q := cellQ N n c.1
    let total (F : (p : ℕ) → Index N n k t p g → Original106Action → ℝ) :=
      ∑ p∈P, ∑ A : Original106Action, ∑ l∈selectedLevel N n k t p g A,levelMark l*F p l A
    total (fun _ l _ => inheritedDefect Q l) = total (fun _ l A =>
      Part5OriginalH430FreshBankBudget.strictDebt l A + correction l A + (modelRow l A-parentModel l) -
        switched l A) := by
  dsimp only
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro l hl
  have ho := (levelOccurrence_source l).1
  have hmask := owned_member_masked_count hN ht hu hn hp ho
  have hQ := (original_fibre_geometry hN ht hu hn hp).1
  dsimp only at hmask
  unfold inheritedDefect
  rw [←hmask,hQ]
  exact congrArg (fun y => levelMark l*y)
    (exact_previous_net hN ht hu hn (mem_filter.mp hp).1 l A hl)

end
end ImbalancedChen.Part5OriginalH430OriginalReceiptSwitches
