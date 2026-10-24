import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector
import ImbalancedChen.ActualThirdOriginalP4ASymmetricTentPrerequisites

/- SOURCEONLY / UNCOMPILED. Small dispatch bridge: original source selection
supplies the exact symmetric branch/root guards consumed by the new all-six
saved integer leaf. Post-selection residual/low/log guards are not inferred. -/
namespace ImbalancedChen.P0SymmetricSelectedGuardBridge
noncomputable section
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites

theorem selected_tent_literal_branch_root
    (s : TentSum) (side : TentSide) (x0 x1 z0 z1 : ℤ)
    (hselected : originalMinorant ![x0,x0,z0] ![x1,x1,z1]
      (48000*2^24) 481573208064 = some (.tent s side)) :
    literalSymmetricBranch s side x0 x1 z0 z1 ∧
      literalSymmetricRoot s side x0 x1 z0 z1 := by
  have h := selected_tent_guards ![x0,x0,z0] ![x1,x1,z1]
    (48000*2^24) 481573208064 s side hselected
  cases side <;>
    simpa only [branchTest, deltaNumerator, rawSum, rootTest,
      literalSymmetricBranch, literalSymmetricRoot,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h

end
end ImbalancedChen.P0SymmetricSelectedGuardBridge
