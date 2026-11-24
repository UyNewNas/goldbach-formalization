import ImbalancedChen.P2Winner9PullingArchiveCore
import ImbalancedChen.P2Winner9PullingOrderChecks
import ImbalancedChen.P2Winner9CompletePullingData

/-! Concrete global witnesses for all 11,026 original Winner9 cells. -/

namespace ImbalancedChen.P2Winner9CompletePullingFlags

open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9PullingArchiveCore (Witnesses)

def witnesses : Witnesses where
  count := 11026
  geometryWord := P2Winner9CompletePullingData.geometryWord
  orderedWord := P2Winner9CompletePullingData.orderedWord

abbrev checkedRow (ordinal : ℕ) (row : RawRow) : Bool := witnesses.checkedRow ordinal row

def orderStep (rank : ℕ) : Prop :=
  witnesses.orderedKey rank < witnesses.orderedKey (rank + 1)

instance (rank : ℕ) : Decidable (orderStep rank) := by
  unfold orderStep
  infer_instance

end ImbalancedChen.P2Winner9CompletePullingFlags
