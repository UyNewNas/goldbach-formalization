import ImbalancedChen.P5OriginalChildIntegerWireBinding
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000
import ImbalancedChen.Data.P5SubdivisionStoredBlock000

/-!
Two original-parent kernel performance probes, source positions 0 and 5.

Every original `ChildIndex` remains in the sum (64 children). The formulas
are the existing original 3/4 directed logarithm integer expressions;
this file defines no alternative evaluator, accepted-data premise, or
weaker parent inequality. Actual literal rows are read at their positions.

Row 0 selects the child sum; row 5 retains the old parent bound. Neither
branch selection is a theorem premise or a shortcut in the computation.
Success would concern precisely these two rows, not the whole archive.

This module deliberately does not import P5FullStoredParentSameOwnerBinding.
Its existing integer-definition module has additional finite declarations
and a substantial import closure; consult PROBE_DEPENDENCIES.json before
interpreting a cold build as the timing of these two declarations alone.
-/
namespace ImbalancedChen.P5OriginalParentExactKernelProbe

open scoped BigOperators
open P5OldFifthExact64ChildTiling P5OriginalChildIntegerWireBinding

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem source_row000000_original34_exact_max :
    let raw := Data.P1HistoricalFifthSavedDataBlock000.rows[0]'(by
      change 0 < 2048
      decide)
    let saved := Data.P5SubdivisionStoredBlock000.rows[0]'(by
      rw [Data.P5SubdivisionStoredBlock000.rows_size]
      decide)
    saved.newQ80 = max saved.oldQ80
      (∑ c : ChildIndex, originalExactFloor (originalFields raw c)) := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem source_row000005_original34_exact_max :
    let raw := Data.P1HistoricalFifthSavedDataBlock000.rows[5]'(by
      change 5 < 2048
      decide)
    let saved := Data.P5SubdivisionStoredBlock000.rows[5]'(by
      rw [Data.P5SubdivisionStoredBlock000.rows_size]
      decide)
    saved.newQ80 = max saved.oldQ80
      (∑ c : ChildIndex, originalExactFloor (originalFields raw c)) := by
  decide +kernel

#print axioms source_row000000_original34_exact_max
#print axioms source_row000005_original34_exact_max

end ImbalancedChen.P5OriginalParentExactKernelProbe
