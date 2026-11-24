import ImbalancedChen.P5OriginalChildIntegerWireBinding
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000
import ImbalancedChen.Data.P5SubdivisionStoredBlock000

/-!
One original-parent kernel performance probe, source position 5.

Every original `ChildIndex` remains in the sum (64 children). The formulas
are the existing original 3/4 directed logarithm integer expressions;
this file defines no alternative evaluator, accepted-data premise, or
weaker parent inequality. Actual literal rows are read at their positions.

Row 5 retains the old parent bound. That branch selection is not a
theorem premise or a shortcut in the computation. The original wire
module already states the exact replacements for rows 0 and 1, so this
probe does not compute either again. Success concerns only row 5.

This module deliberately does not import P5FullStoredParentSameOwnerBinding.
Its existing integer-definition module has additional finite declarations
and a substantial import closure; consult PROBE_DEPENDENCIES.json before
interpreting a cold build as the timing of this new declaration alone.
-/
namespace ImbalancedChen.P5OriginalParentExactKernelProbe

open scoped BigOperators
open P5OldFifthExact64ChildTiling P5OriginalChildIntegerWireBinding

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

#print axioms source_row000005_original34_exact_max

end ImbalancedChen.P5OriginalParentExactKernelProbe
