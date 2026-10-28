import ImbalancedChen.P2Winner9SelectedRowIntegerScales
import ImbalancedChen.P2Winner9SeedLiteralRowBatch
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The two original curvature Q0 records are statically transcribed and bound
to the same actual typed row data used by the measured k=1 result.
All finite rounding bodies remain unexecuted. This file proves the
arithmetic direction into the exact Jensen*(1+T10+Q0) expression; it does
not assert that expression is already below the actual physical integral.
The adopted mixed Q6 floor is a distinct later obligation.
-/

namespace ImbalancedChen.P2Winner9SelectedCurvatureFloorWitness

open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor

/-- Literal curvature-stream fields for simplex_id=21. -/
def row21TotalQ80 : Nat := 16007085917676593648460

def row21RawQ96 : Nat := 33473824252327663860

/-- Literal curvature-stream fields for simplex_id=22. -/
def row22TotalQ80 : Nat := 15389547820376111661547

def row22RawQ96 : Nat := 6447903780770652011

/-- The row21 exact reconstruction is the pre-existing closed source
proposal, specialized to the unchanged actual Row21.data. -/
theorem row21_rounding :
    curvatureFloorQ80 (total Row21.data).num (total Row21.data).den row21TotalQ80 ∧
      jensenProductFloorQ96 Row21.data.jensenNum Row21.data.jensenDen
        row21TotalQ80 row21RawQ96 := by
  exact ImbalancedChen.P2Winner9Row21PrimitiveBinding.row21_exact_rounding_proposal

/-- Exact cross-product rounding obligations for original row22, with
its own reconstructed integer data. The closed body has not run.
Its reduction may need a compiler-owned resource-safe implementation. -/
theorem row22_rounding :
    curvatureFloorQ80 (total Row22.data).num (total Row22.data).den row22TotalQ80 ∧
      jensenProductFloorQ96 Row22.data.jensenNum Row22.data.jensenDen
        row22TotalQ80 row22RawQ96 := by
  decide +kernel

/-- The saved row21 curvature raw floor has the correct directed
arithmetic inequality for this actual typed row's exact expression. -/
theorem row21_raw_arithmetic_lower :
    (row21RawQ96 : ℚ) / q96 ≤
      ((Row21.data.jensenNum : ℚ) / Row21.data.jensenDen) *
        (1 + value (total Row21.data)) :=
  total_directed_floor_semantics Row21.data row21TotalQ80 row21RawQ96
    row21_rounding.1 row21_rounding.2

theorem row22_raw_arithmetic_lower :
    (row22RawQ96 : ℚ) / q96 ≤
      ((Row22.data.jensenNum : ℚ) / Row22.data.jensenDen) *
        (1 + value (total Row22.data)) :=
  total_directed_floor_semantics Row22.data row22TotalQ80 row22RawQ96
    row22_rounding.1 row22_rounding.2

/-- Literal raw fields match the original joined archive's chronology.
This is data alignment only, never an analytic enclosure. -/
theorem row21_archive_raw_alignment :
    (ImbalancedChen.P2Winner9SeedLiteralRowBatch.batchRows[21]!).curvatureRawQ96 =
      row21RawQ96 := by decide +kernel

theorem row22_archive_raw_alignment :
    (ImbalancedChen.P2Winner9SeedLiteralRowBatch.batchRows[22]!).curvatureRawQ96 =
      row22RawQ96 := by decide +kernel

end ImbalancedChen.P2Winner9SelectedCurvatureFloorWitness
