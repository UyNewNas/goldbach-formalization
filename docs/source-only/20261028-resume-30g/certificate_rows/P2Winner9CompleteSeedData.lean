import ImbalancedChen.P2Winner9CompleteSeedVertices
import ImbalancedChen.P2Winner9CompleteSeedBlock00
import ImbalancedChen.P2Winner9CompleteSeedBlock01
import ImbalancedChen.P2Winner9CompleteSeedBlock02
import ImbalancedChen.P2Winner9CompleteSeedBlock03
import ImbalancedChen.P2Winner9CompleteSeedBlock04
import ImbalancedChen.P2Winner9CompleteSeedBlock05
import ImbalancedChen.P2Winner9CompleteSeedBlock06
import ImbalancedChen.P2Winner9CompleteSeedBlock07
import ImbalancedChen.P2Winner9CompleteSeedBlock08
import ImbalancedChen.P2Winner9CompleteSeedBlock09
import ImbalancedChen.P2Winner9CompleteSeedBlock10
import ImbalancedChen.P2Winner9CompleteSeedBlock11
import ImbalancedChen.P2Winner9CompleteSeedBlock12
import ImbalancedChen.P2Winner9CompleteSeedBlock13
import ImbalancedChen.P2Winner9CompleteSeedBlock14
import ImbalancedChen.P2Winner9CompleteSeedBlock15
import ImbalancedChen.P2Winner9CompleteSeedBlock16
import ImbalancedChen.P2Winner9CompleteSeedBlock17
import ImbalancedChen.P2Winner9CompleteSeedBlock18
import ImbalancedChen.P2Winner9CompleteSeedBlock19
import ImbalancedChen.P2Winner9CompleteSeedBlock20
import ImbalancedChen.P2Winner9CompleteSeedBlock21
import ImbalancedChen.P2Winner9CompleteSeedBlock22
import ImbalancedChen.P2Winner9CompleteSeedBlock23
import ImbalancedChen.P2Winner9CompleteSeedBlock24
import ImbalancedChen.P2Winner9CompleteSeedBlock25
import ImbalancedChen.P2Winner9CompleteSeedBlock26
import ImbalancedChen.P2Winner9CompleteSeedBlock27
import ImbalancedChen.P2Winner9CompleteSeedBlock28
import ImbalancedChen.P2Winner9CompleteSeedBlock29
import ImbalancedChen.P2Winner9CompleteSeedBlock30
import ImbalancedChen.P2Winner9CompleteSeedBlock31
import ImbalancedChen.P2Winner9CompleteSeedBlock32
import ImbalancedChen.P2Winner9CompleteSeedBlock33
import ImbalancedChen.P2Winner9CompleteSeedBlock34
import ImbalancedChen.P2Winner9CompleteSeedBlock35
import ImbalancedChen.P2Winner9CompleteSeedBlock36
import ImbalancedChen.P2Winner9CompleteSeedBlock37
import ImbalancedChen.P2Winner9CompleteSeedBlock38
import ImbalancedChen.P2Winner9CompleteSeedBlock39
import ImbalancedChen.P2Winner9CompleteSeedBlock40
import ImbalancedChen.P2Winner9CompleteSeedBlock41
import ImbalancedChen.P2Winner9CompleteSeedBlock42
import ImbalancedChen.P2Winner9CompleteSeedBlock43

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
This is the actual complete 11026-row source family, not an arbitrary
selected set. Every stream retains original ordinal, every raw field and
every ordered physical vertex list. All finite source-check proof bodies
below are unexecuted. No all-row analytic enclosure or triangulation
ownership is inferred from these data/identity checks.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedData
open P2Winner9CompleteSeedTypes

abbrev RowIndex := Fin 11026

def allRows : Array RawRow := #[
  P2Winner9CompleteSeedBlock00.rows,
  P2Winner9CompleteSeedBlock01.rows,
  P2Winner9CompleteSeedBlock02.rows,
  P2Winner9CompleteSeedBlock03.rows,
  P2Winner9CompleteSeedBlock04.rows,
  P2Winner9CompleteSeedBlock05.rows,
  P2Winner9CompleteSeedBlock06.rows,
  P2Winner9CompleteSeedBlock07.rows,
  P2Winner9CompleteSeedBlock08.rows,
  P2Winner9CompleteSeedBlock09.rows,
  P2Winner9CompleteSeedBlock10.rows,
  P2Winner9CompleteSeedBlock11.rows,
  P2Winner9CompleteSeedBlock12.rows,
  P2Winner9CompleteSeedBlock13.rows,
  P2Winner9CompleteSeedBlock14.rows,
  P2Winner9CompleteSeedBlock15.rows,
  P2Winner9CompleteSeedBlock16.rows,
  P2Winner9CompleteSeedBlock17.rows,
  P2Winner9CompleteSeedBlock18.rows,
  P2Winner9CompleteSeedBlock19.rows,
  P2Winner9CompleteSeedBlock20.rows,
  P2Winner9CompleteSeedBlock21.rows,
  P2Winner9CompleteSeedBlock22.rows,
  P2Winner9CompleteSeedBlock23.rows,
  P2Winner9CompleteSeedBlock24.rows,
  P2Winner9CompleteSeedBlock25.rows,
  P2Winner9CompleteSeedBlock26.rows,
  P2Winner9CompleteSeedBlock27.rows,
  P2Winner9CompleteSeedBlock28.rows,
  P2Winner9CompleteSeedBlock29.rows,
  P2Winner9CompleteSeedBlock30.rows,
  P2Winner9CompleteSeedBlock31.rows,
  P2Winner9CompleteSeedBlock32.rows,
  P2Winner9CompleteSeedBlock33.rows,
  P2Winner9CompleteSeedBlock34.rows,
  P2Winner9CompleteSeedBlock35.rows,
  P2Winner9CompleteSeedBlock36.rows,
  P2Winner9CompleteSeedBlock37.rows,
  P2Winner9CompleteSeedBlock38.rows,
  P2Winner9CompleteSeedBlock39.rows,
  P2Winner9CompleteSeedBlock40.rows,
  P2Winner9CompleteSeedBlock41.rows,
  P2Winner9CompleteSeedBlock42.rows,
  P2Winner9CompleteSeedBlock43.rows
].flatten

def entry (i : RowIndex) : RawRow := allRows[i.val]!

def physicalVertices (i : RowIndex) (k : Fin 9) : Fin 8 → ℚ :=
  P2Winner9CompleteSeedVertices.coordinates[(entry i).vertexIds k]!

/-- Exact arity and all ordinal/shape/max chronology checks are closed
source proposals only. No field, zero case or unsuccessful alternate
candidate was filtered out by this family representation. -/
theorem full_source_shapes_and_chronology :
    allRows.size = 11026 ∧
    P2Winner9CompleteSeedVertices.coordinates.size = 201 ∧
    ∀ i : RowIndex,
      (entry i).parentId = i.val ∧ (entry i).logId = i.val ∧
      (entry i).curvatureId = i.val ∧ (entry i).mixedId = i.val ∧
      (∀ k : Fin 9, (entry i).vertexIds k < 201) ∧
      (entry i).logGapFloors.size = 10 ∧
      (entry i).mixedDegree = 6 ∧
      (entry i).mixedMomentFloors.size = 10 ∧
      (∀ j : Fin 10, ((entry i).mixedMomentFloors[j.val]!).size = 7) ∧
      (entry i).mixedTermFloors.size = 7 ∧
      (entry i).parentJensenFloor = (entry i).logOld ∧
      (entry i).curvatureCurrent = (entry i).logSelected ∧
      (entry i).curvatureSelected = max (entry i).logSelected (entry i).curvatureRaw ∧
      (entry i).mixedPrevious = (entry i).curvatureSelected ∧
      (entry i).mixedSelected = max (entry i).curvatureSelected (entry i).mixedRaw := by
  decide +kernel

end ImbalancedChen.P2Winner9CompleteSeedData
