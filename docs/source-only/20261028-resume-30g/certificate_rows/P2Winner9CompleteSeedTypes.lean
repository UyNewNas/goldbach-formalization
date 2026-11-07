import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual unfiltered winner9 seed archive schema. A Row keeps original IDs,
physical ordered vertices/volume/means/Jensen data and all selected log,
curvature and mixed field families. No source decision/checker was run.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedTypes

structure RawRow where
  parentId : Nat
  vertexIds : Fin 9 → Nat
  physicalVolume : ℚ
  meanGap : ℚ
  means : Fin 10 → ℚ
  jensen : ℚ
  parentJensenFloor : Nat
  logId : Nat
  logGapFloors : Array Nat
  logOld : Nat
  logSelected : Nat
  curvatureId : Nat
  curvatureCurrent : Nat
  curvaturePlain : Nat
  curvatureTotalQ80 : Nat
  curvatureDiagnosticQ80 : Nat
  curvatureRaw : Nat
  curvatureSelected : Nat
  mixedId : Nat
  mixedPrevious : Nat
  mixedDegree : Nat
  mixedMomentFloors : Array (Array Nat)
  mixedTermFloors : Array Nat
  mixedCorrectionQ80 : Nat
  mixedTotalQ80 : Nat
  mixedRaw : Nat
  mixedSelected : Nat
  deriving Inhabited

end ImbalancedChen.P2Winner9CompleteSeedTypes
