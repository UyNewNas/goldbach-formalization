import ImbalancedChen.OriginalAscendingThirteenCellOwnership
import ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows

/-!
SOURCE ONLY / UNCOMPILED. Lossless 13-by-97 strict rational row payload
from A23/s23_low alternative of navigation48e7b215239e9236f3e4d632a228f3a11a2161aa43d16b79257758de7107ecb4.
All1261rows are represented by103verbatim rational vectors and their
literal index table. The two zero identities are not inserted as strict
rows. Independent ascending semantic expressions have exactly the same
coefficients and real evaluations. The proved affine evaluator is reused;
none of the descending policy's geometry or coefficients is substituted.
No producer, certifier, compiler or numerical replay was executed.
-/
namespace ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows
noncomputable section
open scoped BigOperators
open OriginalAscendingThirteenCellOwnership
open OriginalDescendingFifteenLiteralAffineRows

def oldExpr : Expr := K (1 / 2) + (1 / 2 : ℚ) • (X 0 + X 3)
def thirdExpr : Expr := K (1 / 2) + (1 / 2 : ℚ) • (X 1 + X 2)
def newExpr : Expr := K (1 / 2) + (1 / 2 : ℚ) • (X 1 + X 3 + X 7) - K (1 / 1000000)

def semanticExpr (i : Fin 13) : Fin 97 → Expr :=
  ![K (25 / 128) - X 0,
    X 2 - K (1 / 100),
    X 7 - K (53 / 13824),
    X 0 - X 1,
    X 1 - X 2,
    X 2 - X 3,
    X 3 - X 4,
    X 4 - X 5,
    X 5 - X 6,
    X 6 - X 7,
    thirdExpr - (3 : ℚ) • X 0,
    thirdExpr - (X 0 + X 1 + (3 : ℚ) • X 2),
    thirdExpr - (X 0 + X 1 + X 2 + X 3 + (3 : ℚ) • X 4),
    thirdExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + (3 : ℚ) • X 6),
    oldExpr - thirdExpr,
    (K (57 / 64) - (3 / 2 : ℚ) • (X 0 + X 3)) - oldExpr,
    oldExpr - K (153 / 256) + (3 / 8 : ℚ) • X 2,
    K (25 / 128) - X 1 - X 2,
    newExpr - oldExpr,
    (K (57 / 64) - (3 / 2 : ℚ) • (X 1 + X 3 + X 7)) - K (1 / 1000000) - newExpr,
    newExpr - ((2 : ℚ) • X 0),
    newExpr - (X 1 + X 3 + X 7 + (2 : ℚ) • X 0),
    newExpr - (X 0 + (2 : ℚ) • X 1),
    newExpr - (X 0 + X 1 + (2 : ℚ) • X 2),
    newExpr - (X 1 + X 3 + X 7 + X 0 + (2 : ℚ) • X 2),
    newExpr - (X 0 + X 1 + X 2 + (2 : ℚ) • X 3),
    newExpr - (X 0 + X 1 + X 2 + X 3 + (2 : ℚ) • X 4),
    newExpr - (X 1 + X 3 + X 7 + X 0 + X 2 + (2 : ℚ) • X 4),
    newExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + (2 : ℚ) • X 5),
    newExpr - (X 1 + X 3 + X 7 + X 0 + X 2 + X 4 + (2 : ℚ) • X 5),
    newExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + (2 : ℚ) • X 6),
    newExpr - (X 1 + X 3 + X 7 + X 0 + X 2 + X 4 + X 5 + (2 : ℚ) • X 6),
    newExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + X 6 + (2 : ℚ) • X 7),
    oldExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + X 6 + X 7 + X 7),
    (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + X 6 + X 7 + (3 : ℚ) • X 7) - newExpr,
    oldExpr - (if 1 ∈ leftMasks i then ascendingExpr 1 else descendingExpr 1),
    oldExpr - (if 2 ∈ leftMasks i then ascendingExpr 2 else descendingExpr 2),
    oldExpr - (if 3 ∈ leftMasks i then ascendingExpr 3 else descendingExpr 3),
    oldExpr - (if 4 ∈ leftMasks i then ascendingExpr 4 else descendingExpr 4),
    oldExpr - (if 5 ∈ leftMasks i then ascendingExpr 5 else descendingExpr 5),
    oldExpr - (if 6 ∈ leftMasks i then ascendingExpr 6 else descendingExpr 6),
    oldExpr - (if 7 ∈ leftMasks i then ascendingExpr 7 else descendingExpr 7),
    oldExpr - (if 8 ∈ leftMasks i then ascendingExpr 8 else descendingExpr 8),
    oldExpr - (if 10 ∈ leftMasks i then ascendingExpr 10 else descendingExpr 10),
    oldExpr - (if 11 ∈ leftMasks i then ascendingExpr 11 else descendingExpr 11),
    oldExpr - (if 12 ∈ leftMasks i then ascendingExpr 12 else descendingExpr 12),
    oldExpr - (if 13 ∈ leftMasks i then ascendingExpr 13 else descendingExpr 13),
    oldExpr - (if 14 ∈ leftMasks i then ascendingExpr 14 else descendingExpr 14),
    oldExpr - (if 15 ∈ leftMasks i then ascendingExpr 15 else descendingExpr 15),
    oldExpr - (if 16 ∈ leftMasks i then ascendingExpr 16 else descendingExpr 16),
    oldExpr - (if 17 ∈ leftMasks i then ascendingExpr 17 else descendingExpr 17),
    oldExpr - (if 18 ∈ leftMasks i then ascendingExpr 18 else descendingExpr 18),
    oldExpr - (if 19 ∈ leftMasks i then ascendingExpr 19 else descendingExpr 19),
    oldExpr - (if 20 ∈ leftMasks i then ascendingExpr 20 else descendingExpr 20),
    oldExpr - (if 21 ∈ leftMasks i then ascendingExpr 21 else descendingExpr 21),
    oldExpr - (if 22 ∈ leftMasks i then ascendingExpr 22 else descendingExpr 22),
    oldExpr - (if 23 ∈ leftMasks i then ascendingExpr 23 else descendingExpr 23),
    oldExpr - (if 24 ∈ leftMasks i then ascendingExpr 24 else descendingExpr 24),
    oldExpr - (if 25 ∈ leftMasks i then ascendingExpr 25 else descendingExpr 25),
    oldExpr - (if 26 ∈ leftMasks i then ascendingExpr 26 else descendingExpr 26),
    oldExpr - (if 27 ∈ leftMasks i then ascendingExpr 27 else descendingExpr 27),
    oldExpr - (if 28 ∈ leftMasks i then ascendingExpr 28 else descendingExpr 28),
    oldExpr - (if 29 ∈ leftMasks i then ascendingExpr 29 else descendingExpr 29),
    oldExpr - (if 30 ∈ leftMasks i then ascendingExpr 30 else descendingExpr 30),
    oldExpr - (if 31 ∈ leftMasks i then ascendingExpr 31 else descendingExpr 31),
    oldExpr - (if 32 ∈ leftMasks i then ascendingExpr 32 else descendingExpr 32),
    oldExpr - (if 33 ∈ leftMasks i then ascendingExpr 33 else descendingExpr 33),
    oldExpr - (if 34 ∈ leftMasks i then ascendingExpr 34 else descendingExpr 34),
    oldExpr - (if 35 ∈ leftMasks i then ascendingExpr 35 else descendingExpr 35),
    oldExpr - (if 36 ∈ leftMasks i then ascendingExpr 36 else descendingExpr 36),
    oldExpr - (if 37 ∈ leftMasks i then ascendingExpr 37 else descendingExpr 37),
    oldExpr - (if 38 ∈ leftMasks i then ascendingExpr 38 else descendingExpr 38),
    oldExpr - (if 39 ∈ leftMasks i then ascendingExpr 39 else descendingExpr 39),
    oldExpr - (if 40 ∈ leftMasks i then ascendingExpr 40 else descendingExpr 40),
    oldExpr - (if 41 ∈ leftMasks i then ascendingExpr 41 else descendingExpr 41),
    oldExpr - (if 42 ∈ leftMasks i then ascendingExpr 42 else descendingExpr 42),
    oldExpr - (if 43 ∈ leftMasks i then ascendingExpr 43 else descendingExpr 43),
    oldExpr - (if 44 ∈ leftMasks i then ascendingExpr 44 else descendingExpr 44),
    oldExpr - (if 45 ∈ leftMasks i then ascendingExpr 45 else descendingExpr 45),
    oldExpr - (if 46 ∈ leftMasks i then ascendingExpr 46 else descendingExpr 46),
    oldExpr - (if 47 ∈ leftMasks i then ascendingExpr 47 else descendingExpr 47),
    oldExpr - (if 48 ∈ leftMasks i then ascendingExpr 48 else descendingExpr 48),
    oldExpr - (if 49 ∈ leftMasks i then ascendingExpr 49 else descendingExpr 49),
    oldExpr - (if 50 ∈ leftMasks i then ascendingExpr 50 else descendingExpr 50),
    oldExpr - (if 51 ∈ leftMasks i then ascendingExpr 51 else descendingExpr 51),
    oldExpr - (if 52 ∈ leftMasks i then ascendingExpr 52 else descendingExpr 52),
    oldExpr - (if 53 ∈ leftMasks i then ascendingExpr 53 else descendingExpr 53),
    oldExpr - (if 54 ∈ leftMasks i then ascendingExpr 54 else descendingExpr 54),
    oldExpr - (if 55 ∈ leftMasks i then ascendingExpr 55 else descendingExpr 55),
    oldExpr - (if 56 ∈ leftMasks i then ascendingExpr 56 else descendingExpr 56),
    oldExpr - (if 57 ∈ leftMasks i then ascendingExpr 57 else descendingExpr 57),
    oldExpr - (if 58 ∈ leftMasks i then ascendingExpr 58 else descendingExpr 58),
    oldExpr - (if 59 ∈ leftMasks i then ascendingExpr 59 else descendingExpr 59),
    oldExpr - (if 60 ∈ leftMasks i then ascendingExpr 60 else descendingExpr 60),
    oldExpr - (if 61 ∈ leftMasks i then ascendingExpr 61 else descendingExpr 61),
    oldExpr - (if 62 ∈ leftMasks i then ascendingExpr 62 else descendingExpr 62),
    oldExpr - (if 63 ∈ leftMasks i then ascendingExpr 63 else descendingExpr 63)]
def literalPool : Fin 103 → Fin 9 → ℚ :=
  ![![25/128, -1, 0, 0, 0, 0, 0, 0, 0],
    ![-1/100, 0, 0, 1, 0, 0, 0, 0, 0],
    ![-53/13824, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, -1],
    ![1/2, -3, 1/2, 1/2, 0, 0, 0, 0, 0],
    ![1/2, -1, -1/2, -5/2, 0, 0, 0, 0, 0],
    ![1/2, -1, -1/2, -1/2, -1, -3, 0, 0, 0],
    ![1/2, -1, -1/2, -1/2, -1, -1, -1, -3, 0],
    ![0, 1/2, -1/2, -1/2, 1/2, 0, 0, 0, 0],
    ![25/64, -2, 0, 0, -2, 0, 0, 0, 0],
    ![-25/256, 1/2, 0, 3/8, 1/2, 0, 0, 0, 0],
    ![25/128, 0, -1, -1, 0, 0, 0, 0, 0],
    ![-1/1000000, -1/2, 1/2, 0, 0, 0, 0, 0, 1/2],
    ![25/64, 0, -2, 0, -2, 0, 0, 0, -2],
    ![499999/1000000, -2, 1/2, 0, 1/2, 0, 0, 0, 1/2],
    ![499999/1000000, -2, -1/2, 0, -1/2, 0, 0, 0, -1/2],
    ![499999/1000000, -1, -3/2, 0, 1/2, 0, 0, 0, 1/2],
    ![499999/1000000, -1, -1/2, -2, 1/2, 0, 0, 0, 1/2],
    ![499999/1000000, -1, -1/2, -2, -1/2, 0, 0, 0, -1/2],
    ![499999/1000000, -1, -1/2, -1, -3/2, 0, 0, 0, 1/2],
    ![499999/1000000, -1, -1/2, -1, -1/2, -2, 0, 0, 1/2],
    ![499999/1000000, -1, -1/2, -1, -1/2, -2, 0, 0, -1/2],
    ![499999/1000000, -1, -1/2, -1, -1/2, -1, -2, 0, 1/2],
    ![499999/1000000, -1, -1/2, -1, -1/2, -1, -2, 0, -1/2],
    ![499999/1000000, -1, -1/2, -1, -1/2, -1, -1, -2, 1/2],
    ![499999/1000000, -1, -1/2, -1, -1/2, -1, -1, -2, -1/2],
    ![499999/1000000, -1, -1/2, -1, -1/2, -1, -1, -1, -3/2],
    ![1/2, -1/2, -1, -1, -1/2, -1, -1, -1, -2],
    ![-499999/1000000, 1, 1/2, 1, 1/2, 1, 1, 1, 7/2],
    ![0, 0, 0, 0, 1/2, 0, 0, 0, 0],
    ![0, 1/2, -1/2, 0, 1/2, 0, 0, 0, 0],
    ![-25/64, 2, 3/2, 0, 1/2, 0, 0, 0, 0],
    ![0, 1/2, 0, -1/2, 1/2, 0, 0, 0, 0],
    ![-25/64, 2, 0, 3/2, 1/2, 0, 0, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 1/2, 0, 0, 0, 0],
    ![0, 1/2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1/2, -1/2, 0, 0, 0, 0, 0, 0],
    ![-25/64, 2, 3/2, 0, 2, 0, 0, 0, 0],
    ![0, 1/2, 0, -1/2, 0, 0, 0, 0, 0],
    ![-25/64, 2, 0, 3/2, 2, 0, 0, 0, 0],
    ![-25/64, 1/2, 3/2, 3/2, 2, 0, 0, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 2, 0, 0, 0, 0],
    ![0, 1/2, 0, 0, 1/2, -1/2, 0, 0, 0],
    ![0, 0, 0, 0, 1/2, -1/2, 0, 0, 0],
    ![0, 1/2, -1/2, 0, 1/2, -1/2, 0, 0, 0],
    ![-25/64, 2, 3/2, 0, 1/2, 3/2, 0, 0, 0],
    ![0, 1/2, 0, -1/2, 1/2, -1/2, 0, 0, 0],
    ![-25/64, 2, 0, 3/2, 1/2, 3/2, 0, 0, 0],
    ![-25/64, 1/2, 3/2, 3/2, 1/2, 3/2, 0, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 1/2, 3/2, 0, 0, 0],
    ![0, 1/2, 0, 0, 0, -1/2, 0, 0, 0],
    ![-25/64, 2, 0, 0, 2, 3/2, 0, 0, 0],
    ![-25/64, 1/2, 3/2, 0, 2, 3/2, 0, 0, 0],
    ![-25/64, 2, 3/2, 0, 2, 3/2, 0, 0, 0],
    ![0, 1/2, 0, -1/2, 0, -1/2, 0, 0, 0],
    ![-25/64, 2, 0, 3/2, 2, 3/2, 0, 0, 0],
    ![-25/64, 1/2, 3/2, 3/2, 2, 3/2, 0, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 2, 3/2, 0, 0, 0],
    ![0, 1/2, 0, 0, 1/2, 0, -1/2, 0, 0],
    ![0, 0, 0, 0, 1/2, 0, -1/2, 0, 0],
    ![0, 1/2, -1/2, 0, 1/2, 0, -1/2, 0, 0],
    ![-25/64, 2, 3/2, 0, 1/2, 0, 3/2, 0, 0],
    ![0, 1/2, 0, -1/2, 1/2, 0, -1/2, 0, 0],
    ![-25/64, 2, 0, 3/2, 1/2, 0, 3/2, 0, 0],
    ![-25/64, 1/2, 3/2, 3/2, 1/2, 0, 3/2, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 1/2, 0, 3/2, 0, 0],
    ![0, 1/2, 0, 0, 0, 0, -1/2, 0, 0],
    ![-25/64, 2, 0, 0, 2, 0, 3/2, 0, 0],
    ![-25/64, 1/2, 3/2, 0, 2, 0, 3/2, 0, 0],
    ![-25/64, 2, 3/2, 0, 2, 0, 3/2, 0, 0],
    ![0, 1/2, 0, -1/2, 0, 0, -1/2, 0, 0],
    ![-25/64, 2, 0, 3/2, 2, 0, 3/2, 0, 0],
    ![-25/64, 1/2, 3/2, 3/2, 2, 0, 3/2, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 2, 0, 3/2, 0, 0],
    ![0, 1/2, 0, 0, 1/2, -1/2, -1/2, 0, 0],
    ![0, 0, 0, 0, 1/2, -1/2, -1/2, 0, 0],
    ![0, 1/2, -1/2, 0, 1/2, -1/2, -1/2, 0, 0],
    ![-25/64, 2, 3/2, 0, 1/2, 3/2, 3/2, 0, 0],
    ![0, 1/2, 0, -1/2, 1/2, -1/2, -1/2, 0, 0],
    ![-25/64, 2, 0, 3/2, 1/2, 3/2, 3/2, 0, 0],
    ![-25/64, 1/2, 3/2, 3/2, 1/2, 3/2, 3/2, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 1/2, 3/2, 3/2, 0, 0],
    ![0, 1/2, 0, 0, 0, -1/2, -1/2, 0, 0],
    ![-25/64, 2, 0, 0, 2, 3/2, 3/2, 0, 0],
    ![-25/64, 1/2, 3/2, 0, 2, 3/2, 3/2, 0, 0],
    ![-25/64, 2, 3/2, 0, 2, 3/2, 3/2, 0, 0],
    ![-25/64, 1/2, 0, 3/2, 2, 3/2, 3/2, 0, 0],
    ![-25/64, 2, 0, 3/2, 2, 3/2, 3/2, 0, 0],
    ![-25/64, 1/2, 3/2, 3/2, 2, 3/2, 3/2, 0, 0],
    ![-25/64, 2, 3/2, 3/2, 2, 3/2, 3/2, 0, 0],
    ![-25/64, 2, 0, 0, 1/2, 3/2, 3/2, 0, 0],
    ![0, 1/2, 0, -1/2, 0, -1/2, -1/2, 0, 0],
    ![-25/64, 1/2, 3/2, 0, 1/2, 3/2, 3/2, 0, 0],
    ![-25/64, 1/2, 0, 3/2, 2, 3/2, 0, 0, 0],
    ![-25/64, 1/2, 0, 3/2, 2, 0, 3/2, 0, 0],
    ![-25/64, 1/2, 0, 3/2, 1/2, 3/2, 3/2, 0, 0],
    ![-25/64, 1/2, 0, 0, 2, 3/2, 3/2, 0, 0]]
def literalIndex : Fin 13 → Fin 97 → Fin 103 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 96, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 96, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 96, 98, 83, 84, 85, 86, 87, 88, 89, 90, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 96, 98, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 100, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 96, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 96, 98, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 100, 77, 78, 79, 80, 96, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 100, 77, 78, 79, 80, 96, 98, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 100, 77, 78, 79, 80, 96, 98, 83, 101, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 14, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 100, 77, 78, 79, 80, 96, 98, 83, 101, 85, 86, 87, 102, 89, 90, 91, 92, 93, 94, 95]]

def exportedCoefficients (i : Fin 13) (r : Fin 97) : Fin 9 → ℚ := literalPool (literalIndex i r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem literal_coefficients_match : ∀ (i : Fin 13) (r : Fin 97) (k : Fin 9),
    exportedCoefficients i r k = coefficients (semanticExpr i r) k := by decide

def semanticSlack (i : Fin 13) (r : Fin 97) (t : Fin 8 → ℝ) : ℝ := evaluate (semanticExpr i r) t

theorem exportedRow_eval_eq_semanticSlack (i : Fin 13) (r : Fin 97) (t : Fin 8 → ℝ) :
    evaluateCoefficients (exportedCoefficients i r) t = semanticSlack i r t := by
  have h : exportedCoefficients i r = coefficients (semanticExpr i r) :=
    funext (fun k => literal_coefficients_match i r k)
  rw [h]
  exact evaluate_coefficients (semanticExpr i r) t

def StrictExportedRows (i : Fin 13) (t : Fin 8 → ℝ) : Prop :=
  ∀ r : Fin 97, 0 < evaluateCoefficients (exportedCoefficients i r) t
def StrictSemanticRows (i : Fin 13) (t : Fin 8 → ℝ) : Prop := ∀ r : Fin 97, 0 < semanticSlack i r t

theorem strictExportedRows_iff_strictSemanticRows (i : Fin 13) (t : Fin 8 → ℝ) :
    StrictExportedRows i t ↔ StrictSemanticRows i t := by
  simp only [StrictExportedRows, StrictSemanticRows, exportedRow_eval_eq_semanticSlack]

end
end ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows
