import ImbalancedChen.OriginalDescendingFifteenCellOwnership

/-!
SOURCE ONLY / UNCOMPILED. Lossless literal export of the original 1440
rational affine rows in navigation SHA420ec389ac361a175bd429ab9bf4215fc42a4e1ec7a7e382f244773ea98083b1.
The 104 distinct nine-entry vectors are copied as rational literals;
the 15-by-96 index table recovers their original cell and row order.
No exporter, solver, integral certifier or numerical replay was executed.

The separate semantic expression generator reconstructs the original
96 named slacks. Its rational coefficients are proved equal to every
exported entry; real evaluation and the strict-positive convention then
agree for every real point. Neither a payload-match hypothesis nor an
integral lower bound is accepted as an assumption.
-/

namespace ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows
noncomputable section
open scoped BigOperators
open OriginalDescendingFifteenCellOwnership

inductive Expr where
  | constant : ℚ → Expr
  | coord : Fin 8 → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | scale : ℚ → Expr → Expr

instance : Add Expr := ⟨Expr.add⟩
instance : Sub Expr := ⟨Expr.sub⟩
instance : SMul ℚ Expr := ⟨Expr.scale⟩

def K : ℚ → Expr := Expr.constant
def X : Fin 8 → Expr := Expr.coord

def coefficients : Expr → Fin 9 → ℚ
  | .constant c => fun k => if k = 0 then c else 0
  | .coord j => fun k => if k = j.succ then 1 else 0
  | .add a b => fun k => coefficients a k + coefficients b k
  | .sub a b => fun k => coefficients a k - coefficients b k
  | .scale c a => fun k => c * coefficients a k

def evaluate : Expr → (Fin 8 → ℝ) → ℝ
  | .constant c, _ => c
  | .coord j, t => t j
  | .add a b, t => evaluate a t + evaluate b t
  | .sub a b, t => evaluate a t - evaluate b t
  | .scale c a, t => (c : ℝ) * evaluate a t

def evaluateCoefficients (a : Fin 9 → ℚ) (t : Fin 8 → ℝ) : ℝ :=
  (a 0 : ℝ) + ∑ j : Fin 8, (a j.succ : ℝ) * t j

private theorem evaluateCoefficients_add (a b : Fin 9 → ℚ) (t : Fin 8 → ℝ) :
    evaluateCoefficients (fun k => a k + b k) t =
      evaluateCoefficients a t + evaluateCoefficients b t := by
  simp only [evaluateCoefficients, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

private theorem evaluateCoefficients_sub (a b : Fin 9 → ℚ) (t : Fin 8 → ℝ) :
    evaluateCoefficients (fun k => a k - b k) t =
      evaluateCoefficients a t - evaluateCoefficients b t := by
  simp only [evaluateCoefficients, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring

private theorem evaluateCoefficients_scale (c : ℚ) (a : Fin 9 → ℚ) (t : Fin 8 → ℝ) :
    evaluateCoefficients (fun k => c * a k) t = (c : ℝ) * evaluateCoefficients a t := by
  simp only [evaluateCoefficients, Rat.cast_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem evaluate_coefficients (e : Expr) (t : Fin 8 → ℝ) :
    evaluateCoefficients (coefficients e) t = evaluate e t := by
  induction e with
  | constant c => simp [coefficients, evaluateCoefficients, evaluate]
  | coord j => simp [coefficients, evaluateCoefficients, evaluate, Fin.succ_inj]
  | add a b ha hb =>
      rw [coefficients, evaluateCoefficients_add, ha, hb]
      rfl
  | sub a b ha hb =>
      rw [coefficients, evaluateCoefficients_sub, ha, hb]
      rfl
  | scale c a ha =>
      rw [coefficients, evaluateCoefficients_scale, ha]
      rfl

def oldExpr : Expr := K (57 / 64) - (3 / 2 : ℚ) • (X 1 + X 2)
def newExpr : Expr := K (57 / 64) - (3 / 2 : ℚ) • (X 0 + X 7) - K (1 / 1000000)

def subsetExpr (m : ℕ) : Expr :=
  (if m.testBit 0 then X 0 else K 0) +
  (if m.testBit 1 then X 1 else K 0) +
  (if m.testBit 2 then X 2 else K 0) +
  (if m.testBit 3 then X 3 else K 0) +
  (if m.testBit 4 then X 4 else K 0) +
  (if m.testBit 5 then X 5 else K 0)

def ascendingExpr (m : ℕ) : Expr := K (1 / 2) + (1 / 2 : ℚ) • subsetExpr m
def descendingExpr (m : ℕ) : Expr := K (57 / 64) - (3 / 2 : ℚ) • subsetExpr m

def semanticExpr (i : Fin 15) : Fin 96 → Expr :=
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
    oldExpr - (3 : ℚ) • X 0,
    oldExpr - (X 0 + X 1 + (3 : ℚ) • X 2),
    oldExpr - (X 0 + X 1 + X 2 + X 3 + (3 : ℚ) • X 4),
    oldExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + (3 : ℚ) • X 6),
    (K (1 / 2) + (1 / 2 : ℚ) • (X 1 + X 2)) - oldExpr,
    oldExpr - (K (153 / 256) - (3 / 8 : ℚ) • X 2),
    newExpr - oldExpr,
    (K (1 / 2) + (1 / 2 : ℚ) • (X 0 + X 7) - K (1 / 1000000)) - newExpr,
    newExpr - ((2 : ℚ) • X 0),
    newExpr - (X 0 + (2 : ℚ) • X 1),
    newExpr - (X 0 + X 7 + (2 : ℚ) • X 1),
    newExpr - (X 0 + X 1 + (2 : ℚ) • X 2),
    newExpr - (X 0 + X 7 + X 1 + (2 : ℚ) • X 2),
    newExpr - (X 0 + X 1 + X 2 + (2 : ℚ) • X 3),
    newExpr - (X 0 + X 7 + X 1 + X 2 + (2 : ℚ) • X 3),
    newExpr - (X 0 + X 1 + X 2 + X 3 + (2 : ℚ) • X 4),
    newExpr - (X 0 + X 7 + X 1 + X 2 + X 3 + (2 : ℚ) • X 4),
    newExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + (2 : ℚ) • X 5),
    newExpr - (X 0 + X 7 + X 1 + X 2 + X 3 + X 4 + (2 : ℚ) • X 5),
    newExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + (2 : ℚ) • X 6),
    newExpr - (X 0 + X 7 + X 1 + X 2 + X 3 + X 4 + X 5 + (2 : ℚ) • X 6),
    newExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + X 6 + (2 : ℚ) • X 7),
    oldExpr - (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + X 6 + X 7 + X 7),
    (X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + X 6 + X 7 + (3 : ℚ) • X 7) - newExpr,
    oldExpr - (if 1 ∈ leftMasks i then ascendingExpr 1 else descendingExpr 1),
    oldExpr - (if 2 ∈ leftMasks i then ascendingExpr 2 else descendingExpr 2),
    oldExpr - (if 3 ∈ leftMasks i then ascendingExpr 3 else descendingExpr 3),
    oldExpr - (if 4 ∈ leftMasks i then ascendingExpr 4 else descendingExpr 4),
    oldExpr - (if 5 ∈ leftMasks i then ascendingExpr 5 else descendingExpr 5),
    oldExpr - (if 7 ∈ leftMasks i then ascendingExpr 7 else descendingExpr 7),
    oldExpr - (if 8 ∈ leftMasks i then ascendingExpr 8 else descendingExpr 8),
    oldExpr - (if 9 ∈ leftMasks i then ascendingExpr 9 else descendingExpr 9),
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

def literalPool : Fin 104 → Fin 9 → ℚ :=
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
    ![57/64, -3, -3/2, -3/2, 0, 0, 0, 0, 0],
    ![57/64, -1, -5/2, -9/2, 0, 0, 0, 0, 0],
    ![57/64, -1, -5/2, -5/2, -1, -3, 0, 0, 0],
    ![57/64, -1, -5/2, -5/2, -1, -1, -1, -3, 0],
    ![-25/64, 0, 2, 2, 0, 0, 0, 0, 0],
    ![75/256, 0, -3/2, -9/8, 0, 0, 0, 0, 0],
    ![-1/1000000, -3/2, 3/2, 3/2, 0, 0, 0, 0, -3/2],
    ![-25/64, 2, 0, 0, 0, 0, 0, 0, 2],
    ![13916/15625, -7/2, 0, 0, 0, 0, 0, 0, -3/2],
    ![13916/15625, -5/2, -2, 0, 0, 0, 0, 0, -3/2],
    ![13916/15625, -5/2, -2, 0, 0, 0, 0, 0, -5/2],
    ![13916/15625, -5/2, -1, -2, 0, 0, 0, 0, -3/2],
    ![13916/15625, -5/2, -1, -2, 0, 0, 0, 0, -5/2],
    ![13916/15625, -5/2, -1, -1, -2, 0, 0, 0, -3/2],
    ![13916/15625, -5/2, -1, -1, -2, 0, 0, 0, -5/2],
    ![13916/15625, -5/2, -1, -1, -1, -2, 0, 0, -3/2],
    ![13916/15625, -5/2, -1, -1, -1, -2, 0, 0, -5/2],
    ![13916/15625, -5/2, -1, -1, -1, -1, -2, 0, -3/2],
    ![13916/15625, -5/2, -1, -1, -1, -1, -2, 0, -5/2],
    ![13916/15625, -5/2, -1, -1, -1, -1, -1, -2, -3/2],
    ![13916/15625, -5/2, -1, -1, -1, -1, -1, -2, -5/2],
    ![13916/15625, -5/2, -1, -1, -1, -1, -1, -1, -7/2],
    ![57/64, -1, -5/2, -5/2, -1, -1, -1, -1, -2],
    ![-13916/15625, 5/2, 1, 1, 1, 1, 1, 1, 11/2],
    ![25/64, -1/2, -3/2, -3/2, 0, 0, 0, 0, 0],
    ![25/64, 0, -2, -3/2, 0, 0, 0, 0, 0],
    ![0, 3/2, 0, -3/2, 0, 0, 0, 0, 0],
    ![25/64, 0, -3/2, -2, 0, 0, 0, 0, 0],
    ![0, 3/2, -3/2, 0, 0, 0, 0, 0, 0],
    ![0, 3/2, 0, 0, 0, 0, 0, 0, 0],
    ![25/64, 0, -3/2, -3/2, -1/2, 0, 0, 0, 0],
    ![0, 3/2, -3/2, -3/2, 3/2, 0, 0, 0, 0],
    ![25/64, 0, -2, -3/2, -1/2, 0, 0, 0, 0],
    ![0, 3/2, 0, -3/2, 3/2, 0, 0, 0, 0],
    ![25/64, 0, -3/2, -2, -1/2, 0, 0, 0, 0],
    ![0, 3/2, -3/2, 0, 3/2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 3/2, 0, 0, 0, 0],
    ![0, 3/2, 0, 0, 3/2, 0, 0, 0, 0],
    ![25/64, 0, -3/2, -3/2, 0, -1/2, 0, 0, 0],
    ![0, 3/2, -3/2, -3/2, 0, 3/2, 0, 0, 0],
    ![25/64, 0, -2, -3/2, 0, -1/2, 0, 0, 0],
    ![0, 3/2, 0, -3/2, 0, 3/2, 0, 0, 0],
    ![25/64, 0, -3/2, -2, 0, -1/2, 0, 0, 0],
    ![0, 3/2, -3/2, 0, 0, 3/2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 3/2, 0, 0, 0],
    ![0, 3/2, 0, 0, 0, 3/2, 0, 0, 0],
    ![25/64, 0, -3/2, -3/2, -1/2, -1/2, 0, 0, 0],
    ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 0, 0, 0],
    ![25/64, 0, -2, -3/2, -1/2, -1/2, 0, 0, 0],
    ![0, 3/2, 0, -3/2, 3/2, 3/2, 0, 0, 0],
    ![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0],
    ![0, 3/2, -3/2, 0, 3/2, 3/2, 0, 0, 0],
    ![0, 0, 0, 0, 3/2, 3/2, 0, 0, 0],
    ![0, 3/2, 0, 0, 3/2, 3/2, 0, 0, 0],
    ![25/64, 0, -3/2, -3/2, 0, 0, -1/2, 0, 0],
    ![0, 3/2, -3/2, -3/2, 0, 0, 3/2, 0, 0],
    ![25/64, 0, -2, -3/2, 0, 0, -1/2, 0, 0],
    ![0, 3/2, 0, -3/2, 0, 0, 3/2, 0, 0],
    ![25/64, 0, -3/2, -2, 0, 0, -1/2, 0, 0],
    ![0, 3/2, -3/2, 0, 0, 0, 3/2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 3/2, 0, 0],
    ![0, 3/2, 0, 0, 0, 0, 3/2, 0, 0],
    ![25/64, 0, -3/2, -3/2, -1/2, 0, -1/2, 0, 0],
    ![0, 3/2, -3/2, -3/2, 3/2, 0, 3/2, 0, 0],
    ![25/64, 0, -2, -3/2, -1/2, 0, -1/2, 0, 0],
    ![0, 3/2, 0, -3/2, 3/2, 0, 3/2, 0, 0],
    ![25/64, 0, -3/2, -2, -1/2, 0, -1/2, 0, 0],
    ![0, 3/2, -3/2, 0, 3/2, 0, 3/2, 0, 0],
    ![0, 0, 0, 0, 3/2, 0, 3/2, 0, 0],
    ![0, 3/2, 0, 0, 3/2, 0, 3/2, 0, 0],
    ![25/64, 0, -3/2, -3/2, 0, -1/2, -1/2, 0, 0],
    ![0, 3/2, -3/2, -3/2, 0, 3/2, 3/2, 0, 0],
    ![25/64, 0, -2, -3/2, 0, -1/2, -1/2, 0, 0],
    ![0, 3/2, 0, -3/2, 0, 3/2, 3/2, 0, 0],
    ![25/64, 0, -3/2, -2, 0, -1/2, -1/2, 0, 0],
    ![0, 3/2, -3/2, 0, 0, 3/2, 3/2, 0, 0],
    ![0, 0, 0, 0, 0, 3/2, 3/2, 0, 0],
    ![0, 3/2, 0, 0, 0, 3/2, 3/2, 0, 0],
    ![25/64, 0, -3/2, -3/2, -1/2, -1/2, -1/2, 0, 0],
    ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 3/2, 0, 0],
    ![25/64, 0, -2, -3/2, -1/2, -1/2, -1/2, 0, 0],
    ![0, 3/2, 0, -3/2, 3/2, 3/2, 3/2, 0, 0],
    ![25/64, 0, -3/2, -2, -1/2, -1/2, -1/2, 0, 0],
    ![0, 3/2, -3/2, 0, 3/2, 3/2, 3/2, 0, 0],
    ![0, 0, 0, 0, 3/2, 3/2, 3/2, 0, 0],
    ![0, 3/2, 0, 0, 3/2, 3/2, 3/2, 0, 0],
    ![0, 0, 0, -3/2, 3/2, 3/2, 3/2, 0, 0],
    ![0, 0, -3/2, 0, 3/2, 3/2, 3/2, 0, 0],
    ![0, 0, 0, -3/2, 3/2, 3/2, 0, 0, 0],
    ![0, 0, -3/2, 0, 3/2, 3/2, 0, 0, 0],
    ![0, 0, 0, -3/2, 3/2, 0, 3/2, 0, 0],
    ![0, 0, 0, -3/2, 0, 3/2, 3/2, 0, 0],
    ![0, 0, -3/2, 0, 3/2, 0, 3/2, 0, 0],
    ![0, 0, -3/2, 0, 0, 3/2, 3/2, 0, 0]]

def literalIndex : Fin 15 → Fin 96 → Fin 104 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 76, 77, 78, 79, 80, 81, 101, 83, 84, 85, 86, 87, 88, 89, 96, 91, 92, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 76, 77, 78, 79, 80, 81, 101, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 76, 77, 78, 79, 80, 81, 101, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 102, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 102, 77, 78, 79, 80, 81, 101, 83, 84, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 98, 59, 99, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 100, 75, 102, 77, 78, 79, 80, 81, 101, 83, 103, 85, 86, 87, 88, 89, 96, 91, 97, 93, 94, 95]]

def exportedCoefficients (i : Fin 15) (r : Fin 96) : Fin 9 → ℚ :=
  literalPool (literalIndex i r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem literal_coefficients_match : ∀ (i : Fin 15) (r : Fin 96) (k : Fin 9),
    exportedCoefficients i r k = coefficients (semanticExpr i r) k := by decide

def semanticSlack (i : Fin 15) (r : Fin 96) (t : Fin 8 → ℝ) : ℝ :=
  evaluate (semanticExpr i r) t

theorem exportedRow_eval_eq_semanticSlack (i : Fin 15) (r : Fin 96) (t : Fin 8 → ℝ) :
    evaluateCoefficients (exportedCoefficients i r) t = semanticSlack i r t := by
  have h : exportedCoefficients i r = coefficients (semanticExpr i r) :=
    funext (fun k => literal_coefficients_match i r k)
  rw [h]
  exact evaluate_coefficients (semanticExpr i r) t

def StrictExportedRows (i : Fin 15) (t : Fin 8 → ℝ) : Prop :=
  ∀ r : Fin 96, 0 < evaluateCoefficients (exportedCoefficients i r) t

def StrictSemanticRows (i : Fin 15) (t : Fin 8 → ℝ) : Prop :=
  ∀ r : Fin 96, 0 < semanticSlack i r t

theorem strictExportedRows_iff_strictSemanticRows (i : Fin 15) (t : Fin 8 → ℝ) :
    StrictExportedRows i t ↔ StrictSemanticRows i t := by
  simp only [StrictExportedRows, StrictSemanticRows, exportedRow_eval_eq_semanticSlack]

end
end ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows
