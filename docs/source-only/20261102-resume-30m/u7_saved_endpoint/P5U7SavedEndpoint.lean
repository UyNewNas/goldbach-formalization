import ImbalancedChen.P5U7Q80Backend
import ImbalancedChen.P5U7OriginalMidpointSum
import ImbalancedChen.P5OriginalDirectedMidpoint
import Mathlib.Data.Rat.BigOperators

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original 1024 cells, both original kernels and signed whole-cell curvature.
The endpoint proofs below are closed pure kernel proof terms, authored but
UNEVALUATED. The 64-term log enclosure is an alternative backend;
no equality to a historical producer run or printed total is asserted.
-/
namespace ImbalancedChen.P5U7SavedEndpoint

open Set MeasureTheory
open Certificates.P2DirectedLogRounding (Enclosure)
open P5U7Q80Backend P5U7OriginalMidpoint P5U7OriginalScalarCorrection
open scoped BigOperators

abbrev E := P5U7Q80Backend.Expr
private def c (q : ℚ) : E := .rational q
private def v : E := .variable
private def subE (a b : E) : E := .add a (.neg b)
private def oneMinus : E := subE (c 1) v
private def oneMinusTwo : E := subE (c 1) (.mul (c 2) v)

def primeLogExpr : E := .log (.div oneMinusTwo v)
def primeLogFirstExpr : E := subE (.div (c (-2)) oneMinusTwo) (.div (c 1) v)
def primeLogSecondExpr : E :=
  .add (.div (c (-4)) (.pow oneMinusTwo 2)) (.div (c 1) (.pow v 2))
def reciprocalExpr : E := .add (.div (c 1) v) (.div (c 1) oneMinus)
def reciprocalFirstExpr : E :=
  .add (.div (c (-1)) (.pow v 2)) (.div (c 1) (.pow oneMinus 2))
def reciprocalSecondExpr : E :=
  .add (.div (c 2) (.pow v 3)) (.div (c 2) (.pow oneMinus 3))

/-- Literal main_value(t,7), retaining its original denominator product. -/
def primeValueExpr : E := .div primeLogExpr (.mul v oneMinus)
/-- Literal main_second(t,7), without replacing signed curvature by abs. -/
def primeSecondExpr : E :=
  .add (.add (.mul primeLogSecondExpr reciprocalExpr)
    (.mul (.mul (c 2) primeLogFirstExpr) reciprocalFirstExpr))
    (.mul primeLogExpr reciprocalSecondExpr)

private def uMinus : E := subE v (c 1)
private def uPlus : E := .add v (c 1)
def correctionAExpr : E := .div (.log uMinus) v
def correctionAFirstExpr : E :=
  subE (.div (c 1) (.mul v uMinus)) (.div (.log uMinus) (.pow v 2))
def correctionASecondExpr : E :=
  .add (subE (.div (.neg (subE (.mul (c 2) v) (c 1)))
      (.mul (.pow v 2) (.pow uMinus 2)))
    (.div (c 1) (.mul uMinus (.pow v 2))))
    (.div (.mul (c 2) (.log uMinus)) (.pow v 3))
def correctionBExpr : E := .log (.div (c (191 / 59)) uPlus)
def correctionBFirstExpr : E := .div (c (-1)) uPlus
def correctionBSecondExpr : E := .div (c 1) (.pow uPlus 2)

def correctionValueExpr : E := .mul correctionAExpr correctionBExpr
def correctionSecondExpr : E :=
  .add (.add (.mul correctionASecondExpr correctionBExpr)
    (.mul (.mul (c 2) correctionAFirstExpr) correctionBFirstExpr))
    (.mul correctionAExpr correctionBSecondExpr)

/-- These identities bind every interval node to the actual old-K kernels. -/
theorem primeValueExpr_eval {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    primeValueExpr.eval t = primeValue t := by
  rw [primeValue_eq ht ht1]
  simp [primeValueExpr, primeLogExpr, oneMinusTwo, oneMinus,
    subE, c, v, Expr.eval, sub_eq_add_neg]

theorem primeSecondExpr_eval (t : ℝ) : primeSecondExpr.eval t = primeSecond t := by
  simp [primeSecondExpr, primeLogSecondExpr, primeLogFirstExpr, primeLogExpr,
    reciprocalExpr, reciprocalFirstExpr, reciprocalSecondExpr, oneMinusTwo, oneMinus,
    subE, c, v, Expr.eval, primeSecond, primeLogSecond, primeLogFirst, primeLog,
    reciprocal, reciprocalFirst, reciprocalSecond, sub_eq_add_neg]

theorem correctionValueExpr_eval (u : ℝ) :
    correctionValueExpr.eval u = scalarCorrectionKernel u := by
  simp [correctionValueExpr, correctionAExpr, correctionBExpr, scalarCorrectionKernel,
    uMinus, uPlus, subE, c, v, Expr.eval, sub_eq_add_neg]

theorem correctionSecondExpr_eval (u : ℝ) :
    correctionSecondExpr.eval u = correctionSecond u := by
  simp [correctionSecondExpr, correctionASecondExpr, correctionAFirstExpr,
    correctionAExpr, correctionBExpr, correctionBFirstExpr, correctionBSecondExpr,
    correctionSecond, correctionASecond, correctionAFirst, correctionA,
    correctionB, correctionBFirst, correctionBSecond,
    uMinus, uPlus, subE, c, v, Expr.eval, sub_eq_add_neg]

def primeLeft : ℚ := 59 / 250
def primeRight : ℚ := 1 / 3
def correctionLeft : ℚ := 2
def correctionRight : ℚ := 132 / 59

private theorem prime_regular_cast :
    (∀ t ∈ Icc (primeLeft : ℝ) (primeRight : ℝ), HasDerivAt primeValue (primeFirst t) t) ∧
    (∀ t ∈ Icc (primeLeft : ℝ) (primeRight : ℝ), HasDerivAt primeFirst (primeSecond t) t) ∧
    ContinuousOn primeSecond (Icc (primeLeft : ℝ) (primeRight : ℝ)) := by
  simpa [primeLeft, primeRight] using prime_regular

private theorem correction_regular_cast :
    (∀ u ∈ Icc (correctionLeft : ℝ) (correctionRight : ℝ),
      HasDerivAt scalarCorrectionKernel (correctionFirst u) u) ∧
    (∀ u ∈ Icc (correctionLeft : ℝ) (correctionRight : ℝ),
      HasDerivAt correctionFirst (correctionSecond u) u) ∧
    ContinuousOn correctionSecond (Icc (correctionLeft : ℝ) (correctionRight : ℝ)) := by
  simpa [correctionLeft, correctionRight] using correction_regular

def pointInput (a b : ℚ) (k : ℕ) : Enclosure := qpoint (midpoint1024 a b k)
def cellInput (a b : ℚ) (k : ℕ) : Enclosure :=
  qrange (mesh1024 a b k) (mesh1024 a b (k + 1))

def primePointBox (k : ℕ) : Enclosure := primeValueExpr.box (pointInput primeLeft primeRight k)
def primeCurvatureBox (k : ℕ) : Enclosure :=
  primeSecondExpr.box (cellInput primeLeft primeRight k)
def correctionPointBox (k : ℕ) : Enclosure :=
  correctionValueExpr.box (pointInput correctionLeft correctionRight k)
def correctionCurvatureBox (k : ℕ) : Enclosure :=
  correctionSecondExpr.box (cellInput correctionLeft correctionRight k)

/-- Closed finite positivity obligations, not supplied Boolean truth.
No containment or saved-endpoint proposition occurs in this finite guard.
This proof term has not been elaborated, reduced or checked in this task. -/
theorem all1024_operation_domains : ∀ k : Fin 1024,
    primeValueExpr.Valid (pointInput primeLeft primeRight k) ∧
    primeSecondExpr.Valid (cellInput primeLeft primeRight k) ∧
    correctionValueExpr.Valid (pointInput correctionLeft correctionRight k) ∧
    correctionSecondExpr.Valid (cellInput correctionLeft correctionRight k) := by
  decide

private theorem midpoint_mem {a b : ℚ} (hab : a ≤ b) {k : ℕ} (hk : k < 1024) :
    (midpoint1024 a b k : ℝ) ∈ Icc (a : ℝ) (b : ℝ) := by
  have hL := mesh1024_bounds hab k hk.le
  have hR := mesh1024_bounds hab (k + 1) (by omega)
  have hQ : a ≤ midpoint1024 a b k ∧ midpoint1024 a b k ≤ b := by
    dsimp [midpoint1024]
    constructor <;> linarith [hL.1, hL.2, hR.1, hR.2]
  constructor
  · exact_mod_cast hQ.1
  · exact_mod_cast hQ.2

/-- Actual Q80 midpoint box; no caller-supplied value containment. -/
theorem primePointBox_contains {k : ℕ} (hk : k < 1024) :
    (primePointBox k).Contains (primeValue (midpoint1024 primeLeft primeRight k : ℝ)) := by
  have hm := midpoint_mem (a := primeLeft) (b := primeRight) (by norm_num [primeLeft, primeRight]) hk
  have h := Expr.box_sound (qpoint_contains (midpoint1024 primeLeft primeRight k))
    primeValueExpr (all1024_operation_domains ⟨k, hk⟩).1
  have ht0 : (0 : ℝ) < (midpoint1024 primeLeft primeRight k : ℝ) :=
    (show (0 : ℝ) < (primeLeft : ℝ) by norm_num [primeLeft]).trans_le hm.1
  have ht1 : (midpoint1024 primeLeft primeRight k : ℝ) < (1 : ℝ) :=
    hm.2.trans_lt (by norm_num [primeRight])
  rw [primeValueExpr_eval ht0 ht1] at h
  exact h

/-- Actual WHOLE closed-cell Q80 curvature, including both endpoints. -/
theorem primeCurvatureBox_contains {k : ℕ} (hk : k < 1024)
    {t : ℝ} (ht : t ∈ Icc (mesh1024 primeLeft primeRight k : ℝ)
      (mesh1024 primeLeft primeRight (k + 1) : ℝ)) :
    (primeCurvatureBox k).Contains (primeSecond t) := by
  have h := Expr.box_sound (qrange_contains ht) primeSecondExpr
    (all1024_operation_domains ⟨k, hk⟩).2.1
  simpa only [primeSecondExpr_eval] using h

theorem correctionPointBox_contains {k : ℕ} (hk : k < 1024) :
    (correctionPointBox k).Contains
      (scalarCorrectionKernel (midpoint1024 correctionLeft correctionRight k : ℝ)) := by
  have h := Expr.box_sound (qpoint_contains (midpoint1024 correctionLeft correctionRight k))
    correctionValueExpr (all1024_operation_domains ⟨k, hk⟩).2.2.1
  simpa only [correctionValueExpr_eval] using h

theorem correctionCurvatureBox_contains {k : ℕ} (hk : k < 1024)
    {u : ℝ} (hu : u ∈ Icc (mesh1024 correctionLeft correctionRight k : ℝ)
      (mesh1024 correctionLeft correctionRight (k + 1) : ℝ)) :
    (correctionCurvatureBox k).Contains (correctionSecond u) := by
  have h := Expr.box_sound (qrange_contains hu) correctionSecondExpr
    (all1024_operation_domains ⟨k, hk⟩).2.2.2
  simpa only [correctionSecondExpr_eval] using h

/-- All rational constants and both multiplications round outward at Q80. -/
def primeCellBox (k : ℕ) : Enclosure :=
  P5OriginalDirectedMidpoint.cellEnclosure
    (mesh1024 primeLeft primeRight k) (mesh1024 primeLeft primeRight (k + 1))
    (primePointBox k) (primeCurvatureBox k)
def correctionCellBox (k : ℕ) : Enclosure :=
  P5OriginalDirectedMidpoint.cellEnclosure
    (mesh1024 correctionLeft correctionRight k) (mesh1024 correctionLeft correctionRight (k + 1))
    (correctionPointBox k) (correctionCurvatureBox k)

private theorem exactCell_eq_cellIntegral {f f' f'' : ℝ → ℝ} {a b : ℚ}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' (Icc (a : ℝ) (b : ℝ)))
    {k : ℕ} (hk : k < 1024) :
    exactCell f f'' a b k =
      ∫ x in (mesh1024 a b k : ℝ)..(mesh1024 a b (k + 1) : ℝ), f x := by
  have hs := mesh1024_cell_subset hab hk
  have ho : (mesh1024 a b k : ℝ) ≤ (mesh1024 a b (k + 1) : ℝ) := by
    exact_mod_cast mesh1024_monotone hab (Nat.le_succ k)
  have h := P5OriginalSignedMidpoint.midpoint_identity ho
    (fun x hx => hf x (hs hx)) (fun x hx => hf' x (hs hx)) (hc.mono hs)
  have hstep : (mesh1024 a b (k + 1) : ℝ) - (mesh1024 a b k : ℝ) =
      ((b - a : ℚ) / 1024 : ℝ) := by
    rw [mesh1024_step]
    push_cast
    ring
  rw [hstep] at h
  simpa only [exactCell, midpoint1024, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] using h.symm

/-- The K analytic midpoint theorem now consumes constructed boxes only. -/
theorem primeCellBox_contains {k : ℕ} (hk : k < 1024) :
    (primeCellBox k).Contains (exactCell primeValue primeSecond primeLeft primeRight k) := by
  have hab : primeLeft ≤ primeRight := by norm_num [primeLeft, primeRight]
  have hs := mesh1024_cell_subset hab hk
  have h := P5OriginalDirectedMidpoint.cellEnclosure_contains_integral
    (mesh1024_monotone hab (Nat.le_succ k)) (primePointBox k) (primeCurvatureBox k)
    (fun x hx => prime_regular_cast.1 x (hs hx))
    (fun x hx => prime_regular_cast.2.1 x (hs hx)) (prime_regular_cast.2.2.mono hs)
    (by simpa [midpoint1024] using primePointBox_contains hk)
    (fun x hx => primeCurvatureBox_contains hk hx)
  rw [← exactCell_eq_cellIntegral hab prime_regular_cast.1 prime_regular_cast.2.1 prime_regular_cast.2.2 hk] at h
  exact h

theorem correctionCellBox_contains {k : ℕ} (hk : k < 1024) :
    (correctionCellBox k).Contains
      (exactCell scalarCorrectionKernel correctionSecond correctionLeft correctionRight k) := by
  have hab : correctionLeft ≤ correctionRight := by norm_num [correctionLeft, correctionRight]
  have hs := mesh1024_cell_subset hab hk
  have h := P5OriginalDirectedMidpoint.cellEnclosure_contains_integral
    (mesh1024_monotone hab (Nat.le_succ k)) (correctionPointBox k) (correctionCurvatureBox k)
    (fun x hx => correction_regular_cast.1 x (hs hx))
    (fun x hx => correction_regular_cast.2.1 x (hs hx)) (correction_regular_cast.2.2.mono hs)
    (by simpa [midpoint1024] using correctionPointBox_contains hk)
    (fun x hx => correctionCurvatureBox_contains hk hx)
  rw [← exactCell_eq_cellIntegral hab correction_regular_cast.1 correction_regular_cast.2.1
    correction_regular_cast.2.2 hk] at h
  exact h

def sumBoxes1024 (B : ℕ → Enclosure) : Enclosure :=
  ⟨∑ k ∈ Finset.range 1024, (B k).lower, ∑ k ∈ Finset.range 1024, (B k).upper⟩

private theorem sumBoxes1024_contains {B : ℕ → Enclosure} {f : ℕ → ℝ}
    (h : ∀ k < 1024, (B k).Contains (f k)) :
    (sumBoxes1024 B).Contains (∑ k ∈ Finset.range 1024, f k) := by
  constructor
  · simp only [sumBoxes1024, Enclosure.Contains, Rat.cast_sum]
    exact Finset.sum_le_sum (fun k hk => (h k (Finset.mem_range.mp hk)).1)
  · simp only [sumBoxes1024, Enclosure.Contains, Rat.cast_sum]
    exact Finset.sum_le_sum (fun k hk => (h k (Finset.mem_range.mp hk)).2)

def archiveK0 : ℚ := 67619 / 10000
/-- K0 multiplies each of the two positive scalar components exactly once.
The primitive U7 has no external multiplicity two or Chen quarter here. -/
def archivedBox : Enclosure :=
  (qmul (qpoint archiveK0) (sumBoxes1024 primeCellBox)).add
    (qmul (qpoint archiveK0) (sumBoxes1024 correctionCellBox))

def savedArchivedUpper : ℚ := 1672464594622060236183097 / (2 : ℚ) ^ 80
def savedScalarUpper : ℚ := savedArchivedUpper / archiveK0

/-- Closed exact total comparison. This term is UNEVALUATED and unverified;
the saved numerator is a comparison target, never an assumed total. -/
theorem closed_saved_upper_comparison : archivedBox.upper ≤ savedArchivedUpper := by
  decide

theorem archivedBox_contains :
    archivedBox.Contains (p5U7OriginalOmegaIntegral (67619 / 10000)) := by
  have hp := sumBoxes1024_contains (B := primeCellBox) primeCellBox_contains
  have hc := sumBoxes1024_contains (B := correctionCellBox) correctionCellBox_contains
  have h := Enclosure.add_contains
    (qmul_contains (qpoint_contains archiveK0) hp)
    (qmul_contains (qpoint_contains archiveK0) hc)
  rw [archivedU7_eq_two_exactSum1024]
  simpa only [archivedBox, archiveK0, exactSum1024, primeLeft, primeRight,
    correctionLeft, correctionRight, Rat.cast_div, Rat.cast_ofNat, mul_add] using h

/-- Original saved upper, with no finite guard or containment hypothesis. -/
theorem original_archived_U7_le_saved :
    p5U7OriginalOmegaIntegral (67619 / 10000) ≤
      (1672464594622060236183097 : ℝ) / 2 ^ 80 := by
  have hQ : (archivedBox.upper : ℝ) ≤ (savedArchivedUpper : ℝ) := by
    exact_mod_cast closed_saved_upper_comparison
  exact archivedBox_contains.2.trans (by simpa [savedArchivedUpper] using hQ)

theorem original_scalar_U7_le_saved :
    p5U7OriginalOmegaIntegral 1 ≤
      ((1672464594622060236183097 : ℝ) / 2 ^ 80) / (67619 / 10000) := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 67619 / 10000)).mpr
  have h := original_archived_U7_le_saved
  rw [originalOmegaIntegral_eq_mul] at h
  simpa only [mul_comm] using h

end ImbalancedChen.P5U7SavedEndpoint






