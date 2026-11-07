import ImbalancedChen.P2OriginalSixthSourceLossConvergence
import ImbalancedChen.ActualPrimePolyhedralTestFunctions

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

Rational affine rows for every strict face of the ORIGINAL eleven source
cells.  The two-plane priority min is expanded into its two actual rows.
Constant faces (in particular the literal eta face) are retained and
proved nonzero; no null-wall hypothesis is imported from a caller.
-/

namespace ImbalancedChen.P2OriginalSixthProperAffineWalls

noncomputable section
open Classical Set Filter MeasureTheory
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthSourceCompactCores

structure Row where
  constant : ℚ
  coefficient : Fin 6 → ℚ

def Row.eval (r : Row) (t : Physical) : ℝ :=
  r.constant + ∑ i, (r.coefficient i : ℝ) * t i
def Row.const (q : ℚ) : Row := ⟨q, fun _ => 0⟩
def Row.coord (i : Fin 6) : Row := ⟨0, fun j => if j = i then 1 else 0⟩
def Row.add (r s : Row) : Row := ⟨r.constant + s.constant, fun i => r.coefficient i + s.coefficient i⟩
def Row.sub (r s : Row) : Row := ⟨r.constant - s.constant, fun i => r.coefficient i - s.coefficient i⟩
def Row.scale (q : ℚ) (r : Row) : Row := ⟨q*r.constant, fun i => q*r.coefficient i⟩
def Row.sumRow (P : Fin 6 → Prop) [DecidablePred P] : Row :=
  ⟨0, fun i => if P i then 1 else 0⟩

@[simp] theorem Row.eval_const (q : ℚ) (t : Physical) : (Row.const q).eval t = (q : ℝ) := by
  simp [Row.eval, Row.const]
@[simp] theorem Row.eval_coord (i : Fin 6) (t : Physical) : (Row.coord i).eval t = t i := by
  simp [Row.eval, Row.coord]
@[simp] theorem Row.eval_add (r s : Row) (t : Physical) :
    (r.add s).eval t = r.eval t + s.eval t := by
  simp only [Row.eval, Row.add, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  ring
@[simp] theorem Row.eval_sub (r s : Row) (t : Physical) :
    (r.sub s).eval t = r.eval t - s.eval t := by
  simp only [Row.eval, Row.sub, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring
@[simp] theorem Row.eval_scale (q : ℚ) (r : Row) (t : Physical) :
    (r.scale q).eval t = (q : ℝ)*r.eval t := by
  simp only [Row.eval, Row.scale, Rat.cast_mul, mul_assoc, ← Finset.mul_sum]
  ring
@[simp] theorem Row.eval_sumRow (P : Fin 6 → Prop) [DecidablePred P] (t : Physical) :
    (Row.sumRow P).eval t = ∑ i ∈ Finset.univ.filter P, t i := by
  simp only [Row.eval, Row.sumRow, Rat.cast_zero, zero_add, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P i <;> simp [h]

def r0Row : Row := (Row.const (1/2)).add ((Row.coord 0).scale (1/2))
def s6Row : Row := Row.sumRow (fun _ => True)
def h3Row : Row := ((Row.coord 0).add (Row.coord 1)).add ((Row.coord 2).scale 3)
def h5Row : Row := (((Row.coord 0).add (Row.coord 1)).add (Row.coord 2)).add
  ((Row.coord 3).add ((Row.coord 4).scale 3))
def clippedRow : Row := (Row.sumRow (fun i => i.val < 5)).add
  (((Row.coord 5).scale 4).add (Row.const (-1/1000000)))
def oldRow (c : Cell) : Row :=
  match c.family with
  | .pair17 => (Row.const (57/64)).sub (((Row.coord 0).add (Row.coord 4)).scale (3/2))
  | .pair12 => (Row.const (1/2)).add (((Row.coord 2).add (Row.coord 3)).scale (1/2))
  | _ => r0Row
def newRow (c : Cell) : Row :=
  if c.family = .tent33 then
    (Row.const (1/2-1/1000000)).add (((Row.coord 0).add (Row.coord 5)).scale (1/2))
  else clippedRow
def maskRow (mask : ℕ) : Row := Row.sumRow (fun i => bit mask i.val = true)
def fullRow (i : Fin 6) : Row :=
  (Row.sumRow (fun j => j < i)).add ((Row.coord i).scale 2)
def remainingRow (mask : ℕ) (i : Fin 6) : Row :=
  (maskRow mask).add ((Row.sumRow (fun j => j < i ∧ bit mask j.val = false)).add
    ((Row.coord i).scale 2))
def aboveRow (c : Cell) : Row :=
  if c.family = .pair17 ∨ c.family = .pair12 then (oldRow c).sub r0Row else Row.const 1
def winnerRow (c : Cell) : Row :=
  match c.family with
  | .pair17 => ((Row.coord 0).add (Row.coord 4)).sub (Row.const (25/128))
  | .pair12 => (Row.const (25/128)).sub ((Row.coord 2).add (Row.coord 3))
  | _ => Row.const 1

@[simp] theorem eval_r0Row (t : Physical) : r0Row.eval t = R0 t := by simp [r0Row, R0] <;> ring
@[simp] theorem eval_s6Row (t : Physical) : s6Row.eval t = S6 t := by
  simp [s6Row, S6_eq_sum]
@[simp] theorem eval_h3Row (t : Physical) : h3Row.eval t = H3 t := by simp [h3Row, H3]
@[simp] theorem eval_h5Row (t : Physical) : h5Row.eval t = H5 t := by simp [h5Row, H5] <;> ring
@[simp] theorem eval_clippedRow (t : Physical) : clippedRow.eval t = clippedCap t := by
  norm_num [clippedRow, clippedCap, S5, eta, Finset.sum_filter, Fin.sum_univ_succ] <;> ring
@[simp] theorem eval_oldRow (c : Cell) (t : Physical) : (oldRow c).eval t = oldCap c t := by
  cases c <;> simp [oldRow, oldCap, Cell.family] <;> ring
@[simp] theorem eval_newRow (c : Cell) (t : Physical) : (newRow c).eval t = newCap c t := by
  cases c <;> simp [newRow, newCap, Cell.family, ascending33, eta] <;> ring
@[simp] theorem eval_maskRow (mask : ℕ) (t : Physical) :
    (maskRow mask).eval t = selectedSum mask t := by
  simp only [maskRow, Row.eval_sumRow, Finset.sum_filter, selectedSum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : bit mask i.val <;> simp [h]
@[simp] theorem eval_fullRow (i : Fin 6) (t : Physical) : (fullRow i).eval t = fullSquare i t := by
  simp [fullRow, fullSquare]
@[simp] theorem eval_remainingRow (mask : ℕ) (i : Fin 6) (t : Physical) :
    (remainingRow mask i).eval t = remainingSquare mask i t := by
  simp [remainingRow, remainingSquare, add_assoc]
@[simp] theorem eval_aboveRow (c : Cell) (t : Physical) :
    (aboveRow c).eval t = pairAboveSlack c t := by
  unfold aboveRow pairAboveSlack
  split_ifs <;> simp
@[simp] theorem eval_winnerRow (c : Cell) (t : Physical) :
    (winnerRow c).eval t = winnerSlack c t := by
  cases c <;> simp [winnerRow, winnerSlack, Cell.family, mu]

def baseRow (c : Cell) : Fin 18 → Row :=
  ![Row.coord 5, (Row.coord 4).sub (Row.coord 5), (Row.coord 3).sub (Row.coord 4),
    (Row.coord 2).sub (Row.coord 3), (Row.coord 1).sub (Row.coord 2),
    (Row.coord 0).sub (Row.coord 1), (Row.const (25/128)).sub (Row.coord 0),
    (Row.const (1/50)).sub (Row.coord 5), (Row.coord 5).sub (Row.const (53/4608)),
    r0Row.sub h3Row, r0Row.sub h5Row, aboveRow c, winnerRow c,
    (newRow c).sub (oldRow c),
    ((Row.const (1/2)).add ((maskRow c.selectedMask).scale (1/2))).sub (newRow c),
    ((Row.const (57/64)).sub ((maskRow c.selectedMask).scale (3/2))).sub (newRow c),
    (r0Row.sub s6Row).sub (Row.coord 5),
    ((Row.coord 5).scale 3).sub ((newRow c).sub s6Row)]

def priorityRow (c : Cell) (j : Fin 2) : Row :=
  match c with
  | .singleton34_1371 => (newRow c).sub
      ((Row.const (57/64)).sub (((Row.coord 0).add (Row.coord 5)).scale (3/2)))
  | .singleton50_1353 | .singleton50_1355 =>
      if j = 0 then (newRow c).sub
        ((Row.const (57/64)).sub (((Row.coord 0).add (Row.coord 5)).scale (3/2)))
      else (newRow c).sub
        ((Row.const (1/2)).add (((Row.coord 1).add (Row.coord 5)).scale (1/2)))
  | .tent33_1371 | .tent33_1867 => clippedRow.sub
      ((Row.const (1/2)).add (((Row.coord 0).add (Row.coord 5)).scale (1/2)))
  | _ => Row.const 1

abbrev RowIndex := Fin 18 ⊕ (Fin 6 ⊕ (Fin 6 ⊕ Fin 2))

def sourceRow (c : Cell) : RowIndex → Row
  | .inl i => baseRow c i
  | .inr (.inl i) => (newRow c).sub (fullRow i)
  | .inr (.inr (.inl i)) =>
      if bit c.selectedMask i.val = false then (newRow c).sub (remainingRow c.selectedMask i)
      else Row.const 1
  | .inr (.inr (.inr i)) => priorityRow c i

theorem eval_baseRow (c : Cell) (i : Fin 18) (t : Physical) :
    (baseRow c i).eval t = baseFace c i.castSucc t := by
  fin_cases i <;> simp [baseRow, baseFace, mu, newResidual] <;> ring

theorem eval_priority_min (c : Cell) (t : Physical) :
    min ((priorityRow c 0).eval t) ((priorityRow c 1).eval t) = prioritySlack c t := by
  cases c <;> simp [priorityRow, prioritySlack, descending33, ascending33, ascending34] <;> ring

/-- The exact finite source row table has no identically zero face.
Its alternatives distinguish proper affine walls from nonzero constant
faces; the decision is a small rational table, not a numerical checker. -/
theorem sourceRow_nontrivial (c : Cell) (i : RowIndex) :
    (∃ k : Fin 6, (sourceRow c i).coefficient k ≠ 0) ∨
      ((∀ k : Fin 6, (sourceRow c i).coefficient k = 0) ∧
        (sourceRow c i).constant ≠ 0) := by
  cases c <;> rcases i with i | (i | (i | i)) <;> fin_cases i <;> decide

def Row.linearPart (r : Row) : Physical →L[ℝ] ℝ :=
  ∑ i : Fin 6, (r.coefficient i : ℝ) • ContinuousLinearMap.proj i

theorem Row.eval_eq_affine (r : Row) (t : Physical) :
    r.eval t = (r.constant : ℝ) + r.linearPart t := by
  simp [Row.eval, Row.linearPart]

theorem Row.linearPart_single (r : Row) (k : Fin 6) :
    r.linearPart (Pi.single k 1) = (r.coefficient k : ℝ) := by
  simp [Row.linearPart, Pi.single_apply]

theorem sourceRow_zero_volume (c : Cell) (i : RowIndex) :
    volume {t : Physical | (sourceRow c i).eval t = 0} = 0 := by
  rcases sourceRow_nontrivial c i with ⟨k, hk⟩ | ⟨hcoeff, hconst⟩
  · have hL : (sourceRow c i).linearPart ≠ 0 := by
      intro hzero
      have h := congrArg (fun L : Physical →L[ℝ] ℝ => L (Pi.single k 1)) hzero
      rw [Row.linearPart_single] at h
      exact hk (by exact_mod_cast h)
    have heq : {t : Physical | (sourceRow c i).eval t = 0} =
        {t | (sourceRow c i).linearPart t = -((sourceRow c i).constant : ℝ)} := by
      ext t
      rw [Row.eval_eq_affine]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact affinePrimeWall_volume_zero _ hL _
  · have heq : {t : Physical | (sourceRow c i).eval t = 0} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      simp only [Row.eval, hcoeff, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
      exact_mod_cast hconst
    rw [heq, measure_empty]

theorem ae_sourceRows_nonzero (c : Cell) :
    ∀ᵐ t : Physical ∂volume, ∀ i : RowIndex, (sourceRow c i).eval t ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  rw [ae_iff]
  simpa only [not_not] using sourceRow_zero_volume c i

private theorem fold_min_lt (fs : List (Physical → ℝ)) (t : Physical) (d : ℝ) :
    fs.foldr (fun f z => min (f t) z) 1 < d ↔
      1 < d ∨ ∃ f ∈ fs, f t < d := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [min_lt_iff, ih, or_assoc, or_left_comm]

private theorem fold_min_positive (fs : List (Physical → ℝ)) (t : Physical) :
    0 < fs.foldr (fun f z => min (f t) z) 1 ↔ ∀ f ∈ fs, 0 < f t := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp [lt_min_iff, ih]

/-- An omitted original source point is near an ACTUAL proper source
row, including the two priority alternatives.  No wall-coverage premise
is left to an arithmetic caller. -/
theorem omitted_has_positive_row (c : Cell) (n : ℕ) (t : Physical)
    (ht : t ∈ omittedSource c n) :
    ∃ i : RowIndex, 0 < (sourceRow c i).eval t ∧
      (sourceRow c i).eval t < 1 / (n + 1 : ℝ) := by
  have hphys : PhysicalCell c t := ht.1
  have hw := (physicalCell_iff c t).mp hphys
  have hmargin : strictMargin c t < 1 / (n + 1 : ℝ) := by
    by_contra h
    exact ht.2 ⟨⟨physicalCell_mem_ambientCube c t hphys, hw.1⟩, le_of_not_gt h⟩
  have hcut : 1 / (n + 1 : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    positivity
  obtain h | ⟨f, hf, hsmall⟩ := (fold_min_lt (sourceFaces c) t _).mp hmargin
  · exact False.elim ((not_lt_of_ge hcut) h)
  have hpositive : ∀ f ∈ sourceFaces c, 0 < f t := by
    exact (fold_min_positive (sourceFaces c) t).mp hw.2
  rcases List.mem_append.mp hf with hb | hrest
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    by_cases hj : j.val < 18
    · let k : Fin 18 := ⟨j.val, hj⟩
      have hk : k.castSucc = j := Fin.ext rfl
      refine ⟨.inl k, ?_, ?_⟩
      · simpa only [sourceRow, eval_baseRow, hk] using
          (show 0 < baseFace c j t from hpositive _ (List.mem_append_left _ hb))
      · simpa only [sourceRow, eval_baseRow, hk] using hsmall
    · have hjlast : j = 18 := Fin.ext (by omega)
      subst j
      have hp : 0 < prioritySlack c t := by
        simpa only [baseFace, Matrix.cons_val_succ, Matrix.cons_val_zero] using hpositive _
          (List.mem_append_left _ hb)
      have hs : prioritySlack c t < 1 / (n + 1 : ℝ) := by
        simpa only [baseFace, Matrix.cons_val_succ, Matrix.cons_val_zero] using hsmall
      rw [← eval_priority_min] at hp hs
      rcases min_lt_iff.mp hs with h0 | h1
      · exact ⟨.inr (.inr (.inr 0)), (lt_min_iff.mp hp).1, h0⟩
      · exact ⟨.inr (.inr (.inr 1)), (lt_min_iff.mp hp).2, h1⟩
  · rcases List.mem_append.mp hrest with hfull | hcomp
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hfull
      refine ⟨.inr (.inl i), ?_, ?_⟩
      · simpa [sourceRow, fullFace] using hpositive _ (List.mem_append_right _
          (List.mem_append_left _ hfull))
      · simpa [sourceRow, fullFace] using hsmall
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hcomp
      refine ⟨.inr (.inr (.inl i)), ?_, ?_⟩
      · simpa [sourceRow, complementFace] using hpositive _ (List.mem_append_right _
          (List.mem_append_right _ hcomp))
      · simpa [sourceRow, complementFace] using hsmall

end
end ImbalancedChen.P2OriginalSixthProperAffineWalls
