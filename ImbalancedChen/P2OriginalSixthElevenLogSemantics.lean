import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral
import ImbalancedChen.Certificates.RationalLogCertificate
import Mathlib.Data.Fin.VecNotation

/-!
SOURCE ONLY / UNCOMPILED. No producer, numerical replay, Lean, lake, or CI run.

Literal source: saving #7 `eleven_sixth_cells_final_log` in
`docs/part2/adopted-evidence-catalog.json`. The complete local frozen source is
`../tmp/publication-20261010/verification-renewal-v2/_runs/full-final/`:

* sixth-log-moment-jensen-20261009.py, `physical` and `data_at`;
* sixth-log-moment-jensen-independent-20261009.py, `at_vertex`;
* sixth-license-family-20261009.tex;
* sixth-pair17-winner-20261009.tex;
* sixth-pair12-ascending-cell-20261009.py, `build`;
* sixth-tent33-ascending-20261009.py, `constraints`;
* sixth-log-moment-jensen-20261009.tex.

These are SIX-coordinate physical cells, with seven vertices per simplex and
EIGHT affine denominator factors. Pair12 means old subset mask12={3,4};
pair17 means old subset mask17={1,5}. Neither is a change of rank. Pair12
vertices are already physical; all other source vertices use the stated
invertible chart. The exact eleven IDs below are the complete selected #7
list, not the later #9/#10 mask34 families.

This file proves the physical chart dictionary, branch caps and residuals,
ordinary residual guards at the same sixth node, the factor-four density
normalization, conservative comparison with an inherited cap, and the actual
logarithmic integral identities. It does not assume a target integral/gain.
The 2631-simplex covers, gap-weighted moments, finite log-Jensen remainder,
Q80 factor floors and Q96 endpoint floors are NOT proved here. In particular
the catalog's final rational gain is not declared as a theorem.
-/

namespace ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics

open Set MeasureTheory MathlibNt.SieveTheory
open scoped BigOperators

abbrev Physical := Fin 6 → ℝ

inductive Family where
  | singleton | pair17 | pair12 | tent33
  deriving DecidableEq, Repr

inductive Cell where
  | singleton33_1355 | singleton33_1371 | singleton33_1867 | singleton34_1371
  | singleton50_1353 | singleton50_1355
  | pair17_1355 | pair17_1867 | pair12_fixed | tent33_1371 | tent33_1867
  deriving DecidableEq, Repr

def Cell.family : Cell → Family
  | .singleton33_1355 | .singleton33_1371 | .singleton33_1867 | .singleton34_1371
  | .singleton50_1353 | .singleton50_1355 => .singleton
  | .pair17_1355 | .pair17_1867 => .pair17
  | .pair12_fixed => .pair12
  | .tent33_1371 | .tent33_1867 => .tent33

def Cell.pattern : Cell → ℕ
  | .singleton33_1355 | .singleton50_1355 | .pair17_1355 => 1355
  | .singleton33_1371 | .singleton34_1371 | .tent33_1371 => 1371
  | .singleton33_1867 | .pair17_1867 | .tent33_1867 => 1867
  | .singleton50_1353 => 1353
  | .pair12_fixed => 0

def Cell.selectedMask : Cell → ℕ
  | .singleton34_1371 => 34
  | .singleton50_1353 | .singleton50_1355 => 50
  | _ => 33

def Cell.sourceID : Cell → String
  | .singleton33_1355 => "33-1355"
  | .singleton33_1371 => "33-1371"
  | .singleton33_1867 => "33-1867"
  | .singleton34_1371 => "34-1371"
  | .singleton50_1353 => "50-1353"
  | .singleton50_1355 => "50-1355"
  | .pair17_1355 => "pair17-new33-1355"
  | .pair17_1867 => "pair17-new33-1867"
  | .pair12_fixed => "pair12-fixed"
  | .tent33_1371 => "tent33-ascending-1371"
  | .tent33_1867 => "tent33-ascending-1867"

def allCells : List Cell :=
  [.singleton33_1355, .singleton33_1371, .singleton33_1867, .singleton34_1371,
   .singleton50_1353, .singleton50_1355, .pair17_1355, .pair17_1867,
   .pair12_fixed, .tent33_1371, .tent33_1867]

theorem allCells_complete (c : Cell) : c ∈ allCells := by
  cases c <;> decide

theorem eleven_cells : allCells.length = 11 := by rfl

def bit (m k : ℕ) : Bool := decide (m / 2 ^ k % 2 = 1)

def variableMasks : List ℕ := [6, 10, 12, 14, 18, 20, 22, 24, 26, 28, 30]

/-- Literal frozen pair12 `old31_branches`, indexed by mask minus one. -/
def pair12Branches : List Bool :=
  [false, false, true, false, true, true, true, false, true, true, true,
   false, true, true, true, false, true, false, true, false, true, true, true,
   false, true, true, true, true, true, true, true]

def Cell.descending (c : Cell) (mask : ℕ) : Bool :=
  if c.family = .pair12 then (pair12Branches[mask - 1]?).getD false
  else if mask ∈ [1, 2, 4, 8, 16] then false
  else if bit mask 0 then true
  else bit c.pattern (variableMasks.idxOf mask)

noncomputable section

def eta : ℝ := 1 / 1000000
def mu : ℝ := 25 / 128
def R0 (t : Physical) : ℝ := (1 + t 0) / 2
def S5 (t : Physical) : ℝ := t 0 + t 1 + t 2 + t 3 + t 4
def S6 (t : Physical) : ℝ := S5 t + t 5
def H3 (t : Physical) : ℝ := t 0 + t 1 + 3 * t 2
def H5 (t : Physical) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4
def W (t : Physical) : ℝ := 153 / 256 - 3 * t 2 / 8
def tent (s : ℝ) : ℝ := min ((1 + s) / 2) (57 / 64 - 3 * s / 2)

/-- The source chart q=(x,y,z,a,c,r), with a=R0-S5 and c=R0-H5. -/
def physical (q : Physical) : Physical :=
  ![q 0, q 1, q 2, (1 - q 0) / 2 - q 1 - q 2 - 3 * q 3 / 2 + q 4 / 2,
    (q 3 - q 4) / 2, q 5]

def chart (t : Physical) : Physical :=
  ![t 0, t 1, t 2, R0 t - S5 t, R0 t - H5 t, t 5]

/-- Pair12 source points are already physical; other groups use the chart. -/
def decode (c : Cell) (q : Physical) : Physical :=
  if c.family = .pair12 then q else physical q

theorem physical_chart (t : Physical) : physical (chart t) = t := by
  ext i
  fin_cases i <;> simp [physical, chart, R0, S5, H5] <;> ring

theorem chart_physical (q : Physical) : chart (physical q) = q := by
  ext i
  fin_cases i <;> simp [physical, chart, R0, S5, H5] <;> ring

theorem physical_injective : Function.Injective physical := by
  intro q q' h
  have he := congrArg chart h
  simpa only [chart_physical] using he

theorem decode_pair12 (q : Physical) : decode .pair12_fixed q = q := by
  simp [decode, Cell.family]

theorem S6_eq_sum (t : Physical) : S6 t = ∑ i : Fin 6, t i := by
  simp [S6, S5, Fin.sum_univ_succ]
  <;> ring

def oldCap (c : Cell) (t : Physical) : ℝ :=
  match c.family with
  | .singleton | .tent33 => R0 t
  | .pair17 => 57 / 64 - 3 * (t 0 + t 4) / 2
  | .pair12 => (1 + t 2 + t 3) / 2

def clippedCap (t : Physical) : ℝ := S5 t + 4 * t 5 - eta
def ascending33 (t : Physical) : ℝ := (1 + t 0 + t 5) / 2
def descending33 (t : Physical) : ℝ := 57 / 64 - 3 * (t 0 + t 5) / 2
def ascending34 (t : Physical) : ℝ := (1 + t 1 + t 5) / 2

def newCap (c : Cell) (t : Physical) : ℝ :=
  if c.family = .tent33 then ascending33 t - eta else clippedCap t

def oldResidual (c : Cell) (t : Physical) : ℝ := oldCap c t - S6 t
def newResidual (c : Cell) (t : Physical) : ℝ := newCap c t - S6 t
def gap (c : Cell) (t : Physical) : ℝ := newCap c t - oldCap c t

def subsetSum (mask : ℕ) (t : Physical) : ℝ :=
  ∑ i : Fin 5, if bit mask i.val then t i.castSucc else 0

def selectedSum (mask : ℕ) (t : Physical) : ℝ :=
  ∑ i : Fin 6, if bit mask i.val then t i else 0

def fullSquare (j : Fin 6) (t : Physical) : ℝ :=
  (∑ i : Fin 6, if i < j then t i else 0) + 2 * t j

def remainingSquare (mask : ℕ) (j : Fin 6) (t : Physical) : ℝ :=
  selectedSum mask t +
    (∑ i : Fin 6, if i < j ∧ bit mask i.val = false then t i else 0) + 2 * t j

def branchLicense (descending : Bool) (cap s : ℝ) : Prop :=
  if descending then 57 / 64 - 3 * s / 2 ≤ cap else s ≤ 2 * cap - 1

theorem branchLicense_sound {descending : Bool} {cap s : ℝ}
    (h : branchLicense descending cap s) : tent s ≤ cap := by
  cases descending with
  | false =>
      change s ≤ 2 * cap - 1 at h
      exact (min_le_left _ _).trans (by linarith)
  | true =>
      change 57 / 64 - 3 * s / 2 ≤ cap at h
      exact (min_le_right _ _).trans h

theorem tent_ascending {s : ℝ} (hs : s ≤ mu) : tent s = (1 + s) / 2 := by
  apply min_eq_left
  dsimp [mu] at hs
  linarith

theorem tent_descending {s : ℝ} (hs : mu ≤ s) : tent s = 57 / 64 - 3 * s / 2 := by
  apply min_eq_right
  dsimp [mu] at hs
  linarith

theorem subsetSum_one (t : Physical) : subsetSum 1 t = t 0 := by
  norm_num [subsetSum, bit, Fin.sum_univ_succ]

theorem subsetSum_seventeen (t : Physical) : subsetSum 17 t = t 0 + t 4 := by
  norm_num [subsetSum, bit, Fin.sum_univ_succ]

theorem subsetSum_twelve (t : Physical) : subsetSum 12 t = t 2 + t 3 := by
  norm_num [subsetSum, bit, Fin.sum_univ_succ]

def priority (c : Cell) (t : Physical) : Prop :=
  match c with
  | .singleton34_1371 => descending33 t < newCap c t
  | .singleton50_1353 | .singleton50_1355 =>
      descending33 t < newCap c t ∧ ascending34 t < newCap c t
  | .tent33_1371 | .tent33_1867 => ascending33 t < clippedCap t
  | _ => True

def winnerPlane (c : Cell) (t : Physical) : Prop :=
  match c.family with
  | .pair17 => mu < t 0 + t 4
  | .pair12 => t 2 + t 3 < mu
  | _ => True

/-- Literal physical licensing predicates used by the selected #7 cells.
Old branch and winning-subset identities are kept nonstrict. The displayed
history, residual, gap, square, tent, and priority guards are strict as in
the source's compact physical interior. No integral estimate is a field. -/
structure PhysicalCell (c : Cell) (t : Physical) : Prop where
  rpos : 0 < t 5
  order : t 5 < t 4 ∧ t 4 < t 3 ∧ t 3 < t 2 ∧ t 2 < t 1 ∧ t 1 < t 0
  largest : t 0 < mu
  oldCutoff : t 5 < 1 / 50
  compactCutoff : 53 / 4608 < t 5
  history3 : H3 t < R0 t
  history5 : H5 t < R0 t
  oldW : W t ≤ R0 t
  oldBranches : ∀ mask ∈ Finset.Icc 1 31,
    branchLicense (c.descending mask) (oldCap c t) (subsetSum mask t)
  first3Branches : ∀ mask ∈ Finset.Icc 1 7,
    branchLicense (c.descending mask) (R0 t) (subsetSum mask t)
  comparison : R0 t ≤ oldCap c t
  pairAbove : c.family = .pair17 ∨ c.family = .pair12 → R0 t < oldCap c t
  winner : winnerPlane c t
  positiveGap : oldCap c t < newCap c t
  selectedAscending : newCap c t < (1 + selectedSum c.selectedMask t) / 2
  selectedDescending : newCap c t < 57 / 64 - 3 * selectedSum c.selectedMask t / 2
  fullSquares : ∀ j : Fin 6, fullSquare j t < newCap c t
  remainingSquares : ∀ j : Fin 6, bit c.selectedMask j.val = false →
    remainingSquare c.selectedMask j t < newCap c t
  oldArgument : t 5 < R0 t - S6 t
  newArgument : newResidual c t < 3 * t 5
  priority : priority c t

/-- Every old subset is bounded and one literal old subset attains the
comparison cap. Together with W dominance this identifies the actual raw
envelope, rather than assuming that the inherited buffered cap equals it. -/
theorem PhysicalCell.raw_envelope {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    W t ≤ oldCap c t ∧
      (∀ mask ∈ Finset.Icc 1 31, tent (subsetSum mask t) ≤ oldCap c t) ∧
        ∃ mask ∈ Finset.Icc 1 31, tent (subsetSum mask t) = oldCap c t := by
  refine ⟨hc.oldW.trans hc.comparison, ?_, ?_⟩
  · intro mask hm
    exact branchLicense_sound (hc.oldBranches mask hm)
  · cases hf : c.family with
    | singleton =>
        refine ⟨1, by decide, ?_⟩
        rw [subsetSum_one, tent_ascending hc.largest.le]
        simp only [oldCap, hf, R0]
    | tent33 =>
        refine ⟨1, by decide, ?_⟩
        rw [subsetSum_one, tent_ascending hc.largest.le]
        simp only [oldCap, hf, R0]
    | pair17 =>
        have hw : mu < t 0 + t 4 := by simpa only [winnerPlane, hf] using hc.winner
        refine ⟨17, by decide, ?_⟩
        rw [subsetSum_seventeen, tent_descending hw.le]
        simp only [oldCap, hf]
    | pair12 =>
        have hw : t 2 + t 3 < mu := by simpa only [winnerPlane, hf] using hc.winner
        refine ⟨12, by decide, ?_⟩
        rw [subsetSum_twelve, tent_ascending hw.le]
        simp only [oldCap, hf]

/-- Historical first-three licenses stay at R0, including in the pair
families where the raw old fifth comparison is strictly larger. -/
theorem PhysicalCell.third_envelope {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    W t ≤ R0 t ∧
      (∀ mask ∈ Finset.Icc 1 7, tent (subsetSum mask t) ≤ R0 t) ∧
        tent (subsetSum 1 t) = R0 t := by
  refine ⟨hc.oldW, ?_, ?_⟩
  · intro mask hm
    exact branchLicense_sound (hc.first3Branches mask hm)
  · rw [subsetSum_one, tent_ascending hc.largest.le]
    rfl

theorem PhysicalCell.coordinates_pos {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    ∀ i : Fin 6, 0 < t i := by
  intro i
  fin_cases i <;> linarith [hc.rpos, hc.order.1, hc.order.2.1,
    hc.order.2.2.1, hc.order.2.2.2.1, hc.order.2.2.2.2]

/-- These residuals share the sixth-node cutoff r=t6 and the same S6. -/
theorem PhysicalCell.residual_guards {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    0 < t 5 ∧ t 5 < oldResidual c t ∧
      oldResidual c t < newResidual c t ∧ newResidual c t < 3 * t 5 := by
  refine ⟨hc.rpos, ?_, ?_, hc.newArgument⟩
  · dsimp only [oldResidual]
    linarith only [hc.oldArgument, hc.comparison]
  · exact sub_lt_sub_right hc.positiveGap (S6 t)

theorem PhysicalCell.argument_guards {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    1 < oldResidual c t / t 5 ∧
      oldResidual c t / t 5 < newResidual c t / t 5 ∧
        newResidual c t / t 5 < 3 := by
  have h := hc.residual_guards
  exact ⟨(one_lt_div h.1).mpr h.2.1,
    (div_lt_div_iff_of_pos_right h.1).mpr h.2.2.1,
    (div_lt_iff₀ h.1).mpr h.2.2.2⟩

theorem chart_initial_residual (q : Physical) :
    R0 (physical q) - S6 (physical q) = q 3 - q 5 := by
  simp [physical, R0, S6, S5]
  ring

theorem clipped_new_residual (t : Physical) : clippedCap t - S6 t = 3 * t 5 - eta := by
  dsimp [clippedCap, S6]
  ring

theorem nonTent_new_residual (c : Cell) (t : Physical) (hc : c.family ≠ .tent33) :
    newResidual c t = 3 * t 5 - eta := by
  rw [newResidual, newCap, if_neg hc]
  exact clipped_new_residual t

theorem singleton_chart_gap (q : Physical) :
    gap .singleton33_1355 (physical q) = 4 * q 5 - q 3 - eta := by
  simp [gap, newCap, oldCap, Cell.family, clippedCap, physical, R0, S5]
  ring

theorem pair17_chart_residual (q : Physical) :
    oldResidual .pair17_1355 (physical q) =
      q 3 - q 5 + oldCap .pair17_1355 (physical q) - R0 (physical q) := by
  have h := chart_initial_residual q
  dsimp only [oldResidual]
  linarith only [h]

theorem tent33_chart_data (q : Physical) :
    gap .tent33_1371 (physical q) = q 5 / 2 - eta ∧
      newResidual .tent33_1371 (physical q) = q 3 - q 5 / 2 - eta := by
  simp [gap, newResidual, newCap, oldCap, Cell.family, ascending33,
    physical, R0, S6, S5]
  constructor <;> ring

/-- The factor order is exactly producer `data_at` / reviewer `at_vertex`. -/
def factors (c : Cell) (t : Physical) : Fin 8 → ℝ :=
  ![oldResidual c t, newResidual c t, t 0, t 1, t 2, t 3, t 4, t 5]

def coordinateProduct (t : Physical) : ℝ := ∏ i : Fin 6, t i
def factorProduct (c : Cell) (t : Physical) : ℝ := ∏ j : Fin 8, factors c t j
def savingKernel (c : Cell) (t : Physical) : ℝ := 4 * gap c t / factorProduct c t

theorem factorProduct_eq (c : Cell) (t : Physical) :
    factorProduct c t = oldResidual c t * newResidual c t * coordinateProduct t := by
  simp [factorProduct, coordinateProduct, factors, Fin.prod_univ_succ]
  <;> ring

theorem PhysicalCell.factors_pos {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    ∀ j : Fin 8, 0 < factors c t j := by
  have hr := hc.residual_guards
  have hp := hc.coordinates_pos
  intro j
  fin_cases j <;> simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    first | exact hp _ | linarith only [hr.1, hr.2.1, hr.2.2.1]

theorem PhysicalCell.coordinateProduct_pos {c : Cell} {t : Physical}
    (hc : PhysicalCell c t) : 0 < coordinateProduct t := by
  exact Finset.prod_pos (fun i _ => hc.coordinates_pos i)

theorem PhysicalCell.savingKernel_pos {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    0 < savingKernel c t := by
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hc.positiveGap))
    (Finset.prod_pos (fun j _ => hc.factors_pos j))

/-- Exact same-sixth-node profile from the existing actual Rosser limit
supplier. The original factor four occurs once, before prefix mass. -/
theorem savingKernel_eq_actual_profile (c : Cell) (t : Physical) :
    savingKernel c t =
      primeBoxInitialSavingProfile (oldCap c t) (newCap c t) t / coordinateProduct t := by
  rw [savingKernel, factorProduct_eq]
  simp only [primeBoxInitialSavingProfile, ← S6_eq_sum, gap, oldResidual, newResidual,
    div_div]

def normalizedOrdinary (cap : ℝ) (t : Physical) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / t 5) *
    suzukiContinuousUpperFactor ((cap - S6 t) / t 5)

theorem normalizedOrdinary_initial {cap : ℝ} {t : Physical}
    (hr : 0 < t 5) (hl : t 5 < cap - S6 t) (hu : cap - S6 t ≤ 3 * t 5) :
    normalizedOrdinary cap t = 4 / (cap - S6 t) := by
  exact normalized_suzukiUpperFactor_initial (cap - S6 t) (t 5) hr hl hu

theorem PhysicalCell.same_node_normalization {c : Cell} {t : Physical}
    (hc : PhysicalCell c t) :
    (normalizedOrdinary (oldCap c t) t - normalizedOrdinary (newCap c t) t) /
      coordinateProduct t = savingKernel c t := by
  have h := hc.residual_guards
  rw [normalizedOrdinary_initial h.1 h.2.1 (by
      dsimp only [oldResidual, newResidual] at h
      linarith only [h.2.2.1, h.2.2.2]),
    normalizedOrdinary_initial h.1 (by
      dsimp only [oldResidual, newResidual] at h
      linarith only [h.2.1, h.2.2.1]) h.2.2.2.le]
  rw [savingKernel, factorProduct_eq]
  have ho : oldResidual c t ≠ 0 := ne_of_gt (h.1.trans h.2.1)
  have hn : newResidual c t ≠ 0 := ne_of_gt ((h.1.trans h.2.1).trans h.2.2.1)
  have hp := hc.coordinateProduct_pos.ne'
  dsimp only [oldResidual, newResidual] at ho hn ⊢
  dsimp only [gap]
  field_simp [ho, hn, hp] <;> ring

/-- The actual inherited cap need only be at most R. It is never assumed
equal to the raw winning envelope. This comparison concerns the continuous
ordinary profile supplied by limits of the same actual residual density. -/
theorem PhysicalCell.inherited_cap_saving {c : Cell} {t : Physical}
    (hc : PhysicalCell c t) {lambda : ℝ}
    (hlambda : lambda ≤ oldCap c t) (hguard : t 5 < lambda - S6 t) :
    savingKernel c t ≤
      (normalizedOrdinary lambda t - normalizedOrdinary (newCap c t) t) /
        coordinateProduct t := by
  have hr := hc.residual_guards
  have hsmall : 0 < lambda - S6 t := hr.1.trans hguard
  have hcomp : lambda - S6 t ≤ oldCap c t - S6 t := sub_le_sub_right hlambda _
  have hu : lambda - S6 t ≤ 3 * t 5 := by
    dsimp only [oldResidual, newResidual] at hr
    linarith only [hcomp, hr.2.2.1, hr.2.2.2]
  have hR : oldCap c t - S6 t ≤ 3 * t 5 := by
    dsimp only [oldResidual, newResidual] at hr
    linarith only [hr.2.2.1, hr.2.2.2]
  have hrecip := one_div_le_one_div_of_le hsmall hcomp
  have hfour : 4 / (oldCap c t - S6 t) ≤ 4 / (lambda - S6 t) := by
    convert mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  rw [← hc.same_node_normalization]
  rw [normalizedOrdinary_initial hr.1 hr.2.1 hR,
    normalizedOrdinary_initial hr.1 hguard hu]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hfour _) hc.coordinateProduct_pos.le

/-- The exact actual logarithmic integrand used before log-Jensen.
There are eight factors; correlations among them are unrestricted. -/
def factorLog (c : Cell) (t : Physical) : ℝ :=
  -(∑ j : Fin 8, Real.log (factors c t j))

theorem factorLog_eq_of_pos (c : Cell) (t : Physical)
    (hp : ∀ j : Fin 8, 0 < factors c t j) :
    factorLog c t = Real.log (1 / factorProduct c t) := by
  have hn : ∀ j ∈ (Finset.univ : Finset (Fin 8)), factors c t j ≠ 0 :=
    fun j _ => (hp j).ne'
  rw [one_div, Real.log_inv, factorProduct, Real.log_prod hn]
  rfl

theorem PhysicalCell.factorLog_eq {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    factorLog c t = Real.log (1 / factorProduct c t) := by
  exact factorLog_eq_of_pos c t hc.factors_pos

theorem exp_factorLog_of_pos (c : Cell) (t : Physical)
    (hp : ∀ j : Fin 8, 0 < factors c t j) :
    Real.exp (factorLog c t) = 1 / factorProduct c t := by
  rw [factorLog_eq_of_pos c t hp]
  exact Real.exp_log (one_div_pos.mpr (Finset.prod_pos (fun j _ => hp j)))

theorem PhysicalCell.exp_factorLog {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    Real.exp (factorLog c t) = 1 / factorProduct c t := by
  exact exp_factorLog_of_pos c t hc.factors_pos

theorem PhysicalCell.logarithmic_kernel {c : Cell} {t : Physical} (hc : PhysicalCell c t) :
    savingKernel c t = 4 * gap c t * Real.exp (factorLog c t) := by
  rw [hc.exp_factorLog, savingKernel]
  ring

/-- A finite rational logarithm certificate can license an actual source
factor-log value at a rationally described point. The argument equality is
algebraic; neither stored endpoint is assumed to bound a real logarithm. -/
theorem factorLog_rational_certificate (c : Cell) (t : Physical)
    (hp : ∀ j : Fin 8, 0 < factors c t j)
    (certificate : RationalLogCertificate) (hcheck : certificate.check = true)
    (hargument : (certificate.argument : ℝ) = 1 / factorProduct c t) :
    (certificate.lower : ℝ) ≤ factorLog c t ∧
      factorLog c t ≤ (certificate.upper : ℝ) := by
  have h := certificate.check_sound hcheck
  rw [hargument, ← factorLog_eq_of_pos c t hp] at h
  exact h

/-- All integrals are in the physical SIX coordinates. The source
`physical_volume` is already a physical volume, so no order factorial or
second chart Jacobian occurs in this expression. -/
def sourceIntegral (c : Cell) (T : Set Physical) : ℝ :=
  ∫ t in T, savingKernel c t

def logarithmicIntegral (c : Cell) (T : Set Physical) : ℝ :=
  ∫ t in T, 4 * gap c t * Real.exp (factorLog c t)

def weightedLogIntegral (c : Cell) (T : Set Physical) : ℝ :=
  ∫ t in T, gap c t * Real.log (1 / factorProduct c t)

def weightedFactorLogIntegral (c : Cell) (T : Set Physical) : ℝ :=
  ∫ t in T, gap c t * factorLog c t

def gapMass (c : Cell) (T : Set Physical) : ℝ := ∫ t in T, gap c t

/-- The actual source gap-weighted expectation, before any Jensen bound. -/
def gapAverage (c : Cell) (T : Set Physical) (f : Physical → ℝ) : ℝ :=
  (∫ t in T, gap c t * f t) / gapMass c T

/-- This form also covers source simplex boundary vertices at which the
affine gap vanishes. Positivity is needed for the eight factors, not for
every vertex gap; no positive-mass assumption is hidden here. -/
theorem sourceIntegral_eq_logarithmic_of_pos (c : Cell) (T : Set Physical)
    (hT : MeasurableSet T) (hp : ∀ t ∈ T, ∀ j : Fin 8, 0 < factors c t j) :
    sourceIntegral c T = logarithmicIntegral c T := by
  apply setIntegral_congr_fun hT
  intro t ht
  rw [exp_factorLog_of_pos c t (hp t ht), savingKernel]
  ring

theorem weightedLogIntegral_eq_of_pos (c : Cell) (T : Set Physical)
    (hT : MeasurableSet T) (hp : ∀ t ∈ T, ∀ j : Fin 8, 0 < factors c t j) :
    weightedLogIntegral c T = weightedFactorLogIntegral c T := by
  apply setIntegral_congr_fun hT
  intro t ht
  rw [factorLog_eq_of_pos c t (hp t ht)]

/-- Literal source expression `4 I_g E_g exp(log(1/product ell))`.
This is an equality of actual physical integrals, not a numerical Jensen
endpoint. In the source G>0 simplex case, I_g is supplied by its moment law. -/
theorem sourceIntegral_eq_gapAverage (c : Cell) (T : Set Physical)
    (hT : MeasurableSet T) (hp : ∀ t ∈ T, ∀ j : Fin 8, 0 < factors c t j)
    (hmass : gapMass c T ≠ 0) :
    sourceIntegral c T =
      4 * gapMass c T * gapAverage c T (fun t => Real.exp (factorLog c t)) := by
  rw [sourceIntegral_eq_logarithmic_of_pos c T hT hp]
  have he : logarithmicIntegral c T =
      4 * (∫ t in T, gap c t * Real.exp (factorLog c t)) := by
    simp only [logarithmicIntegral, mul_assoc, integral_const_mul]
  rw [he, gapAverage]
  field_simp [hmass] <;> ring

/-- This identifies the actual source integral, without assuming any
claimed rational endpoint or final gain. T may be a source physical simplex. -/
theorem sourceIntegral_eq_logarithmic (c : Cell) (T : Set Physical)
    (hT : MeasurableSet T) (hcell : ∀ t ∈ T, PhysicalCell c t) :
    sourceIntegral c T = logarithmicIntegral c T := by
  apply setIntegral_congr_fun hT
  intro t ht
  exact (hcell t ht).logarithmic_kernel

theorem weightedLogIntegral_eq (c : Cell) (T : Set Physical)
    (hT : MeasurableSet T) (hcell : ∀ t ∈ T, PhysicalCell c t) :
    weightedLogIntegral c T = weightedFactorLogIntegral c T := by
  apply setIntegral_congr_fun hT
  intro t ht
  rw [(hcell t ht).factorLog_eq]

/-- The true integral can equivalently be written with the normalized
ordinary residual comparison at the same sixth node, then physical prefix
mass. The factor four has not been multiplied by a Chen quarter. -/
theorem sourceIntegral_eq_same_node (c : Cell) (T : Set Physical)
    (hT : MeasurableSet T) (hcell : ∀ t ∈ T, PhysicalCell c t) :
    sourceIntegral c T = ∫ t in T,
      (normalizedOrdinary (oldCap c t) t - normalizedOrdinary (newCap c t) t) /
        coordinateProduct t := by
  apply setIntegral_congr_fun hT
  intro t ht
  exact (hcell t ht).same_node_normalization.symm

end

end ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics
