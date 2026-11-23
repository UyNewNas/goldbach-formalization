import ImbalancedChen.P1OriginalCoarseContinuationCells
import ImbalancedChen.ActualSelectedPrefixCapSelector
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases

/-!
# Literal stronger-fourth producer geometry and legal continuation interface

SOURCE ONLY. No producer, Lean, lake, numerical replay or runtime was run.

Read-only frozen sources:
* certify_fourth_prefix_stronger.py, SHA256
  25069573985d30beae59a1a2a89ddeb79e56f696e78a5fae5153de0bb8bd378a;
* fourth-prefix-stronger-refinement.tex, SHA256
  cf87c684a5847d289dd748d74705c6e3977bb20b5ed8c1d0d0cadf04ee3565bf.

This is saving #1, replacing the entire old partial-four plus tail gain.
It acts after the actual rank-four frontier and preserves ranks 1 and 3.
The producer endpoint M=v(sum I) is VARIABLE on each numerical rectangle.
Those rectangles need not have inf M > sup L. A checked constant cap on
a sufficiently refined label is therefore a legal realization interface,
not an assertion that the original numerical box had one fixed cap.

The code below proves the source's correlated affine gap and old-cube
tests on closed boxes, its literal six-component third endpoint, and all
selected/full support gates. It then constructs a local constant-cap check
and connects checked refined labels to the original P1 raw-third fallback,
h34Check, and actual fourth policy. No saved gain or final integral is
an assumption. Import P1OriginalCoarseContinuationCells refers to the
adjacent P1 source-only module's intended installation path.
-/

namespace ImbalancedChen.P2OriginalFourthCapProducerInterface

noncomputable section

open Set VariableEnvelope P1OriginalCoarseContinuation
open scoped Classical BigOperators

abbrev Point := Fin 4 → ℝ
abbrev QEndpoint := Fin 4 → ℚ

structure Affine where
  constant : ℚ
  coefficient : Fin 4 → ℚ

def Affine.eval (a : Affine) (t : Point) : ℝ :=
  a.constant + ∑ i, (a.coefficient i : ℝ) * t i

def Affine.neg (a : Affine) : Affine := ⟨-a.constant, fun i => -a.coefficient i⟩
def Affine.sub (a b : Affine) : Affine :=
  ⟨a.constant - b.constant, fun i => a.coefficient i - b.coefficient i⟩

/-- The literal coefficient-sign endpoint evaluation in the producer. -/
def Affine.lower (a : Affine) (lo hi : QEndpoint) : ℚ :=
  a.constant + ∑ i, if 0 ≤ a.coefficient i then a.coefficient i * lo i
    else a.coefficient i * hi i

/-- Exactly the producer's upper(a)=-lower(-a). -/
def Affine.upper (a : Affine) (lo hi : QEndpoint) : ℚ := -a.neg.lower lo hi

theorem Affine.eval_neg (a : Affine) (t : Point) : a.neg.eval t = -a.eval t := by
  simp [Affine.eval, Affine.neg, Finset.sum_neg_distrib] <;> ring

theorem Affine.eval_sub (a b : Affine) (t : Point) :
    (a.sub b).eval t = a.eval t - b.eval t := by
  simp only [Affine.eval, Affine.sub, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem Affine.lower_le_eval (a : Affine) (lo hi : QEndpoint) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    (a.lower lo hi : ℝ) ≤ a.eval t := by
  have hs (i : Fin 4) :
      ((if 0 ≤ a.coefficient i then a.coefficient i * lo i
        else a.coefficient i * hi i : ℚ) : ℝ) ≤ (a.coefficient i : ℝ) * t i := by
    by_cases hc : 0 ≤ a.coefficient i
    · simp only [if_pos hc, Rat.cast_mul]
      exact mul_le_mul_of_nonneg_left (hl i) (by exact_mod_cast hc)
    · simp only [if_neg hc, Rat.cast_mul]
      exact mul_le_mul_of_nonpos_left (hu i) (by exact_mod_cast (le_of_not_ge hc))
  calc
    (a.lower lo hi : ℝ) = (a.constant : ℝ) + ∑ i,
      ((if 0 ≤ a.coefficient i then a.coefficient i * lo i
        else a.coefficient i * hi i : ℚ) : ℝ) := by simp only [Affine.lower, Rat.cast_add, Rat.cast_sum]
    _ ≤ (a.constant : ℝ) + ∑ i, (a.coefficient i : ℝ) * t i :=
      add_le_add_left (Finset.sum_le_sum (fun i _ => hs i)) _
    _ = a.eval t := rfl

theorem Affine.eval_le_upper (a : Affine) (lo hi : QEndpoint) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    a.eval t ≤ (a.upper lo hi : ℝ) := by
  have hn := a.neg.lower_le_eval lo hi t hl hu
  rw [Affine.eval_neg] at hn
  simp only [Affine.upper, Rat.cast_neg]
  linarith

def maskSum (I : Finset (Fin 4)) (t : Point) : ℝ :=
  ∑ i, if i ∈ I then t i else 0

theorem maskSum_eq (I : Finset (Fin 4)) (t : Point) : maskSum I t = ∑ i ∈ I, t i := by
  unfold maskSum
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- At physical t=integer_coordinate/204800 these are vlines/D, D=32*204800:
ascending coefficients (16*N,16*indicator), descending (57*N/2,-48*indicator). -/
def tentPlane (I : Finset (Fin 4)) (side : Bool) : Affine :=
  if side then ⟨57 / 64, fun i => if i ∈ I then -3 / 2 else 0⟩
  else ⟨1 / 2, fun i => if i ∈ I then 1 / 2 else 0⟩

private theorem sum_indicator_mul (I : Finset (Fin 4)) (c : ℝ) (t : Point) :
    (∑ i, (if i ∈ I then c else 0) * t i) = c * maskSum I t := by
  rw [maskSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  split_ifs <;> ring

theorem tentPlane_eval (I : Finset (Fin 4)) (t : Point) (side : Bool) :
    (tentPlane I side).eval t = if side then C (maskSum I t) else A (maskSum I t) := by
  cases side <;>
    simp only [tentPlane, Bool.false_eq_true, if_false, if_true, Affine.eval,
      Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Rat.cast_zero, Rat.cast_one,
      apply_ite, sum_indicator_mul]
  · dsimp [A]
    ring
  · dsimp [C]
    ring

def newCap (I : Finset (Fin 4)) (t : Point) : ℝ :=
  min ((tentPlane I false).eval t) ((tentPlane I true).eval t)

theorem newCap_eq_v (I : Finset (Fin 4)) (t : Point) : newCap I t = v (∑ i ∈ I, t i) := by
  rw [newCap, tentPlane_eval, tentPlane_eval, v_eq_min, maskSum_eq]
  rfl

/-- The actual six old components, in the existing `six` order. -/
def oldMask : Fin 6 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 1, 2}, ∅, {0, 2}, {1, 2}]

def oldPiece (j : Fin 6) (side : Bool) : Affine :=
  if j = 3 then ⟨153 / 256, ![0, 0, -3 / 8, 0]⟩ else tentPlane (oldMask j) side

def oldComponent (t : Point) (j : Fin 6) : ℝ :=
  min ((oldPiece j false).eval t) ((oldPiece j true).eval t)

def oldCap (t : Point) : ℝ := six (t 0) (t 1) (t 2)
def total (t : Point) : ℝ := ∑ i, t i
def oldCube : Affine := ⟨0, ![1, 1, 3, 0]⟩

theorem oldCube_eval (t : Point) : oldCube.eval t = t 0 + t 1 + 3 * t 2 := by
  norm_num [oldCube, Affine.eval, Fin.sum_univ_succ]
  <;> ring

theorem oldComponent_vector (t : Point) : oldComponent t =
    ![v (t 0), v (t 0 + t 1), v (t 0 + t 1 + t 2), B (t 2),
      v (t 0 + t 2), v (t 1 + t 2)] := by
  funext j
  fin_cases j <;>
    simp [oldComponent, oldPiece, oldMask, tentPlane_eval, maskSum_eq,
      Affine.eval, B, cap, v_eq_min, Fin.sum_univ_succ, add_assoc]
  <;> ring

theorem oldComponent_le (t : Point) (j : Fin 6) : oldComponent t j ≤ oldCap t := by
  rw [oldComponent_vector]
  fin_cases j <;> simp [oldCap, six]

theorem oldCap_le_of_components (t : Point) (q : ℝ)
    (h : ∀ j, oldComponent t j ≤ q) : oldCap t ≤ q := by
  simp only [oldComponent_vector] at h
  exact max_le (h 0) (max_le (h 1) (max_le (h 2) (max_le (h 3) (max_le (h 4) (h 5)))))

def gapPiece (I : Finset (Fin 4)) (lo hi : QEndpoint) (j : Fin 6) (side : Bool) : ℝ :=
  max (((tentPlane I side).sub (oldPiece j false)).lower lo hi : ℝ)
    (((tentPlane I side).sub (oldPiece j true)).lower lo hi : ℝ)

/-- Literal min_j min_a max_b inf_box(a-b), preserving coordinate correlation. -/
def gapLower (I : Finset (Fin 4)) (lo hi : QEndpoint) : ℝ :=
  Finset.univ.inf' (show (Finset.univ : Finset (Fin 6)).Nonempty from ⟨0, by simp⟩)
    (fun j => min (gapPiece I lo hi j false) (gapPiece I lo hi j true))

theorem gapLower_le_piece (I : Finset (Fin 4)) (lo hi : QEndpoint) (j : Fin 6) (side : Bool) :
    gapLower I lo hi ≤ gapPiece I lo hi j side := by
  have h := Finset.inf'_le (fun j => min (gapPiece I lo hi j false) (gapPiece I lo hi j true))
    (Finset.mem_univ j)
  cases side
  · exact h.trans (min_le_left _ _)
  · exact h.trans (min_le_right _ _)

theorem gapPiece_le (I : Finset (Fin 4)) (lo hi : QEndpoint) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ))
    (j : Fin 6) (side : Bool) :
    gapPiece I lo hi j side ≤ (tentPlane I side).eval t - oldComponent t j := by
  have h0 := ((tentPlane I side).sub (oldPiece j false)).lower_le_eval lo hi t hl hu
  have h1 := ((tentPlane I side).sub (oldPiece j true)).lower_le_eval lo hi t hl hu
  rw [Affine.eval_sub] at h0 h1
  rw [oldComponent, sub_min]
  exact max_le_max h0 h1

theorem gapLower_le_actual_gap (I : Finset (Fin 4)) (lo hi : QEndpoint) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    gapLower I lo hi ≤ newCap I t - oldCap t := by
  have hc (j : Fin 6) : oldComponent t j ≤ newCap I t - gapLower I lo hi := by
    have h0 := (gapLower_le_piece I lo hi j false).trans (gapPiece_le I lo hi t hl hu j false)
    have h1 := (gapLower_le_piece I lo hi j true).trans (gapPiece_le I lo hi t hl hu j true)
    have hn : gapLower I lo hi + oldComponent t j ≤ newCap I t := by
      exact le_min (by linarith) (by linarith)
    linarith
  have hh := oldCap_le_of_components t _ hc
  linarith

def oldCubeLower (lo hi : QEndpoint) : ℝ :=
  Finset.univ.sup' (show (Finset.univ : Finset (Fin 6)).Nonempty from ⟨0, by simp⟩)
    (fun j => min (((oldPiece j false).sub oldCube).lower lo hi : ℝ)
      (((oldPiece j true).sub oldCube).lower lo hi : ℝ))

theorem oldCubeLower_le (lo hi : QEndpoint) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    oldCubeLower lo hi ≤ oldCap t - oldCube.eval t := by
  apply Finset.sup'_le
  intro j _hj
  have h0 := ((oldPiece j false).sub oldCube).lower_le_eval lo hi t hl hu
  have h1 := ((oldPiece j true).sub oldCube).lower_le_eval lo hi t hl hu
  rw [Affine.eval_sub] at h0 h1
  have hh := min_le_min h0 h1
  rw [← min_sub] at hh
  exact hh.trans (sub_le_sub_right (oldComponent_le t j) _)

def halfGate : Affine := ⟨1 / 2, fun _ => 0⟩

def fullGate (j : Fin 4) : Affine :=
  ⟨0, fun i => (if i < j then 1 else 0) + (if i = j then 2 else 0)⟩

def selectedGate (I : Finset (Fin 4)) (j : Fin 4) : Affine :=
  ⟨0, fun i => (if i ∈ I then 1 else 0) +
    (if i < j ∧ i ∉ I then 1 else 0) + (if i = j then 2 else 0)⟩

theorem halfGate_eval (t : Point) : halfGate.eval t = 1 / 2 := by
  simp [halfGate, Affine.eval]

theorem fullGate_eval (t : Point) (j : Fin 4) : (fullGate j).eval t = prefixSquareExpr t j := by
  fin_cases j <;>
    norm_num [fullGate, Affine.eval, prefixSquareExpr, Finset.sum_filter, Fin.sum_univ_succ]
  <;> ring

theorem selectedGate_eval (I : Finset (Fin 4)) (t : Point) (j : Fin 4) :
    (selectedGate I j).eval t = selectedSquareExpr I t j := by
  unfold selectedSquareExpr
  rw [← maskSum_eq I t]
  by_cases h0 : (0 : Fin 4) ∈ I <;> by_cases h1 : (1 : Fin 4) ∈ I <;>
    by_cases h2 : (2 : Fin 4) ∈ I <;> by_cases h3 : (3 : Fin 4) ∈ I <;>
    fin_cases j <;>
    simp [selectedGate, Affine.eval,
      maskSum, Finset.sum_filter, Fin.sum_univ_succ, h0, h1, h2, h3]
  <;> ring

/-- These are finite rational endpoint inequalities, precisely the source
gateslack>0 test decomposed into its individual affine differences. -/
def WholeBoxGateRows (I : Finset (Fin 4)) (lo hi : QEndpoint) : Prop :=
  (∀ side, 0 < (((tentPlane I side).sub halfGate).lower lo hi : ℝ)) ∧
  (∀ side j, 0 < (((tentPlane I side).sub (fullGate j)).lower lo hi : ℝ)) ∧
  (∀ side j, j ∉ I → 0 < (((tentPlane I side).sub (selectedGate I j)).lower lo hi : ℝ))

private theorem gate_lt_newCap (I : Finset (Fin 4)) (lo hi : QEndpoint) (g : Affine)
    (hg : ∀ side, 0 < (((tentPlane I side).sub g).lower lo hi : ℝ))
    (t : Point) (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    g.eval t < newCap I t := by
  apply lt_min
  · have hs := ((tentPlane I false).sub g).lower_le_eval lo hi t hl hu
    rw [Affine.eval_sub] at hs
    linarith [hg false]
  · have hs := ((tentPlane I true).sub g).lower_le_eval lo hi t hl hu
    rw [Affine.eval_sub] at hs
    linarith [hg true]

theorem WholeBoxGateRows.sound {I : Finset (Fin 4)} {lo hi : QEndpoint}
    (hg : WholeBoxGateRows I lo hi) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    (1 / 2 : ℝ) < newCap I t ∧
      (∀ j, prefixSquareExpr t j < newCap I t) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < newCap I t) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [halfGate_eval] using gate_lt_newCap I lo hi halfGate hg.1 t hl hu
  · intro j
    simpa only [fullGate_eval] using gate_lt_newCap I lo hi (fullGate j)
      (fun side => hg.2.1 side j) t hl hu
  · intro j hj
    simpa only [selectedGate_eval] using gate_lt_newCap I lo hi (selectedGate I j)
      (fun side => hg.2.2 side j hj) t hl hu

theorem whole_box_endpoint_license (I : Finset (Fin 4)) (lo hi : QEndpoint)
    (hgap : 0 < gapLower I lo hi) (hcube : 0 < oldCubeLower lo hi)
    (hgates : WholeBoxGateRows I lo hi) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    oldCube.eval t < oldCap t ∧ oldCap t < newCap I t ∧
      (1 / 2 : ℝ) < newCap I t ∧
      (∀ j, prefixSquareExpr t j < newCap I t) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < newCap I t) := by
  have hdelta := gapLower_le_actual_gap I lo hi t hl hu
  have hold := oldCubeLower_le lo hi t hl hu
  exact ⟨by linarith, by linarith, hgates.sound t hl hu⟩

def sumAffine : Affine := ⟨0, fun _ => 1⟩

theorem sumAffine_eval (t : Point) : sumAffine.eval t = total t := by
  simp [sumAffine, Affine.eval, total]

/-- Literal correlated R0 and R1 from the producer, in physical units. -/
def oldResidualUpper (lo hi : QEndpoint) : ℝ :=
  Finset.univ.sup' (show (Finset.univ : Finset (Fin 6)).Nonempty from ⟨0, by simp⟩)
    (fun j => min (((oldPiece j false).sub sumAffine).upper lo hi : ℝ)
      (((oldPiece j true).sub sumAffine).upper lo hi : ℝ))

def newResidualUpper (I : Finset (Fin 4)) (lo hi : QEndpoint) : ℝ :=
  max (oldResidualUpper lo hi)
    (min (((tentPlane I false).sub sumAffine).upper lo hi : ℝ)
      (((tentPlane I true).sub sumAffine).upper lo hi : ℝ))

theorem old_residual_le_upper (lo hi : QEndpoint) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    oldCap t - total t ≤ oldResidualUpper lo hi := by
  have hc (j : Fin 6) : oldComponent t j ≤ oldResidualUpper lo hi + total t := by
    have h0 := ((oldPiece j false).sub sumAffine).eval_le_upper lo hi t hl hu
    have h1 := ((oldPiece j true).sub sumAffine).eval_le_upper lo hi t hl hu
    rw [Affine.eval_sub, sumAffine_eval] at h0 h1
    have hm := min_le_min h0 h1
    rw [← min_sub] at hm
    have hj := Finset.le_sup' (fun j =>
      min (((oldPiece j false).sub sumAffine).upper lo hi : ℝ)
        (((oldPiece j true).sub sumAffine).upper lo hi : ℝ)) (Finset.mem_univ j)
    have hh : oldComponent t j - total t ≤ oldResidualUpper lo hi := hm.trans hj
    linarith
  have hh := oldCap_le_of_components t _ hc
  linarith

theorem new_residual_le_upper (I : Finset (Fin 4)) (lo hi : QEndpoint) (t : Point)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    newCap I t - total t ≤ newResidualUpper I lo hi := by
  have h0 := ((tentPlane I false).sub sumAffine).eval_le_upper lo hi t hl hu
  have h1 := ((tentPlane I true).sub sumAffine).eval_le_upper lo hi t hl hu
  rw [Affine.eval_sub, sumAffine_eval] at h0 h1
  have hm := min_le_min h0 h1
  rw [← min_sub] at hm
  exact hm.trans (le_max_right _ _)

/-- The only producer inputs inherited from the NPZ witness: integer
coordinate endpoints and a numeric mask. No stored gain is part of a row. -/
structure ProducerRow where
  lo : Fin 4 → ℕ
  hi : Fin 4 → ℕ
  mask : ℕ

def ProducerRow.selected (r : ProducerRow) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => Nat.testBit r.mask i.val)

def ProducerRow.lower (r : ProducerRow) : QEndpoint := fun i => (r.lo i : ℚ) / 204800
def ProducerRow.upper (r : ProducerRow) : QEndpoint := fun i => (r.hi i : ℚ) / 204800

def ProducerRow.box (r : ProducerRow) : Set Point :=
  {t | (∀ i, (r.lower i : ℝ) ≤ t i) ∧ (∀ i, t i ≤ (r.upper i : ℝ))}

def ProducerRow.candidate (r : ProducerRow) (t : Point) : ℝ := newCap r.selected t
def ProducerRow.bufferedCandidate (r : ProducerRow) (e : ℝ) (t : Point) : ℝ :=
  r.candidate t - 2 * e

/-- Original closed-box geometry, without reflected data or final outputs. -/
def ProducerRow.Geometry (r : ProducerRow) : Prop :=
  9 ≤ r.mask ∧ r.mask ≤ 15 ∧
  (∀ i, r.lo i < r.hi i) ∧
  (∀ i : Fin 3, r.hi i.succ ≤ r.lo i.castSucc) ∧
  3 / 200 ≤ r.lower 3 ∧ r.upper 0 ≤ 39 / 200 ∧
  0 < gapLower r.selected r.lower r.upper ∧
  0 < oldCubeLower r.lower r.upper ∧ WholeBoxGateRows r.selected r.lower r.upper ∧
  0 < oldResidualUpper r.lower r.upper ∧
  newResidualUpper r.selected r.lower r.upper < 5 * (r.lower 3 : ℝ)

theorem ProducerRow.candidate_eq (r : ProducerRow) (t : Point) :
    r.candidate t = v (∑ i ∈ r.selected, t i) := newCap_eq_v _ _

theorem ProducerRow.bufferedCandidate_eq (r : ProducerRow) (e : ℝ) (t : Point) :
    r.bufferedCandidate e t = v (∑ i ∈ r.selected, t i) - 2 * e := by
  rw [ProducerRow.bufferedCandidate, ProducerRow.candidate_eq]

theorem ProducerRow.geometry_sound (r : ProducerRow) (h : r.Geometry)
    (t : Point) (ht : t ∈ r.box) :
    oldCube.eval t < oldCap t ∧ oldCap t < r.candidate t ∧
      (1 / 2 : ℝ) < r.candidate t ∧
      (∀ j, prefixSquareExpr t j < r.candidate t) ∧
      (∀ j ∉ r.selected, selectedSquareExpr r.selected t j < r.candidate t) := by
  rcases h with ⟨_hmasklo, _hmaskhi, _hwidth, _horder, _hcut, _htop,
    hgap, hcube, hgates, _hr0, _hr1⟩
  exact whole_box_endpoint_license r.selected r.lower r.upper hgap hcube hgates t ht.1 ht.2

theorem ProducerRow.ordered (r : ProducerRow) (h : r.Geometry)
    (t : Point) (ht : t ∈ r.box) : Ordered (t 0) (t 1) (t 2) ∧ 0 < t 3 ∧ t 3 ≤ t 2 := by
  rcases h with ⟨_hmasklo, _hmaskhi, _hwidth, horder, hcut, htop,
    _hgap, _hcube, _hgates, _hr0, _hr1⟩
  have hadj (i : Fin 3) : (r.upper i.succ : ℝ) ≤ (r.lower i.castSucc : ℝ) := by
    have hn : (r.hi i.succ : ℝ) ≤ (r.lo i.castSucc : ℝ) := by exact_mod_cast horder i
    simpa only [ProducerRow.upper, ProducerRow.lower, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat] using div_le_div_of_nonneg_right hn (by norm_num : (0 : ℝ) ≤ 204800)
  have h10 : t 1 ≤ t 0 := (ht.2 1).trans ((hadj 0).trans (ht.1 0))
  have h21 : t 2 ≤ t 1 := (ht.2 2).trans ((hadj 1).trans (ht.1 1))
  have h32 : t 3 ≤ t 2 := (ht.2 3).trans ((hadj 2).trans (ht.1 2))
  have hcutR : (3 / 200 : ℝ) ≤ (r.lower 3 : ℝ) := by exact_mod_cast hcut
  have htopR : (r.upper 0 : ℝ) ≤ (39 / 200 : ℝ) := by exact_mod_cast htop
  have ht3 : 0 < t 3 := by linarith [ht.1 3]
  refine ⟨⟨ht3.le.trans h32, h21, h10, ?_⟩, ht3, h32⟩
  exact (ht.2 0).trans (htopR.trans (by norm_num [mu]))

/-- Exact source range 1<s_old<s_new<5.  The source integer inequality
r1<160*lo4 is exactly R1<5*(lo4/204800), since D=32*204800. -/
theorem ProducerRow.residual_range (r : ProducerRow) (h : r.Geometry)
    (t : Point) (ht : t ∈ r.box) :
    1 < (oldCap t - total t) / t 3 ∧
      (oldCap t - total t) / t 3 < (r.candidate t - total t) / t 3 ∧
        (r.candidate t - total t) / t 3 < 5 := by
  have hg := r.geometry_sound h t ht
  have ho := r.ordered h t ht
  have hidentity : oldCube.eval t - total t = 2 * t 2 - t 3 := by
    rw [oldCube_eval]
    norm_num [total, Fin.sum_univ_succ]
    <;> ring
  have hR1 : newResidualUpper r.selected r.lower r.upper < 5 * (r.lower 3 : ℝ) :=
    h.2.2.2.2.2.2.2.2.2.2
  have hup : r.candidate t - total t ≤ newResidualUpper r.selected r.lower r.upper :=
    new_residual_le_upper r.selected r.lower r.upper t ht.1 ht.2
  refine ⟨(one_lt_div ho.2.1).mpr ?_, (div_lt_div_iff_of_pos_right ho.2.1).mpr ?_,
    (div_lt_iff₀ ho.2.1).mpr ?_⟩
  · linarith [hg.1, ho.2.2]
  · linarith [hg.2.1]
  · linarith [ht.1 3]

theorem producer_oldCap_eq_original (t : Point) (ht : Ordered (t 0) (t 1) (t 2)) :
    oldCap t = original (t 0) (t 1) (t 2) := (original_eq_six ht).symm

theorem producer_cap_lt_global (I : Finset (Fin 4)) (t : Point) :
    newCap I t < (299 / 500 : ℝ) := by
  rw [newCap_eq_v]
  exact (v_le_cap _).trans_lt (by norm_num [cap])

/-- Strict pointwise geometry creates a check on ALL sufficiently near
rational endpoint pairs. It does not fix one cap on the original rectangle. -/
theorem exists_refined_constant_cap_radius (I : Finset (Fin 4)) (old : ℚ) (t : Point)
    (hold : (old : ℝ) ≤ oldCap t) (hgap : oldCap t < newCap I t)
    (hhalf : (1 / 2 : ℝ) < newCap I t)
    (hfull : ∀ j, prefixSquareExpr t j < newCap I t)
    (hselected : ∀ j ∉ I, selectedSquareExpr I t j < newCap I t) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ l u : QEndpoint,
      dist (fun i => (l i : ℝ)) t < delta → dist (fun i => (u i : ℝ)) t < delta →
        selectedBoxCapCheck I old (299 / 500) l u = true := by
  have hM : newCap I t < ((299 / 500 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using producer_cap_lt_global I t
  have hl : SelectedPrefixLicense I old (299 / 500) t := by
    rw [← newCap_eq_v, min_eq_right hM.le]
    exact ⟨hold.trans_lt hgap, hhalf, hfull, hselected⟩
  exact exists_selectedBoxCapCheck_radius_of_strict I old (299 / 500) t hl

/-- The genuine inherited original coarse third exponent is bounded by L,
using its box and endpoint theorem, including the original gated envelope. -/
theorem original_third_exponent_le_oldCap (e : ℚ) (he : 0 ≤ e) (m : ℕ)
    (j : FourthCell m) (t : Point)
    (hbox : (HistoricalThirdCoarse.box m
      (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox (t 0) (t 1) (t 2))
    (ht : Ordered (t 0) (t 1) (t 2)) :
    (thirdCellExponent e m j : ℝ) ≤ oldCap t := by
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hg := HistoricalThirdCoarse.gamma_le_endpoint (e : ℝ)
    (HistoricalThirdCoarse.box m (historicalPrefixProject (by omega : 3 ≤ 4) j))
    heR hbox ht.1 ht.2.1 ht.2.2.1
  rw [HistoricalThirdCoarse.endpoint, if_pos ht.2.2.2, original_eq_six ht] at hg
  simp only [thirdCellExponent, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  change _ - 2 * (e : ℝ) ≤ oldCap t
  dsimp [oldCap]
  linarith

/-- Original producer geometry plus the actual old coarse-cell endpoint
constructs the strict selected-prefix license, without an enclosure claim. -/
theorem producer_selectedPrefixLicense (r : ProducerRow) (hr : r.Geometry)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ) (j : FourthCell m) (t : Point) (ht : t ∈ r.box)
    (hbox : (HistoricalThirdCoarse.box m
      (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox (t 0) (t 1) (t 2)) :
    SelectedPrefixLicense r.selected (thirdCellExponent e m j) (299 / 500) t := by
  have hg := r.geometry_sound hr t ht
  have hold := original_third_exponent_le_oldCap e he m j t hbox (r.ordered hr t ht).1
  have hM : r.candidate t < ((299 / 500 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using producer_cap_lt_global r.selected t
  rw [SelectedPrefixLicense, ← ProducerRow.candidate_eq r t, min_eq_right hM.le]
  exact ⟨hold.trans_lt hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩

/-- Compact refinement uses one positive radius for the entire compact
patch in a fixed old label. The numerical producer rectangle is not
silently assigned a constant endpoint. -/
theorem producer_compact_refinement_radius (r : ProducerRow) (hr : r.Geometry)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ) (j : FourthCell m)
    (K : Set Point) (hK : IsCompact K) (hKbox : K ⊆ r.box)
    (hcoarse : ∀ t ∈ K, (HistoricalThirdCoarse.box m
      (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox (t 0) (t 1) (t 2)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ K, ∀ l u : QEndpoint,
      dist (fun i => (l i : ℝ)) t < delta → dist (fun i => (u i : ℝ)) t < delta →
        selectedBoxCapCheck r.selected (thirdCellExponent e m j) (299 / 500) l u = true := by
  exact exists_selectedBoxCapCheck_uniform_radius r.selected (thirdCellExponent e m j)
    (299 / 500) K hK (fun t ht => producer_selectedPrefixLicense r hr e he m j t
      (hKbox ht) (hcoarse t ht))

/-- A concrete cap table for refined fourth labels. The old cap is the
actual cell's Gamma-2e; no constant global old level is substituted. -/
def refinedCap (e : ℚ) (m : ℕ) (masks : FourthCell m → Finset (Fin 4))
    (j : FourthCell m) : ℚ :=
  selectedBoxCap (masks j) (thirdCellExponent e m j) (299 / 500)
    (qLogPrimeMeshLo 0 (19 / 96) m j) (qLogPrimeMeshHi 0 (19 / 96) m j)

theorem refined_h34Check (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (masks : FourthCell m → Finset (Fin 4))
    (hchecks : ∀ j ∈ selectedFourthCells e chi m omega J4,
      selectedBoxCapCheck (masks j) (thirdCellExponent e m j) (299 / 500)
        (qLogPrimeMeshLo 0 (19 / 96) m j) (qLogPrimeMeshHi 0 (19 / 96) m j) = true) :
    h34Check e chi m omega J4 (refinedCap e m masks) = true := by
  simp only [h34Check, decide_eq_true_eq]
  intro j hj
  exact (selectedCapLower_old_le _ _ _).trans
    (selectedBoxCap_between _ _ _ _ _ (hchecks j hj)).1.le

/-- Direct binding to the original P1 continuation, with its raw Q3 frozen
at the third ancestor, outside-cell fallback, and real rank four intact. -/
theorem actual_original_third_le_refined_fourth
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J4 : Finset (FourthCell m))
    (masks : FourthCell m → Finset (Fin 4))
    (hchecks : ∀ j ∈ selectedFourthCells e chi m omega J4,
      selectedBoxCapCheck (masks j) (thirdCellExponent e m j) (299 / 500)
        (qLogPrimeMeshLo 0 (19 / 96) m j) (qLogPrimeMeshHi 0 (19 / 96) m j) = true)
    (N : ℝ) (history : List ℕ) (hN : 1 < N) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p) :
    HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega N history ≤
      level4 e chi m omega J4 (refinedCap e m masks) N history := by
  exact frozenLevel_le_level4 e chi m omega J4 (refinedCap e m masks) N history
    (refined_h34Check e chi m omega J4 masks hchecks) hN hlen hpos

theorem refined_policy_frontier_four (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (masks : FourthCell m → Finset (Fin 4)) (N : ℝ)
    (weight : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4 (policy4 e chi m omega J4 (refinedCap e m masks) N)
        weight pre positive mass carrier =
      firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
        weight pre positive mass carrier :=
  policy4_frontier_four e chi m omega J4 (refinedCap e m masks) N
    weight pre carrier positive mass

theorem refined_level_on_selected_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (masks : FourthCell m → Finset (Fin 4))
    (N : ℝ) (history : List ℕ) (hlen : history.length = 4)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (ht : primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    level4 e chi m omega J4 (refinedCap e m masks) N history =
      N ^ (refinedCap e m masks j : ℝ) :=
  level4_on_selected_cell e chi m omega J4 (refinedCap e m masks) N history hlen j hj ht

theorem refined_level_outside (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (masks : FourthCell m → Finset (Fin 4))
    (N : ℝ) (history : List ℕ)
    (hout : ∀ j ∈ selectedFourthCells e chi m omega J4,
      primeHistoryLogCoordinates N 4 history ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    level4 e chi m omega J4 (refinedCap e m masks) N history =
      HistoricalThirdCoarse.frozenLevel (e : ℝ) chi m omega N history :=
  level4_outside e chi m omega J4 (refinedCap e m masks) N history hout

end

end ImbalancedChen.P2OriginalFourthCapProducerInterface
