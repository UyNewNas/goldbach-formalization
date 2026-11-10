import ImbalancedChen.P4AOriginalSavedSixthWordAccess
import ImbalancedChen.P5OldFifthFiveCoordinateBarycentric

/-! Six-dimensional rational planes for the original grid-400,
632104-row saved sixth witness. The new tent has two planes; for each
of the 31 inherited subsets the saved midpoint picks ONE global upper
plane, with the original first-minimum convention. The W branch is
the thirty-second old plane. All field reads are from the S09 NPY. -/
namespace ImbalancedChen.P4AOriginalSavedSixthPlanes
noncomputable section
open scoped BigOperators
open P4AOriginalSavedSixthArchive (Row word selectedMask)
open Certificates.P2OriginalSixthElevenLogSemantics (Physical bit)

abbrev PointQ := Fin 6 → ℚ
abbrev Corner := Fin 6 → Bool

structure Plane where
  base : ℚ
  coeff : Fin 6 → ℚ

def Plane.evalQ (p : Plane) (t : PointQ) := p.base + ∑ j, p.coeff j * t j
def Plane.sub (p q : Plane) : Plane := ⟨p.base-q.base, fun j => p.coeff j-q.coeff j⟩
def Plane.plus (p q : Plane) : Plane := ⟨p.base+q.base, fun j => p.coeff j+q.coeff j⟩
def Plane.scale (r : ℚ) (p : Plane) : Plane := ⟨r*p.base, fun j => r*p.coeff j⟩
def constant (r : ℚ) : Plane := ⟨r,fun _ => 0⟩
def coord (j : Fin 6) : Plane := ⟨0,fun k => if j=k then 1 else 0⟩
def total : Plane := ⟨0,fun _ => 1⟩
def slots (k mask : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun j => j.val < k ∧ bit mask j.val
def selected (k m : ℕ) : Plane := ⟨0,fun j => if j ∈ slots k m then 1 else 0⟩
def tentPlane (k m : ℕ) (desc : Bool) : Plane :=
  if desc then (constant (57/64)).plus ((selected k m).scale (-3/2))
  else (constant (1/2)).plus ((selected k m).scale (1/2))
def rescue : Plane := (constant (153/256)).plus ((coord 2).scale (-3/8))
def chosenMask (i : Row) : ℕ := (P4AOriginalSavedSixthWordAccess.word i 7).toNat
def lowerQ (i : Row) : PointQ := fun j => (P4AOriginalSavedSixthWordAccess.word i ⟨j.val+1,by omega⟩ : ℚ)/400
def upperQ (i : Row) : PointQ := fun j => ((P4AOriginalSavedSixthWordAccess.word i ⟨j.val+1,by omega⟩ : ℚ)+1)/400
def midpointQ (i : Row) : PointQ := fun j => (lowerQ i j+upperQ i j)/2
def vertexQ (i : Row) (b : Corner) : PointQ := fun j => if b j then upperQ i j else lowerQ i j
def oldPlane (i : Row) (m : ℕ) : Plane :=
  let a := tentPlane 5 m false
  let d := tentPlane 5 m true
  let t := midpointQ i
  if a.evalQ t ≤ d.evalQ t ∧ a.evalQ t ≤ 153/256 then a
  else if d.evalQ t ≤ 153/256 then d else constant (153/256)
def oldFace (i : Row) (m : Fin 32) : Plane := if m.val = 0 then rescue else oldPlane i m.val
def newFace (i : Row) (b : Bool) : Plane := tentPlane 6 (chosenMask i) b

def oldQ (i : Row) (t : PointQ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun m : Fin 32 => (oldFace i m).evalQ t)
def gapQ (i : Row) (t : PointQ) : ℚ :=
  min ((newFace i false).evalQ t) ((newFace i true).evalQ t) - oldQ i t

def upperBound (p : Plane) (lo hi : PointQ) : ℚ :=
  p.base + ∑ j, p.coeff j * (if 0 ≤ p.coeff j then hi j else lo j)
def lowerBound (p : Plane) (lo hi : PointQ) : ℚ :=
  p.base + ∑ j, p.coeff j * (if 0 ≤ p.coeff j then lo j else hi j)

open Set VariableEnvelope P1OriginalVariableFourthContinuation
open Certificates.P2OriginalSixthElevenLogSemantics (S6 subsetSum selectedSum W)

def Plane.eval (p : Plane) (t : Physical) : ℝ := (p.base:ℝ) + ∑ j, (p.coeff j:ℝ) * t j
def lift (t : PointQ) : Physical := fun j => (t j : ℝ)
def box (i : Row) := logPrimeBox (lift (lowerQ i)) (lift (upperQ i))

@[simp] theorem cast_evalQ (p : Plane) (t : PointQ) : (p.evalQ t : ℝ) = p.eval (lift t) := by
  simp [Plane.evalQ,Plane.eval,lift]
@[simp] theorem eval_sub (p q : Plane) (t : Physical) :
    (p.sub q).eval t = p.eval t-q.eval t := by
  simp [Plane.sub,Plane.eval,sub_mul,Finset.sum_sub_distrib]; ring
@[simp] theorem eval_plus (p q : Plane) (t : Physical) :
    (p.plus q).eval t = p.eval t+q.eval t := by
  simp [Plane.plus,Plane.eval,add_mul,Finset.sum_add_distrib]; ring
@[simp] theorem eval_scale (p : Plane) (r : ℚ) (t : Physical) :
    (p.scale r).eval t = (r:ℝ)*p.eval t := by
  simp [Plane.scale,Plane.eval,mul_add,Finset.mul_sum,mul_assoc]
@[simp] theorem eval_constant (r : ℚ) (t : Physical) : (constant r).eval t = (r:ℝ) := by
  simp [constant,Plane.eval]
@[simp] theorem eval_coord (j : Fin 6) (t : Physical) : (coord j).eval t = t j := by
  simp [coord,Plane.eval,ite_mul]
@[simp] theorem eval_total (t : Physical) : total.eval t = S6 t := by
  simp [total,Plane.eval,Certificates.P2OriginalSixthElevenLogSemantics.S6_eq_sum]
@[simp] theorem eval_selected (k m : ℕ) (t : Physical) :
    (selected k m).eval t = ∑ j ∈ slots k m,t j := by
  simp [selected,Plane.eval,ite_mul,Finset.sum_filter]
theorem sum_five (m : ℕ) (t : Physical) : ∑ j ∈ slots 5 m, t j = subsetSum m t := by
  simp [slots,Finset.sum_filter,subsetSum,Fin.sum_univ_succ]
theorem sum_six (m : ℕ) (t : Physical) : ∑ j ∈ slots 6 m,t j = selectedSum m t := by
  simp [slots,Finset.sum_filter,selectedSum]
@[simp] theorem eval_tent (k m : ℕ) (s : Bool) (t : Physical) :
    (tentPlane k m s).eval t =
      if s then C (∑ j ∈ slots k m,t j) else A (∑ j ∈ slots k m,t j) := by
  cases s <;> simp [tentPlane,A,C] <;> ring
@[simp] theorem eval_rescue (t : Physical) : rescue.eval t = W t := by
  simp [rescue,W]; ring

theorem width_pos (i : Row) (j : Fin 6) : lowerQ i j < upperQ i j := by
  unfold lowerQ upperQ
  linarith
theorem eval_le_upper (p : Plane) {a b : PointQ} {t : Physical} (ht : t ∈ Icc (lift a) (lift b)) :
    p.eval t ≤ (upperBound p a b : ℝ) := by
  unfold upperBound Plane.eval
  push_cast
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  by_cases h : 0 ≤ p.coeff j
  · simp only [if_pos h]
    exact mul_le_mul_of_nonneg_left (ht.2 j) (by exact_mod_cast h)
  · simp only [if_neg h]
    exact mul_le_mul_of_nonpos_left (ht.1 j) (by exact_mod_cast (le_of_not_ge h))
theorem lower_le_eval (p : Plane) {a b : PointQ} {t : Physical} (ht : t ∈ Icc (lift a) (lift b)) :
    (lowerBound p a b : ℝ) ≤ p.eval t := by
  unfold lowerBound Plane.eval
  push_cast
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  by_cases h : 0 ≤ p.coeff j
  · simp only [if_pos h]
    exact mul_le_mul_of_nonneg_left (ht.1 j) (by exact_mod_cast h)
  · simp only [if_neg h]
    exact mul_le_mul_of_nonpos_left (ht.2 j) (by exact_mod_cast (le_of_not_ge h))

theorem corners_match (i : Row) (hg : word i 0 = 400) :
    P4AOriginalSavedSixthArchive.lowerCorner i = lift (lowerQ i) ∧
    P4AOriginalSavedSixthArchive.upperCorner i = lift (upperQ i) := by
  constructor <;> funext j <;> simp [P4AOriginalSavedSixthArchive.lowerCorner,
    P4AOriginalSavedSixthArchive.upperCorner,P4AOriginalSavedSixthArchive.denominator,
    hg,lift,lowerQ,upperQ,P4AOriginalSavedSixthWordAccess.word_eq]
theorem midpoint_match (i : Row) (hg : word i 0 = 400) :
    P4AOriginalSavedSixthArchive.midpoint i = lift (midpointQ i) := by
  funext j
  simp [P4AOriginalSavedSixthArchive.midpoint,(corners_match i hg).1,
    (corners_match i hg).2,lift,midpointQ]

theorem old_plane_match (i : Row) (hg : word i 0 = 400) (m : ℕ) (t : Physical) :
    (oldPlane i m).eval t = P4AOriginalSavedSixthArchive.oldPlane i m t := by
  have castA (b : Bool) : ((tentPlane 5 m b).evalQ (midpointQ i) : ℝ) =
      if b then C (subsetSum m (P4AOriginalSavedSixthArchive.midpoint i))
      else A (subsetSum m (P4AOriginalSavedSixthArchive.midpoint i)) := by
    rw [cast_evalQ,eval_tent,sum_five,midpoint_match i hg]
  have hA := castA false
  have hD := castA true
  simp only [Bool.false_eq_true,if_false,if_true] at hA hD
  have ha : (A (subsetSum m (P4AOriginalSavedSixthArchive.midpoint i)) ≤
      C (subsetSum m (P4AOriginalSavedSixthArchive.midpoint i))) ↔
      (tentPlane 5 m false).evalQ (midpointQ i) ≤ (tentPlane 5 m true).evalQ (midpointQ i) := by
    rw [← hA,← hD]; exact_mod_cast Iff.rfl
  have hb : (A (subsetSum m (P4AOriginalSavedSixthArchive.midpoint i)) ≤ cap) ↔
      (tentPlane 5 m false).evalQ (midpointQ i) ≤ 153/256 := by
    rw [← hA]; unfold cap; exact_mod_cast Iff.rfl
  have hc : (C (subsetSum m (P4AOriginalSavedSixthArchive.midpoint i)) ≤ cap) ↔
      (tentPlane 5 m true).evalQ (midpointQ i) ≤ 153/256 := by
    rw [← hD]; unfold cap; exact_mod_cast Iff.rfl
  unfold oldPlane P4AOriginalSavedSixthArchive.oldPlane
  simp only [ha,hb,hc]
  split_ifs <;> simp [eval_tent,sum_five,cap]

theorem oldFace_le (i : Row) (hg : word i 0 = 400) (m : Fin 32) (t : Physical) :
    (oldFace i m).eval t ≤ P4AOriginalSavedSixthArchive.oldUpper i t := by
  unfold oldFace
  split
  · simp only [eval_rescue]; exact finiteMax_seed_le _ _ _ _
  · rename_i hm
    rw [old_plane_match i hg]
    exact finiteMax_row_le _ _ _ _ m.val (Finset.mem_Icc.mpr ⟨by omega,by omega⟩) trivial

theorem oldUpper_le (i : Row) (hg : word i 0 = 400) (t : Physical) (R : ℝ)
    (h : ∀ m : Fin 32, (oldFace i m).eval t ≤ R) :
    P4AOriginalSavedSixthArchive.oldUpper i t ≤ R := by
  apply finiteMax_le
  · simpa [oldFace] using h 0
  · intro m hm _
    obtain ⟨hm0,hm1⟩ := Finset.mem_Icc.mp hm
    simpa [oldFace,show m ≠ 0 by omega,old_plane_match i hg] using h ⟨m,by omega⟩

theorem new_min (i : Row) (t : Physical) :
    min ((newFace i false).eval t) ((newFace i true).eval t) =
    P4AOriginalSavedSixthArchive.endpoint i t := by
  simp [newFace,chosenMask,P4AOriginalSavedSixthWordAccess.word_eq,selectedMask,
    P4AOriginalSavedSixthArchive.endpoint,VariableEnvelope.v_eq_min,sum_six]

theorem literal_gap (i : Row) (hg : word i 0 = 400) (t : PointQ) :
    (gapQ i t : ℝ) = P4AOriginalSavedSixthArchive.endpoint i (lift t) -
      P4AOriginalSavedSixthArchive.oldUpper i (lift t) := by
  have ho : (oldQ i t : ℝ) = P4AOriginalSavedSixthArchive.oldUpper i (lift t) := by
    apply le_antisymm
    · obtain ⟨m,_,hm⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun m : Fin 32 => (oldFace i m).evalQ t)
      simp only [oldQ,hm,cast_evalQ]
      exact oldFace_le i hg m _
    · apply oldUpper_le i hg
      intro m
      rw [← cast_evalQ]; exact_mod_cast Finset.le_sup' (f := fun k : Fin 32 => (oldFace i k).evalQ t) (Finset.mem_univ m)
  simp only [gapQ,Rat.cast_sub,Rat.cast_min,cast_evalQ,ho,new_min]

end
end ImbalancedChen.P4AOriginalSavedSixthPlanes
