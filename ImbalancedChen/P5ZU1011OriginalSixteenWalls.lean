import ImbalancedChen.P5ZU1011OriginalSixteenPolicyBank

/-!
Actual sixteen-policy proper affine walls and scalar dictionaries.
Selected masks 1..15 are proved nonempty, so no form-nonzero supplier is
requested. Full/selected square walls are separated from the half-integral
cap coefficients by evaluation at an actual coordinate basis vector.
The W cap is treated separately; its two branch flags are IDENTICAL.

High table knots 51..200 have proper affine equality walls. This file
makes no null-set assertion about the full max-two clamp cell L<=2w.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenWalls

open Set
open Classical
open U11Integral
open Part5OriginalUpsilon5CausalDictionary
open U1011OriginalSixteenPolicyBank
open scoped BigOperators

noncomputable section

def basis (i : Fin 4) : LogFour := fun j => if j=i then 1 else 0

/-- This is a fact about every actual selected source ID 1..15. -/
theorem exists_selected (p : Policy) (hp : p.val<15) : ∃ i : Fin 4, Selected p i := by
  fin_cases p <;>
    first
    | exact ⟨0, by norm_num [Selected,sourceId]⟩
    | exact ⟨1, by norm_num [Selected,sourceId]⟩
    | exact ⟨2, by norm_num [Selected,sourceId]⟩
    | exact ⟨3, by norm_num [Selected,sourceId]⟩
    | omega

theorem selectedMass_basis (p : Policy) (i : Fin 4) :
    selectedMass p (basis i) = if Selected p i then 1 else 0 := by
  unfold selectedMass
  calc
    _ = if Selected p i then basis i i else 0 := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [basis,hji]
      · intro h
        exact (h (Finset.mem_univ i)).elim
    _ = _ := by simp [basis]

theorem selectedLinear_basis (p : Policy) (i : Fin 4) :
    selectedLinear p (basis i) = if Selected p i then 1 else 0 := by
  rw [selectedLinear_apply,selectedMass_basis]

theorem fullSquareLinear_basis (j : Fin 4) : fullSquareLinear j (basis j)=2 := by
  rw [fullSquareLinear_apply]
  fin_cases j <;> norm_num [fullSquare,basis,Fin.sum_univ_succ]

theorem selectedSquareLinear_basis (p : Policy) (j : Fin 4) :
    selectedSquareLinear p j (basis j)=(if Selected p j then 1 else 0)+2 := by
  rw [selectedSquareLinear_apply]
  unfold selectedSquare
  rw [selectedMass_basis]
  have hsum : (∑ i : Fin 4, if i.val<j.val ∧ ¬Selected p i then basis j i else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hij : i=j
    · subst i
      simp
    · simp [basis,hij]
  rw [hsum]
  simp [basis]

theorem sumLinear_basis (i : Fin 4) : sumLinear (basis i)=1 := by
  rw [sumLinear_apply]
  fin_cases i <;> norm_num [U11SelectedLargest.prefixSum,basis]

theorem capLinear_basis (p : Policy) (left : Bool) (i : Fin 4) :
    capLinear p left (basis i)=
      if p.val<15 then (if left then (1/2:ℝ) else -(3/2:ℝ))*
        (if Selected p i then 1 else 0)
      else -(3/8:ℝ)*(if (2 : Fin 4)=i then 1 else 0) := by
  simp [capLinear,selectedLinear_basis,basis,smul_eq_mul]

/-- The cap-half gate has a proper wall for each of the sixteen policies. -/
theorem capLinear_ne_zero (p : Policy) (left : Bool) : capLinear p left ≠ 0 := by
  intro hz
  by_cases hp : p.val<15
  · obtain ⟨i,hi⟩ := exists_selected p hp
    have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis i)) hz
    rw [capLinear_basis] at he
    simp only [hp,if_true,hi,ContinuousLinearMap.zero_apply] at he
    cases left <;> norm_num at he
  · have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis 2)) hz
    rw [capLinear_basis] at he
    norm_num [hp] at he

def halfGate (p : Policy) (left : Bool) : LogFour →L[ℝ] ℝ := -capLinear p left

def fullGate (p : Policy) (left : Bool) (j : Fin 4) : LogFour →L[ℝ] ℝ :=
  fullSquareLinear j-capLinear p left

def selectedGate (p : Policy) (left : Bool) (j : Fin 4) : LogFour →L[ℝ] ℝ :=
  selectedSquareLinear p j-capLinear p left

def branchGate (p : Policy) : LogFour →L[ℝ] ℝ := capLinear p true-capLinear p false

def highKnotGate (p : Policy) (left : Bool) (j : Fin 201) : LogFour →L[ℝ] ℝ :=
  capLinear p left-sumLinear-floorGrid j.val • ContinuousLinearMap.proj 3

def wExtraGate (left : Bool) : LogFour →L[ℝ] ℝ :=
  (1/2:ℝ) • ContinuousLinearMap.proj 0-capLinear wPolicy left

theorem halfGate_ne_zero (p : Policy) (left : Bool) : halfGate p left ≠ 0 := by
  exact neg_ne_zero.mpr (capLinear_ne_zero p left)

/-- The integer square coefficient 2 cannot equal a selected half-cap
coefficient (0,1/2,-3/2), nor the W coefficient (0,-3/8). -/
theorem fullGate_ne_zero (p : Policy) (left : Bool) (j : Fin 4) :
    fullGate p left j ≠ 0 := by
  intro hz
  have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis j)) hz
  simp only [fullGate,ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,
    fullSquareLinear_basis,capLinear_basis] at he
  split_ifs at he <;> norm_num at he

/-- Selected-square coefficients at their own coordinate are 2 or 3;
this proves properness even before restricting to unselected j. -/
theorem selectedGate_ne_zero (p : Policy) (left : Bool) (j : Fin 4) :
    selectedGate p left j ≠ 0 := by
  intro hz
  have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis j)) hz
  simp only [selectedGate,ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,
    selectedSquareLinear_basis,capLinear_basis] at he
  split_ifs at he <;> norm_num at he

theorem branchGate_ne_zero (p : Policy) (hp : p.val<15) : branchGate p ≠ 0 := by
  obtain ⟨i,hi⟩ := exists_selected p hp
  intro hz
  have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis i)) hz
  simp only [branchGate,ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,
    capLinear_basis] at he
  norm_num [hp,hi] at he

/-- The W policy has ONE cap branch: its artificial true/false difference
is zero, and is explicitly excluded from the proper branch-wall theorem. -/
theorem w_branchGate_eq_zero : branchGate wPolicy=0 := by
  simp [branchGate,capLinear,wPolicy]

/-- Coordinate zero separates all actual cap-minus-prefix walls from
zero. The smallest-coordinate knot term vanishes on this test vector. -/
theorem highKnotGate_ne_zero (p : Policy) (left : Bool) (j : Fin 201)
    (_hj : 50<j.val) : highKnotGate p left j ≠ 0 := by
  intro hz
  have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis 0)) hz
  simp only [highKnotGate,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.zero_apply,smul_eq_mul,
    sumLinear_basis,capLinear_basis] at he
  norm_num [basis] at he
  split_ifs at he <;> norm_num at he

theorem wExtraGate_ne_zero (left : Bool) : wExtraGate left ≠ 0 := by
  intro hz
  have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis 0)) hz
  norm_num [wExtraGate,capLinear,wPolicy,basis,smul_eq_mul] at he

theorem coordinateGate_ne_zero (i : Fin 4) :
    (ContinuousLinearMap.proj i : LogFour →L[ℝ] ℝ) ≠ 0 := by
  intro hz
  have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis i)) hz
  norm_num [basis] at he

/-- Exact affine dictionaries for the original literal strict tests. -/
theorem halfGate_dictionary (p : Policy) (left : Bool) (v : LogFour) :
    (1/2:ℝ)<affineCap p left v ↔
      halfGate p left v<capOffset p left-1/2 := by
  simp only [affineCap,halfGate,ContinuousLinearMap.neg_apply]
  linarith

theorem fullGate_dictionary (p : Policy) (left : Bool) (j : Fin 4) (v : LogFour) :
    fullSquare j v<affineCap p left v ↔ fullGate p left j v<capOffset p left := by
  simp only [affineCap,fullGate,ContinuousLinearMap.sub_apply,fullSquareLinear_apply]
  linarith

theorem selectedGate_dictionary (p : Policy) (left : Bool) (j : Fin 4) (v : LogFour) :
    selectedSquare p j v<affineCap p left v ↔ selectedGate p left j v<capOffset p left := by
  simp only [affineCap,selectedGate,ContinuousLinearMap.sub_apply,selectedSquareLinear_apply]
  linarith

theorem branchGate_dictionary (p : Policy) (v : LogFour) :
    affineCap p true v≤affineCap p false v ↔
      branchGate p v≤capOffset p false-capOffset p true := by
  simp only [affineCap,branchGate,ContinuousLinearMap.sub_apply]
  linarith

theorem wExtraGate_dictionary (left : Bool) (v : LogFour) :
    (1+v 0)/2<affineCap wPolicy left v ↔
      wExtraGate left v<capOffset wPolicy left-1/2 := by
  simp only [affineCap,wExtraGate,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  linarith

theorem highKnotGate_dictionary (p : Policy) (left : Bool) (j : Fin 201) (v : LogFour)
    (hbranch : cap p v=affineCap p left v) :
    typedResidual p v=floorGrid j.val*v 3 ↔
      highKnotGate p left j v= -capOffset p left := by
  simp only [typedResidual,hbranch,affineCap,highKnotGate,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,sumLinear_apply]
  linarith

/-- Original high-knot query, with no supplied form-properness premise.
The separate max-two clamp is never identified with this equality wall. -/
theorem max_query_highKnot_dictionary (p : Policy) (left : Bool) (j : Fin 201)
    (hj : 50<j.val) (v : LogFour) (hw : 0<v 3)
    (hbranch : cap p v=affineCap p left v) :
    max 2 (typedResidual p v/v 3)=floorGrid j.val ↔
      highKnotGate p left j v= -capOffset p left := by
  have hjR : (50:ℝ)<(j.val:ℝ) := by exact_mod_cast hj
  have hgrid : (2:ℝ)<floorGrid j.val := by dsimp [floorGrid]; linarith
  rw [←highKnotGate_dictionary p left j v hbranch]
  constructor
  · intro heq
    have hq : 2≤typedResidual p v/v 3 := by
      by_contra hn
      have hm := max_eq_left (le_of_lt (lt_of_not_ge hn))
      rw [hm] at heq
      linarith
    have hqeq : typedResidual p v/v 3=floorGrid j.val := by
      simpa only [max_eq_right hq] using heq
    exact (div_eq_iff hw.ne').1 hqeq
  · intro heq
    have hqeq : typedResidual p v/v 3=floorGrid j.val := (div_eq_iff hw.ne').2 heq
    rw [hqeq,max_eq_right hgrid.le]

end

end ImbalancedChen.P5Z.U1011OriginalSixteenWalls
