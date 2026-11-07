import ImbalancedChen.P5ZU1011SelectedLargestKnotPayment
import ImbalancedChen.P5ZU1011FixedH248PrimeBox
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Original selected-largest policy: the actual two physical cap branches,
all ten full/selected-square inequalities, all402 scalar states, and the
complete unmasked original U11 support. Each resulting piece has its TRUE
prime harmonic limit, supplied by the actual affine-gate PNT theorem.
No cell mean, policy licence, AP estimate or H248 correctness is a premise.
This file concerns a fixed geometric support; no moving-mask limit occurs.
-/

namespace ImbalancedChen.P5Z.U1011SelectedLargestAllCellPrimeTests

noncomputable section
open Set MeasureTheory Filter Topology
open Classical
open U11Integral U11Canonical U11H248 U1011H248Partition
open U1011SelectedLargestKnotPayment
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

abbrev Cube : Set LogFour := univ.pi (fun _ : Fin 4 => Icc (417/5000:ℝ) (59/250:ℝ))

def mixed {r : ℕ} (F : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ)
    (weak : Fin r → Bool) : Set LogFour :=
  {v | ∀ j, if weak j then F j v ≤ c j else F j v < c j}

theorem measurableSet_mixed {r : ℕ} (F : Fin r → LogFour →L[ℝ] ℝ)
    (c : Fin r → ℝ) (weak : Fin r → Bool) : MeasurableSet (mixed F c weak) := by
  simp only [mixed, setOf_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : weak j = true
  · simp only [hj, ↓reduceIte]
    exact (isClosed_le (F j).continuous continuous_const).measurableSet
  · simp only [hj, ↓reduceIte]
    exact (isOpen_lt (F j).continuous continuous_const).measurableSet

theorem tendsto_prime_mixed {r : ℕ} (F : Fin r → LogFour →L[ℝ] ℝ)
    (c : Fin r → ℝ) (weak : Fin r → Bool) (hF : ∀ j, F j ≠ 0)
    (f : LogFour → ℝ) (hf : ContinuousOn f Cube) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ))
        ((mixed F c weak).indicator f)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417/5000:ℝ))
          (fun _ => (59/250:ℝ)) ∩ mixed F c weak, f v * ∏ i, 1/v i)) := by
  apply tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0:ℝ)<417/5000) (by norm_num : (417/5000:ℝ)<59/250)
    F c hF _ (measurableSet_mixed F c weak) ?_ ?_ f hf
  · intro v hv j
    by_cases hj : weak j = true
    · simpa only [hj, ↓reduceIte] using (hv j).le
    · simpa only [hj, ↓reduceIte] using hv j
  · intro v hv j
    by_cases hj : weak j = true
    · simpa only [hj, ↓reduceIte] using hv j
    · exact (by simpa only [hj, ↓reduceIte] using hv j : F j v < c j).le

def supportForms : Fin 6 → LogFour →L[ℝ] ℝ :=
  ![-ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 3-ContinuousLinearMap.proj 2,
    ContinuousLinearMap.proj 2-ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 1,-ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 0]
def supportBounds : Fin 6 → ℝ := ![-(417/5000:ℝ),0,0,19/125,-(19/125:ℝ),59/250]
def supportWeak : Fin 6 → Bool := ![true,false,false,false,true,false]

theorem support_dictionary (v : LogFour) :
    v ∈ mixed supportForms supportBounds supportWeak ↔ v ∈ originalDomain ∅ := by
  simp [mixed, supportForms, supportBounds, supportWeak, originalDomain,
    Fin.forall_fin_succ, neg_le_neg_iff]

theorem supportForms_ne_zero : ∀ j, supportForms j ≠ 0 := by
  intro j he
  have h0 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![1,0,0,0]) he
  have h1 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![0,1,0,0]) he
  have h2 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![0,0,1,0]) he
  have h3 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![0,0,0,1]) he
  fin_cases j <;> norm_num [supportForms] at *

def thresholdSlope : Fin 5 → LogFour →L[ℝ] ℝ :=
  ![0,2 • ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 0+2 • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 0+ContinuousLinearMap.proj 1+2 • ContinuousLinearMap.proj 2,
    prefixLinear+ContinuousLinearMap.proj 3]
def thresholdConstant : Fin 5 → ℝ := ![1/2,0,0,0,0]

def eligibleFormsCap (left : Bool) (i : Fin 5) : LogFour →L[ℝ] ℝ :=
  thresholdSlope i-capLinear left
def eligibleBoundsCap (left : Bool) (i : Fin 5) : ℝ :=
  capConstant left-thresholdConstant i
def eligibleForms : Fin (5+5) → LogFour →L[ℝ] ℝ :=
  Fin.append (eligibleFormsCap true) (eligibleFormsCap false)
def eligibleBounds : Fin (5+5) → ℝ :=
  Fin.append (eligibleBoundsCap true) (eligibleBoundsCap false)

theorem eligibleForms_ne_zero : ∀ j, eligibleForms j ≠ 0 := by
  have hcap (left : Bool) (i : Fin 5) : eligibleFormsCap left i ≠ 0 := by
    intro he
    have h0 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![1,0,0,0]) he
    have h1 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![0,1,0,0]) he
    cases left <;> fin_cases i <;>
      norm_num [eligibleFormsCap, thresholdSlope, capLinear, prefixLinear] at *
  simp only [eligibleForms, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  exact ⟨hcap true,hcap false⟩

def branchForm (left : Bool) : LogFour →L[ℝ] ℝ :=
  if left then capLinear true-capLinear false else capLinear false-capLinear true
def branchBound (left : Bool) : ℝ :=
  if left then capConstant false-capConstant true else capConstant true-capConstant false

theorem branchForm_ne_zero (left : Bool) : branchForm left ≠ 0 := by
  intro he
  have h0 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![1,0,0,0]) he
  cases left <;> norm_num [branchForm,capLinear] at h0

def branchCell (left : Bool) : Set LogFour :=
  mixed (fun _ : Fin 1 => branchForm left) (fun _ => branchBound left) (fun _ => left)

theorem branchCell_residual {left : Bool} {v : LogFour} (hv : v ∈ branchCell left) :
    U11SelectedLargest.residual 0 v = branchResidual left v := by
  have h := hv 0
  cases left
  · have hc : 57/64-(3/2:ℝ)*v 0 ≤ (1+v 0)/2 := by
      simp only [branchForm, branchBound, Bool.false_eq_true, if_false,
        capLinear, capConstant, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,smul_eq_mul] at h
      linarith
    rw [branchResidual_false]
    simp only [U11SelectedLargest.residual,U11SelectedLargest.cap,min_eq_right hc]
  · have hc : (1+v 0)/2 ≤ 57/64-(3/2:ℝ)*v 0 := by
      simp only [branchForm, branchBound, if_true, capLinear, capConstant,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul] at h
      linarith
    rw [branchResidual_true]
    simp only [U11SelectedLargest.residual,U11SelectedLargest.cap,min_eq_left hc]

def lowerKnot (i : Fin 200) : Fin 201 := ⟨i.val,by omega⟩
def upperKnot (i : Fin 200) : Fin 201 := ⟨i.val+1,by omega⟩
def twoKnot : Fin 201 := ⟨50,by norm_num⟩
def lastKnot : Fin 201 := ⟨200,by norm_num⟩
def minusW : LogFour →L[ℝ] ℝ := -ContinuousLinearMap.proj 3

/-- Four literal atom inequalities. Impossible below-clamp states remain
empty pieces; no serialized state is silently discarded. -/
def atomForms (left : Bool) : AtomState → Fin 4 → LogFour →L[ℝ] ℝ
  | none => ![-knotForm left lastKnot,minusW,minusW,minusW]
  | some (.inl i) => ![-knotForm left twoKnot,-knotForm left (lowerKnot i),
      knotForm left (upperKnot i),minusW]
  | some (.inr j) => if j.val=50 then
      ![knotForm left twoKnot,minusW,minusW,minusW]
    else ![-knotForm left twoKnot,knotForm left j,-knotForm left j,minusW]

def atomBounds (left : Bool) : AtomState → Fin 4 → ℝ
  | none => ![capConstant left,0,0,0]
  | some (.inl _) => ![capConstant left,capConstant left,-capConstant left,0]
  | some (.inr j) => if j.val=50 then ![-capConstant left,0,0,0]
    else ![capConstant left,-capConstant left,capConstant left,0]

def atomWeak : AtomState → Fin 4 → Bool
  | none => ![false,false,false,false]
  | some (.inl _) => ![false,false,false,false]
  | some (.inr j) => if j.val=50 then ![true,false,false,false]
    else ![true,true,true,false]

theorem atomForms_ne_zero (left : Bool) (state : AtomState) :
    ∀ j, atomForms left state j ≠ 0 := by
  have hm : minusW ≠ 0 := by
    intro he
    have h3 := congrArg (fun F : LogFour →L[ℝ] ℝ => F ![0,0,0,1]) he
    norm_num [minusW] at h3
  cases state with
  | none => intro j; fin_cases j <;> simp only [atomForms,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val] <;>
      first | exact hm | exact knotForm_ne_zero _ _ | exact neg_ne_zero.mpr (knotForm_ne_zero _ _)
  | some state =>
    cases state with
    | inl i => intro j; fin_cases j <;> simp only [atomForms,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val] <;>
        first | exact hm | exact knotForm_ne_zero _ _ | exact neg_ne_zero.mpr (knotForm_ne_zero _ _)
    | inr i =>
      by_cases hi : i.val=50 <;> intro j <;> fin_cases j <;>
        simp only [atomForms,hi,↓reduceIte,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val] <;>
        first | exact hm | exact knotForm_ne_zero _ _ | exact neg_ne_zero.mpr (knotForm_ne_zero _ _)

def pieceForms (left : Bool) (state : AtomState) : Fin (6+(10+(1+4))) → LogFour →L[ℝ] ℝ :=
  Fin.append supportForms (Fin.append eligibleForms
    (Fin.append (fun _ : Fin 1 => branchForm left) (atomForms left state)))
def pieceBounds (left : Bool) (state : AtomState) : Fin (6+(10+(1+4))) → ℝ :=
  Fin.append supportBounds (Fin.append eligibleBounds
    (Fin.append (fun _ : Fin 1 => branchBound left) (atomBounds left state)))
def pieceWeak (left : Bool) (state : AtomState) : Fin (6+(10+(1+4))) → Bool :=
  Fin.append supportWeak (Fin.append (fun _ : Fin 10 => false)
    (Fin.append (fun _ : Fin 1 => left) (atomWeak state)))
def piece (left : Bool) (state : AtomState) : Set LogFour :=
  mixed (pieceForms left state) (pieceBounds left state) (pieceWeak left state)

theorem pieceForms_ne_zero (left : Bool) (state : AtomState) :
    ∀ j, pieceForms left state j ≠ 0 := by
  simp only [pieceForms,Fin.forall_fin_add,Fin.append_left,Fin.append_right]
  exact ⟨supportForms_ne_zero,eligibleForms_ne_zero,
    (fun _ => branchForm_ne_zero left),atomForms_ne_zero left state⟩

theorem piece_components {left : Bool} {state : AtomState} {v : LogFour}
    (hv : v ∈ piece left state) :
    v ∈ originalDomain ∅ ∧ (∀ j, eligibleForms j v < eligibleBounds j) ∧
      v ∈ branchCell left ∧ v ∈ mixed (atomForms left state) (atomBounds left state) (atomWeak state) := by
  have hh := hv
  change (∀ j, if pieceWeak left state j then
    pieceForms left state j v ≤ pieceBounds left state j else
      pieceForms left state j v < pieceBounds left state j) at hh
  simp only [pieceWeak,pieceForms,pieceBounds,Fin.forall_fin_add,
    Fin.append_left,Fin.append_right,Bool.false_eq_true,if_false] at hh
  exact ⟨(support_dictionary v).1 hh.1,hh.2.1,hh.2.2.1,hh.2.2.2⟩

theorem piece_eligible {left : Bool} {state : AtomState} {v : LogFour}
    (hv : v ∈ piece left state) : U11SelectedLargest.eligible 0 v := by
  have he := (piece_components hv).2.1
  have ht (i : Fin 5) : thresholdSlope i v+thresholdConstant i < U11SelectedLargest.cap v := by
    have hl := he (Fin.castAdd 5 i)
    have hr := he (Fin.natAdd 5 i)
    simp only [eligibleForms,eligibleBounds,Fin.append_left,Fin.append_right,
      eligibleFormsCap,eligibleBoundsCap,ContinuousLinearMap.sub_apply] at hl hr
    apply lt_min
    · simp only [capLinear,capConstant,if_true,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul] at hl
      linarith
    · simp only [capLinear,capConstant,Bool.false_eq_true,if_false,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul] at hr
      linarith
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  have h3 := ht 3
  have h4 := ht 4
  simp only [thresholdSlope,thresholdConstant,prefixLinear,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,zero_add,add_zero] at h0 h1 h2 h3 h4
  exact ⟨rfl,h0,⟨h1,h2,h3,h4⟩,⟨h2,h3,h4⟩⟩

theorem piece_lookup {left : Bool} {state : AtomState} {v : LogFour}
    (hv : v ∈ piece left state) :
    H248 (max 2 (U11SelectedLargest.residual 0 v/v 3)) = stateValue state := by
  have hparts := piece_components hv
  have hw := (originalDomain_denominators_pos ∅ v hparts.1).1
  have hb := branchCell_residual hparts.2.2.1
  have ha := hparts.2.2.2
  have hbeta : branchLinear left v+capConstant left = U11SelectedLargest.residual 0 v := hb.symm
  cases state with
  | none =>
    have h0 := ha 0
    simp only [atomForms,atomBounds,atomWeak,Matrix.cons_val_zero,if_false,
      ContinuousLinearMap.neg_apply,knotForm,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
      lastKnot,floorGrid] at h0
    have hq : 5 < U11SelectedLargest.residual 0 v/v 3 := (lt_div_iff₀ hw).2 (by linarith)
    exact H248_eq_stateValue ((mem_scalarCell_none_iff _).2 hq)
  | some state =>
    cases state with
    | inl i =>
      have h0 := ha 0
      have h1 := ha 1
      have h2 := ha 2
      simp only [atomForms,atomBounds,atomWeak,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,if_false,ContinuousLinearMap.neg_apply,knotForm,
        ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul,twoKnot,lowerKnot,upperKnot] at h0 h1 h2
      have htwo : floorGrid 50 = (2:ℝ) := by norm_num [floorGrid]
      rw [htwo] at h0
      have hgrid : floorGrid (i.val+1) ≤ 5 := by
        have hi : i.val+1≤200 := by omega
        have hiR : (i.val:ℝ)+1≤200 := by exact_mod_cast hi
        simp only [floorGrid,Nat.cast_add,Nat.cast_one]
        linarith
      exact U1011FixedH248.H248_affine_open_cell i _ _ hw
        (by linarith) (by linarith) (by linarith) hgrid
    | inr j =>
      by_cases hj : j.val=50
      · have h0 := ha 0
        simp only [atomForms,atomBounds,atomWeak,if_pos hj,Matrix.cons_val_zero,if_true,
          knotForm,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.proj_apply,smul_eq_mul,twoKnot] at h0
        have htwo : floorGrid 50 = (2:ℝ) := by norm_num [floorGrid]
        rw [htwo] at h0
        have hj' : j=U1011H248Clamp.clampKnot := by apply Fin.ext; exact hj
        rw [hj']
        exact (U1011H248Clamp.H248_affine_clamp _ _ hw (by linarith)).trans
          (U1011H248Clamp.clampKnot_value H248Numerators).symm
      · have h0 := ha 0
        have h1 := ha 1
        have h2 := ha 2
        simp only [atomForms,atomBounds,atomWeak,if_neg hj,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val,if_true,ContinuousLinearMap.neg_apply,
          knotForm,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.proj_apply,smul_eq_mul,twoKnot] at h0 h1 h2
        have htwo : floorGrid 50 = (2:ℝ) := by norm_num [floorGrid]
        rw [htwo] at h0
        have heq : U11SelectedLargest.residual 0 v/v 3 = floorGrid j.val :=
          (div_eq_iff hw.ne').2 (by linarith)
        have hquery : max 2 (U11SelectedLargest.residual 0 v/v 3) = floorGrid j.val := by
          rw [max_eq_right ((le_div_iff₀ hw).2 (by linarith)),heq]
        have hjR : (j.val:ℝ)≤200 := by exact_mod_cast (show j.val≤200 by omega)
        have hgrid : floorGrid j.val ∈ Icc (1:ℝ) 5 := by
          constructor <;> dsimp [floorGrid] <;> linarith [Nat.cast_nonneg j.val]
        exact H248_eq_stateValue (show U11SelectedLargest.residual 0 v/v 3 ∈
          scalarCell (some (.inr j)) from ⟨by rwa [hquery],hquery⟩)

def switched : LogFour → ℝ := switchedKernel currentK LiLiuPrereqBuchstab.buchstab
def pieceMinimum (state : AtomState) (v : LogFour) : ℝ :=
  min (switched v) (4*(1-stateValue state)/
    max (417/5000:ℝ) (U11SelectedLargest.residual 0 v))

theorem pieceMinimum_eq_actual {left : Bool} {state : AtomState} {v : LogFour}
    (hv : v ∈ piece left state) :
    pieceMinimum state v = min (switched v)
      (ordinaryKernel H248 U11SelectedLargest.residual 0 v) := by
  have hd := (piece_components hv).1
  have he := piece_eligible hv
  have hr := U11SelectedLargest.eligible_residual_gt_smallest ∅ 0 v hd he
  have hlo : (417/5000:ℝ) ≤ U11SelectedLargest.residual 0 v := hd.1.trans hr.le
  simp only [pieceMinimum,ordinaryKernel,max_eq_right hlo,piece_lookup hv]

theorem continuousOn_pieceMinimum (state : AtomState) : ContinuousOn (pieceMinimum state) Cube := by
  have hs : ContinuousOn switched Cube :=
    (continuousOn_canonical_switched_compactBox currentK).mono (by
      intro v hv
      exact ⟨fun j => (hv j (mem_univ _)).1,fun j => (hv j (mem_univ _)).2⟩)
  have hd : ContinuousOn (fun v => max (417/5000:ℝ) (U11SelectedLargest.residual 0 v)) Cube :=
    continuousOn_const.max (U11SelectedLargest.continuous_residual 0).continuousOn
  exact hs.min (continuousOn_const.div hd (fun v _ =>
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<417/5000)
      (le_max_left _ _)).ne'))

/-- ALL cap branches and ALL402 literal states have their actual
four-prime harmonic PNT mean. Every input here is original finite geometry
or a literal table state, rather than a whole-cell convergence hypothesis. -/
theorem tendsto_actual_allCell_piece (left : Bool) (state : AtomState) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ))
        ((piece left state).indicator (pieceMinimum state))) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417/5000:ℝ))
          (fun _ => (59/250:ℝ)) ∩ piece left state,
        pieceMinimum state v * ∏ i, 1/v i)) :=
  tendsto_prime_mixed (pieceForms left state) (pieceBounds left state) (pieceWeak left state)
    (pieceForms_ne_zero left state) (pieceMinimum state) (continuousOn_pieceMinimum state)

def actualMinimum (v : LogFour) : ℝ :=
  min (switched v) (ordinaryKernel H248 U11SelectedLargest.residual 0 v)

/-- Every actual physical branch and every table state, including the
positive-measure clamp and the zero exterior, transfers the ORIGINAL
nonlinear switched/ordinary minimum. No cell mean is a premise. -/
theorem tendsto_actual_original_allCell_piece (left : Bool) (state : AtomState) :
    Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417/5000:ℝ)) (fun _ => (59/250:ℝ))
        ((piece left state).indicator actualMinimum)) atTop
      (𝓝 (∫ v in logPrimeBox (fun _ : Fin 4 => (417/5000:ℝ))
          (fun _ => (59/250:ℝ)) ∩ piece left state,
        actualMinimum v * ∏ i, 1/v i)) := by
  have htest : (piece left state).indicator actualMinimum =
      (piece left state).indicator (pieceMinimum state) := by
    funext v
    by_cases hv : v ∈ piece left state
    · simp only [indicator_of_mem hv]
      exact (pieceMinimum_eq_actual hv).symm
    · simp only [indicator_of_notMem hv]
  have hint : (∫ v in logPrimeBox (fun _ : Fin 4 => (417/5000:ℝ))
      (fun _ => (59/250:ℝ)) ∩ piece left state, pieceMinimum state v * ∏ i, 1/v i) =
      ∫ v in logPrimeBox (fun _ : Fin 4 => (417/5000:ℝ))
        (fun _ => (59/250:ℝ)) ∩ piece left state, actualMinimum v * ∏ i, 1/v i := by
    apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter (measurableSet_mixed _ _ _))
    intro v hv
    rw [pieceMinimum_eq_actual hv.2]
  rw [htest,←hint]
  exact tendsto_actual_allCell_piece left state

end

end ImbalancedChen.P5Z.U1011SelectedLargestAllCellPrimeTests
