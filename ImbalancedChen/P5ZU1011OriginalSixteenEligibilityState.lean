import ImbalancedChen.P5ZU1011OriginalSixteenPolicyBank

/-!
# Actual sixteen-policy cap ownership and first-failed eligibility cells

The literal bank has fifteen selected min(A,C) policies and one W policy.
Cap ties belong to the left branch; W has exactly one canonical branch.
Every eligibility test is an actual affine gate. A failed policy owns the
first failed literal test, with weak failure and strict earlier successes.
No generic 402-state partition or nonlinear-min interchange is used.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenEligibilityState

noncomputable section
open Set MeasureTheory
open Classical
open U11Integral U1011OriginalSixteenPolicyBank

abbrev Test := Fin 11
abbrev Status := Option Test
abbrev PolicyState := Bool × Status

def branchOwned (p : Policy) (b : Bool) (v : LogFour) : Prop :=
  if p.val<15 then
    if b then affineCap p true v ≤ affineCap p false v
    else affineCap p false v < affineCap p true v
  else b=true

theorem exists_branchOwned (p : Policy) (v : LogFour) : ∃ b, branchOwned p b v := by
  by_cases hp : p.val<15
  · by_cases h : affineCap p true v ≤ affineCap p false v
    · exact ⟨true,by simpa [branchOwned,hp] using h⟩
    · exact ⟨false,by simpa [branchOwned,hp] using lt_of_not_ge h⟩
  · exact ⟨true,by simp [branchOwned,hp]⟩

theorem branchOwned_unique {p : Policy} {v : LogFour} {b c : Bool}
    (hb : branchOwned p b v) (hc : branchOwned p c v) : b=c := by
  by_cases hp : p.val<15
  · cases b <;> cases c <;> simp [branchOwned,hp] at hb hc ⊢ <;> linarith
  · have hbt : b=true := by simpa [branchOwned,hp] using hb
    have hct : c=true := by simpa [branchOwned,hp] using hc
    exact hbt.trans hct.symm

theorem cap_eq_owned_affine {p : Policy} {b : Bool} {v : LogFour}
    (hb : branchOwned p b v) : cap p v=affineCap p b v := by
  by_cases hp : p.val<15
  · cases b with
    | false =>
        have h : affineCap p false v<affineCap p true v := by simpa [branchOwned,hp] using hb
        simpa [hp,min_eq_right h.le] using cap_eq_affine_circuit p v
    | true =>
        have h : affineCap p true v≤affineCap p false v := by simpa [branchOwned,hp] using hb
        simpa [hp,min_eq_left h] using cap_eq_affine_circuit p v
  · have hbt : b=true := by simpa [branchOwned,hp] using hb
    subst b
    simpa [hp] using cap_eq_affine_circuit p v

/-- Literal test order: lower cap, four full squares, four unselected
squares, W balance, W x cutoff. Disabled tests are true, not fake failures. -/
def testPass (p : Policy) (b : Bool) (i : Test) (v : LogFour) : Prop :=
  ![(1/2:ℝ)<affineCap p b v,
    fullSquare 0 v<affineCap p b v,fullSquare 1 v<affineCap p b v,
    fullSquare 2 v<affineCap p b v,fullSquare 3 v<affineCap p b v,
    (p.val<15 ∧ ¬Selected p 0) → selectedSquare p 0 v<affineCap p b v,
    (p.val<15 ∧ ¬Selected p 1) → selectedSquare p 1 v<affineCap p b v,
    (p.val<15 ∧ ¬Selected p 2) → selectedSquare p 2 v<affineCap p b v,
    (p.val<15 ∧ ¬Selected p 3) → selectedSquare p 3 v<affineCap p b v,
    (¬p.val<15) → (1+v 0)/2<affineCap p b v,
    (¬p.val<15) → v 0<(25/128:ℝ)] i

def testEnabled (p : Policy) (i : Test) : Prop :=
  ![True,True,True,True,True,
    p.val<15 ∧ ¬Selected p 0,p.val<15 ∧ ¬Selected p 1,
    p.val<15 ∧ ¬Selected p 2,p.val<15 ∧ ¬Selected p 3,
    ¬p.val<15,¬p.val<15] i

def testLinear (p : Policy) (b : Bool) : Test → (LogFour →L[ℝ] ℝ) :=
  ![-capLinear p b,
    fullSquareLinear 0-capLinear p b,fullSquareLinear 1-capLinear p b,
    fullSquareLinear 2-capLinear p b,fullSquareLinear 3-capLinear p b,
    selectedSquareLinear p 0-capLinear p b,selectedSquareLinear p 1-capLinear p b,
    selectedSquareLinear p 2-capLinear p b,selectedSquareLinear p 3-capLinear p b,
    (1/2:ℝ) • ContinuousLinearMap.proj 0-capLinear p b,ContinuousLinearMap.proj 0]

def testOffset (p : Policy) (b : Bool) : Test → ℝ :=
  ![capOffset p b-1/2,capOffset p b,capOffset p b,capOffset p b,capOffset p b,
    capOffset p b,capOffset p b,capOffset p b,capOffset p b,
    capOffset p b-1/2,25/128]

private theorem half_gate_iff (p : Policy) (b : Bool) (v : LogFour) :
    (-capLinear p b) v<capOffset p b-1/2 ↔ (1/2:ℝ)<affineCap p b v := by
  simp only [ContinuousLinearMap.neg_apply,affineCap]
  linarith

private theorem cap_gate_iff (p : Policy) (b : Bool) (F : LogFour →L[ℝ] ℝ) (v : LogFour) :
    (F-capLinear p b) v<capOffset p b ↔ F v<affineCap p b v := by
  simp only [ContinuousLinearMap.sub_apply,affineCap]
  linarith

private theorem w_balance_gate_iff (p : Policy) (b : Bool) (v : LogFour) :
    ((1/2:ℝ) • ContinuousLinearMap.proj 0-capLinear p b) v<capOffset p b-1/2 ↔
      (1+v 0)/2<affineCap p b v := by
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,affineCap]
  linarith

theorem testPass_iff_affine (p : Policy) (b : Bool) (i : Test) (v : LogFour) :
    testPass p b i v ↔ (testEnabled p i → testLinear p b i v<testOffset p b i) := by
  fin_cases i <;>
    simp [testPass,testEnabled,testLinear,testOffset,half_gate_iff,cap_gate_iff,
      w_balance_gate_iff,fullSquareLinear_apply,selectedSquareLinear_apply]

theorem typedEligible_iff_all_tests {p : Policy} {b : Bool} {v : LogFour}
    (hb : branchOwned p b v) : TypedEligible p v ↔ ∀ i, testPass p b i v := by
  have hcap := cap_eq_owned_affine hb
  simp only [TypedEligible,hcap]
  by_cases hp : p.val<15 <;>
    simp [testPass,Fin.forall_fin_succ,hp,and_assoc]

def statusHolds (p : Policy) (b : Bool) : Status → LogFour → Prop
  | none,v => ∀ i, testPass p b i v
  | some j,v => ¬testPass p b j v ∧ ∀ i, i<j → testPass p b i v

theorem exists_statusHolds (p : Policy) (b : Bool) (v : LogFour) :
    ∃ s, statusHolds p b s v := by
  by_cases hall : ∀ i, testPass p b i v
  · exact ⟨none,hall⟩
  · let F : Finset Test := Finset.univ.filter (fun i => ¬testPass p b i v)
    have hF : F.Nonempty := by
      obtain ⟨i,hi⟩ := not_forall.mp hall
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    let j := F.min' hF
    have hj : j ∈ F := Finset.min'_mem F hF
    refine ⟨some j,(Finset.mem_filter.mp hj).2,?_⟩
    intro i hij
    by_contra hi
    have hiF : i ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
    have hji : j≤i := Finset.min'_le F i hiF
    exact (not_le_of_gt hij) hji

theorem statusHolds_unique {p : Policy} {b : Bool} {v : LogFour} {s t : Status}
    (hs : statusHolds p b s v) (ht : statusHolds p b t v) : s=t := by
  cases s with
  | none =>
      cases t with
      | none => rfl
      | some j => exact (ht.1 (hs j)).elim
  | some i =>
      cases t with
      | none => exact (hs.1 (ht i)).elim
      | some j =>
          rcases lt_trichotomy i j with h | h | h
          · exact (hs.1 (ht.2 i h)).elim
          · exact congrArg some h
          · exact (ht.1 (hs.2 j h)).elim

/-- A failed status really names an enabled original eligibility test. -/
theorem failed_test_enabled {p : Policy} {b : Bool} {j : Test} {v : LogFour}
    (h : statusHolds p b (some j) v) : testEnabled p j := by
  by_contra hn
  exact h.1 ((testPass_iff_affine p b j v).2 (fun hj => (hn hj).elim))

def policyCell (p : Policy) (s : PolicyState) : Set LogFour :=
  {v | branchOwned p s.1 v ∧ statusHolds p s.1 s.2 v}

def chosenBranch (p : Policy) (v : LogFour) : Bool := Classical.choose (exists_branchOwned p v)
def chosenStatus (p : Policy) (b : Bool) (v : LogFour) : Status :=
  Classical.choose (exists_statusHolds p b v)
def chosenPolicyState (p : Policy) (v : LogFour) : PolicyState :=
  (chosenBranch p v,chosenStatus p (chosenBranch p v) v)

theorem chosenPolicyState_mem (p : Policy) (v : LogFour) :
    v ∈ policyCell p (chosenPolicyState p v) :=
  ⟨Classical.choose_spec (exists_branchOwned p v),Classical.choose_spec (exists_statusHolds p _ v)⟩

theorem policyCell_unique {p : Policy} {v : LogFour} {s t : PolicyState}
    (hs : v ∈ policyCell p s) (ht : v ∈ policyCell p t) : s=t := by
  have hb : s.1=t.1 := branchOwned_unique hs.1 ht.1
  apply Prod.ext hb
  have hh : statusHolds p s.1 t.2 v := hb.symm ▸ ht.2
  exact statusHolds_unique hs.2 hh

theorem typedEligible_iff_status_none {p : Policy} {v : LogFour} {s : PolicyState}
    (hs : v ∈ policyCell p s) : TypedEligible p v ↔ s.2=none := by
  rw [typedEligible_iff_all_tests hs.1]
  cases hstatus : s.2 with
  | none =>
      have h := hs.2
      rw [hstatus] at h
      simp only [statusHolds] at h
      simp [hstatus,h]
  | some j =>
      have h := hs.2
      rw [hstatus] at h
      constructor
      · intro hall
        exact (h.1 (hall j)).elim
      · intro hn
        simp [hstatus] at hn

/-- Actual strict/weak affine gates. Failure is weak and branch ties stay
with left, so no boundary is dropped or assigned twice. -/
structure MixedGate where
  linear : LogFour →L[ℝ] ℝ
  offset : ℝ
  strict : Bool

def MixedGate.Holds (g : MixedGate) (v : LogFour) : Prop :=
  if g.strict then g.linear v<g.offset else g.linear v≤g.offset

def trueGate : MixedGate := ⟨0,1,true⟩
def falseGate : MixedGate := ⟨0,0,true⟩

def branchGate (p : Policy) (b : Bool) : MixedGate :=
  if p.val<15 then
    if b then ⟨capLinear p true-capLinear p false,capOffset p false-capOffset p true,false⟩
    else ⟨capLinear p false-capLinear p true,capOffset p true-capOffset p false,true⟩
  else if b then trueGate else falseGate

def passGate (p : Policy) (b : Bool) (i : Test) : MixedGate :=
  if testEnabled p i then ⟨testLinear p b i,testOffset p b i,true⟩ else trueGate

def failGate (p : Policy) (b : Bool) (i : Test) : MixedGate :=
  if testEnabled p i then ⟨-testLinear p b i,-testOffset p b i,false⟩ else falseGate

theorem branchGate_iff (p : Policy) (b : Bool) (v : LogFour) :
    (branchGate p b).Holds v ↔ branchOwned p b v := by
  by_cases hp : p.val<15 <;> cases b <;>
    simp [branchGate,branchOwned,MixedGate.Holds,trueGate,falseGate,hp,
      ContinuousLinearMap.sub_apply,affineCap] <;> linarith

theorem passGate_iff (p : Policy) (b : Bool) (i : Test) (v : LogFour) :
    (passGate p b i).Holds v ↔ testPass p b i v := by
  rw [testPass_iff_affine]
  by_cases hi : testEnabled p i <;> simp [passGate,MixedGate.Holds,trueGate,hi]

theorem failGate_iff (p : Policy) (b : Bool) (i : Test) (v : LogFour) :
    (failGate p b i).Holds v ↔ ¬testPass p b i v := by
  rw [testPass_iff_affine]
  by_cases hi : testEnabled p i
  · simp only [failGate,if_pos hi,MixedGate.Holds,Bool.false_eq_true,if_false,
      ContinuousLinearMap.neg_apply,hi,true_implies]
    linarith
  · simp [failGate,MixedGate.Holds,falseGate,hi]

/-- One cap-ownership row, eleven possible strict earlier tests, and one
weak first-failure row. This is an actual concatenation of affine gates. -/
abbrev GateSlot := Unit ⊕ Test ⊕ Unit

def relevant (s : Status) (i : Test) : Prop := match s with
  | none => True
  | some j => i<j

def gateFamily (p : Policy) (s : PolicyState) : GateSlot → MixedGate
  | .inl _ => branchGate p s.1
  | .inr (.inl i) => if relevant s.2 i then passGate p s.1 i else trueGate
  | .inr (.inr _) => match s.2 with
      | none => trueGate
      | some j => failGate p s.1 j

def affineCell (p : Policy) (s : PolicyState) : Set LogFour :=
  {v | ∀ k : GateSlot, (gateFamily p s k).Holds v}

theorem policyCell_eq_affineCell (p : Policy) (s : PolicyState) : policyCell p s=affineCell p s := by
  ext v
  rcases s with ⟨b,s⟩
  cases s with
  | none =>
      constructor
      · rintro ⟨hb,hs⟩ k
        cases k with
        | inl u => exact (branchGate_iff p b v).2 hb
        | inr k =>
            cases k with
            | inl i => simpa [gateFamily,relevant] using (passGate_iff p b i v).2 (hs i)
            | inr u => simp [gateFamily,MixedGate.Holds,trueGate]
      · intro h
        refine ⟨(branchGate_iff p b v).1 (h (.inl ())),?_⟩
        intro i
        apply (passGate_iff p b i v).1
        simpa [gateFamily,relevant] using h (.inr (.inl i))
  | some j =>
      constructor
      · rintro ⟨hb,hfail,hprev⟩ k
        cases k with
        | inl u => exact (branchGate_iff p b v).2 hb
        | inr k =>
            cases k with
            | inl i =>
                by_cases hi : i<j
                · simpa [gateFamily,relevant,hi] using (passGate_iff p b i v).2 (hprev i hi)
                · simp [gateFamily,relevant,hi,MixedGate.Holds,trueGate]
            | inr u => exact (failGate_iff p b j v).2 hfail
      · intro h
        refine ⟨(branchGate_iff p b v).1 (h (.inl ())),?_,?_⟩
        · exact (failGate_iff p b j v).1 (h (.inr (.inr ())))
        · intro i hi
          apply (passGate_iff p b i v).1
          simpa [gateFamily,relevant,hi] using h (.inr (.inl i))

theorem MixedGate.measurableSet_holds (g : MixedGate) : MeasurableSet {v | g.Holds v} := by
  cases h : g.strict
  · simpa [MixedGate.Holds,h] using measurableSet_le g.linear.continuous.measurable measurable_const
  · simpa [MixedGate.Holds,h] using measurableSet_lt g.linear.continuous.measurable measurable_const

theorem measurableSet_policyCell (p : Policy) (s : PolicyState) : MeasurableSet (policyCell p s) := by
  rw [policyCell_eq_affineCell]
  exact MeasurableSet.iInter (fun k => MixedGate.measurableSet_holds (gateFamily p s k))

end
end ImbalancedChen.P5Z.U1011OriginalSixteenEligibilityState
