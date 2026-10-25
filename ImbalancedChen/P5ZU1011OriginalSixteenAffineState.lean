import ImbalancedChen.P5ZU1011OriginalSixteenEligibilityState
import ImbalancedChen.P5ZU1011H248CommonPartition
import ImbalancedChen.P5ZU1011OriginalSixteenStateKernel

/-!
# Complete actual sixteen-policy mixed-affine common state

Every actual min(A,C) branch and first-failed eligibility state is retained.
Eligible policies have exactly302 reachable max-two H248 states: the full
clamp half-space,150open cells,150higher knots and zero exterior. Ineligible
policies have one canonical exterior tag. The nonlinear bank is partitioned
geometrically before any mean; no generic402-state theorem is specialized.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenAffineState

noncomputable section
open Set MeasureTheory
open Classical
open U11Integral U11H248 U1011H248Clamp U1011H248Partition
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenEligibilityState
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary

/-- Clamp, open50..199, knots51..200, exterior. -/
abbrev QueryState := Unit ⊕ Fin 150 ⊕ Fin 150 ⊕ Unit

def clampState : QueryState := .inl ()
def openState (i : Fin 150) : QueryState := .inr (.inl i)
def knotState (j : Fin 150) : QueryState := .inr (.inr (.inl j))
def exteriorState : QueryState := .inr (.inr (.inr ()))

def openIndex (i : Fin 150) : Fin 200 := ⟨i.val+50,by omega⟩
def knotIndex (j : Fin 150) : Fin 201 := ⟨j.val+51,by omega⟩

def atomOf : QueryState → AtomState
  | .inl _ => some (.inr clampKnot)
  | .inr (.inl i) => some (.inl (openIndex i))
  | .inr (.inr (.inl j)) => some (.inr (knotIndex j))
  | .inr (.inr (.inr _)) => none

theorem queryState_card : Fintype.card QueryState=302 := by norm_num [QueryState]

theorem clamp_state_value : stateValue (atomOf clampState)=
    min (floorValue H248Numerators 49) (floorValue H248Numerators 50) := by
  change floorKnotValue H248Numerators clampKnot=_
  exact clampKnot_value H248Numerators

theorem atomOf_injective : Function.Injective atomOf := by
  intro s t h
  rcases s with a | i | j | a <;> rcases t with b | k | l | b <;>
    simp [atomOf,openIndex,knotIndex,clampKnot,Fin.ext_iff] at h ⊢ <;> omega

/-- Direct scalar coverage of reachable max-two states. Queries below two
all belong to clamp50; below-two table atoms never create extra owners. -/
theorem exists_queryState (x : ℝ) : ∃ q : QueryState, x ∈ scalarCell (atomOf q) := by
  by_cases htwo : x ≤ 2
  · refine ⟨clampState,?_⟩
    change max 2 x ∈ Icc (1 : ℝ) 5 ∧ max 2 x=floorGrid 50
    rw [max_eq_left htwo,floorGrid_fifty]
    norm_num
  · have htwo' : (2 : ℝ)<x := lt_of_not_ge htwo
    by_cases hfive : 5<x
    · exact ⟨exteriorState,(mem_scalarCell_none_iff x).2 hfive⟩
    · obtain ⟨b,hb⟩ := exists_upperAtom_of_mem (s := x)
        (show x ∈ Icc (1 : ℝ) 5 from ⟨by linarith,le_of_not_gt hfive⟩)
      cases b with
      | inl i =>
          have hi : 50≤i.val := by
            by_contra hn
            have hval : (i.val : ℝ)+1≤50 := by
              exact_mod_cast (show i.val+1≤50 by omega)
            have hh := hb.2.2
            simp only [floorGrid,Nat.cast_add,Nat.cast_one] at hh
            linarith
          let k : Fin 150 := ⟨i.val-50,by omega⟩
          have hk : openIndex k=i := by apply Fin.ext; dsimp [openIndex,k]; omega
          refine ⟨openState k,?_⟩
          change max 2 x ∈ upperAtomSet (.inl (openIndex k))
          rw [hk,max_eq_right htwo'.le]
          exact hb
      | inr j =>
          have hj : 50<j.val := by
            by_contra hn
            have hval : (j.val : ℝ)≤50 := by exact_mod_cast (show j.val≤50 by omega)
            have hh : x=floorGrid j.val := hb.2
            dsimp only [floorGrid] at hh
            linarith
          let k : Fin 150 := ⟨j.val-51,by omega⟩
          have hk : knotIndex k=j := by apply Fin.ext; dsimp [knotIndex,k]; omega
          refine ⟨knotState k,?_⟩
          change max 2 x ∈ upperAtomSet (.inr (knotIndex k))
          rw [hk,max_eq_right htwo'.le]
          exact hb

def chosenQueryState (x : ℝ) : QueryState := Classical.choose (exists_queryState x)

theorem chosenQueryState_mem (x : ℝ) : x ∈ scalarCell (atomOf (chosenQueryState x)) :=
  Classical.choose_spec (exists_queryState x)

theorem queryState_unique {x : ℝ} {q r : QueryState}
    (hq : x ∈ scalarCell (atomOf q)) (hr : x ∈ scalarCell (atomOf r)) : q=r :=
  atomOf_injective (scalarCell_unique hq hr)

def residualLinear (p : Policy) (b : Bool) : LogFour →L[ℝ] ℝ := capLinear p b-sumLinear

def residualForm (p : Policy) (b : Bool) (q : ℝ) : LogFour →L[ℝ] ℝ :=
  residualLinear p b-q • ContinuousLinearMap.proj 3

def affineResidual (p : Policy) (b : Bool) (v : LogFour) : ℝ :=
  affineCap p b v-U11SelectedLargest.prefixSum v

theorem affineResidual_apply (p : Policy) (b : Bool) (v : LogFour) :
    affineResidual p b v=residualLinear p b v+capOffset p b := by
  simp only [affineResidual,affineCap,residualLinear,ContinuousLinearMap.sub_apply,sumLinear_apply]
  ring

theorem residualForm_apply (p : Policy) (b : Bool) (q : ℝ) (v : LogFour) :
    residualForm p b q v=affineResidual p b v-capOffset p b-q*v 3 := by
  simp only [residualForm,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,affineResidual_apply]
  ring

def upperGate (p : Policy) (b : Bool) (q : ℝ) (strict : Bool) : MixedGate :=
  ⟨residualForm p b q,-capOffset p b,strict⟩

def lowerGate (p : Policy) (b : Bool) (q : ℝ) (strict : Bool) : MixedGate :=
  ⟨-residualForm p b q,capOffset p b,strict⟩

theorem upperGate_strict_iff (p : Policy) (b : Bool) (q : ℝ) (v : LogFour) :
    (upperGate p b q true).Holds v ↔ affineResidual p b v<q*v 3 := by
  simp only [upperGate,MixedGate.Holds,if_true,residualForm_apply]
  linarith

theorem upperGate_weak_iff (p : Policy) (b : Bool) (q : ℝ) (v : LogFour) :
    (upperGate p b q false).Holds v ↔ affineResidual p b v≤q*v 3 := by
  simp only [upperGate,MixedGate.Holds,Bool.false_eq_true,if_false,residualForm_apply]
  linarith

theorem lowerGate_strict_iff (p : Policy) (b : Bool) (q : ℝ) (v : LogFour) :
    (lowerGate p b q true).Holds v ↔ q*v 3<affineResidual p b v := by
  simp only [lowerGate,MixedGate.Holds,if_true,ContinuousLinearMap.neg_apply,residualForm_apply]
  linarith

theorem lowerGate_weak_iff (p : Policy) (b : Bool) (q : ℝ) (v : LogFour) :
    (lowerGate p b q false).Holds v ↔ q*v 3≤affineResidual p b v := by
  simp only [lowerGate,MixedGate.Holds,Bool.false_eq_true,if_false,
    ContinuousLinearMap.neg_apply,residualForm_apply]
  linarith

/-- A table query gives at most two actual affine gates. Knot equality is
two weak rows; clamp50 is one FULL weak half-space, not an equality. -/
def queryGates (p : Policy) (b : Bool) : QueryState → Fin 2 → MixedGate
  | .inl _ => ![upperGate p b 2 false,trueGate]
  | .inr (.inl i) => ![lowerGate p b (floorGrid (openIndex i).val) true,
      upperGate p b (floorGrid ((openIndex i).val+1)) true]
  | .inr (.inr (.inl j)) => ![upperGate p b (floorGrid (knotIndex j).val) false,
      lowerGate p b (floorGrid (knotIndex j).val) false]
  | .inr (.inr (.inr _)) => ![lowerGate p b 5 true,trueGate]

def queryCell (p : Policy) (b : Bool) (q : QueryState) : Set LogFour :=
  {v | affineResidual p b v/v 3 ∈ scalarCell (atomOf q)}

theorem queryCell_iff_affine_gates (p : Policy) (b : Bool) (q : QueryState)
    (v : LogFour) (hw : 0<v 3) :
    v ∈ queryCell p b q ↔ ∀ i : Fin 2, (queryGates p b q i).Holds v := by
  rcases q with u | i | j | u
  · simpa [queryCell,atomOf,queryGates,Fin.forall_fin_succ,upperGate_weak_iff,
      MixedGate.Holds,trueGate] using
      mem_scalarCell_clamp_iff (affineResidual p b v) (v 3) hw
  · simpa [queryCell,atomOf,queryGates,Fin.forall_fin_succ,lowerGate_strict_iff,
      upperGate_strict_iff] using
      mem_scalarCell_open_iff (openIndex i) (by dsimp [openIndex]; omega)
        (affineResidual p b v) (v 3) hw
  · have hh := mem_scalarCell_knot_iff (knotIndex j) (by dsimp [knotIndex]; omega)
      (affineResidual p b v) (v 3) hw
    simpa [queryCell,atomOf,queryGates,Fin.forall_fin_succ,upperGate_weak_iff,
      lowerGate_weak_iff,le_antisymm_iff] using hh
  · have hh : affineResidual p b v/v 3 ∈ scalarCell none ↔ 5*v 3<affineResidual p b v :=
      (mem_scalarCell_none_iff _).trans (lt_div_iff₀ hw)
    simpa [queryCell,atomOf,queryGates,Fin.forall_fin_succ,lowerGate_strict_iff,
      MixedGate.Holds,trueGate] using hh

theorem queryCell_clamp_iff (p : Policy) (b : Bool) (v : LogFour) (hw : 0<v 3) :
    v ∈ queryCell p b clampState ↔ affineResidual p b v≤2*v 3 :=
  mem_scalarCell_clamp_iff (affineResidual p b v) (v 3) hw

structure State where
  policies : Policy → PolicyState
  query : Policy → QueryState

def stateEquiv : State ≃ ((Policy → PolicyState) × (Policy → QueryState)) where
  toFun s := (s.policies,s.query)
  invFun s := ⟨s.1,s.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

instance : Fintype State := Fintype.ofEquiv _ stateEquiv.symm
instance : DecidableEq State := Classical.decEq _

theorem state_ext {s t : State} (hp : s.policies=t.policies) (hq : s.query=t.query) : s=t := by
  cases s
  cases t
  cases hp
  cases hq
  rfl

/-- The ineligible atom has one canonical value. This prevents spurious
multiple state owners for a policy whose candidate is switched fallback. -/
def commonCell (s : State) : Set LogFour :=
  {v | 0<v 3 ∧ ∀ p : Policy,
    v ∈ policyCell p (s.policies p) ∧
      if (s.policies p).2=none then v ∈ queryCell p (s.policies p).1 (s.query p)
      else s.query p=exteriorState}

def chosenState (v : LogFour) : State where
  policies p := chosenPolicyState p v
  query p := if (chosenPolicyState p v).2=none then
    chosenQueryState (affineResidual p (chosenPolicyState p v).1 v/v 3) else exteriorState

theorem chosenState_mem (v : LogFour) (hw : 0<v 3) : v ∈ commonCell (chosenState v) := by
  refine ⟨hw,?_⟩
  intro p
  refine ⟨chosenPolicyState_mem p v,?_⟩
  by_cases he : (chosenPolicyState p v).2=none
  · simpa [commonCell,chosenState,he,queryCell] using
      chosenQueryState_mem (affineResidual p (chosenPolicyState p v).1 v/v 3)
  · simp [chosenState,he]

theorem commonCell_unique {s t : State} {v : LogFour}
    (hs : v ∈ commonCell s) (ht : v ∈ commonCell t) : s=t := by
  have hp : s.policies=t.policies := by
    funext p
    exact policyCell_unique (hs.2 p).1 (ht.2 p).1
  apply state_ext hp
  funext p
  have hps : s.policies p=t.policies p := congrFun hp p
  by_cases he : (s.policies p).2=none
  · have hqs : v ∈ queryCell p (s.policies p).1 (s.query p) := by
      simpa only [he,if_true] using (hs.2 p).2
    have hqt : v ∈ queryCell p (s.policies p).1 (t.query p) := by
      simpa only [← hps,he,if_true] using (ht.2 p).2
    exact queryState_unique hqs hqt
  · have hqs : s.query p=exteriorState := by simpa only [he,if_false] using (hs.2 p).2
    have hqt : t.query p=exteriorState := by
      simpa only [← hps,he,if_false] using (ht.2 p).2
    exact hqs.trans hqt.symm

theorem iUnion_commonCell : (⋃ s : State,commonCell s)={v : LogFour | 0<v 3} := by
  ext v
  constructor
  · intro hv
    obtain ⟨s,hs⟩ := Set.mem_iUnion.mp hv
    exact hs.1
  · intro hw
    exact Set.mem_iUnion.mpr ⟨chosenState v,chosenState_mem v hw⟩

/-- Positive smallest coordinate, then all16 concatenated actual policy
and query gates. No same-cell bound or bank correctness premise. -/
abbrev CommonGateSlot := Unit ⊕ (Policy × (GateSlot ⊕ Fin 2))

theorem commonGateSlot_card : Fintype.card CommonGateSlot=241 := by
  norm_num [CommonGateSlot,GateSlot,Test,Policy]

def positiveGate : MixedGate := ⟨-ContinuousLinearMap.proj 3,0,true⟩

theorem positiveGate_iff (v : LogFour) : positiveGate.Holds v ↔ 0<v 3 := by
  simp only [positiveGate,MixedGate.Holds,if_true,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.proj_apply]
  linarith

def commonGates (s : State) : CommonGateSlot → MixedGate
  | .inl _ => positiveGate
  | .inr (p,.inl k) => gateFamily p (s.policies p) k
  | .inr (p,.inr i) =>
      if (s.policies p).2=none then queryGates p (s.policies p).1 (s.query p) i
      else if s.query p=exteriorState then trueGate else falseGate

def commonAffineCell (s : State) : Set LogFour :=
  {v | ∀ k : CommonGateSlot,(commonGates s k).Holds v}

/-- The nonlinear actual bank's common state is exactly one finite mixed
affine region, with canonical ineligible tags enforced by constant rows. -/
theorem commonCell_eq_affineCell (s : State) : commonCell s=commonAffineCell s := by
  ext v
  constructor
  · rintro ⟨hw,hpol⟩ k
    cases k with
    | inl u => exact (positiveGate_iff v).2 hw
    | inr k =>
        rcases k with ⟨p,k⟩
        cases k with
        | inl k =>
            have hh : v ∈ affineCell p (s.policies p) := by
              rw [← policyCell_eq_affineCell]
              exact (hpol p).1
            exact hh k
        | inr i =>
            by_cases he : (s.policies p).2=none
            · have hq : v ∈ queryCell p (s.policies p).1 (s.query p) := by
                simpa only [he,if_true] using (hpol p).2
              have hh := (queryCell_iff_affine_gates p (s.policies p).1 (s.query p) v hw).1 hq i
              simpa only [commonGates,he,if_true] using hh
            · have hq : s.query p=exteriorState := by
                simpa only [he,if_false] using (hpol p).2
              simp [commonGates,he,hq,MixedGate.Holds,trueGate]
  · intro h
    have hw : 0<v 3 := (positiveGate_iff v).1 (h (.inl ()))
    refine ⟨hw,?_⟩
    intro p
    refine ⟨?_,?_⟩
    · rw [policyCell_eq_affineCell]
      intro k
      exact h (.inr (p,.inl k))
    · by_cases he : (s.policies p).2=none
      · simp only [he,if_true]
        apply (queryCell_iff_affine_gates p (s.policies p).1 (s.query p) v hw).2
        intro i
        simpa only [commonGates,he,if_true] using h (.inr (p,.inr i))
      · simp only [he,if_false]
        by_contra hq
        have hh := h (.inr (p,.inr 0))
        simp [commonGates,he,hq,MixedGate.Holds,falseGate] at hh

theorem measurableSet_commonCell (s : State) : MeasurableSet (commonCell s) := by
  rw [commonCell_eq_affineCell]
  exact MeasurableSet.iInter (fun k => MixedGate.measurableSet_holds (commonGates s k))

theorem commonCells_disjoint {s t : State} (hne : s≠t) :
    Disjoint (commonCell s) (commonCell t) :=
  Set.disjoint_left.mpr (fun v hs ht => hne (commonCell_unique hs ht))

/-- Exact map into the independently frozen actual16 nonlinear kernel
state. The active flag is computed from all actual eligibility tests. -/
def kernelState (s : State) : U1011OriginalSixteenStateKernel.State where
  branch p := (s.policies p).1
  active p := if (s.policies p).2=none then true else false
  atom p := atomOf (s.query p)

theorem commonCell_subset_kernelState (s : State) :
    commonCell s ⊆ U1011OriginalSixteenStateKernel.stateCell (kernelState s) := by
  intro v hv p
  have hpol := (hv.2 p).1
  have hcap := cap_eq_owned_affine hpol.1
  refine ⟨hcap,?_,?_⟩
  · have he := typedEligible_iff_status_none hpol
    by_cases hstatus : (s.policies p).2=none
    · have helig : TypedEligible p v := he.mpr hstatus
      simp [kernelState,hstatus,helig]
    · have helig : ¬TypedEligible p v := fun h => hstatus (he.mp h)
      simp [kernelState,hstatus,helig]
  · intro hactive
    have he : (s.policies p).2=none := by
      simpa [kernelState] using hactive
    have hq : v ∈ queryCell p (s.policies p).1 (s.query p) := by
      simpa only [he,if_true] using (hv.2 p).2
    simpa only [queryCell,typedResidual,hcap,affineResidual,kernelState] using hq

def originalCell (mask : Set (ℝ×ℝ)) (s : State) : Set LogFour :=
  originalDomain mask ∩ commonCell s

theorem originalCell_subset_kernelState (mask : Set (ℝ×ℝ)) (s : State) :
    originalCell mask s ⊆ originalDomain mask ∩
      U1011OriginalSixteenStateKernel.stateCell (kernelState s) := by
  intro v hv
  exact ⟨hv.1,commonCell_subset_kernelState s hv.2⟩

theorem measurableSet_originalCell (mask : Set (ℝ×ℝ)) (hm : MeasurableSet mask) (s : State) :
    MeasurableSet (originalCell mask s) :=
  (U11Integral.measurableSet_originalDomain mask hm).inter (measurableSet_commonCell s)

/-- Exact cover of the ORIGINAL domain, including every retained mask
point. The positive smallest coordinate follows from that domain itself. -/
theorem iUnion_originalCell (mask : Set (ℝ×ℝ)) :
    (⋃ s : State,originalCell mask s)=originalDomain mask := by
  ext v
  constructor
  · intro hv
    obtain ⟨s,hs⟩ := Set.mem_iUnion.mp hv
    exact hs.1
  · intro hv
    have hw := (originalDomain_denominators_pos mask v hv).1
    exact Set.mem_iUnion.mpr ⟨chosenState v,hv,chosenState_mem v hw⟩

/-- The actual H lookup on each eligible policy has its literal scalar
value. Clamp50 retains the adjacent minimum and the entire weak cell. -/
theorem H248_eq_queryState {s : State} {v : LogFour} (hv : v ∈ commonCell s)
    (p : Policy) (he : TypedEligible p v) :
    H248 (max 2 (typedResidual p v/v 3))=stateValue (atomOf (s.query p)) := by
  have hpol := (hv.2 p).1
  have hs := (typedEligible_iff_status_none hpol).1 he
  have hq : v ∈ queryCell p (s.policies p).1 (s.query p) := by
    simpa only [hs,if_true] using (hv.2 p).2
  have hcap := cap_eq_owned_affine hpol.1
  apply H248_eq_stateValue
  simpa only [queryCell,typedResidual,hcap,affineResidual] using hq

/-- The eligible clamp state keeps the entire positive-width band
w<L<=2w and the adjacent-min table value. It is never replaced by L=2w. -/
theorem eligible_clamp_dictionary {s : State} {v : LogFour} (hv : v ∈ commonCell s)
    (p : Policy) (he : TypedEligible p v) (hc : s.query p=clampState) :
    v 3<typedResidual p v ∧ typedResidual p v≤2*v 3 ∧
      H248 (max 2 (typedResidual p v/v 3))=
        min (floorValue H248Numerators 49) (floorValue H248Numerators 50) := by
  have hpol := (hv.2 p).1
  have hs := (typedEligible_iff_status_none hpol).1 he
  have hq : v ∈ queryCell p (s.policies p).1 clampState := by
    simpa only [hs,if_true,hc] using (hv.2 p).2
  have hcap := cap_eq_owned_affine hpol.1
  have hupper := (queryCell_clamp_iff p (s.policies p).1 v hv.1).1 hq
  refine ⟨typedEligible_residual_gt_smallest p v he,?_,?_⟩
  · simpa only [typedResidual,hcap,affineResidual] using hupper
  · rw [H248_eq_queryState hv p he,hc,clamp_state_value]

/-- Exact state-kernel equality on the original domain, obtained from
the actual eligibility and query geometry rather than an hMean premise. -/
theorem actualMinimum_eq_kernel {s : State} {v : LogFour} (mask : Set (ℝ×ℝ))
    (hv : v ∈ originalCell mask s) :
    U1011OriginalSixteenStateKernel.actualMinimum v=
      U1011OriginalSixteenStateKernel.frozenMinimum (kernelState s) v :=
  U1011OriginalSixteenStateKernel.actualMinimum_eq_frozen (kernelState s) mask hv.1
    (commonCell_subset_kernelState s hv.2)

end
end ImbalancedChen.P5Z.U1011OriginalSixteenAffineState
