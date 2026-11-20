import ImbalancedChen.P2OriginalSixthPullingUnion

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
An exact affine-row presentation of the ORIGINAL PhysicalCell fields.
The nonstrict old licence fields are kept nonstrict, including their zero
identities. All strict fields are explicit. No geometric/source inclusion
or target integral bound is accepted as a record field or premise.
-/
namespace ImbalancedChen.P2OriginalSixthPhysicalGateRows
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthPullingUnion (Affine eval evalQ)
open P2OriginalSixthMomentRow (Point)
inductive Gate where
  | rpos | order (j : Fin 5) | largest | oldCutoff | compactCutoff
  | history3 | history5 | oldW | oldBranch (m : Fin 31) | first3Branch (m : Fin 7)
  | comparison | pairAbove | winner | positiveGap | selectedAscending | selectedDescending
  | fullSquare (j : Fin 6) | remainingSquare (j : Fin 6) | oldArgument | newArgument
  | priority (j : Fin 3)
  deriving DecidableEq, Fintype

def Gate.strict : Gate → Bool
  | .oldW | .oldBranch _ | .first3Branch _ | .comparison => false
  | _ => true

def value (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) : Gate → Point → ℝ
  | .rpos,t => t 5
  | .order j,t => t j.castSucc-t j.succ
  | .largest,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.mu-t 0
  | .oldCutoff,t => 1/50-t 5
  | .compactCutoff,t => t 5-53/4608
  | .history3,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.H3 t
  | .history5,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.H5 t
  | .oldW,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.W t
  | .oldBranch m,t => if c.descending (m.val+1) then
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t-(57/64-3*ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum (m.val+1) t/2)
      else 2*ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t-1-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum (m.val+1) t
  | .first3Branch m,t => if c.descending (m.val+1) then
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-(57/64-3*ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum (m.val+1) t/2)
      else 2*ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-1-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum (m.val+1) t
  | .comparison,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t
  | .pairAbove,t => if c.family=.pair17 ∨ c.family=.pair12 then ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t else 1
  | .winner,t => match c.family with
      | .pair17 => t 0+t 4-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.mu
      | .pair12 => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.mu-t 2-t 3
      | _ => 1
  | .positiveGap,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t
  | .selectedAscending,t => (1+ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.selectedSum c.selectedMask t)/2-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t
  | .selectedDescending,t => 57/64-3*ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.selectedSum c.selectedMask t/2-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t
  | .fullSquare j,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.fullSquare j t
  | .remainingSquare j,t => if ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit c.selectedMask j.val then 1
      else ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare c.selectedMask j t
  | .oldArgument,t => ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S6 t-t 5
  | .newArgument,t => 3*t 5-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newResidual c t
  | .priority j,t => match j.val with
      | 0 => if c=.singleton34_1371 ∨ c=.singleton50_1353 ∨ c=.singleton50_1355 then
          ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.descending33 t else 1
      | 1 => if c=.singleton50_1353 ∨ c=.singleton50_1355 then ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending34 t else 1
      | _ => if c.family=.tent33 then ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33 t else 1

def valid (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (g : Gate) (t : Point) : Prop :=
  if g.strict then 0 < value c g t else 0 ≤ value c g t

def constant (q : ℚ) : Affine := Fin.cons q (fun _ => 0)
def coord (j : Fin 6) : Affine := Fin.cons 0 (fun k => if k=j then 1 else 0)
def r0 : Affine := (1/2:ℚ) • (constant 1+coord 0)
def s5 : Affine := coord 0+coord 1+coord 2+coord 3+coord 4
def s6 : Affine := s5+coord 5
def h3 : Affine := coord 0+coord 1+(3:ℚ) • coord 2
def h5 : Affine := coord 0+coord 1+coord 2+coord 3+(3:ℚ) • coord 4
def w : Affine := constant (153/256)-(3/8:ℚ) • coord 2
def old (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) : Affine := match c.family with
  | .singleton | .tent33 => r0
  | .pair17 => constant (57/64)-(3/2:ℚ) • (coord 0+coord 4)
  | .pair12 => (1/2:ℚ) • (constant 1+coord 2+coord 3)
def clipped : Affine := s5+(4:ℚ) • coord 5-constant (1/1000000)
def asc33 : Affine := (1/2:ℚ) • (constant 1+coord 0+coord 5)
def desc33 : Affine := constant (57/64)-(3/2:ℚ) • (coord 0+coord 5)
def asc34 : Affine := (1/2:ℚ) • (constant 1+coord 1+coord 5)
def next (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) : Affine :=
  if c.family=.tent33 then asc33-constant (1/1000000) else clipped
def subset (m : ℕ) : Affine := ∑ j : Fin 5, if ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit m j.val then coord j.castSucc else 0
def selected (m : ℕ) : Affine := ∑ j : Fin 6, if ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit m j.val then coord j else 0
def square (j : Fin 6) : Affine :=
  (∑ k : Fin 6, if k<j then coord k else 0)+(2:ℚ) • coord j
def remaining (m : ℕ) (j : Fin 6) : Affine :=
  selected m+(∑ k : Fin 6, if k<j ∧ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit m k.val=false then coord k else 0)+(2:ℚ) • coord j

def row (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) : Gate → Affine
  | .rpos => coord 5
  | .order j => coord j.castSucc-coord j.succ
  | .largest => constant (25/128)-coord 0
  | .oldCutoff => constant (1/50)-coord 5
  | .compactCutoff => coord 5-constant (53/4608)
  | .history3 => r0-h3
  | .history5 => r0-h5
  | .oldW => r0-w
  | .oldBranch m => if c.descending (m.val+1) then old c-(constant (57/64)-(3/2:ℚ) • subset (m.val+1))
      else (2:ℚ) • old c-constant 1-subset (m.val+1)
  | .first3Branch m => if c.descending (m.val+1) then r0-(constant (57/64)-(3/2:ℚ) • subset (m.val+1))
      else (2:ℚ) • r0-constant 1-subset (m.val+1)
  | .comparison => old c-r0
  | .pairAbove => if c.family=.pair17 ∨ c.family=.pair12 then old c-r0 else constant 1
  | .winner => match c.family with
      | .pair17 => coord 0+coord 4-constant (25/128)
      | .pair12 => constant (25/128)-coord 2-coord 3
      | _ => constant 1
  | .positiveGap => next c-old c
  | .selectedAscending => (1/2:ℚ) • (constant 1+selected c.selectedMask)-next c
  | .selectedDescending => constant (57/64)-(3/2:ℚ) • selected c.selectedMask-next c
  | .fullSquare j => next c-square j
  | .remainingSquare j => if ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit c.selectedMask j.val then constant 1 else next c-remaining c.selectedMask j
  | .oldArgument => r0-s6-coord 5
  | .newArgument => (3:ℚ) • coord 5-(next c-s6)
  | .priority j => match j.val with
      | 0 => if c=.singleton34_1371 ∨ c=.singleton50_1353 ∨ c=.singleton50_1355 then next c-desc33 else constant 1
      | 1 => if c=.singleton50_1353 ∨ c=.singleton50_1355 then next c-asc34 else constant 1
      | _ => if c.family=.tent33 then clipped-asc33 else constant 1

@[simp] theorem eval_constant (q : ℚ) (t : Point) : eval (constant q) t = (q:ℝ) := by
  simp [eval,constant]
@[simp] theorem eval_coord (j : Fin 6) (t : Point) : eval (coord j) t = t j := by
  simp [eval,coord,ite_mul]
@[simp] theorem eval_zero (t : Point) : eval 0 t = 0 := by simp [eval]
@[simp] theorem eval_add (a b : Affine) (t : Point) : eval (a+b) t = eval a t+eval b t := by
  simp [eval,add_mul,Finset.sum_add_distrib]
  ring
@[simp] theorem eval_sub (a b : Affine) (t : Point) : eval (a-b) t = eval a t-eval b t := by
  simp [eval,sub_mul,Finset.sum_sub_distrib]
  ring
@[simp] theorem eval_smul (q : ℚ) (a : Affine) (t : Point) : eval (q • a) t = (q:ℝ)*eval a t := by
  simp [eval,Pi.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
  ring
@[simp] theorem eval_sum {ι : Type*} (s : Finset ι) (a : ι → Affine) (t : Point) :
    eval (∑ j ∈ s, a j) t = ∑ j ∈ s, eval (a j) t := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha,ih]

theorem eval_row (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (g : Gate) (t : Point) : eval (row c g) t = value c g t := by
  cases g <;> cases c <;>
    simp [row,value,r0,s5,s6,h3,h5,w,old,clipped,asc33,desc33,asc34,next,
      subset,selected,square,remaining,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S5,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S6,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.H3,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.H5,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.W,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.descending33,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending34,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newResidual,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
      ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.fullSquare,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.mu,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.eta,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.selectedMask]
  all_goals try { split <;> simp_all }
  all_goals ring

theorem valid_of_physicalCell {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Point} (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) :
    ∀ g, valid c g t := by
  intro g
  cases g with
  | rpos => simpa [valid,Gate.strict,value] using hc.rpos
  | order j =>
      rcases hc.order with ⟨h5,h4,h3,h2,h1⟩
      fin_cases j <;> simp only [valid,Gate.strict,value,sub_pos] <;> assumption
  | largest => simpa [valid,Gate.strict,value,sub_pos] using hc.largest
  | oldCutoff => simpa [valid,Gate.strict,value,sub_pos] using hc.oldCutoff
  | compactCutoff => simpa [valid,Gate.strict,value,sub_pos] using hc.compactCutoff
  | history3 => simpa [valid,Gate.strict,value,sub_pos] using hc.history3
  | history5 => simpa [valid,Gate.strict,value,sub_pos] using hc.history5
  | oldW => simpa [valid,Gate.strict,value,sub_nonneg] using hc.oldW
  | oldBranch m =>
      have hm : m.val+1 ∈ Finset.Icc 1 31 := by simp only [Finset.mem_Icc]; omega
      have hh := hc.oldBranches (m.val+1) hm
      cases hd : c.descending (m.val+1) <;>
        simpa [valid,Gate.strict,value,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.branchLicense,hd,sub_nonneg] using hh
  | first3Branch m =>
      have hm : m.val+1 ∈ Finset.Icc 1 7 := by simp only [Finset.mem_Icc]; omega
      have hh := hc.first3Branches (m.val+1) hm
      cases hd : c.descending (m.val+1) <;>
        simpa [valid,Gate.strict,value,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.branchLicense,hd,sub_nonneg] using hh
  | comparison => simpa [valid,Gate.strict,value,sub_nonneg] using hc.comparison
  | pairAbove =>
      by_cases hp : c.family=.pair17 ∨ c.family=.pair12
      · simpa [valid,Gate.strict,value,hp,sub_pos] using hc.pairAbove hp
      · simp [valid,Gate.strict,value,hp]
  | winner =>
      have hh := hc.winner
      cases hf : c.family <;> simp only [valid,Gate.strict,value,hf,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.winnerPlane] at hh ⊢
      all_goals first | norm_num | linarith
  | positiveGap => simpa [valid,Gate.strict,value,sub_pos] using hc.positiveGap
  | selectedAscending => simpa [valid,Gate.strict,value,sub_pos] using hc.selectedAscending
  | selectedDescending => simpa [valid,Gate.strict,value,sub_pos] using hc.selectedDescending
  | fullSquare j => simpa [valid,Gate.strict,value,sub_pos] using hc.fullSquares j
  | remainingSquare j =>
      cases hb : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit c.selectedMask j.val
      · simpa [valid,Gate.strict,value,hb,sub_pos] using hc.remainingSquares j hb
      · simp [valid,Gate.strict,value,hb]
  | oldArgument => simpa [valid,Gate.strict,value,sub_pos] using hc.oldArgument
  | newArgument => simpa [valid,Gate.strict,value,sub_pos] using hc.newArgument
  | priority j =>
      have hp := hc.priority
      fin_cases j <;> cases c <;>
        simp_all [valid,Gate.strict,value,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.priority,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family]

theorem physicalCell_of_valid {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Point} (h : ∀ g, valid c g t) : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t := by
  refine {
    rpos := by simpa [valid,Gate.strict,value] using h .rpos
    order := ?_
    largest := by simpa [valid,Gate.strict,value,sub_pos] using h .largest
    oldCutoff := by simpa [valid,Gate.strict,value,sub_pos] using h .oldCutoff
    compactCutoff := by simpa [valid,Gate.strict,value,sub_pos] using h .compactCutoff
    history3 := by simpa [valid,Gate.strict,value,sub_pos] using h .history3
    history5 := by simpa [valid,Gate.strict,value,sub_pos] using h .history5
    oldW := by simpa [valid,Gate.strict,value,sub_nonneg] using h .oldW
    oldBranches := ?_
    first3Branches := ?_
    comparison := by simpa [valid,Gate.strict,value,sub_nonneg] using h .comparison
    pairAbove := ?_
    winner := ?_
    positiveGap := by simpa [valid,Gate.strict,value,sub_pos] using h .positiveGap
    selectedAscending := by simpa [valid,Gate.strict,value,sub_pos] using h .selectedAscending
    selectedDescending := by simpa [valid,Gate.strict,value,sub_pos] using h .selectedDescending
    fullSquares := fun j => by simpa [valid,Gate.strict,value,sub_pos] using h (.fullSquare j)
    remainingSquares := ?_
    oldArgument := by simpa [valid,Gate.strict,value,sub_pos] using h .oldArgument
    newArgument := by simpa [valid,Gate.strict,value,sub_pos] using h .newArgument
    priority := ?_ }
  · exact ⟨by simpa [valid,Gate.strict,value,sub_pos] using h (.order 4),
      by simpa [valid,Gate.strict,value,sub_pos] using h (.order 3),
      by simpa [valid,Gate.strict,value,sub_pos] using h (.order 2),
      by simpa [valid,Gate.strict,value,sub_pos] using h (.order 1),
      by simpa [valid,Gate.strict,value,sub_pos] using h (.order 0)⟩
  · intro mask hm
    let m : Fin 31 := ⟨mask-1,by have hh := Finset.mem_Icc.mp hm; omega⟩
    have hv : m.val+1=mask := by have hh := Finset.mem_Icc.mp hm; dsimp [m]; omega
    have hh := h (.oldBranch m)
    cases hd : c.descending mask <;>
      simpa [valid,Gate.strict,value,hv,hd,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.branchLicense,sub_nonneg] using hh
  · intro mask hm
    let m : Fin 7 := ⟨mask-1,by have hh := Finset.mem_Icc.mp hm; omega⟩
    have hv : m.val+1=mask := by have hh := Finset.mem_Icc.mp hm; dsimp [m]; omega
    have hh := h (.first3Branch m)
    cases hd : c.descending mask <;>
      simpa [valid,Gate.strict,value,hv,hd,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.branchLicense,sub_nonneg] using hh
  · intro hp
    simpa [valid,Gate.strict,value,hp,sub_pos] using h .pairAbove
  · have hh := h .winner
    cases hf : c.family <;> simp only [valid,Gate.strict,value,hf,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.winnerPlane] at hh ⊢
    all_goals first | trivial | linarith
  · intro j hb
    simpa [valid,Gate.strict,value,hb,sub_pos] using h (.remainingSquare j)
  · have h0 := h (.priority 0)
    have h1 := h (.priority 1)
    have h2 := h (.priority 2)
    cases c <;> simp_all [valid,Gate.strict,value,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.priority,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,sub_pos]

theorem physicalCell_iff_rows (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : Point) :
    ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t ↔ ∀ g, if g.strict then 0 < eval (row c g) t else 0 ≤ eval (row c g) t := by
  simp_rw [eval_row]
  exact ⟨valid_of_physicalCell,physicalCell_of_valid⟩

end
end ImbalancedChen.P2OriginalSixthPhysicalGateRows
