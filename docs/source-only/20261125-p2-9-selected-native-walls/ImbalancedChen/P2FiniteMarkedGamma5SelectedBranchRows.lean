import ImbalancedChen.P2FiniteMarkedGamma5SelectedFirstChange

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedBranchRows
noncomputable section
open P5OriginalActionMassBound P5OriginalFeedbackDomains P2Selected430CausalOccurrenceExporter
open Part5OriginalH430RequestedReads P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers (SingleRule)
open Part5OriginalH430MemberGateRows Part5OriginalH430BankSlotTargets
open P2FiniteMarkedGamma5StrictPhysicalChildren P2FiniteMarkedGamma5RealSelectedPrefix
open P2FiniteMarkedGamma5SelectedQueryRows
open Set

/-- A row stores the signed affine value together with its original strictness.
The same construction may act on scalars or on symbolic affine functions. -/
abbrev Test (V : Type*) := Bool × V

def passes (r : Test ℝ) : Prop := if r.1 then 0 < r.2 else 0 ≤ r.2
def allPass (rs : List (Test ℝ)) : Prop := ∀ r ∈ rs, passes r

@[simp] theorem pass_nil : allPass [] := by simp [allPass]
@[simp] theorem pass_cons (r : Test ℝ) (rs : List (Test ℝ)) :
    allPass (r::rs) ↔ passes r ∧ allPass rs := by simp [allPass]
@[simp] theorem pass_append (rs ss : List (Test ℝ)) :
    allPass (rs++ss) ↔ allPass rs ∧ allPass ss := by simp [allPass,forall_and]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def windowRows (one T L C : V) : List (Test V) :=
  [(true,L),(false,one-T),(true,C)]

def strictOne (one T L C x : V) : List (Test V) :=
  windowRows one T L C ++ [(true,x),(true,C-x),(true,L-x)]

def strictPair (one T L C x y : V) : List (Test V) :=
  windowRows one T L C ++ [(true,x),(true,y-x),(true,C-x),(true,C-y),(true,L-(x+y))]

def bunch (up : Bool) (g : ℝ) (L D x : V) : List (Test V) :=
  [(false,g • L-(if up then D else (2:ℝ) • D))] ++
    (if up then [(false,L-(3:ℝ) • x)] else []) ++
    [(false,D-g • x),(false,(6:ℝ) • x-L)]

def interval (c d : ℝ) (L x : V) : List (Test V) :=
  [(true,x-c • L),(true,d • L-x)]

/-- These are precisely the four existing W2pairRows catalogues with a
symbolic residual and both symbolic coordinates. -/
def pairDomainRows (P : W2Parameters) (j : Fin 4) (L x y : V) : List (Test V) :=
  ![[(true,x-a0 P • L),(true,y-x),(true,a2 P • L-y),(true,L-(y+(2:ℝ) • x))],
    interval (a0 P) (a1 P) L x ++ interval (a2 P) (a3 P) L y,
    [(true,x-a0 P • L),(true,y-x),(true,a1 P • L-y)],
    interval (a0 P) (a1 P) L x ++ interval (a1 P) (a2 P) L y] j

def literalRows (g : ℝ) (one T L C D x y : V) : StepShape → List (Test V)
  | .buchstabUpper => strictOne one T L C x ++ bunch true g L D x
  | .buchstabLower => strictOne one T L C x ++ bunch false g L D x
  | .w1Singleton i j => strictOne one T L C x ++
      interval (1/W1Anchor j) (1/W1Target i) L x
  | .w2Singleton j u => strictOne one T L C x ++
      interval (a0 (originalW2At j))
        (![b (originalW2At j),a2 (originalW2At j),a3 (originalW2At j)] u) L x
  | .w2Pair j u => strictPair one T L C x y ++ pairDomainRows (originalW2At j) u L x y
  | _ => []

private theorem bunch_exact (p : PhysicalNode) (up : Bool) (z : Point) {g D : ℝ}
    (h : represents p g D) (hL : 0 < residual p) (hx : 0 < z 0) :
    allPass (bunch up g (residual p) D (z 0)) ↔
      oneDomain p (.buchstab up p.argument) z := by
  rw [buchstab_rows_iff p up z h hL hx]
  cases up <;> simp [bunch,passes,sub_nonneg,smul_eq_mul,and_assoc]

private theorem interval_matches (c d L s x : ℝ) :
    allPass (interval c d L x) ↔ AllRows (intervalRows c d x) L s := by
  simp [interval,intervalRows,passes,GateRow.accepts,GateRow.value,strictRow,smul_eq_mul,
    sub_eq_add_neg,neg_mul,add_comm,add_left_comm,add_assoc]

private theorem pair_matches (P : W2Parameters) (j : Fin 4) (p : PhysicalNode) (z : Point) :
    allPass (pairDomainRows P j (residual p) (z 0) (z 1)) ↔
      AllRows (W2pairRows P j z) (residual p) p.argument := by
  fin_cases j <;>
    simp [pairDomainRows,W2pairRows,interval,passes,GateRow.accepts,GateRow.value,
      strictRow,smul_eq_mul,sub_eq_add_neg,neg_mul,add_comm,add_left_comm,add_assoc,and_assoc]

private theorem one_matches (p : PhysicalNode) (z : Point) :
    allPass (strictOne 1 p.total (residual p) p.ceiling (z 0)) ↔
      window p ∧ 0 < z 0 ∧ z 0 < p.ceiling ∧ z 0 < residual p := by
  simp [strictOne,windowRows,passes,window,sub_nonneg,sub_pos,and_assoc]

private theorem pair_tests (p : PhysicalNode) (z : Point) :
    allPass (strictPair 1 p.total (residual p) p.ceiling (z 0) (z 1)) ↔
      window p ∧ 0 < z 0 ∧ z 0 < z 1 ∧ z 0 < p.ceiling ∧
        z 1 < p.ceiling ∧ z 0+z 1 < residual p := by
  simp [strictPair,windowRows,passes,window,sub_nonneg,sub_pos,and_assoc]

def literalGate (p : PhysicalNode) (z : Point) : StepShape → Prop
  | .buchstabUpper => singleGate p (.buchstab true p.argument) z
  | .buchstabLower => singleGate p (.buchstab false p.argument) z
  | .w1Singleton i j => singleGate p (.w1 i j) z
  | .w2Singleton j u => singleGate p (.w2 j u) z
  | .w2Pair j u => pairGate p j u z
  | _ => True

theorem gate_iff_rows (p : PhysicalNode) (z : Point) (s : StepShape) {g D : ℝ}
    (h : represents p g D) :
    literalGate p z s ↔
      allPass (literalRows g 1 p.total (residual p) p.ceiling D (z 0) (z 1) s) := by
  cases s with
  | buchstabUpper | buchstabLower =>
    simp only [literalGate,literalRows,pass_append,one_matches,singleGate]
    by_cases hL : 0 < residual p <;> by_cases hx : 0 < z 0
    all_goals first
      | rw [bunch_exact p _ z h hL hx]; tauto
      | simp [window,hL,hx]
  | w1Singleton i j =>
    simp only [literalGate,literalRows,pass_append,one_matches,singleGate]
    by_cases hL : 0 < residual p
    · rw [interval_matches _ _ _ p.argument, intervalRows_iff hL]
      change _ ∧ _ ∧ (z 0/residual p ∈ Set.Ioo _ _) ∧ _ ↔ _
      tauto
    · simp [window,hL]
  | w2Singleton j u =>
    simp only [literalGate,literalRows,pass_append,one_matches,singleGate]
    by_cases hL : 0 < residual p
    · rw [interval_matches _ _ _ p.argument]
      change _ ↔ _ ∧ AllRows (W2singleRows (originalW2At j) u (z 0)) _ _
      rw [W2singleRows_iff hL]
      change _ ∧ _ ∧ (z 0/residual p ∈ W2SingletonDomain _ _) ∧ _ ↔ _
      tauto
    · simp [window,hL]
  | w2Pair j u =>
    simp only [literalGate,literalRows,pass_append,pair_tests,pairGate,pair_matches]
    by_cases hL : 0 < residual p
    · rw [W2pairRows_iff hL]
      tauto
    · simp [window,hL]
  | _ => simp [literalRows,literalGate]

/-- Discrete tags and the incoming upper/lower type are unchanged between
points on one fixed itinerary. Incompatible choices never change. -/
theorem changed_branch_gate (p q : TypedNode) (hu : p.upper=q.upper) (x y : Point)
    (c : Choice) (s : StepShape)
    (h : ¬ (branch p x c s ↔ branch q y c s)) :
    ¬ (literalGate p.physical x s ↔ literalGate q.physical y s) := by
  intro he
  apply h
  cases c with
  | retained => cases s <;> rfl
  | buchstab =>
    cases s <;> cases hp : p.upper <;> simp_all [branch,literalGate]
  | bank k =>
    cases ha : actionOfSlot k with
    | inl ab =>
      obtain ⟨i,j⟩ := ab
      cases s <;> simp_all [branch,ha,bankGate,literalGate]
    | inr j =>
      cases s <;> simp_all [branch,ha,bankGate,literalGate]

/-- The catalogue is functorial under evaluation. Consequently using
actual coordinate projections in a finite affine-function module gives
the exact physical rows above, including strict endpoints and pair order. -/
theorem map_literalRows {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (g : ℝ) (one T L C D x y : V) (s : StepShape) :
    (literalRows g one T L C D x y s).map (fun r => (r.1,f r.2)) =
      literalRows g (f one) (f T) (f L) (f C) (f D) (f x) (f y) s := by
  cases s with
  | w2Pair j u => fin_cases u <;>
      simp [literalRows,strictPair,windowRows,pairDomainRows,interval]
  | _ => simp [literalRows,strictOne,windowRows,bunch,interval]

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedBranchRows
