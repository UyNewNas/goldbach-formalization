import ImbalancedChen.Part5OriginalH430PrimeRegularGerms
import ImbalancedChen.Part5OriginalH430FixedProgramL1

namespace ImbalancedChen.Part5OriginalH430FixedPrimeScreen
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2PhysicalIncomingPrefixCells Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenTableRootMass
open Part5OriginalH430FullMemberStrips Part5OriginalH430NativeQueryPaths
open Part5OriginalH430PrimeRegularGerms Part5OriginalH430FixedProgramL1
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables Part5UpperTables.OriginalU34

local macro "germs" : tactic => `(tactic|
  repeat' first
    | assumption | exact pw_const _ | exact st_const _
    | apply Stable.and | apply PW.le | apply PW.lt | apply PW.eq
    | apply PW.min | apply PW.max | apply PW.piece | apply PW.add | apply PW.sub
    | apply PW.div | apply PW.mul | apply PW.neg)

variable {r : ℕ}

private theorem exponent_cell {f : Space r → ℝ} (hf : PW f) (lo hi : ℝ) (m : ℕ) (c : CellCode m) :
    Stable (fun x => f x ∈ exponentCell lo hi m c) := by
  cases c <;> simp only [exponentCell,mem_singleton_iff,mem_Ico] <;> germs

private theorem raw {f : Space r → ℝ} (hf : PW f) (m : ℕ) :
    PW (fun x => rawLower m (f x)) := by
  let S : Finset (Poly r × Poly r) := Finset.univ.image (fun c : CellCode m => (MvPolynomial.C (lowerEndpoint m c),1))
  have hc (c : CellCode m) := exponent_cell hf 0 1 m c
  have hI : Stable (fun x => f x ∈ Ico (0:ℝ) 1) := (PW.le (pw_const 0) hf).and (hf.lt (pw_const 1))
  refine ⟨S,?_⟩
  filter_upwards [Filter.eventually_all.mpr hc,hI] with x hs hI
  let c := exponentCode 0 1 m (f x)
  refine ⟨_,Finset.mem_image_of_mem (fun q : CellCode m => (MvPolynomial.C (lowerEndpoint m q),1)) (Finset.mem_univ c),
    by simp [ev],?_⟩
  filter_upwards [hI,hs c] with y hy hcell
  have he : exponentCode 0 1 m (f y) = c := by
    by_cases hx : f x ∈ Ico (0:ℝ) 1
    · have hqy := hy.mpr hx
      exact exponentCode_eq_of_cell zero_lt_one ⟨hqy.1,hqy.2.le⟩
        (hcell.mpr (exponentCode_membership ⟨hx.1,hx.2.le⟩))
    · simp [c,exponentCode,hx,fun h => hx (hy.mp h)]
  simp [rawLower,he,ev]

private theorem frozen {f : Space r → ℝ} (hf : PW f) (n : ℕ) :
    PW (fun x => frozenLevel n (f x)) := by
  induction n with
  | zero => exact raw hf 0
  | succ n ih => exact ih.max (raw hf _)

def Fields (p : Space r → TypedNode) :=
  PW (fun x => residual (p x).physical) ∧ PW (fun x => (p x).physical.argument) ∧
    PW (fun x => (p x).physical.ceiling)

private theorem residual_pw (k : Root) (tau : ℝ) {t : Space r → ℝ} (ht : PW t) :
    PW (fun x => sourceResidual k tau (t x)) := by
  cases k <;> simp only [sourceResidual,U3Residual,mainResidual,tailResidual,VariableEnvelope.v,
    VariableEnvelope.A,VariableEnvelope.C] <;> germs

private theorem root_fields (k : Root) (v : Option ℕ) {t : Space r → ℝ} (ht : PW t) :
    Fields (fun x => match v with | none => sourceRoot k 0 (t x)
      | some n => frozenRoot n k (finiteTau n) (t x)) := by
  cases v with
  | none =>
    have hr := residual_pw k 0 ht
    exact ⟨by simpa only [sourceRoot_residual] using hr,
      (pw_const 2).max (hr.div (pw_const a)),ht⟩
  | some n =>
    have hp := ht.add (residual_pw k (finiteTau n) ht)
    have hr := (frozen hp n).sub ht
    exact ⟨hr,(pw_const 2).max (hr.div (pw_const a)),ht⟩

private theorem perform_fields {p : Space r → TypedNode} (hp : Fields p)
    (a : StepShape) {z : Space r → Point} (hz : ∀ i, PW (fun x => z x i)) :
    Fields (fun x => advance (p x) a (z x)) := by
  obtain ⟨hL,hs,hC⟩ := hp
  have h0 := hz 0
  have h1 := hz 1
  have hu (i : Fin 2) := (hz i).div hL
  cases a with
  | retain => exact ⟨hL,hs,hC⟩
  | transport _ | w1Fixed _ _ | w2Fixed _ _ => exact ⟨hL,pw_const _,hC⟩
  | buchstabUpper | buchstabLower =>
    exact ⟨by simpa only [advance,perform,residual_appendOne] using hL.sub h0,
      (hL.div h0).sub (pw_const 1),h0⟩
  | w1Singleton _ _ | w2Singleton _ _ =>
    exact ⟨by simpa only [advance,perform,residual_appendOne] using hL.sub h0,
      (pw_const _).mul ((pw_const 1).sub (hu 0)),h0⟩
  | w2Pair i j =>
    refine ⟨by simpa only [advance,perform,residual_appendPair] using (hL.sub h1).sub h0,?_,h0⟩
    by_cases hj : j.val < 2
    · simpa only [advance,perform,appendPair,pairProfile,if_pos hj,fixedPairProfile,normalized]
        using (pw_const (originalW2At i).s0).mul (((pw_const 1).sub (hu 0)).sub (hu 1))
    · simpa only [advance,perform,appendPair,pairProfile,if_neg hj,movingPairProfile,normalized]
        using (((pw_const 1).sub (hu 0)).sub (hu 1)).div (hu 0)

private theorem local_stable {p : Space r → TypedNode} (hp : Fields p)
    (a : StepShape) {z : Space r → Point} (hz : ∀ i, PW (fun x => z x i)) :
    Stable (fun x => LocalDomain (p x).physical a (z x)) := by
  obtain ⟨hL,hs,hC⟩ := hp
  have h0 := hz 0
  have h1 := hz 1
  cases a with
  | w2Pair _ j => fin_cases j
  | w2Singleton _ j => fin_cases j
  | _ => skip
  all_goals
    simp only [LocalDomain,OneGate,PairGate,normalized,buchstabArgument,buchstabUpperDomain,
      buchstabLowerDomain,W1Domain,W2SingletonDomain,W2PairDomain,W2Singleton2,W2Singleton3,
      W2Singleton4,W2Pair5,W2Pair6,W2Pair7,W2Pair8,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,mem_setOf_eq,mem_Icc,mem_Ioo,and_true]
    germs

private theorem cell_stable (lo hi : ℝ) {mesh : ℕ} (a : PhysicalCell mesh × PhysicalCell mesh)
    {z : Space r → Point} (hz : ∀ i, PW (fun x => z x i)) :
    Stable (fun x => cellMember lo hi mesh a (z x)) :=
  (((pw_const lo).le (hz 0)).and ((hz 0).le (pw_const hi))).and
    ((((pw_const lo).le (hz 1)).and ((hz 1).le (pw_const hi))).and
      ((exponent_cell (hz 0) lo hi mesh a.1).and (exponent_cell (hz 1) lo hi mesh a.2)))

private theorem terminal {f : Space r → ℝ} (hf : PW f) (lo : Bool) (b : FloorAtom) :
    Stable (fun x => f x ∈ tableAtomSet lo b) := by
  cases lo <;> cases b <;> simp only [tableAtomSet,floorAtomSet,upperAtomSet,if_true,if_false,
    Bool.false_eq_true,mem_inter_iff,mem_Icc,mem_Ioo,mem_singleton_iff] <;> germs

private theorem walk {d mesh : ℕ} (lo hi : ℝ) {p : Space r → TypedNode} (hp : Fields p)
    {b : Bool} (hb : ∀ x, (p x).upper=b) (code : Program mesh d) {z : Space r → Coordinates d}
    (hz : ∀ i j, PW (fun x => z x i j)) (lower : Bool) (atom : FloorAtom) :
    Stable (fun x => QueryMember lo hi (p x) code (z x) lower atom) := by
  induction d generalizing p b with
  | zero => simpa only [QueryMember,Member,realize,true_and] using terminal hp.2.1 lower atom
  | succ d ih =>
    have htail := ih (perform_fields hp (code 0).1 (hz 0))
      (fun x => congrArg (fun u => childUpper u (code 0).1) (hb x)) (tail code)
      (fun i j => hz i.succ j)
    have hcell := cell_stable lo hi (code 0).2 (hz 0)
    have hloc := local_stable hp (code 0).1 (hz 0)
    filter_upwards [htail,hcell,hloc] with x hx hc hl
    filter_upwards [hx,hc,hl] with y hy hcy hly
    simp only [QueryMember,Member,realize,hb] at hy ⊢
    tauto

def view {ι : Type*} {r : ℕ} (e : Fin r ≃ ι) (x : Space r) : ι → ℝ :=
  fun i => x (e.symm i)

/-- Same original prime slots and full specified Program at fixed
precision, including the entire cumulative rootCode staircase. -/
theorem fixed_stable {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom) (v : Option ℕ) :
    Stable (fun x => view e x ∈ fixedSet k code lower atom v) := by
  have ht := pw_coord (e.symm (.inl ()))
  have hz (i : Fin d) (j : Fin 2) :
      PW (fun x : Space r => nativeCoordinates (shapes code) (view e x) i j) := by
    unfold nativeCoordinates
    split_ifs <;> first | exact pw_coord _ | exact pw_const _
  exact walk 0 1 (root_fields k v ht) (b := true) (fun x => by cases v <;> rfl) code hz lower atom

theorem difference_stable {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (lower : Bool) (atom : FloorAtom) (n : ℕ) :
    Stable (fun x => view e x ∈ fixedDifference k code lower atom n) := by
  have hI := fixed_stable k code e lower atom none
  have hS := fixed_stable k code e lower atom (some n)
  exact (hI.and hS.not).or (hS.and hI.not)

theorem rootBand_stable {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) :
    Stable (fun x => nativeRootCoordinate (view e x) ∈ rootBand k) := by
  have ht := pw_coord (e.symm (.inl ()))
  cases k <;> exact ((pw_const _).le ht).and (ht.le (pw_const _))

end
end ImbalancedChen.Part5OriginalH430FixedPrimeScreen
