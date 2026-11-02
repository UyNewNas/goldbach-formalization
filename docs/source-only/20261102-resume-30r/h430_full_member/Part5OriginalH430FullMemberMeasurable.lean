import ImbalancedChen.Part5OriginalH430FullMemberStrips

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Joint measurability of the actual complete fixed-Program domain, including
every typed/cell gate and its terminal closed query atom.  The root prime
coordinate and all descendant native coordinates vary together.  No
measurability of Member is assumed, and no assertion of small strip mass
or smooth approximation follows from this result alone.
-/

namespace ImbalancedChen.Part5OriginalH430FullMemberMeasurable

noncomputable section
open Set MeasureTheory Classical
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenRootMass Part5OriginalH430FullMemberStrips
open Part5OriginalH430NativeQueryPaths
open Part5OriginalUpsilon5CausalDictionary (a FloorAtom)

section GenericCoordinateMaps

variable {X : Type*} [MeasurableSpace X]

def StateMeasurable (p : X → PhysicalNode) : Prop :=
  Measurable (fun x => residual (p x)) ∧
  Measurable (fun x => (p x).argument) ∧
  Measurable (fun x => (p x).ceiling)

theorem perform_stateMeasurable {p : X → PhysicalNode} (hp : StateMeasurable p)
    {z : X → Point} (hz : ∀ i, Measurable (fun x => z x i)) (shape : StepShape) :
    StateMeasurable (fun x => perform (p x) shape (z x)) := by
  obtain ⟨hL,hs,hC⟩ := hp
  have hu (i : Fin 2) : Measurable (fun x => normalized (p x) (z x) i) :=
    (hz i).div hL
  cases shape with
  | retain => exact ⟨hL,hs,hC⟩
  | transport i => exact ⟨hL,measurable_const,hC⟩
  | buchstabUpper =>
      exact ⟨by simpa only [perform,residual_appendOne] using hL.sub (hz 0),
        (hL.div (hz 0)).sub_const 1,hz 0⟩
  | buchstabLower =>
      exact ⟨by simpa only [perform,residual_appendOne] using hL.sub (hz 0),
        (hL.div (hz 0)).sub_const 1,hz 0⟩
  | w1Fixed i j => exact ⟨hL,measurable_const,hC⟩
  | w1Singleton i j =>
      exact ⟨by simpa only [perform,residual_appendOne] using hL.sub (hz 0),
        measurable_const.mul (measurable_const.sub (hu 0)),hz 0⟩
  | w2Fixed j anchor => exact ⟨hL,measurable_const,hC⟩
  | w2Singleton j piece =>
      exact ⟨by simpa only [perform,residual_appendOne] using hL.sub (hz 0),
        measurable_const.mul (measurable_const.sub (hu 0)),hz 0⟩
  | w2Pair j piece =>
      refine ⟨by simpa only [perform,residual_appendPair] using (hL.sub (hz 1)).sub (hz 0),
        ?_,hz 0⟩
      by_cases hpiece : piece.val < 2
      · simpa only [perform,appendPair,pairProfile,hpiece,if_true,fixedPairProfile] using
          measurable_const.mul ((measurable_const.sub (hu 0)).sub (hu 1))
      · simpa only [perform,appendPair,pairProfile,hpiece,if_false,movingPairProfile] using
          ((measurable_const.sub (hu 0)).sub (hu 1)).div (hu 0)

theorem measurableSet_LocalDomain {p : X → PhysicalNode} (hp : StateMeasurable p)
    {z : X → Point} (hz : ∀ i, Measurable (fun x => z x i)) (shape : StepShape) :
    MeasurableSet {x | LocalDomain (p x) shape (z x)} := by
  obtain ⟨hL,hs,hC⟩ := hp
  have hpos : MeasurableSet {x | 0 < residual (p x)} :=
    measurableSet_lt measurable_const hL
  have hu (i : Fin 2) : Measurable (fun x => normalized (p x) (z x) i) :=
    (hz i).div hL
  have hv : Measurable (fun x => normalized (p x) (z x)) := by
    apply measurable_pi_lambda
    intro i
    exact hu i
  have hw : Measurable (fun x => buchstabArgument (p x) (z x)) :=
    (hL.div (hz 0)).sub_const 1
  have hone : MeasurableSet {x | OneGate (p x) (z x 0)} :=
    (measurableSet_lt measurable_const (hz 0)).inter
      ((measurableSet_le (hz 0) hC).inter
        (measurableSet_le (measurable_const.mul (hz 0)) hL))
  have hpair : MeasurableSet {x | PairGate (p x) (z x 0) (z x 1)} :=
    (measurableSet_lt measurable_const (hz 0)).inter
      ((measurableSet_lt (hz 0) (hz 1)).inter
        ((measurableSet_le (hz 1) hC).inter
          ((measurableSet_le (measurable_const.mul (hz 1)) hL).inter
            (measurableSet_le ((hz 1).add (measurable_const.mul (hz 0))) hL))))
  cases shape with
  | retain => simpa only [LocalDomain,and_true] using hpos
  | transport i => exact hpos.inter (measurableSet_le hs measurable_const)
  | buchstabUpper =>
      exact hpos.inter (hone.inter
        ((measurableSet_le (measurable_const.max (hs.sub_const 1)) hw).inter
          (measurableSet_le hw measurable_const)))
  | buchstabLower =>
      exact hpos.inter ((measurableSet_le measurable_const hs).inter (hone.inter
        ((measurableSet_le (hs.sub_const 1) hw).inter
          (measurableSet_le hw measurable_const))))
  | w1Fixed i j =>
      exact hpos.inter ((measurableSet_le hs measurable_const).inter
        (measurableSet_le (hL.div_const _) hC))
  | w1Singleton i j =>
      exact hpos.inter (hone.inter
        ((measurableSet_Ioo.preimage (hu 0)).inter
          ((measurableSet_le hs measurable_const).inter
            (measurableSet_le (hL.div_const _) hC))))
  | w2Fixed j anchor =>
      exact hpos.inter ((measurableSet_le hs measurable_const).inter
        (measurableSet_le (hL.div_const _) hC))
  | w2Singleton j piece =>
      exact hpos.inter (hone.inter
        (((measurableSet_W2SingletonDomain _ piece).preimage (hu 0)).inter
          ((measurableSet_le hs measurable_const).inter
            (measurableSet_le (hL.div_const _) hC))))
  | w2Pair j piece =>
      exact hpos.inter (hpair.inter
        (((measurableSet_W2PairDomain _ piece).preimage hv).inter
          ((measurableSet_le hs measurable_const).inter
            (measurableSet_le (hL.div_const _) hC))))

theorem measurableSet_exponentCell (lo hi : ℝ) (mesh : ℕ)
    (c : PhysicalCell mesh) :
    MeasurableSet (P2PhysicalIncomingPrefixCells.exponentCell lo hi mesh c) := by
  cases c with
  | none => exact measurableSet_singleton _
  | some i => exact measurableSet_Ico

theorem measurableSet_cellMember (lo hi : ℝ) (mesh : ℕ)
    (c : PhysicalCell mesh × PhysicalCell mesh) {z : X → Point}
    (hz : ∀ i, Measurable (fun x => z x i)) :
    MeasurableSet {x | cellMember lo hi mesh c (z x)} :=
  (measurableSet_Icc.preimage (hz 0)).inter
    ((measurableSet_Icc.preimage (hz 1)).inter
      (((measurableSet_exponentCell lo hi mesh c.1).preimage (hz 0)).inter
        ((measurableSet_exponentCell lo hi mesh c.2).preimage (hz 1))))

theorem realize_stateMeasurable {mesh depth : ℕ} {p : X → TypedNode}
    (hp : StateMeasurable (fun x => (p x).physical))
    (code : Program mesh depth) {z : X → Coordinates depth}
    (hz : ∀ i j, Measurable (fun x => z x i j)) :
    StateMeasurable (fun x => (realize depth (p x) code (z x)).physical) := by
  induction depth generalizing p with
  | zero => exact hp
  | succ depth ih =>
      exact ih (perform_stateMeasurable hp (hz 0) (code 0).1)
        (tail code) (fun i j => hz i.succ j)

/-- Joint measurability of the complete recursive typed/cell domain. -/
theorem measurableSet_Member {lo hi : ℝ} {mesh depth : ℕ} {p : X → TypedNode}
    (hp : StateMeasurable (fun x => (p x).physical))
    {b : Bool} (hb : ∀ x, (p x).upper=b)
    (code : Program mesh depth) {z : X → Coordinates depth}
    (hz : ∀ i j, Measurable (fun x => z x i j)) :
    MeasurableSet {x | Member lo hi depth (p x) code (z x)} := by
  induction depth generalizing p b with
  | zero => exact MeasurableSet.univ
  | succ depth ih =>
      have hin : MeasurableSet {x | incomingAllowed (p x).upper (code 0).1} := by
        by_cases h : incomingAllowed b (code 0).1
        · simpa only [hb,h,Set.setOf_true] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set X))
        · simpa only [hb,h,Set.setOf_false] using (MeasurableSet.empty : MeasurableSet (∅ : Set X))
      have hnext := perform_stateMeasurable hp (hz 0) (code 0).1
      have htype (x : X) : (advance (p x) (code 0).1 (z x 0)).upper =
          childUpper b (code 0).1 := by simp only [advance,hb]
      exact (measurableSet_cellMember lo hi mesh (code 0).2 (hz 0)).inter
        (hin.inter ((measurableSet_LocalDomain hp (hz 0) (code 0).1).inter
          (ih hnext htype (tail code) (fun i j => hz i.succ j))))

theorem measurableSet_QueryMember {lo hi : ℝ} {mesh depth : ℕ} {p : X → TypedNode}
    (hp : StateMeasurable (fun x => (p x).physical))
    {b : Bool} (hb : ∀ x, (p x).upper=b)
    (code : Program mesh depth) {z : X → Coordinates depth}
    (hz : ∀ i j, Measurable (fun x => z x i j)) (lower : Bool) (atom : FloorAtom) :
    MeasurableSet {x | QueryMember lo hi (p x) code (z x) lower atom} :=
  (measurableSet_Member hp hb code hz).inter
    ((measurableSet_tableAtomSet lower atom).preimage (realize_stateMeasurable hp code hz).2.1)

theorem canonicalProgram_member_iff {lo hi : ℝ} {mesh depth : ℕ}
    (p : TypedNode) (shape : Fin depth → StepShape) (z : Coordinates depth) :
    Member lo hi depth p (canonicalProgram lo hi mesh shape z) z ↔
      LocalPath lo hi depth p shape z := by
  constructor
  · intro hm
    induction depth generalizing p with
    | zero => trivial
    | succ depth ih =>
        exact ⟨hm.1.1,hm.1.2.1,hm.2.1,hm.2.2.1,ih _ _ _ hm.2.2.2⟩
  · exact canonicalProgram_member p shape z

theorem measurableSet_LocalPath {lo hi : ℝ} {depth : ℕ} {p : X → TypedNode}
    (hp : StateMeasurable (fun x => (p x).physical))
    {b : Bool} (hb : ∀ x, (p x).upper=b)
    (shape : Fin depth → StepShape) {z : X → Coordinates depth}
    (hz : ∀ i j, Measurable (fun x => z x i j)) :
    MeasurableSet {x | LocalPath lo hi depth (p x) shape (z x)} := by
  induction depth generalizing p b with
  | zero => exact MeasurableSet.univ
  | succ depth ih =>
      have hin : MeasurableSet {x | incomingAllowed (p x).upper (shape 0)} := by
        by_cases h : incomingAllowed b (shape 0)
        · simpa only [hb,h,Set.setOf_true] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set X))
        · simpa only [hb,h,Set.setOf_false] using (MeasurableSet.empty : MeasurableSet (∅ : Set X))
      have htype (x : X) : (advance (p x) (shape 0) (z x 0)).upper =
          childUpper b (shape 0) := by simp only [advance,hb]
      exact (measurableSet_Icc.preimage (hz 0 0)).inter
        ((measurableSet_Icc.preimage (hz 0 1)).inter
          (hin.inter ((measurableSet_LocalDomain hp (hz 0) (shape 0)).inter
            (ih (perform_stateMeasurable hp (hz 0) (shape 0)) htype
              (tail shape) (fun i j => hz i.succ j)))))

theorem realize_eq_of_shapes {mesh depth : ℕ} (p : TypedNode)
    (code other : Program mesh depth) (z : Coordinates depth)
    (h : ∀ i, (code i).1=(other i).1) :
    realize depth p code z=realize depth p other z := by
  induction depth generalizing p with
  | zero => rfl
  | succ depth ih =>
      change realize depth (advance p (code 0).1 (z 0)) (tail code) (tail z) =
        realize depth (advance p (other 0).1 (z 0)) (tail other) (tail z)
      rw [h 0]
      exact ih _ _ _ _ (fun i => h i.succ)

theorem measurableSet_nativeProgram_QueryMember {depth : ℕ} {p : X → TypedNode}
    (hp : StateMeasurable (fun x => (p x).physical))
    {b : Bool} (hb : ∀ x, (p x).upper=b)
    (mesh : ℕ) (shape : Fin depth → StepShape)
    {z : X → Coordinates depth} (hz : ∀ i j, Measurable (fun x => z x i j))
    (lower : Bool) (atom : FloorAtom) :
    MeasurableSet {x | QueryMember 0 1 (p x)
      (canonicalProgram 0 1 mesh shape (z x)) (z x) lower atom} := by
  let code : Program mesh depth := canonicalProgram 0 1 mesh shape (fun _ _ => 0)
  have hm : MeasurableSet {x | Member 0 1 depth (p x)
      (canonicalProgram 0 1 mesh shape (z x)) (z x)} := by
    simpa only [canonicalProgram_member_iff] using measurableSet_LocalPath hp hb shape hz
  have he (x : X) : realize depth (p x) (canonicalProgram 0 1 mesh shape (z x)) (z x) =
      realize depth (p x) code (z x) := realize_eq_of_shapes _ _ _ _ (fun _ => rfl)
  have hq : Measurable (fun x => (realize depth (p x)
      (canonicalProgram 0 1 mesh shape (z x)) (z x)).physical.argument) := by
    simpa only [he] using (realize_stateMeasurable hp code hz).2.1
  exact hm.inter ((measurableSet_tableAtomSet lower atom).preimage hq)

end GenericCoordinateMaps

theorem sourceRoot_stateMeasurable (k : Root) (tau : ℝ) :
    StateMeasurable (fun t => (sourceRoot k tau t).physical) := by
  refine ⟨?_,?_,measurable_id⟩
  · simpa only [sourceRoot_residual] using sourceResidual_measurable k tau
  · exact measurable_const.max ((sourceResidual_measurable k tau).div_const a)

theorem frozenRoot_stateMeasurable (n : ℕ) (k : Root) (tau : ℝ) :
    StateMeasurable (fun t => (frozenRoot n k tau t).physical) := by
  refine ⟨frozenResidual_measurable n k tau,?_,measurable_id⟩
  change Measurable (fun t => max 2
    ((frozenLevel n (sourceRoot k tau t).physical.total-t)/a))
  simpa only [frozenRoot_residual] using
    measurable_const.max ((frozenResidual_measurable n k tau).div_const a)

/-- The actual ideal and frozen families share one joint native space.
No positivity, admission or atom-stability hypothesis is used here. -/
theorem actual_joint_Member_measurable (lo hi : ℝ) (n : ℕ) (k : Root) (tau : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) :
    MeasurableSet {x : ℝ × Coordinates depth |
      Member lo hi depth (sourceRoot k 0 x.1) code x.2} ∧
    MeasurableSet {x : ℝ × Coordinates depth |
      Member lo hi depth (frozenRoot n k tau x.1) code x.2} := by
  have hz (i : Fin depth) (j : Fin 2) :
      Measurable (fun x : ℝ × Coordinates depth => x.2 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)
  have hi := sourceRoot_stateMeasurable k 0
  have hf := frozenRoot_stateMeasurable n k tau
  exact ⟨measurableSet_Member
    ⟨hi.1.comp measurable_fst,hi.2.1.comp measurable_fst,hi.2.2.comp measurable_fst⟩
    (fun _ => rfl) code hz,
    measurableSet_Member
    ⟨hf.1.comp measurable_fst,hf.2.1.comp measurable_fst,hf.2.2.comp measurable_fst⟩
    (fun _ => rfl) code hz⟩

theorem actual_joint_QueryMember_measurable (lo hi : ℝ) (n : ℕ) (k : Root) (tau : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (lower : Bool) (atom : FloorAtom) :
    MeasurableSet {x : ℝ × Coordinates depth |
      QueryMember lo hi (sourceRoot k 0 x.1) code x.2 lower atom} ∧
    MeasurableSet {x : ℝ × Coordinates depth |
      QueryMember lo hi (frozenRoot n k tau x.1) code x.2 lower atom} := by
  have hz (i : Fin depth) (j : Fin 2) :
      Measurable (fun x : ℝ × Coordinates depth => x.2 i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)
  have hi := sourceRoot_stateMeasurable k 0
  have hf := frozenRoot_stateMeasurable n k tau
  exact ⟨measurableSet_QueryMember
    ⟨hi.1.comp measurable_fst,hi.2.1.comp measurable_fst,hi.2.2.comp measurable_fst⟩
    (fun _ => rfl) code hz lower atom,
    measurableSet_QueryMember
    ⟨hf.1.comp measurable_fst,hf.2.1.comp measurable_fst,hf.2.2.comp measurable_fst⟩
    (fun _ => rfl) code hz lower atom⟩

/-- The space has exactly ONE root slot plus each action's zero/one/two
prime slots.  Padding coordinates are constants, never extra integration
variables or multiplicities.  The canonical physical owner varies with x. -/
theorem actual_native_QueryMember_measurable {depth : ℕ}
    (n mesh : ℕ) (k : Root) (tau : ℝ) (shape : Fin depth → StepShape)
    (lower : Bool) (atom : FloorAtom) :
    MeasurableSet {x : NativeSlot shape → ℝ |
      QueryMember 0 1 (sourceRoot k 0 (nativeRootCoordinate x))
        (nativeProgram mesh shape x) (nativeCoordinates shape x) lower atom} ∧
    MeasurableSet {x : NativeSlot shape → ℝ |
      QueryMember 0 1 (frozenRoot n k tau (nativeRootCoordinate x))
        (nativeProgram mesh shape x) (nativeCoordinates shape x) lower atom} := by
  have ht : Measurable (nativeRootCoordinate : (NativeSlot shape → ℝ) → ℝ) :=
    measurable_pi_apply (.inl ())
  have hz (i : Fin depth) (j : Fin 2) :
      Measurable (fun x : NativeSlot shape → ℝ => nativeCoordinates shape x i j) := by
    unfold nativeCoordinates
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const
  have hi := sourceRoot_stateMeasurable k 0
  have hf := frozenRoot_stateMeasurable n k tau
  exact ⟨measurableSet_nativeProgram_QueryMember
    ⟨hi.1.comp ht,hi.2.1.comp ht,hi.2.2.comp ht⟩ (fun _ => rfl) mesh shape hz lower atom,
    measurableSet_nativeProgram_QueryMember
    ⟨hf.1.comp ht,hf.2.1.comp ht,hf.2.2.comp ht⟩ (fun _ => rfl) mesh shape hz lower atom⟩

end
end ImbalancedChen.Part5OriginalH430FullMemberMeasurable
