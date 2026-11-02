import ImbalancedChen.Part5OriginalH430MemberGateRows
import ImbalancedChen.Part5OriginalH430RootSourceDictionary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Full Member symmetric differences are derived by a FIRST differing gate,
after a common genuinely admitted prefix.  Neither ideal Member nor
frozen Member, nor their equivalence, is an assumption of the cover.
Cell ownership and incoming type are retained exactly.  Terminal query
atoms include the original singleton knots and the lower [2,5] guard.

The result is a pointwise containment by explicit walls.  It does not
assert that every such wall is proper under every native/history
pullback, or that its actual parent-Theta mass is small.
-/

namespace ImbalancedChen.Part5OriginalH430FullMemberStrips

noncomputable section
open Set Classical Filter Topology
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430MemberGateRows Part5OriginalH430NativeQueryPaths
open Part5OriginalH430FrozenPerturbation Part5OriginalH430DescendantLimits
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenRootMass
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

def GateStrip (p q : PhysicalNode) (shape : StepShape) (z : Point) : Prop :=
  ∃ r ∈ localRows p.ceiling shape z,
    r.value (residual p) p.argument ≠ r.value (residual q) q.argument ∧
    |r.value (residual p) p.argument| ≤
      |r.level|*|residual p-residual q|+|r.query|*|p.argument-q.argument|

/-- Each disjunct carries its actual physical cell and incoming type.
Recursion to a later wall requires BOTH preceding local domains, not
merely an unconstrained path of the correct length. -/
def MemberStrip (lo hi : ℝ) {mesh : ℕ} :
    (depth : ℕ) → TypedNode → TypedNode → Program mesh depth → Coordinates depth → Prop
  | 0, _, _, _, _ => False
  | depth+1, p, q, code, z =>
      cellMember lo hi mesh (code 0).2 (z 0) ∧
      incomingAllowed p.upper (code 0).1 ∧
      (GateStrip p.physical q.physical (code 0).1 (z 0) ∨
       (LocalDomain p.physical (code 0).1 (z 0) ∧
        LocalDomain q.physical (code 0).1 (z 0) ∧
        MemberStrip lo hi depth (advance p (code 0).1 (z 0))
          (advance q (code 0).1 (z 0)) (tail code) (tail z)))

theorem advance_upper_eq {p q : TypedNode} (h : p.upper=q.upper)
    (shape : StepShape) (z : Point) :
    (advance p shape z).upper=(advance q shape z).upper := by
  simp only [advance, h]

theorem realize_upper_eq {mesh depth : ℕ} {p q : TypedNode}
    (h : p.upper=q.upper) (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth p code z).upper=(realize depth q code z).upper := by
  induction depth generalizing p q with
  | zero => exact h
  | succ depth ih => exact ih (advance_upper_eq h _ _) (tail code) (tail z)

/-- The FULL recursive Member is used.  Static cell/type failures cannot
create a difference, and every first differing local row is computed. -/
theorem changed_Member_strip {lo hi : ℝ} {mesh depth : ℕ} {p q : TypedNode}
    (hu : p.upper=q.upper) (hc : p.physical.ceiling=q.physical.ceiling)
    (code : Program mesh depth) (z : Coordinates depth)
    (hchange : ¬ (Member lo hi depth p code z ↔ Member lo hi depth q code z)) :
    MemberStrip lo hi depth p q code z := by
  induction depth generalizing p q with
  | zero => exact False.elim (hchange Iff.rfl)
  | succ depth ih =>
      have hcell : cellMember lo hi mesh (code 0).2 (z 0) := by
        by_contra hn
        apply hchange
        simp only [Member, hn, false_and]
      have hin : incomingAllowed p.upper (code 0).1 := by
        by_contra hn
        apply hchange
        simp only [Member, ← hu, hn, and_false, false_and]
      refine ⟨hcell, hin, ?_⟩
      by_cases hd : LocalDomain p.physical (code 0).1 (z 0) ↔
          LocalDomain q.physical (code 0).1 (z 0)
      · have hp : LocalDomain p.physical (code 0).1 (z 0) := by
          by_contra hn
          have hq : ¬ LocalDomain q.physical (code 0).1 (z 0) :=
            fun h => hn (hd.mpr h)
          apply hchange
          simp only [Member, hn, hq, false_and, and_false]
        have htail : ¬ (Member lo hi depth (advance p (code 0).1 (z 0))
            (tail code) (tail z) ↔
            Member lo hi depth (advance q (code 0).1 (z 0)) (tail code) (tail z)) := by
          intro he
          apply hchange
          simp only [Member, hcell, ← hu, hin, hp, hd.mp hp, true_and]
          exact he
        exact Or.inr ⟨hp,hd.mp hp,ih (advance_upper_eq hu _ _)
          (perform_ceiling_eq hc _ _) (tail code) (tail z) htail⟩
      · exact Or.inl (changed_localDomain_strip hc _ _ hd)

/-- All original 401 atoms: two guard rows, then open interior rows or
TWO weak rows for a knot singleton.  The 1/50 grid is never refined here. -/
def atomRows (lower : Bool) (b : FloorAtom) : List GateRow :=
  [weakRow 0 1 (-(if lower then 2 else 1)), weakRow 0 (-1) 5] ++
  match b with
  | .inl i => [strictRow 0 1 (-(floorGrid i.val)),
                strictRow 0 (-1) (floorGrid (i.val+1))]
  | .inr j => [weakRow 0 1 (-(floorGrid j.val)),
                weakRow 0 (-1) (floorGrid j.val)]

theorem atomRows_length (lower : Bool) (b : FloorAtom) :
    (atomRows lower b).length=4 := by cases b <;> simp [atomRows]

theorem atomRows_iff (lower : Bool) (b : FloorAtom) (L s : ℝ) :
    AllRows (atomRows lower b) L s ↔ s ∈ tableAtomSet lower b := by
  cases lower <;> cases b <;>
    simp [AllRows, atomRows, tableAtomSet, floorAtomSet, upperAtomSet,
      le_antisymm_iff, and_assoc, and_left_comm, and_comm]

def AtomStrip (lower : Bool) (b : FloorAtom) (s t : ℝ) : Prop :=
  s ≠ t ∧ ∃ r ∈ atomRows lower b, |r.value 0 s| ≤ |s-t|

theorem atomRows_coefficients {lower : Bool} {b : FloorAtom} {r : GateRow}
    (hr : r ∈ atomRows lower b) : r.level=0 ∧ |r.query|=1 := by
  cases b <;>
    simp only [atomRows, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
  all_goals rcases hr with (rfl | rfl) | (rfl | rfl) <;>
    norm_num [weakRow, strictRow]

/-- Changed singleton membership also has a closed strip.  A constant
query equal to a knot is excluded by the exact s != t clause. -/
theorem changed_atom_strip (lower : Bool) (b : FloorAtom) {s t : ℝ}
    (hchange : ¬ (s ∈ tableAtomSet lower b ↔ t ∈ tableAtomSet lower b)) :
    AtomStrip lower b s t := by
  have hst : s ≠ t := by intro h; subst t; exact hchange Iff.rfl
  have hex : ∃ r ∈ atomRows lower b, ¬ (r.accepts 0 s ↔ r.accepts 0 t) := by
    by_contra hn
    push_neg at hn
    apply hchange
    rw [← atomRows_iff lower b 0 s, ← atomRows_iff lower b 0 t]
    exact ⟨fun hs r hr => (hn r hr).mp (hs r hr),
      fun ht r hr => (hn r hr).mpr (ht r hr)⟩
  obtain ⟨r,hr,h⟩ := hex
  have he := (changed_row_strip r h).2
  have hc := atomRows_coefficients hr
  exact ⟨hst,r,hr,by simpa only [hc.1,hc.2,abs_zero,zero_mul,one_mul,zero_add] using he⟩

def QueryMember (lo hi : ℝ) {mesh depth : ℕ} (p : TypedNode)
    (code : Program mesh depth) (z : Coordinates depth) (lower : Bool) (b : FloorAtom) : Prop :=
  Member lo hi depth p code z ∧
    (realize depth p code z).physical.argument ∈ tableAtomSet lower b

/-- Full domain plus the actual terminal closed atom, for every table
polarity.  No locality-only truncation is substituted for Member. -/
theorem changed_QueryMember_strip {lo hi : ℝ} {mesh depth : ℕ} {p q : TypedNode}
    (hu : p.upper=q.upper) (hc : p.physical.ceiling=q.physical.ceiling)
    (code : Program mesh depth) (z : Coordinates depth) (lower : Bool) (b : FloorAtom)
    (hchange : ¬ (QueryMember lo hi p code z lower b ↔ QueryMember lo hi q code z lower b)) :
    MemberStrip lo hi depth p q code z ∨
      (Member lo hi depth p code z ∧ Member lo hi depth q code z ∧
       AtomStrip lower b (realize depth p code z).physical.argument
         (realize depth q code z).physical.argument) := by
  by_cases hm : Member lo hi depth p code z ↔ Member lo hi depth q code z
  · have hp : Member lo hi depth p code z := by
      by_contra hn
      have hq : ¬ Member lo hi depth q code z := fun h => hn (hm.mpr h)
      exact hchange (by simp only [QueryMember,hn,hq,false_and])
    refine Or.inr ⟨hp,hm.mp hp,changed_atom_strip lower b ?_⟩
    intro he
    apply hchange
    simp only [QueryMember,hp,hm.mp hp,true_and]
    exact he
  · exact Or.inl (changed_Member_strip hu hc code z hm)

/-- Source U3/U4 roots have identical cell, type and slot data at every
precision.  The arbitrary finite-depth full Member difference is covered
without a membership hypothesis on either side. -/
theorem actual_root_Member_strip (n : ℕ) (k : Root) (tau t lo hi : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth)
    (hchange : ¬ (Member lo hi depth (sourceRoot k 0 t) code z ↔
      Member lo hi depth (frozenRoot n k tau t) code z)) :
    MemberStrip lo hi depth (sourceRoot k 0 t) (frozenRoot n k tau t) code z :=
  changed_Member_strip rfl rfl code z hchange

theorem actual_root_QueryMember_strip (n : ℕ) (k : Root) (tau t lo hi : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth)
    (lower : Bool) (b : FloorAtom)
    (hchange : ¬ (QueryMember lo hi (sourceRoot k 0 t) code z lower b ↔
      QueryMember lo hi (frozenRoot n k tau t) code z lower b)) :
    MemberStrip lo hi depth (sourceRoot k 0 t) (frozenRoot n k tau t) code z ∨
      (Member lo hi depth (sourceRoot k 0 t) code z ∧
       Member lo hi depth (frozenRoot n k tau t) code z ∧
       AtomStrip lower b (realize depth (sourceRoot k 0 t) code z).physical.argument
         (realize depth (frozenRoot n k tau t) code z).physical.argument) :=
  changed_QueryMember_strip rfl rfl code z lower b hchange

/-- The root loss is the sole residual displacement at EVERY prefix.
This is the actual explicit row width, not an assumed error supplier. -/
theorem actual_row_width {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth) (r : GateRow) :
    |r.level|*|residual (realize depth (sourceRoot k 0 t) code z).physical-
      residual (realize depth (frozenRoot n k tau t) code z).physical| ≤
        |r.level|*levelError n tau := by
  rw [actual_descendant_residual_loss, abs_of_nonneg (rootLoss_bounds htau htauhi ht).1]
  exact mul_le_mul_of_nonneg_left (rootLoss_bounds htau htauhi ht).2 (abs_nonneg _)

/-- At each common admitted prefix supplied by MemberStrip recursion,
the full row width tends to zero.  This is not a uniform parent-mass
statement, and a non-proper zero stratum is not discarded. -/
theorem actual_row_width_tendsto {k : Root} {t lo hi : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) (r : GateRow) :
    Tendsto (fun n => |r.level|*levelError n (finiteTau n) +
      |r.query|*|(idealDescendant k t code z).argument-
        (frozenDescendant n k t code z).argument|) atTop (𝓝 0) := by
  have harg := (tendsto_const_nhds.sub (frozenDescendant_argument_tendsto ht hz)).abs
  simpa only [sub_self,abs_zero,mul_zero,add_zero] using
    (tendsto_const_nhds.mul levelError_finiteTau_tendsto).add
      (tendsto_const_nhds.mul harg)

/-- All saved ancestor choices agree at the same native prefix.  The
statement includes inherit/equality choices of ANY fixed CapPlan. -/
theorem actual_same_prefix_choices {mesh depth capDepth capMesh : ℕ}
    (P : P2PhysicalIncomingPrefixCells.CapPlan capDepth capMesh)
    (a b : ℝ) (n : ℕ) (k : Root) (tau t : ℝ)
    (code : Program mesh depth) (z : Coordinates depth) (rank : ℕ) :
    P2PhysicalIncomingPrefixCells.incomingChoice P a b rank
      (markedWord (realize depth (sourceRoot k 0 t) code z).physical) =
    P2PhysicalIncomingPrefixCells.incomingChoice P a b rank
      (markedWord (realize depth (frozenRoot n k tau t) code z).physical) := by
  have hs := realize_slots_eq (p := sourceRoot k 0 t) (q := frozenRoot n k tau t)
    rfl code z
  unfold markedWord
  rw [hs]

/-- The analytic full/selected square lists are EXACTLY the same on the
two nodes at any fixed ell_aux.  This does not turn ell_aux into the
physical total or manufacture a legal distribution factorization. -/
theorem actual_same_coverGates (ell_aux : ℝ) (n : ℕ) (k : Root) (tau t : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth) :
    Part5OriginalH430RootSourceDictionary.coverGates ell_aux
      (realize depth (sourceRoot k 0 t) code z).physical ↔
    Part5OriginalH430RootSourceDictionary.coverGates ell_aux
      (realize depth (frozenRoot n k tau t) code z).physical := by
  have hs := realize_slots_eq (p := sourceRoot k 0 t) (q := frozenRoot n k tau t)
    rfl code z
  simp only [Part5OriginalH430RootSourceDictionary.coverGates, word, hs]

theorem perform_argument_eq_of_zeroArity {p q : PhysicalNode}
    (hs : p.argument=q.argument) (shape : StepShape) (z : Point)
    (hzero : arity shape=0) :
    (perform p shape z).argument=(perform q shape z).argument := by
  cases shape <;> simp_all [arity,perform,compareAt]

/-- Retain keeps the earlier query, while zero-prime comparisons use the
same fixed argument.  Equality at ANY original knot survives the whole
zero-prime segment exactly, regardless of the two residual levels. -/
theorem realize_argument_eq_of_zeroArity {mesh depth : ℕ} {p q : TypedNode}
    (hs : p.physical.argument=q.physical.argument)
    (code : Program mesh depth) (z : Coordinates depth)
    (hzero : ∀ i, arity (code i).1=0) :
    (realize depth p code z).physical.argument=(realize depth q code z).physical.argument := by
  induction depth generalizing p q with
  | zero => exact hs
  | succ depth ih =>
      exact ih (perform_argument_eq_of_zeroArity hs _ _ (hzero 0))
        (tail code) (tail z) (fun i => hzero i.succ)

/-- The positive-measure U3 clamp and every subsequent zero-prime
inherit/comparison segment have IDENTICAL atom membership, including
the adjacent minimum at two.  Nothing here declares the clamp null. -/
theorem actual_clamp_zeroPrime_atoms {n : ℕ} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand .U3)
    (hclamp : Part5UpperTables.OriginalU34.clampStart ≤ t)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth)
    (hzero : ∀ i, arity (code i).1=0) (lower : Bool) (b : FloorAtom) :
    ((realize depth (sourceRoot .U3 0 t) code z).physical.argument ∈ tableAtomSet lower b ↔
      (realize depth (frozenRoot n .U3 tau t) code z).physical.argument ∈ tableAtomSet lower b) := by
  have hs : (sourceRoot .U3 0 t).physical.argument=(frozenRoot n .U3 tau t).physical.argument :=
    (actual_U3_clamp hclamp).1.trans (finite_frozen_U3_clamp htau htauhi ht hclamp).1.symm
  rw [realize_argument_eq_of_zeroArity hs code z hzero]

/-- The cover is already applicable to the actual integer-log itinerary;
no freely chosen physical Program or replacement history is required. -/
theorem actual_integer_log_Member_strip {depth : ℕ}
    (N n mesh : ℕ) (k : Root) (tau : ℝ)
    (shape : Fin depth → StepShape) (p : NativeSlot shape → ℕ)
    (hchange : let x := nativePrimeLogs N p
      ¬ (Member 0 1 depth (sourceRoot k 0 (nativeRootCoordinate x))
          (nativeProgram mesh shape x) (nativeCoordinates shape x) ↔
        Member 0 1 depth (frozenRoot n k tau (nativeRootCoordinate x))
          (nativeProgram mesh shape x) (nativeCoordinates shape x))) :
    let x := nativePrimeLogs N p
    MemberStrip 0 1 depth (sourceRoot k 0 (nativeRootCoordinate x))
      (frozenRoot n k tau (nativeRootCoordinate x))
      (nativeProgram mesh shape x) (nativeCoordinates shape x) := by
  exact actual_root_Member_strip n k tau _ 0 1 _ _ hchange

end
end ImbalancedChen.Part5OriginalH430FullMemberStrips
