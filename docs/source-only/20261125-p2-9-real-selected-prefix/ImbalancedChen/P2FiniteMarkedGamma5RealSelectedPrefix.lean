import ImbalancedChen.P2FiniteMarkedGamma5StrictPhysicalChildren
import ImbalancedChen.P2FiniteMarkedGamma5FixedNativeItinerary
import ImbalancedChen.Part5OriginalH430RequestedFrontierTransport

namespace ImbalancedChen.P2FiniteMarkedGamma5RealSelectedPrefix
noncomputable section
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalH430FixedReadDictionary Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadRows Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430TaggedArithmeticReceivers
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430BankSlotTargets Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedFrontierTransport
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SeedHistoryMass Part5OriginalH430NativeQueryPaths
open Part5OriginalH430EmittedNativeQueries Part5OriginalH430JointQueryEnclosure
open P2FiniteMarkedGamma5StrictPhysicalChildren P2FiniteMarkedGamma5FixedNativeItinerary
open P2FiniteMarkedGamma5SelectedItinerary P2FiniteMarkedGamma5SelectedSeedTerminal

def bankGate (v : TypedNode) (z : Point) : Original106Action → StepShape → Prop
  | .inl (a,b), .w1Fixed i j => a=i ∧ b=j
  | .inl (a,b), .w1Singleton i j => a=i ∧ b=j ∧ singleGate v.physical (.w1 i j) z
  | .inr a, .w2Fixed j _ => a=j
  | .inr a, .w2Singleton j u => a=j ∧ singleGate v.physical (.w2 j u) z
  | .inr a, .w2Pair j u => a=j ∧ pairGate v.physical j u z
  | _,_ => False

def branch (v : TypedNode) (z : Point) : Choice → StepShape → Prop
  | .retained,.retain => True
  | .buchstab,.buchstabUpper => v.upper=true ∧ singleGate v.physical (.buchstab v.upper v.physical.argument) z
  | .buchstab,.buchstabLower => v.upper=false ∧ singleGate v.physical (.buchstab v.upper v.physical.argument) z
  | .bank j,s => bankGate v z (actionOfSlot j) s
  | _,_ => False

def modeAfter (owner : Fin 200) : StepShape → ReadMode
  | .retain => .cell owner
  | .w1Fixed _ j => .cell (w1Cell j)
  | .w2Fixed j b => .cell (w2Cell j b)
  | _ => .scalar

abbrev Row := ReadLabel × StepShape × Point

/-- The dummy word never enters the terminal table lookup. -/
def positive (v : TypedNode) (m : ReadMode) : Prop :=
  0 < requestValue (iterate 0) ⟨v,[],m⟩

def walk : ℕ → TypedNode → ReadMode → List Row → Prop
  | _,v,m,[] => positive v m
  | 0,_,_,_::_ => False
  | g+1,v,m,(a,s,z)::rows =>
      nodeResolve (g+1) v m = some a.1 ∧
      (roundDecision (iterate g) v.upper a.1).choice = a.2 ∧
      branch v z a.2 s ∧ walk g (advance v s z) (modeAfter a.1 s) rows

def selected {d : ℕ} (n : ℕ) (k : Root) (t : ℝ) (sh : Fin d → StepShape)
    (a : Fin d → ReadLabel) : Set (NativeSlot sh → ℝ) :=
  {z | d=430 ∧ walk 430 (frozenRoot n k t (z (.inl ()))) .scalar
    (List.ofFn fun i => (a i,sh i,nativeCoordinates sh z i))}

private def valid {N : ℕ} (a : ReadLabel) (e : Edge N) : Prop :=
  match e with
  | .retained i => a.1=i
  | .buchstab _ q | .w1Prime _ _ q | .w2Prime _ _ q => q.val.Prime ∧ q.val.Coprime N
  | .w2Pair _ _ (q,s) => (q.val.Prime ∧ q.val.Coprime N) ∧ (s.val.Prime ∧ s.val.Coprime N)
  | _ => True

private theorem mode_exact {N : ℕ} (a : ReadLabel) (e : Edge N) (h : valid a e) :
    modeAfter a.1 (edgeShape e) = edgeMode e := by
  cases e with
  | retained i => exact congrArg ReadMode.cell h
  | buchstab b q => cases b <;> rfl
  | _ => rfl

variable {N n p : ℕ} {k : Root} {t : ℝ}
variable (hN : 2 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
variable (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
include hN ht ht' hn hp

private theorem branch_exact {o : Occurrence N} (ho : o ∈ rootHistory N n k t p)
    (a : ReadLabel) (e : Edge N) (hv : valid a e) :
    branch o.current.node (edgeCoordinates e) a.2 (edgeShape e) ↔
      branchTest (rootQ N n k t p) o.current a.1 a.2 e := by
  have S := single_physical_iff hN ht ht' hn hp ho
  have P := pair_physical_iff hN ht ht' hn hp ho
  have one (q : Fin (N+1)) :
      (fun j : Fin 2 => physicalPrime N (![q.val,1] j)) = singleCoordinates N q.val := by
    funext j
    fin_cases j <;> simp [singleCoordinates,physicalPrime]
  have two (q s : Fin (N+1)) :
      (fun j : Fin 2 => physicalPrime N (![q.val,s.val] j)) = pairCoordinates N q.val s.val := by
    funext j
    fin_cases j <;> rfl
  obtain ⟨i,c⟩ := a
  cases c with
  | retained =>
    cases e with
    | retained j => exact iff_of_true trivial hv
    | buchstab b q => cases b <;> rfl
    | _ => rfl
  | buchstab =>
    cases e with
    | buchstab b q =>
      obtain ⟨h1,h2⟩ := hv
      cases b <;> simp [branch,branchTest,edgeShape,edgeCoordinates,edgePrimes,one, S _ q h1 h2]
    | _ => rfl
  | bank slot =>
    cases h : actionOfSlot slot with
    | inl ab =>
      obtain ⟨u,v⟩ := ab
      cases e with
      | w1Prime i j q =>
        obtain ⟨h1,h2⟩ := hv
        simp [branch,branchTest,h,bankGate,bankTest,edgeShape,edgeCoordinates,edgePrimes,one,S _ q h1 h2]
      | buchstab b q => cases b <;> simp [branch,branchTest,h,bankGate,bankTest,edgeShape]
      | _ => simp [branch,branchTest,h,bankGate,bankTest,edgeShape]
    | inr b =>
      cases e with
      | w2Prime i j q =>
        obtain ⟨h1,h2⟩ := hv
        simp [branch,branchTest,h,bankGate,bankTest,edgeShape,edgeCoordinates,edgePrimes,one,S _ q h1 h2]
      | w2Pair i j qs =>
        obtain ⟨q,s⟩ := qs
        obtain ⟨⟨hq,hcq⟩,hs,hcs⟩ := hv
        simp [branch,branchTest,h,bankGate,bankTest,edgeShape,edgeCoordinates,edgePrimes,two,P _ _ (q,s) hq hcq hs hcs]
      | buchstab b q => cases b <;> simp [branch,branchTest,h,bankGate,bankTest,edgeShape]
      | _ => simp [branch,branchTest,h,bankGate,bankTest,edgeShape]

private def rowsOf {N : ℕ} : (es : List (Edge N)) → (Fin es.length → ReadLabel) → List Row
  | [],_ => []
  | e::es,a => (a 0,edgeShape e,edgeCoordinates e)::rowsOf es (fun i => a i.succ)

private theorem walk_exact {o : Occurrence N} (ho : o ∈ rootHistory N n k t p)
    (es : List (Edge N)) (a : Fin es.length → ReadLabel)
    (hv : ∀ i, valid (a i) (es.get i)) :
    walk o.remaining o.current.node o.current.mode (rowsOf es a) ↔
      checked (rootQ N n k t p) o.remaining o.current es a ∧
      0 < requestValue (iterate 0) (replay o.current es) := by
  induction es generalizing o with
  | nil =>
    cases hm : o.current.mode <;> simp [walk,rowsOf,checked,replay,positive,requestValue,hm]
  | cons e es ih =>
    cases hg : o.remaining with
    | zero => simp [walk,rowsOf,checked]
    | succ g =>
      have he := hv 0
      have hb := branch_exact hN ht ht' hn hp ho (a 0) e he
      have hm := mode_exact (a 0) e he
      simp only [rowsOf,walk,checked,replay,hb,hm]
      constructor
      · rintro ⟨hi,hc,hs,tail⟩
        have mem := (specified_child_iff (by simpa only [project_resolve] using hi) hc e).mpr hs
        have ho' := history_extend_mem ho hg mem
        have ht' := (ih ho' (fun j => a j.succ) (fun j => hv j.succ))
        have hrem : (extend o e).remaining = g := by simp [extend,hg]
        rw [hrem] at ht'
        obtain ⟨hr,hp'⟩ := ht'.mp tail
        exact ⟨⟨hi,hc,hs,hr⟩,hp'⟩
      · rintro ⟨⟨hi,hc,hs,hr⟩,hp'⟩
        have mem := (specified_child_iff (by simpa only [project_resolve] using hi) hc e).mpr hs
        have ho' := history_extend_mem ho hg mem
        have ht' := (ih ho' (fun j => a j.succ) (fun j => hv j.succ))
        have hrem : (extend o e).remaining = g := by simp [extend,hg]
        rw [hrem] at ht'
        exact ⟨hi,hc,hs,ht'.mpr ⟨hr,hp'⟩⟩

omit hN ht ht' hn hp in
private theorem rows_formula {M : ℕ} (es : List (Edge M)) (a : Fin es.length → ReadLabel) :
    rowsOf es a = List.ofFn (fun i => (a i,edgeShape (es.get i),edgeCoordinates (es.get i))) := by
  induction es with
  | nil => simp [rowsOf]
  | cons e es ih => rw [List.ofFn_succ]; congr 1; exact ih _

omit hN ht ht' hn hp in
private theorem valid_at {M : ℕ} (s : StepShape) (hs : noTransport s) (a : ReadLabel)
    (xs : Fin (arity s) → Fin (M+1)) (h : ∀ i, (xs i).val.Prime ∧ (xs i).val.Coprime M) :
    valid a (edgeAt s hs a.1 xs) := by
  cases s with
  | transport i => exact False.elim (hs i rfl)
  | buchstabUpper | buchstabLower | w1Singleton | w2Singleton => exact h 0
  | w2Pair => exact ⟨h 0,h 1⟩
  | retain => rfl
  | _ => trivial

theorem fixed_prime_selected_iff {d : ℕ} (sh : Fin d → StepShape)
    (hs : ∀ i, noTransport (sh i)) (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1))
    (hroot : (x (.inl ())).val=p)
    (hx : ∀ j, (x j).val.Prime ∧ (x j).val.Coprime N) :
    (fun j => physicalPrime N (x j).val) ∈ selected n k t sh a ↔
      (∃ l ∈ seedPositions N n k t p, (levelOccurrence l).path=pathAt sh hs a x) ∧
        assigned 430 (rootRequest N n k t p) (pathAt sh hs a x) (readsAt sh hs a x) := by
  subst p
  let es := pathAt sh hs a x
  let r := rootRequest N n k t (x (.inl ())).val
  let u := readsAt sh hs a x
  let o : Occurrence N := origin 430 r
  have ho : o ∈ rootHistory N n k t (x (.inl ())).val := by
    change o ∈ _ :: _
    exact List.mem_cons.mpr (Or.inl rfl)
  have hvalid : ∀ i, valid (u i) (es.get i) := by
    intro i
    simpa [u,readsAt,es,pathAt] using valid_at _ (hs (Fin.cast (by simp [es,pathAt]) i))
      (u i) (fun j => x (.inr ⟨_,j⟩)) (fun j => hx (.inr ⟨_,j⟩))
  have hrows : rowsOf es u = List.ofFn (fun i => (a i,sh i,
      nativeCoordinates sh (fun j => physicalPrime N (x j).val) i)) := by
    rw [rows_formula]
    apply List.ext_get
    · simp [es,pathAt]
    · intro i hi hj
      simp only [List.length_ofFn] at hj
      simp [u,readsAt,es,pathAt,edgeAt_shape]
      funext j
      by_cases hj' : j.val < arity (sh ⟨i,hj⟩)
      · simpa [nativeCoordinates,hj'] using edgeAt_coordinate _ (hs ⟨i,hj⟩) (a ⟨i,hj⟩).1
          (fun v => x (.inr ⟨⟨i,hj⟩,v⟩)) ⟨j.val,hj'⟩
      · apply Eq.trans (unused_is_zero _ j (by simpa [edgeAt_shape] using hj'))
        simp [nativeCoordinates,hj']
  have W := walk_exact hN ht ht' hn hp ho es u hvalid
  rw [hrows] at W
  rw [fixed_path_seed_iff]
  have len : es.length=d := by simp [es,pathAt]
  change d=430 ∧ _ ↔ (es.length=430 ∧ _ ∧ _) ∧ _
  rw [len,W,checked_iff]
  tauto

end
end ImbalancedChen.P2FiniteMarkedGamma5RealSelectedPrefix
