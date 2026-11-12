import ImbalancedChen.Part5OriginalH430JointQueryEnclosure
import ImbalancedChen.Part5OriginalH430SmoothPrefixRequests
import ImbalancedChen.Part5OriginalH430OwnedRootCounts

/-! Literal coupling of the native-slot smooth tests with a real, selected
430 history occurrence. Native pair coordinates are small/large; the old
integer word is large/small. The conversion below keeps these orders distinct. -/
namespace ImbalancedChen.Part5OriginalH430EmittedNativeQueries
noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalCausalSmoothAtlas Part5OriginalH430SmoothPrefixRequests
open Part5OriginalH430JointQueryEnclosure
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalUpsilon5CausalDictionary Part5OriginalH430FullMemberStrips
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430NativeQueryPaths Part5OriginalH430IntegerItineraries
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430FixedReadDictionary Part5OriginalH430OwnedRootCounts
open Part5OriginalH430ClosedOwner P2PhysicalIncomingPrefixCells
open P2Selected430CausalOccurrenceExporter

def shapes {N : ℕ} (es : List (Edge N)) : Fin es.length → StepShape :=
  fun i => edgeShape (es.get i)

def tuple {N : ℕ} (p : ℕ) (es : List (Edge N)) : NativeSlot (shapes es) → ℝ
  | .inl _ => physicalPrime N p
  | .inr ⟨i,j⟩ => edgeCoordinates (es.get i) ⟨j.val, lt_of_lt_of_le j.isLt (arity_le_two _)⟩

/-- On the ACTUAL native axes, the root and all earlier edge slots stay fixed;
a pair contributes both small/large axes at precisely its own stage. -/
def past {d : ℕ} {sh : Fin d → StepShape} (t : ℕ) : NativeSlot sh → Prop
  | .inl _ => True
  | .inr ⟨i,_⟩ => i.val < t

def extend {ι : Type*} (before : ι → Prop) (A : Plan)
    (a : {i // before i} → Code A) (b : {i // ¬before i} → Code A) (i : ι) : Code A :=
  if h : before i then a ⟨i,h⟩ else b ⟨i,h⟩

theorem future_marginal {ι : Type*} [Fintype ι] (before : ι → Prop) (A : Plan)
    (a : {i // before i} → Code A) (x : ι → ℝ) (hx : ∀ i, x i ∈ Icc (0:ℝ) 1) :
    (∑ b : {i // ¬before i} → Code A, atom A (extend before A a b) x) =
      atom A a (fun i => x i.val) := by
  have hf (b : {i // ¬before i} → Code A) :
      atom A (extend before A a b) x =
        atom A a (fun i => x i.val) * atom A b (fun i => x i.val) := by
    have hl (i : {i // before i}) : extend before A a b i.val = a i := dif_pos i.property
    have hr (i : {i // ¬before i}) : extend before A a b i.val = b i := dif_neg i.property
    unfold atom
    rw [← Fintype.prod_subtype_mul_prod_subtype before (fun i => mask A (extend before A a b i) (x i))]
    simp only [hl,hr]
  simp only [hf,← Finset.mul_sum,atom_total A (fun i : {i // ¬before i} => hx i.val),mul_one]

theorem pathPrimes_at {N : ℕ} (es : List (Edge N)) (i : Fin es.length) :
    pathPrimes es i = edgePrimes (es.get i) := by
  induction es with
  | nil => exact Fin.elim0 i
  | cons e es ih => exact Fin.cases rfl (fun j => ih j) i

theorem pathCode_at {N : ℕ} (m : ℕ) (es : List (Edge N)) (i : Fin es.length) :
    pathCode m es i = (shapes es i,physicalLabel 0 1 m (edgeCoordinates (es.get i))) := by
  induction es with
  | nil => exact Fin.elim0 i
  | cons e es ih => exact Fin.cases rfl (fun j => ih j) i

theorem unused_is_zero {N : ℕ} (e : Edge N) (k : Fin 2)
    (hk : ¬ k.val < arity (edgeShape e)) : edgeCoordinates e k = 0 := by
  cases e with
  | buchstab b p => cases b <;> fin_cases k <;> simp_all [arity,edgeShape,edgePrimes,edgeCoordinates,physicalPrime]
  | w2Fixed b c => cases c <;> fin_cases k <;> simp_all [arity,edgeShape,edgePrimes,edgeCoordinates,physicalPrime]
  | _ => fin_cases k <;> simp_all [arity,edgeShape,edgePrimes,edgeCoordinates,physicalPrime]

theorem native_coordinates_exact {N : ℕ} (p : ℕ) (es : List (Edge N)) :
    nativeCoordinates (shapes es) (tuple p es) = physicalCoordinates N (pathPrimes es) := by
  funext i k
  change (if h : k.val < arity (shapes es i) then
    tuple p es (.inr ⟨i,⟨k.val,h⟩⟩) else 0) = physicalPrime N (pathPrimes es i k)
  rw [pathPrimes_at]
  split_ifs with h
  · rfl
  · exact (unused_is_zero (es.get i) k h).symm

theorem native_program_exact {N : ℕ} (p m : ℕ) (es : List (Edge N)) :
    nativeProgram m (shapes es) (tuple p es) = pathCode m es := by
  unfold nativeProgram
  rw [native_coordinates_exact]
  funext i
  rw [pathCode_at]
  change (_,physicalLabel 0 1 m (fun k => physicalPrime N (pathPrimes es i k))) = _
  rw [pathPrimes_at]
  rfl

/-- The only permutation in a pair is explicit on the original edge: slot
1 is appended before slot 0. Feedback still evaluates the tuple (0,1). -/
theorem pair_orders {N : ℕ} (a : Fin 36) (b : Fin 4) (v : Fin (N+1) × Fin (N+1)) :
    let e := Edge.w2Pair a b v
    appendedWord (edgeShape e) (edgePrimes e) = [v.2.val,v.1.val] ∧
      edgeCoordinates e 0 = physicalPrime N v.1.val ∧
      edgeCoordinates e 1 = physicalPrime N v.2.val := by exact ⟨rfl,rfl,rfl⟩

theorem bounds_on_path {N : ℕ} {Q : ℝ} (es : List (Edge N)) {r : Request} {g : ℕ}
    (hc : Coherent N Q r) (hs : ChosenPath N Q g r es) :
    ∀ i : Fin es.length, ∀ k : Fin 2, edgeCoordinates (es.get i) k ∈ Icc (0:ℝ) 1 := by
  induction es generalizing g r with
  | nil => intro i; exact Fin.elim0 i
  | cons e es ih =>
    cases g with
    | zero => exact False.elim hs
    | succ g =>
      intro i
      exact Fin.cases (fun k => child_coordinate_bounds hc hs.1 k)
        (fun j k => ih (child_coherent hc hs.1) hs.2 j k) i

theorem emitted_cube {N n : ℕ} {k : Root} {tau : ℝ} {p : ℕ} {o : Occurrence N}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (hb : physicalPrime N p ∈ rootBand k)
    (ho : o ∈ rootHistory N n k tau p) : Cube (tuple p o.path) := by
  have hc := root_coherent hN ht ht' hn hp hb
  have hedges := bounds_on_path o.path hc (history_facts ho).1
  rintro (u | ⟨i,j⟩)
  · exact coherent_prime_unit hc (p := p) (by simp [rootRequest])
  · exact hedges i _

theorem emitted_native_prefix_marginal (A : Plan) (t : ℕ) {N n : ℕ} {k : Root}
    {tau : ℝ} {p : ℕ} {o : Occurrence N} (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand k) (ho : o ∈ rootHistory N n k tau p)
    (j : {i : NativeSlot (shapes o.path) // past t i} → Code A) :
    (∑ b : {i : NativeSlot (shapes o.path) // ¬past t i} → Code A,
      atom A (extend (past t) A j b) (tuple p o.path)) =
      atom A j (fun i => tuple p o.path i.val) :=
  future_marginal (past t) A j _ (emitted_cube hN ht ht' hn hp hb ho)

theorem emitted_query_iff {N n : ℕ} {k : Root} {tau : ℝ} {p : ℕ} {o : Occurrence N}
    (m : ℕ) (lower : Bool) (b : FloorAtom) (hN : 1 < N) (ht : 0 ≤ tau)
    (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand k) (ho : o ∈ rootHistory N n k tau p) :
    tuple p o.path ∈ nativeQuery n m k tau (shapes o.path) lower b ↔
      o.current.node.physical.argument ∈ tableAtomSet lower b := by
  change (Member 0 1 _ (frozenRoot n k tau (physicalPrime N p))
      (nativeProgram m (shapes o.path) (tuple p o.path))
      (nativeCoordinates (shapes o.path) (tuple p o.path)) ∧ _) ↔ _
  simp only [native_program_exact,native_coordinates_exact]
  have hm := rootHistory_member m hN ht ht' hn hp hb ho
  rw [and_iff_right hm]
  have he := (rootHistory_realization m ho).1
  change (Part5OriginalH430FrozenIntegerSupport.historyNode N n k tau p
    (pathCode m o.path) (pathPrimes o.path)).physical.argument ∈ _ ↔ _
  rw [he]

/-- Actual scalar atom, evaluated at the emitted integer request on the same
native axes used by the smooth upper/lower functions. Works on a knot as well
as an open atom. Specified predecessor cell reads stay in the separate ledger. -/
theorem emitted_smooth_enclosure (A : Plan) {N n : ℕ} {k : Root} {tau : ℝ}
    {p : ℕ} {o : Occurrence N} (m : ℕ) (lower : Bool) (b : FloorAtom)
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (hb : physicalPrime N p ∈ rootBand k)
    (ho : o ∈ rootHistory N n k tau p) :
    let D := nativeQuery n m k tau (shapes o.path) lower b
    let x := tuple p o.path
    let sharp : ℝ := if o.current.node.physical.argument ∈ tableAtomSet lower b then 1 else 0
    readout A (sure A D) x ≤ sharp ∧ sharp ≤ readout A (hit A D) x ∧
      readout A (hit A D) x - readout A (sure A D) x = readout A (mixed A D) x := by
  dsimp only
  have hx := emitted_cube hN ht ht' hn hp hb ho
  have h := (every_native_query A n m k tau (shapes o.path) lower b).2.2.2 _ hx
  simpa only [emitted_query_iff m lower b hN ht ht' hn hp hb ho] using h

/-- The original resolve observes only the two fields below. This is a
projection of that read, never a change to the integer history of a request. -/
def nodeResolve (g : ℕ) (v : TypedNode) : ReadMode → Option (Fin 200)
  | .cell i => some i
  | .scalar =>
      if h : ∃ b : FloorAtom, v.physical.argument ∈ tableAtomSet (!v.upper) b then
        some (atomOwner (iterate g v.upper) (Classical.choose h)) else none

theorem project_resolve (g : ℕ) (r : Request) : nodeResolve g r.node r.mode = resolve g r := by
  cases r with | mk v word mode => cases mode <;> rfl

def nativeKey (n m : ℕ) (k : Root) (tau t : ℝ) : RootKey n m :=
  let v := frozenRoot n k tau t
  let s := v.physical.argument
  (rootCode n (sourceRoot k tau t).physical.total,nodeResolve 430 v .scalar,
    if s=2 then true else false,fun j => exponentCode 1 6 j.val s)

theorem nativeKey_exact (N n m : ℕ) (k : Root) (tau : ℝ) (p : ℕ) :
    nativeKey n m k tau (physicalPrime N p) = keyAt N n m k tau p := rfl

/-- A fixed physical root fibre, canonical integer Program, read mode, owner
and selected action, followed by the actual (open OR knot) terminal atom.
No integer divisibility or receiver count is replaced by a smooth gate. -/
def ownedQuery {d : ℕ} (n rootMesh mesh : ℕ) (k : Root) (tau : ℝ)
    (sh : Fin d → StepShape) (key : RootKey n rootMesh) (code : Program mesh d)
    (g : Fin 430) (mode : ReadMode) (owner : Fin 200) (a : Choice)
    (lower : Bool) (b : FloorAtom) : Set (NativeSlot sh → ℝ) := {x |
  let t := nativeRootCoordinate x
  let prog := nativeProgram mesh sh x
  let v := realize d (frozenRoot n k tau t) prog (nativeCoordinates sh x)
  nativeKey n rootMesh k tau t = key ∧ prog = code ∧
    (nodeResolve (g.val+1) v mode = some owner ∧ (roundDecision (iterate g.val) v.upper owner).choice = a) ∧
    x ∈ nativeQuery n mesh k tau sh lower b}

theorem emitted_owned_iff {N n : ℕ} {k : Root} {tau : ℝ} {p : ℕ} {o : Occurrence N}
    {rootMesh mesh : ℕ} (key : RootKey n rootMesh) (code : Program mesh o.path.length)
    (g : Fin 430) (owner : Fin 200) (a : Choice) (lower : Bool) (b : FloorAtom)
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (hb : physicalPrime N p ∈ rootBand k)
    (ho : o ∈ rootHistory N n k tau p) :
    tuple p o.path ∈ ownedQuery n rootMesh mesh k tau (shapes o.path) key code
      g o.current.mode owner a lower b ↔
    keyAt N n rootMesh k tau p = key ∧ pathCode mesh o.path = code ∧
      Selected g.val o.current owner a ∧ o.current.node.physical.argument ∈ tableAtomSet lower b := by
  have hnode : realize o.path.length (frozenRoot n k tau (physicalPrime N p))
      (pathCode mesh o.path) (physicalCoordinates N (pathPrimes o.path)) = o.current.node :=
    (rootHistory_realization mesh ho).1
  unfold ownedQuery
  change (nativeKey n rootMesh k tau (physicalPrime N p) = _ ∧ _ ∧ _ ∧
    tuple p o.path ∈ nativeQuery n mesh k tau (shapes o.path) lower b) ↔ _
  simp only [nativeKey_exact,native_program_exact,native_coordinates_exact,hnode,project_resolve,
    emitted_query_iff mesh lower b hN ht ht' hn hp hb ho,Selected]

end
end ImbalancedChen.Part5OriginalH430EmittedNativeQueries
