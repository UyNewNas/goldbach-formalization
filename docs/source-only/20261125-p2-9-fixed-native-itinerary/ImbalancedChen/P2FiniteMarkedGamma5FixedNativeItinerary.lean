import ImbalancedChen.P2FiniteMarkedGamma5SelectedSeedTerminal

namespace ImbalancedChen.P2FiniteMarkedGamma5FixedNativeItinerary
noncomputable section
open P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SeedHistoryMass
open Part5OriginalH430NativeQueryPaths Part5OriginalH430EmittedNativeQueries
open Part5OriginalH430JointQueryEnclosure
open P2FiniteMarkedGamma5SelectedItinerary P2FiniteMarkedGamma5SelectedSeedTerminal
open scoped Classical BigOperators

abbrev ReadLabel := Fin 200 × Choice

/-- The existing producer has exactly two nonbank choices and 106 bank slots. -/
private def choiceOf : Option (Option (Fin 106)) → Choice
  | none => .retained
  | some none => .buchstab
  | some (some k) => .bank k

theorem choices_finite : Finite Choice := Finite.of_surjective choiceOf (by
  intro c
  cases c with
  | retained => exact ⟨none,rfl⟩
  | buchstab => exact ⟨some none,rfl⟩
  | bank k => exact ⟨some (some k),rfl⟩)

theorem fixed_indices_finite (d : ℕ) : Finite ((Fin d → StepShape) × (Fin d → ReadLabel)) := by
  letI : Finite Choice := choices_finite
  infer_instance

def noTransport (s : StepShape) : Prop := ∀ i, s ≠ .transport i

theorem emitted_noTransport {N : ℕ} (e : Edge N) : noTransport (edgeShape e) := by
  intro i
  cases e with
  | buchstab b p => cases b <;> simp [edgeShape]
  | _ => simp [edgeShape]

/-- A retained label is supplied by the resolved owner. Native pair
coordinate 0 is the smaller prime and 1 the larger, as at the source. -/
def edgeAt {N : ℕ} : (s : StepShape) → noTransport s → Fin 200 →
    (Fin (arity s) → Fin (N+1)) → Edge N
  | .retain, _, i, _ => .retained i
  | .transport j, h, _, _ => False.elim (h j rfl)
  | .buchstabUpper, _, _, x => .buchstab true (x 0)
  | .buchstabLower, _, _, x => .buchstab false (x 0)
  | .w1Fixed a b, _, _, _ => .w1Fixed a b
  | .w1Singleton a b, _, _, x => .w1Prime a b (x 0)
  | .w2Fixed a b, _, _, _ => .w2Fixed a b
  | .w2Singleton a b, _, _, x => .w2Prime a b (x 0)
  | .w2Pair a b, _, _, x => .w2Pair a b (x 0,x 1)

def slots {N : ℕ} : (e : Edge N) → Fin (arity (edgeShape e)) → Fin (N+1)
  | .retained _, i => Fin.elim0 i
  | .buchstab true p, _ => p
  | .buchstab false p, _ => p
  | .w1Fixed _ _, i => Fin.elim0 i
  | .w1Prime _ _ p, _ => p
  | .w2Fixed _ _, i => Fin.elim0 i
  | .w2Prime _ _ p, _ => p
  | .w2Pair _ _ pp, i => if i.val=0 then pp.1 else pp.2

private def ownerFits {N : ℕ} (i : Fin 200) : Edge N → Prop
  | .retained j => i = j
  | _ => True

private theorem ownerFits_of_branch {N : ℕ} {Q : ℝ} {r : Request} {i : Fin 200}
    {c : Choice} {e : Edge N} (h : branchTest Q r i c e) : ownerFits i e := by
  cases e with
  | retained j =>
    cases c with
    | retained => exact h
    | buchstab => exact False.elim h
    | bank k =>
      cases ha : Part5OriginalH430BankSlotTargets.actionOfSlot k <;>
        simp [branchTest,ha,bankTest] at h
  | _ => trivial

private theorem edgeAt_slots {N : ℕ} (e : Edge N) {i : Fin 200} (h : ownerFits i e) :
    edgeAt (edgeShape e) (emitted_noTransport e) i (slots e) = e := by
  cases e with
  | retained j => exact congrArg Edge.retained h
  | buchstab b p => cases b <;> rfl
  | w2Pair a b pp => cases pp; rfl
  | _ => rfl

/-- The full ancestor predicate on successively reconstructed physical
states. branchTest uses the original ordered prime and coprimality
tests, parent window, strict production domains and modulus caps. -/
def checked {N : ℕ} (Q : ℝ) :
    (g : ℕ) → (r : Request) → (es : List (Edge N)) → (Fin es.length → ReadLabel) → Prop
  | _, _, [], _ => True
  | 0, _, _::_, _ => False
  | g+1, r, e::es, a =>
    nodeResolve (g+1) r.node r.mode = some (a 0).1 ∧
    (roundDecision (iterate g) r.node.upper (a 0).1).choice = (a 0).2 ∧
    branchTest Q r (a 0).1 (a 0).2 e ∧
    checked Q g (nextRequest r e) es (fun j => a j.succ)

/-- Literal producer read labels only; membership of the emitted edge in
a prime carrier is not part of this assignment. -/
def assigned {N : ℕ} :
    (g : ℕ) → (r : Request) → (es : List (Edge N)) → (Fin es.length → ReadLabel) → Prop
  | _, _, [], _ => True
  | 0, _, _::_, _ => False
  | g+1, r, e::es, a =>
    resolve (g+1) r = some (a 0).1 ∧
    (roundDecision (iterate g) r.node.upper (a 0).1).choice = (a 0).2 ∧
    assigned g (nextRequest r e) es (fun j => a j.succ)

theorem checked_iff {N : ℕ} (Q : ℝ) (g : ℕ) (r : Request) (es : List (Edge N))
    (a : Fin es.length → ReadLabel) :
    checked Q g r es a ↔ accepts Q g r es ∧ assigned g r es a := by
  induction es generalizing g r with
  | nil => cases g <;> simp [checked,accepts,assigned]
  | cons e es ih =>
    cases g with
    | zero => simp [checked,accepts,assigned]
    | succ g =>
      constructor
      · rintro ⟨hi,hc,hb,htail⟩
        rw [project_resolve] at hi
        obtain ⟨hs,ha⟩ := (ih g (nextRequest r e) _).mp htail
        exact ⟨⟨⟨_,_,hi,hc,hb⟩,hs⟩,hi,hc,ha⟩
      · rintro ⟨⟨⟨i,c,hi,hc,hb⟩,hs⟩,hi',hc',ha⟩
        have he : i = (a 0).1 := Option.some.inj (hi.symm.trans hi')
        have he' : c = (a 0).2 := by simpa only [← he, hc] using hc'
        exact ⟨by simpa only [project_resolve] using hi',hc',
          by simpa only [← he, ← he'] using hb,(ih g (nextRequest r e) _).mpr ⟨hs,ha⟩⟩

theorem accepts_of_checked {N : ℕ} {Q : ℝ} {g : ℕ} {r : Request} {es : List (Edge N)}
    (a : Fin es.length → ReadLabel) (ha : checked Q g r es a) : accepts Q g r es := ((checked_iff Q g r es a).mp ha).1

theorem accepts_iff_unique_reads {N : ℕ} (Q : ℝ) (g : ℕ) (r : Request) (es : List (Edge N)) :
    accepts Q g r es ↔ ∃! a : Fin es.length → ReadLabel, checked Q g r es a := by
  induction es generalizing g r with
  | nil =>
    cases g <;>
      exact ⟨fun _ => ⟨Fin.elim0,trivial,fun _ _ => funext fun i => Fin.elim0 i⟩,fun _ => trivial⟩
  | cons e es ih =>
    cases g with
    | zero => exact ⟨False.elim,fun ⟨_,h,_⟩ => h⟩
    | succ g =>
      constructor
      · rintro ⟨⟨i,c,hi,hc,hb⟩,hs⟩
        obtain ⟨tail,ht,hu⟩ := (ih g (nextRequest r e)).mp hs
        refine ⟨Fin.cases (i,c) tail,⟨by simpa only [project_resolve] using hi,hc,hb,ht⟩,?_⟩
        intro a ha
        obtain ⟨hi',hc',hb',ht'⟩ := ha
        rw [project_resolve,hi] at hi'
        have hi0 := Option.some.inj hi'
        have hc0 : c = (a 0).2 := by simpa only [← hi0, hc] using hc'
        have htail := hu (fun j => a j.succ) ht'
        funext j
        refine Fin.cases ?_ (fun l => congrFun htail l) j
        exact Prod.ext hi0.symm hc0.symm
      · rintro ⟨a,ha,_⟩
        obtain ⟨hi,hc,hb,ht⟩ := ha
        refine ⟨⟨_,_,by simpa only [project_resolve] using hi,hc,hb⟩,?_⟩
        exact accepts_of_checked (fun j => a j.succ) ht

private theorem fits_at {N : ℕ} {Q : ℝ} {g : ℕ} {r : Request}
    {es : List (Edge N)} {a : Fin es.length → ReadLabel} (ha : checked Q g r es a) :
    ∀ i, ownerFits (a i).1 (es.get i) := by
  induction es generalizing g r with
  | nil => exact Fin.elim0
  | cons e es ih =>
    cases g with
    | zero => exact False.elim ha
    | succ g =>
      intro i
      exact Fin.cases (ownerFits_of_branch ha.2.2.1)
        (fun j => ih ha.2.2.2 j) i

/-- Only the argument x varies over the bounded integer tuples. The
root is kept at the distinguished outer slot of the existing NativeSlot. -/
def pathAt {d N : ℕ} (sh : Fin d → StepShape) (hs : ∀ i, noTransport (sh i))
    (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1)) : List (Edge N) :=
  List.ofFn (fun i => edgeAt (sh i) (hs i) (a i).1 (fun j => x (.inr ⟨i,j⟩)))

def coordinates {N : ℕ} (p : Fin (N+1)) (es : List (Edge N)) :
    NativeSlot (shapes es) → Fin (N+1)
  | .inl _ => p
  | .inr ⟨i,j⟩ => slots (es.get i) j

theorem edgeAt_shape {N : ℕ} (s : StepShape) (hs : noTransport s) (i : Fin 200)
    (x : Fin (arity s) → Fin (N+1)) : edgeShape (edgeAt s hs i x) = s := by
  cases s with
  | transport j => exact False.elim (hs j rfl)
  | _ => rfl

theorem edgeAt_coordinate {N : ℕ} (s : StepShape) (hs : noTransport s) (i : Fin 200)
    (x : Fin (arity s) → Fin (N+1)) (j : Fin (arity s)) :
    edgeCoordinates (edgeAt s hs i x) ⟨j.val,lt_of_lt_of_le j.isLt (arity_le_two _)⟩ =
      physicalPrime N (x j).val := by
  cases s with
  | transport k => exact False.elim (hs k rfl)
  | _ => fin_cases j <;> rfl

/-- Every accepted arithmetic path is recovered on its original ordered
native coordinates and its uniquely determined finite read sequence. -/
theorem recover_path {N g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    {a : Fin es.length → ReadLabel} (p : Fin (N+1)) (ha : checked Q g r es a) :
    pathAt (shapes es) (fun i => emitted_noTransport (es.get i)) a (coordinates p es) = es := by
  unfold pathAt
  calc
    _ = List.ofFn es.get := by
      congr 1
      funext i
      exact edgeAt_slots _ (fits_at ha i)
    _ = es := List.ofFn_get es

def readsAt {d N : ℕ} (sh : Fin d → StepShape) (hs : ∀ i, noTransport (sh i))
    (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1)) :
    Fin (pathAt sh hs a x).length → ReadLabel :=
  fun i => a (Fin.cast (by simp [pathAt]) i)

/-- For a fixed index, the original complete positive seed and all its
specified ancestor reads are tested on a single freely varying tuple. -/
theorem fixed_index_seed {N n : ℕ} {k : Root} {t : ℝ} (mesh : ℕ)
    {d : ℕ} (sh : Fin d → StepShape) (hs : ∀ i, noTransport (sh i))
    (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1))
    (hN : 1 < N) (ht : 0 ≤ t) (ht' : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : (x (.inl ())).val.Prime ∧ (x (.inl ())).val.Coprime N)
    (hb : physicalPrime N (x (.inl ())).val ∈ rootBand k) :
    let p := (x (.inl ())).val
    let es := pathAt sh hs a x
    let r := rootRequest N n k t p
    let Q := rootQ N n k t p
    let reads := readsAt sh hs a x
    let terminal := replay r es
    ((∃ l ∈ seedPositions N n k t p, (levelOccurrence l).path = es) ∧
        assigned 430 r es reads) ↔
      d = 430 ∧ checked Q 430 r es reads ∧ terminalTest terminal (fun b =>
        tuple p es ∈ nativeQuery n mesh k t (shapes es) (!terminal.node.upper) b) := by
  dsimp only
  rw [fixed_path_native_seed_iff mesh _ hN ht ht' hn hp hb]
  have hlen : (pathAt sh hs a x).length = d := by simp [pathAt]
  rw [hlen]
  constructor
  · rintro ⟨⟨hd,hacc,hter⟩,hlabels⟩
    exact ⟨hd,(checked_iff _ _ _ _ _).mpr ⟨hacc,hlabels⟩,hter⟩
  · rintro ⟨hd,hreads,hter⟩
    obtain ⟨hacc,hlabels⟩ := (checked_iff _ _ _ _ _).mp hreads
    exact ⟨⟨hd,hacc,hter⟩,hlabels⟩

/-- The old chronological edge number and its slot index are unchanged
under decoding, even though the two Fin types display different bounds. -/
def stageEquiv {d N : ℕ} (sh : Fin d → StepShape) (hs : ∀ i, noTransport (sh i))
    (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1)) :
    Fin d ≃ Fin (pathAt sh hs a x).length :=
  finCongr (by simp [pathAt])

private theorem pathAt_get {d N : ℕ} (sh : Fin d → StepShape) (hs : ∀ i, noTransport (sh i))
    (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1)) (i : Fin d) :
    (pathAt sh hs a x).get (stageEquiv sh hs a x i) =
      edgeAt (sh i) (hs i) (a i).1 (fun j => x (.inr ⟨i,j⟩)) := by
  simp [stageEquiv,pathAt]

theorem pathAt_shape {d N : ℕ} (sh : Fin d → StepShape) (hs : ∀ i, noTransport (sh i))
    (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1)) (i : Fin d) :
    shapes (pathAt sh hs a x) (stageEquiv sh hs a x i) = sh i := by
  unfold shapes
  rw [pathAt_get,edgeAt_shape]

def nativeSlotEquiv {d N : ℕ} (sh : Fin d → StepShape) (hs : ∀ i, noTransport (sh i))
    (a : Fin d → ReadLabel) (x : NativeSlot sh → Fin (N+1)) :
    NativeSlot sh ≃ NativeSlot (shapes (pathAt sh hs a x)) :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sigmaCongr (stageEquiv sh hs a x)
    (fun i => finCongr (congrArg arity (pathAt_shape sh hs a x i).symm)))

/-- Pulling the emitted real tuple back to the fixed atlas recovers
every physical prime coordinate, including the distinguished root. -/
theorem tuple_pathAt_pullback {d N : ℕ} (sh : Fin d → StepShape)
    (hs : ∀ i, noTransport (sh i)) (a : Fin d → ReadLabel)
    (x : NativeSlot sh → Fin (N+1)) :
    (fun j => tuple (x (.inl ())).val (pathAt sh hs a x) (nativeSlotEquiv sh hs a x j)) =
      fun j => physicalPrime N (x j).val := by
  funext j
  rcases j with u | ⟨i,j⟩
  · cases u
    rfl
  · change edgeCoordinates ((pathAt sh hs a x).get (stageEquiv sh hs a x i))
      ⟨j.val,lt_of_lt_of_le j.isLt (arity_le_two _)⟩ = _
    rw [pathAt_get]
    exact edgeAt_coordinate _ _ _ _ j

theorem fixed_chart_value {d N : ℕ} (sh : Fin d → StepShape)
    (hs : ∀ i, noTransport (sh i)) (a : Fin d → ReadLabel)
    (x : NativeSlot sh → Fin (N+1)) (F : (NativeSlot sh → ℝ) → ℝ) :
    F (fun j => tuple (x (.inl ())).val (pathAt sh hs a x) (nativeSlotEquiv sh hs a x j)) =
      F (fun j => physicalPrime N (x j).val) :=
  congrArg F (tuple_pathAt_pullback sh hs a x)

private theorem same_edgeWeight {N M : ℕ} (s : StepShape) (hs : noTransport s)
    (i : Fin 200) (x : Fin (arity s) → Fin (N+1)) (y : Fin (arity s) → Fin (M+1)) :
    edgeWeight (edgeAt s hs i x) = edgeWeight (edgeAt s hs i y) := by
  cases s with
  | transport j => exact False.elim (hs j rfl)
  | w2Fixed b v => cases v <;> rfl
  | _ => rfl

/-- The coefficient itself is the existing product of original edge
weights at both scales. Admissibility changes only its indicator. -/
theorem pathAt_weight_independent {d N M : ℕ} (sh : Fin d → StepShape)
    (hs : ∀ i, noTransport (sh i)) (a : Fin d → ReadLabel)
    (x : NativeSlot sh → Fin (N+1)) (y : NativeSlot sh → Fin (M+1)) :
    ((pathAt sh hs a x).map edgeWeight).prod = ((pathAt sh hs a y).map edgeWeight).prod := by
  have h : (fun i : Fin d => edgeWeight (edgeAt (sh i) (hs i) (a i).1
        (fun j => x (.inr ⟨i,j⟩)))) =
      (fun i : Fin d => edgeWeight (edgeAt (sh i) (hs i) (a i).1
        (fun j => y (.inr ⟨i,j⟩)))) := by
    funext i
    exact same_edgeWeight _ _ _ _ _
  simpa only [pathAt,List.map_ofFn,Function.comp_def] using
    congrArg (fun f : Fin d → ℝ => (List.ofFn f).prod) h

theorem fixed_index_mark {d N M : ℕ} (sh : Fin d → StepShape)
    (hs : ∀ i, noTransport (sh i)) (a : Fin d → ReadLabel)
    (x : NativeSlot sh → Fin (N+1)) (y : NativeSlot sh → Fin (M+1))
    (Q : ℝ) (g : ℕ) (r : Request) :
    (((history N Q g r).filter (fun o => decide (o.path = pathAt sh hs a x))).map mark).sum =
      if accepts Q g r (pathAt sh hs a x) then ((pathAt sh hs a y).map edgeWeight).prod else 0 := by
  rw [fixed_path_mark, pathAt_weight_independent sh hs a x y]

end
end ImbalancedChen.P2FiniteMarkedGamma5FixedNativeItinerary
