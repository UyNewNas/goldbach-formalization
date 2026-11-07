import ImbalancedChen.P2OriginalEfficientPriorityHeap
import ImbalancedChen.P2OriginalPriorityForestLedger
import ImbalancedChen.P2OriginalCompactQ80Encloser

/-!
SOURCEONLY / UNCOMPILED / FINITE RUN UNEVALUATED / P2.4 ENDPOINT OPEN.

The executable evaluator is the concrete original Q80 implementation, not an
`enclose` argument. Heap jobs carry source addresses only for efficient forest
updates; their order uses exactly (-(hi-lo), serial). Every terminal source
leaf, including exact and empty leaves, remains in the ordered forest.
-/
namespace ImbalancedChen.P2OriginalCompactConcreteRunSourceOnly

open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalAdaptiveSourceSplitSourceOnly
open P2OriginalPrioritySerialQueueSourceOnly
open P2OriginalPriorityForestLedgerSourceOnly
open P2OriginalEfficientPriorityHeapSourceOnly

abbrev originalEnclose := P2OriginalCompactQ80EncloserSourceOnly.enclose
abbrev OriginalTree (c : SeedCell) := SourceTree originalEnclose c
abbrev OriginalForest (cs : List SeedCell) := SourceForest originalEnclose cs

/-- Split at a root-to-leaf address. At the leaf, run precisely the original
strict midpoint assertion before constructing side0 and side1. No classical
choice, scan of all leaves, or supplied source-tree witness occurs here. -/
def splitTreeAt (serial : ℕ) : {c : SeedCell} → OriginalTree c → List Bool →
    Option (Entry × OriginalTree c)
  | _, .leaf c old, [] =>
      if width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c) then
        some (⟨c,originalEnclose c,old⟩,
          .split c width
            (.leaf (sourceLeft c) (issueSerial originalEnclose (sourceLeft c) serial))
            (.leaf (sourceRight c)
              (issueSerial originalEnclose (sourceRight c)
                (advance originalEnclose (sourceLeft c) serial))))
      else none
  | _, .split c width left right, false :: path =>
      (splitTreeAt serial left path).map fun result =>
        (result.1,.split c width result.2 right)
  | _, .split c width left right, true :: path =>
      (splitTreeAt serial right path).map fun result =>
        (result.1,.split c width left result.2)
  | _, _, _ => none

/-- Actual source refinement is derived from the executable address update. -/
theorem splitTreeAt_refines {c : SeedCell} (tree : OriginalTree c) (serial : ℕ)
    (path : List Bool) (p : Entry) (tree' : OriginalTree c)
    (h : splitTreeAt serial tree path = some (p,tree')) :
    TreeRefines originalEnclose serial p tree tree' := by
  induction tree generalizing path p tree' with
  | leaf c old =>
      cases path with
      | nil =>
          by_cases hw : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)
          · simp only [splitTreeAt,dif_pos hw] at h
            cases h
            exact TreeRefines.root c old hw
          · simp [splitTreeAt,hw] at h
      | cons b path => simp [splitTreeAt] at h
  | split c width left right ihL ihR =>
      cases path with
      | nil => simp [splitTreeAt] at h
      | cons side path =>
          cases side with
          | false =>
              cases hs : splitTreeAt serial left path with
              | none => simp [splitTreeAt,hs] at h
              | some result =>
                  rcases result with ⟨parent,left'⟩
                  simp only [splitTreeAt,hs,Option.map_some] at h
                  cases h
                  exact TreeRefines.left width right (ihL path parent left' hs)
          | true =>
              cases hs : splitTreeAt serial right path with
              | none => simp [splitTreeAt,hs] at h
              | some result =>
                  rcases result with ⟨parent,right'⟩
                  simp only [splitTreeAt,hs,Option.map_some] at h
                  cases h
                  exact TreeRefines.right width left (ihR path parent right' hs)

/-- The seed number selects one of the ORIGINAL normalized raw21 roots. -/
def splitForestAt (serial : ℕ) : {cs : List SeedCell} → OriginalForest cs →
    ℕ → List Bool → Option (Entry × OriginalForest cs)
  | _, .nil, _, _ => none
  | _, .cons tree rest, 0, path =>
      (splitTreeAt serial tree path).map fun result => (result.1,.cons result.2 rest)
  | _, .cons tree rest, seed + 1, path =>
      (splitForestAt serial rest seed path).map fun result => (result.1,.cons tree result.2)

theorem splitForestAt_refines {cs : List SeedCell} (forest : OriginalForest cs)
    (serial seed : ℕ) (path : List Bool) (p : Entry) (forest' : OriginalForest cs)
    (h : splitForestAt serial forest seed path = some (p,forest')) :
    ForestRefines originalEnclose serial p forest forest' := by
  induction forest generalizing seed p forest' with
  | nil => simp [splitForestAt] at h
  | cons tree rest ih =>
      cases seed with
      | zero =>
          cases hs : splitTreeAt serial tree path with
          | none => simp [splitForestAt,hs] at h
          | some result =>
              rcases result with ⟨parent,tree'⟩
              simp only [splitForestAt,hs,Option.map_some] at h
              cases h
              exact ForestRefines.here rest (splitTreeAt_refines tree serial path parent tree' hs)
      | succ seed =>
          cases hs : splitForestAt serial rest seed path with
          | none => simp [splitForestAt,hs] at h
          | some result =>
              rcases result with ⟨parent,rest'⟩
              simp only [splitForestAt,hs,Option.map_some] at h
              cases h
              exact ForestRefines.there tree (ih seed parent rest' hs)

/-- Cached parent data is checked at the addressed leaf. This finite check
prevents a stale address from silently replacing a different source leaf. -/
def SameEntry (p q : Entry) : Prop :=
  (∀ i : Fin 3, p.cell.1 i = q.cell.1 i ∧ p.cell.2 i = q.cell.2 i) ∧
  p.bounds.lower = q.bounds.lower ∧ p.bounds.upper = q.bounds.upper ∧ p.serial = q.serial

instance (p q : Entry) : Decidable (SameEntry p q) := inferInstanceAs
  (Decidable ((∀ i : Fin 3, p.cell.1 i = q.cell.1 i ∧ p.cell.2 i = q.cell.2 i) ∧
    p.bounds.lower = q.bounds.lower ∧ p.bounds.upper = q.bounds.upper ∧ p.serial = q.serial))

theorem sameEntry_iff (p q : Entry) : SameEntry p q ↔ p = q := by
  constructor
  · rintro ⟨hc,hl,hu,hs⟩
    have hc' : p.cell = q.cell := Prod.ext (funext fun i => (hc i).1) (funext fun i => (hc i).2)
    have hb : p.bounds = q.bounds := by
      cases p.bounds
      cases q.bounds
      simp_all
    cases p
    cases q
    simp_all
  · intro h
    subst q
    exact ⟨fun _ => ⟨rfl,rfl⟩,rfl,rfl,rfl⟩

/-- Side0 precedes side1, and serials advance only for positive error. -/
def spawnJobs (serial : ℕ) (parent : Entry) (seed : ℕ) (path : List Bool) : List Scheduled :=
  [⟨issue originalEnclose (sourceLeft parent.cell) serial,seed,path ++ [false]⟩,
   ⟨issue originalEnclose (sourceRight parent.cell)
      (advance originalEnclose (sourceLeft parent.cell) serial),seed,path ++ [true]⟩]

def treeJobs {c : SeedCell} (seed : ℕ) (path : List Bool) : OriginalTree c → List Scheduled
  | .leaf c serial => [⟨⟨c,originalEnclose c,serial⟩,seed,path⟩]
  | .split _ _ left right =>
      treeJobs seed (path ++ [false]) left ++ treeJobs seed (path ++ [true]) right

def forestJobs : {cs : List SeedCell} → OriginalForest cs → ℕ → List Scheduled
  | _, .nil, _ => []
  | _, .cons tree rest, seed => treeJobs seed [] tree ++ forestJobs rest (seed + 1)

theorem treeJobs_entries {c : SeedCell} (tree : OriginalTree c) (seed : ℕ) (path : List Bool) :
    (treeJobs seed path tree).map Scheduled.entry = treeEntries tree := by
  induction tree generalizing path with
  | leaf c serial => rfl
  | split c width left right ihL ihR =>
      simp only [treeJobs,treeEntries,List.map_append,ihL,ihR]

theorem forestJobs_entries {cs : List SeedCell} (forest : OriginalForest cs) (seed : ℕ) :
    (forestJobs forest seed).map Scheduled.entry = entries forest := by
  induction forest generalizing seed with
  | nil => rfl
  | cons tree rest ih =>
      simp only [forestJobs,entries,List.map_append,treeJobs_entries,ih]

/-- Every evaluator call contributes charges. Only positive uncertainty puts
its addressed entry into the active queue. -/
def putActive (queue : Queue) (job : Scheduled) : Queue :=
  if active job.entry then Batteries.PairingHeap.insert job queue else queue

def putJobs : Queue → List Scheduled → Queue
  | queue, [] => queue
  | queue, job :: rest => putJobs (putActive queue job) rest

def activeJobs (jobs : List Scheduled) : List Scheduled :=
  jobs.filter fun job => decide (active job.entry)

theorem putActive_contents (queue : Queue) (job : Scheduled) :
    (contents (putActive queue job) : Multiset Scheduled) =
      (activeJobs [job] : Multiset Scheduled) + (contents queue : Multiset Scheduled) := by
  by_cases ha : active job.entry
  · simp only [putActive,if_pos ha,contents_insert]
    simp [activeJobs,ha]
  · simp [putActive,ha,activeJobs]

theorem putJobs_contents (queue : Queue) (jobs : List Scheduled) :
    (contents (putJobs queue jobs) : Multiset Scheduled) =
      (activeJobs jobs : Multiset Scheduled) + (contents queue : Multiset Scheduled) := by
  induction jobs generalizing queue with
  | nil => simp [putJobs,activeJobs]
  | cons job jobs ih =>
      rw [putJobs,ih,putActive_contents]
      by_cases ha : active job.entry <;>
        simp [activeJobs,ha,add_assoc,add_left_comm,add_comm]

/-- Executable diagnostic guard, never classical proposition choice. This is
exactly the encloser supplier's stated sourceAssertions scope; it does not
claim that the supplier has proved every internal Python primitive guard. -/
instance (c : SeedCell) : Decidable
    (P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions c) := by
  unfold P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions
    P2OriginalCompactQ80EncloserSourceOnly.jensenAssertions
  cases P2OriginalCompactQ80EncloserSourceOnly.affineCapLower c <;> infer_instance

def sourceCheck (c : SeedCell) : Bool :=
  decide (P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions c)
structure DriverState where
  forest : OriginalForest initialSeeds
  queue : Queue
  serial : ℕ
  splits : ℕ
  totalLower : ℤ
  totalUpper : ℤ
  assertionsPassed : Bool

/-- This is an actual state value at the original normalized21 seeds. -/
def initialDriverState : DriverState :=
  let init := seedForest originalEnclose initialSeeds 0
  ⟨init.1,putJobs Batteries.PairingHeap.empty (forestJobs init.1 0),init.2,0,
    lowerSum (entries init.1),upperSum (entries init.1),
    P2OriginalCompactQ80EncloserSourceOnly.tableAssertions && initialSeeds.all sourceCheck⟩

def LedgerInvariant (st : DriverState) : Prop :=
  st.totalLower = lowerSum (entries st.forest) ∧
  st.totalUpper = upperSum (entries st.forest)

/-- The address-aware content invariant is stated at exact multiplicity.
Its preservation through the complete loop is kept separate from the cached
ledger theorem; it is not assumed by the concrete computation. -/
def AddressHeapInvariant (st : DriverState) : Prop :=
  (contents st.queue : Multiset Scheduled) =
    (activeJobs (forestJobs st.forest 0) : Multiset Scheduled)

theorem initial_ledger : LedgerInvariant initialDriverState := ⟨rfl,rfl⟩

theorem initial_heap : AddressHeapInvariant initialDriverState := by
  unfold AddressHeapInvariant initialDriverState
  rw [putJobs_contents,contents_empty]
  simp

inductive DriverFailure where
  | emptyHeap
  | badAddressOrMidpoint
  | cachedParentMismatch
  | exhaustedFuel
  deriving DecidableEq, Repr

/-- A genuine next-state computation. Failed original assertions and stale
administrative addresses return failure, never a fabricated zero enclosure. -/
def driverStep (st : DriverState) : Except DriverFailure DriverState :=
  match Batteries.PairingHeap.deleteMin st.queue with
  | none => .error .emptyHeap
  | some (job,rest) =>
      match splitForestAt st.serial st.forest job.seed job.path with
      | none => .error .badAddressOrMidpoint
      | some (parent,forest') =>
          if SameEntry parent job.entry then
            let childEntries := children originalEnclose st.serial parent.cell
            let childJobs := spawnJobs st.serial parent job.seed job.path
            .ok ⟨forest',putJobs rest childJobs,
              afterChildren originalEnclose st.serial parent.cell,st.splits + 1,
              st.totalLower - job.entry.bounds.lower + lowerSum childEntries,
              st.totalUpper - job.entry.bounds.upper + upperSum childEntries,
              st.assertionsPassed && sourceCheck (sourceLeft parent.cell) &&
                sourceCheck (sourceRight parent.cell)⟩
          else .error .cachedParentMismatch

/-- The next forest witness and positional replacement are outputs of the
pure computation, not inputs asked of a certificate supplier. -/
theorem driverStep_source (st st' : DriverState) (h : driverStep st = .ok st') :
    ∃ p, ForestRefines originalEnclose st.serial p st.forest st'.forest ∧
      st'.splits = st.splits + 1 ∧
      st'.totalLower = st.totalLower - p.bounds.lower +
        lowerSum (children originalEnclose st.serial p.cell) ∧
      st'.totalUpper = st.totalUpper - p.bounds.upper +
        upperSum (children originalEnclose st.serial p.cell) := by
  unfold driverStep at h
  cases hp : Batteries.PairingHeap.deleteMin st.queue with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨job,rest⟩
      rw [hp] at h
      cases hs : splitForestAt st.serial st.forest job.seed job.path with
      | none => simp [hs] at h
      | some result =>
          rcases result with ⟨parent,forest'⟩
          rw [hs] at h
          by_cases he : SameEntry parent job.entry
          · simp only [if_pos he] at h
            cases h
            refine ⟨parent,splitForestAt_refines _ _ _ _ _ _ hs,rfl,?_,?_⟩
            all_goals simp only [(sameEntry_iff _ _).mp he]
          · simp [he] at h

theorem driverStep_ledger (st st' : DriverState) (h : driverStep st = .ok st')
    (hi : LedgerInvariant st) : LedgerInvariant st' := by
  obtain ⟨p,href,hcount,hl,hu⟩ := driverStep_source st st' h
  obtain ⟨hl',hu',hcount'⟩ := refine_sum_updates href
  exact ⟨by rw [hl,hi.1]; exact hl'.symm,by rw [hu,hi.2]; exact hu'.symm⟩

theorem driverStep_leaf_count (st st' : DriverState) (h : driverStep st = .ok st') :
    (entries st'.forest).length = (entries st.forest).length + 1 := by
  obtain ⟨p,href,_⟩ := driverStep_source st st' h
  exact (refine_sum_updates href).2.2


/-- Exact addressed positional replacement. This strengthens K's unaddressed
entry permutation to the literal navigation data used by the efficient heap. -/
theorem splitTreeAt_jobs {c : SeedCell} (tree : OriginalTree c) (serial seed : ℕ)
    (prefix path : List Bool) (p : Entry) (tree' : OriginalTree c)
    (h : splitTreeAt serial tree path = some (p,tree')) :
    ∃ pre post,
      treeJobs seed prefix tree = pre ++ ⟨p,seed,prefix ++ path⟩ :: post ∧
      treeJobs seed prefix tree' = pre ++ spawnJobs serial p seed (prefix ++ path) ++ post := by
  induction tree generalizing prefix path p tree' with
  | leaf c old =>
      cases path with
      | nil =>
          by_cases hw : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)
          · simp only [splitTreeAt,dif_pos hw] at h
            cases h
            exact ⟨[],[],by simp [treeJobs],by
              simp [treeJobs,spawnJobs,issue]⟩
          · simp [splitTreeAt,hw] at h
      | cons b path => simp [splitTreeAt] at h
  | split c width left right ihL ihR =>
      cases path with
      | nil => simp [splitTreeAt] at h
      | cons side path =>
          cases side with
          | false =>
              cases hs : splitTreeAt serial left path with
              | none => simp [splitTreeAt,hs] at h
              | some result =>
                  rcases result with ⟨parent,left'⟩
                  simp only [splitTreeAt,hs,Option.map_some] at h
                  cases h
                  obtain ⟨pre,post,hold,hnew⟩ := ihL (prefix ++ [false]) path parent left' hs
                  refine ⟨pre,post ++ treeJobs seed (prefix ++ [true]) right,?_,?_⟩
                  · simpa [treeJobs,hold,List.append_assoc] using
                      congrArg (fun xs => xs ++ treeJobs seed (prefix ++ [true]) right) hold
                  · simpa [treeJobs,List.append_assoc] using
                      congrArg (fun xs => xs ++ treeJobs seed (prefix ++ [true]) right) hnew
          | true =>
              cases hs : splitTreeAt serial right path with
              | none => simp [splitTreeAt,hs] at h
              | some result =>
                  rcases result with ⟨parent,right'⟩
                  simp only [splitTreeAt,hs,Option.map_some] at h
                  cases h
                  obtain ⟨pre,post,hold,hnew⟩ := ihR (prefix ++ [true]) path parent right' hs
                  refine ⟨treeJobs seed (prefix ++ [false]) left ++ pre,post,?_,?_⟩
                  · simpa [treeJobs,List.append_assoc] using
                      congrArg (fun xs => treeJobs seed (prefix ++ [false]) left ++ xs) hold
                  · simpa [treeJobs,List.append_assoc] using
                      congrArg (fun xs => treeJobs seed (prefix ++ [false]) left ++ xs) hnew

theorem splitForestAt_jobs {cs : List SeedCell} (forest : OriginalForest cs)
    (serial start seed : ℕ) (path : List Bool) (p : Entry) (forest' : OriginalForest cs)
    (h : splitForestAt serial forest seed path = some (p,forest')) :
    ∃ pre post,
      forestJobs forest start = pre ++ ⟨p,start + seed,path⟩ :: post ∧
      forestJobs forest' start = pre ++ spawnJobs serial p (start + seed) path ++ post := by
  induction forest generalizing start seed p forest' with
  | nil => simp [splitForestAt] at h
  | cons tree rest ih =>
      cases seed with
      | zero =>
          cases hs : splitTreeAt serial tree path with
          | none => simp [splitForestAt,hs] at h
          | some result =>
              rcases result with ⟨parent,tree'⟩
              simp only [splitForestAt,hs,Option.map_some] at h
              cases h
              obtain ⟨pre,post,hold,hnew⟩ := splitTreeAt_jobs tree serial start [] path parent tree' hs
              refine ⟨pre,post ++ forestJobs rest (start + 1),?_,?_⟩
              · simpa [forestJobs,List.append_assoc] using
                  congrArg (fun xs => xs ++ forestJobs rest (start + 1)) hold
              · simpa [forestJobs,List.append_assoc] using
                  congrArg (fun xs => xs ++ forestJobs rest (start + 1)) hnew
      | succ seed =>
          cases hs : splitForestAt serial rest seed path with
          | none => simp [splitForestAt,hs] at h
          | some result =>
              rcases result with ⟨parent,rest'⟩
              simp only [splitForestAt,hs,Option.map_some] at h
              cases h
              obtain ⟨pre,post,hold,hnew⟩ := ih (start + 1) seed parent rest' hs
              refine ⟨treeJobs start [] tree ++ pre,post,?_,?_⟩
              · simpa [forestJobs,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
                  congrArg (fun xs => treeJobs start [] tree ++ xs) hold
              · simpa [forestJobs,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
                  congrArg (fun xs => treeJobs start [] tree ++ xs) hnew

theorem activeJobs_append (xs ys : List Scheduled) :
    activeJobs (xs ++ ys) = activeJobs xs ++ activeJobs ys := by
  simp [activeJobs,List.filter_append]

theorem driverStep_heap (st st' : DriverState) (h : driverStep st = .ok st')
    (hi : AddressHeapInvariant st) : AddressHeapInvariant st' := by
  unfold driverStep at h
  cases hp : Batteries.PairingHeap.deleteMin st.queue with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨job,rest⟩
      rw [hp] at h
      cases hs : splitForestAt st.serial st.forest job.seed job.path with
      | none => simp [hs] at h
      | some result =>
          rcases result with ⟨parent,forest'⟩
          rw [hs] at h
          by_cases he : SameEntry parent job.entry
          · simp only [if_pos he] at h
            cases h
            have hparent : parent = job.entry := (sameEntry_iff _ _).mp he
            have hpop := deleteMin_spec st.queue job rest hp
            have ha : active job.entry := by
              have hm : job ∈ (activeJobs (forestJobs st.forest 0) : Multiset Scheduled) := by
                rw [← hi]
                exact hpop.2.1
              have hm' : job ∈ activeJobs (forestJobs st.forest 0) := hm
              exact of_decide_eq_true (List.mem_filter.mp hm').2
            obtain ⟨pre,post,hold,hnew⟩ :=
              splitForestAt_jobs st.forest st.serial 0 job.seed job.path parent forest' hs
            simp only [Nat.zero_add,hparent] at hold hnew
            have hrest : (contents rest : Multiset Scheduled) =
                (activeJobs pre : Multiset Scheduled) + (activeJobs post : Multiset Scheduled) := by
              apply add_left_cancel (a := ({job} : Multiset Scheduled))
              rw [← hpop.1,hi,hold]
              simp [activeJobs,ha,add_assoc,add_left_comm,add_comm]
            change (contents (putJobs rest (spawnJobs st.serial parent job.seed job.path)) :
                Multiset Scheduled) = (activeJobs (forestJobs forest' 0) : Multiset Scheduled)
            rw [putJobs_contents,hrest,hnew]
            simp only [activeJobs_append,Multiset.coe_add]
            simp [hparent,add_assoc,add_left_comm,add_comm]
          · simp [he] at h

/-- With the source/heap invariant, selecting the efficient heap minimum
selects a genuine original active leaf at maximal uncertainty and oldest tie. -/
theorem selected_original_priority (st : DriverState) (hi : AddressHeapInvariant st)
    (job : Scheduled) (rest : Queue)
    (hp : Batteries.PairingHeap.deleteMin st.queue = some (job,rest)) :
    active job.entry ∧ ∀ other ∈ activeJobs (forestJobs st.forest 0),
      error other.entry ≤ error job.entry ∧
        (error other.entry = error job.entry → job.entry.serial ≤ other.entry.serial) := by
  have hs := deleteMin_spec st.queue job rest hp
  have hm : job ∈ activeJobs (forestJobs st.forest 0) := by
    change job ∈ (activeJobs (forestJobs st.forest 0) : Multiset Scheduled)
    rw [← hi]
    exact hs.2.1
  refine ⟨of_decide_eq_true (List.mem_filter.mp hm).2,?_⟩
  intro other ho
  have ho' : other ∈ contents st.queue := by
    change other ∈ (contents st.queue : Multiset Scheduled)
    rw [hi]
    exact ho
  have hk := hs.2.2 other ho'
  unfold Before at hk
  omega

/-- No two distinct active jobs have the same issued serial. The lower and
upper bounds also show fresh jobs cannot jump ahead of an older equal error. -/
def SerialDiscipline (jobs : List Scheduled) (counter : ℕ) : Prop :=
  (∀ job ∈ jobs, 0 < job.entry.serial ∧ job.entry.serial ≤ counter) ∧
  ∀ p ∈ jobs, ∀ q ∈ jobs, p.entry.serial = q.entry.serial → p = q

theorem seed_jobs_fresh (cs : List SeedCell) (counter seed : ℕ) :
    ∀ job ∈ activeJobs (forestJobs (seedForest originalEnclose cs counter).1 seed),
      counter < job.entry.serial ∧
        job.entry.serial ≤ (seedForest originalEnclose cs counter).2 := by
  induction cs generalizing counter seed with
  | nil => simp [seedForest,forestJobs,activeJobs]
  | cons c cs ih =>
      intro job hj
      change job ∈ activeJobs
        (⟨issue originalEnclose c counter,seed,[]⟩ ::
          forestJobs (seedForest originalEnclose cs (advance originalEnclose c counter)).1
            (seed + 1)) at hj
      have ha : active job.entry := of_decide_eq_true (List.mem_filter.mp hj).2
      have hm := (List.mem_filter.mp hj).1
      rcases List.mem_cons.mp hm with hhead | htail
      · subst job
        have hs := issue_active_fresh originalEnclose c counter ha
        have ht := (seedForest_serial originalEnclose cs (advance originalEnclose c counter)).1
        simp only [seedForest]
        change counter < (issue originalEnclose c counter).serial ∧
          (issue originalEnclose c counter).serial ≤
            (seedForest originalEnclose cs (advance originalEnclose c counter)).2
        rw [hs.1]
        rw [hs.2] at ht
        omega
      · have hj' : job ∈ activeJobs
            (forestJobs (seedForest originalEnclose cs (advance originalEnclose c counter)).1
              (seed + 1)) := List.mem_filter.mpr ⟨htail,by simp [ha]⟩
        have ht := ih (advance originalEnclose c counter) (seed + 1) job hj'
        have hm := advance_mono originalEnclose c counter
        exact ⟨by omega,ht.2⟩

theorem seed_jobs_unique (cs : List SeedCell) (counter seed : ℕ) :
    ∀ p ∈ activeJobs (forestJobs (seedForest originalEnclose cs counter).1 seed),
    ∀ q ∈ activeJobs (forestJobs (seedForest originalEnclose cs counter).1 seed),
      p.entry.serial = q.entry.serial → p = q := by
  induction cs generalizing counter seed with
  | nil => simp [seedForest,forestJobs,activeJobs]
  | cons c cs ih =>
      intro p hp q hq he
      let head : Scheduled := ⟨issue originalEnclose c counter,seed,[]⟩
      let tail := forestJobs
        (seedForest originalEnclose cs (advance originalEnclose c counter)).1 (seed + 1)
      change p ∈ activeJobs (head :: tail) at hp
      change q ∈ activeJobs (head :: tail) at hq
      have hpa : active p.entry := of_decide_eq_true (List.mem_filter.mp hp).2
      have hqa : active q.entry := of_decide_eq_true (List.mem_filter.mp hq).2
      have hpm := List.mem_cons.mp (List.mem_filter.mp hp).1
      have hqm := List.mem_cons.mp (List.mem_filter.mp hq).1
      rcases hpm with rfl | hp'
      · rcases hqm with rfl | hq'
        · rfl
        · have hqt : q ∈ activeJobs tail := List.mem_filter.mpr ⟨hq',by simp [hqa]⟩
          have hf := seed_jobs_fresh cs (advance originalEnclose c counter) (seed + 1) q hqt
          have hh := issue_serial_le originalEnclose c counter
          change (issue originalEnclose c counter).serial = q.entry.serial at he
          omega
      · rcases hqm with rfl | hq'
        · have hpt : p ∈ activeJobs tail := List.mem_filter.mpr ⟨hp',by simp [hpa]⟩
          have hf := seed_jobs_fresh cs (advance originalEnclose c counter) (seed + 1) p hpt
          have hh := issue_serial_le originalEnclose c counter
          change p.entry.serial = (issue originalEnclose c counter).serial at he
          omega
        · exact ih _ _ p (List.mem_filter.mpr ⟨hp',by simp [hpa]⟩)
            q (List.mem_filter.mpr ⟨hq',by simp [hqa]⟩) he

theorem initial_serial : SerialDiscipline (contents initialDriverState.queue) initialDriverState.serial := by
  have hi := initial_heap
  have hr := seed_jobs_fresh initialSeeds 0 0
  have hu := seed_jobs_unique initialSeeds 0 0
  have hm : ∀ job, job ∈ contents initialDriverState.queue ↔
      job ∈ activeJobs (forestJobs (seedForest originalEnclose initialSeeds 0).1 0) := by
    intro job
    change job ∈ (contents initialDriverState.queue : Multiset Scheduled) ↔ _
    rw [hi]
    rfl
  exact ⟨fun job hj => hr job ((hm job).mp hj),
    fun p hp q hq he => hu p ((hm p).mp hp) q ((hm q).mp hq) he⟩

theorem spawnJobs_entries (serial : ℕ) (parent : Entry) (seed : ℕ) (path : List Bool) :
    (spawnJobs serial parent seed path).map Scheduled.entry =
      children originalEnclose serial parent.cell := rfl

theorem spawnJobs_fresh (serial : ℕ) (parent : Entry) (seed : ℕ) (path : List Bool)
    (job : Scheduled) (hj : job ∈ activeJobs (spawnJobs serial parent seed path)) :
    serial < job.entry.serial ∧
      job.entry.serial ≤ afterChildren originalEnclose serial parent.cell := by
  have ha : active job.entry := of_decide_eq_true (List.mem_filter.mp hj).2
  have hm : job.entry ∈ children originalEnclose serial parent.cell := by
    rw [← spawnJobs_entries serial parent seed path]
    exact List.mem_map.mpr ⟨job,(List.mem_filter.mp hj).1,rfl⟩
  exact ⟨active_children_fresh _ _ _ _ hm ha,children_serial_le _ _ _ _ hm⟩

theorem spawnJobs_unique (serial : ℕ) (parent : Entry) (seed : ℕ) (path : List Bool) :
    ∀ p ∈ activeJobs (spawnJobs serial parent seed path),
    ∀ q ∈ activeJobs (spawnJobs serial parent seed path),
      p.entry.serial = q.entry.serial → p = q := by
  intro p hp q hq he
  have hpa : active p.entry := of_decide_eq_true (List.mem_filter.mp hp).2
  have hqa : active q.entry := of_decide_eq_true (List.mem_filter.mp hq).2
  have hpm := (List.mem_filter.mp hp).1
  have hqm := (List.mem_filter.mp hq).1
  simp only [spawnJobs,List.mem_cons,List.mem_singleton] at hpm hqm
  rcases hpm with rfl | rfl <;> rcases hqm with rfl | rfl
  · rfl
  · have ht := active_children_tie_order originalEnclose serial parent.cell hpa hqa
    omega
  · have ht := active_children_tie_order originalEnclose serial parent.cell hqa hpa
    omega
  · rfl

theorem driverStep_serial (st st' : DriverState) (h : driverStep st = .ok st')
    (hi : SerialDiscipline (contents st.queue) st.serial) :
    SerialDiscipline (contents st'.queue) st'.serial := by
  unfold driverStep at h
  cases hp : Batteries.PairingHeap.deleteMin st.queue with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨job,rest⟩
      rw [hp] at h
      cases hs : splitForestAt st.serial st.forest job.seed job.path with
      | none => simp [hs] at h
      | some result =>
          rcases result with ⟨parent,forest'⟩
          rw [hs] at h
          by_cases he : SameEntry parent job.entry
          · simp only [if_pos he] at h
            cases h
            let fresh := activeJobs (spawnJobs st.serial parent job.seed job.path)
            have hpop := deleteMin_spec st.queue job rest hp
            have hrest : ∀ p ∈ contents rest, p ∈ contents st.queue := by
              intro p hm
              change p ∈ (contents st.queue : Multiset Scheduled)
              rw [hpop.1]
              simp [hm]
            have hm : ∀ p,
                p ∈ contents (putJobs rest (spawnJobs st.serial parent job.seed job.path)) ↔
                  p ∈ fresh ∨ p ∈ contents rest := by
              intro p
              change p ∈ (contents (putJobs rest
                (spawnJobs st.serial parent job.seed job.path)) : Multiset Scheduled) ↔ _
              rw [putJobs_contents]
              simp only [Multiset.mem_add,Multiset.mem_coe]
              rfl
            have hmono := afterChildren_mono originalEnclose st.serial parent.cell
            refine ⟨?_,?_⟩
            · intro p hmem
              rcases (hm p).mp hmem with hf | ho
              · have hb := spawnJobs_fresh st.serial parent job.seed job.path p hf
                exact ⟨by omega,hb.2⟩
              · have hb := hi.1 p (hrest p ho)
                exact ⟨hb.1,hb.2.trans hmono⟩
            · intro p hp' q hq' heq
              rcases (hm p).mp hp' with hpf | hpo <;>
                rcases (hm q).mp hq' with hqf | hqo
              · exact spawnJobs_unique st.serial parent job.seed job.path p hpf q hqf heq
              · have hn := (spawnJobs_fresh st.serial parent job.seed job.path p hpf).1
                have ho := (hi.1 q (hrest q hqo)).2
                omega
              · have hn := (spawnJobs_fresh st.serial parent job.seed job.path q hqf).1
                have ho := (hi.1 p (hrest p hpo)).2
                omega
              · exact hi.2 p (hrest p hpo) q (hrest q hqo) heq
          · simp [he] at h

/-- Multiplicity-sensitive strengthening: every active serial occurs once. -/
def SerialNodup (jobs : List Scheduled) : Prop :=
  (jobs.map fun job => job.entry.serial).Nodup

theorem seed_jobs_nodup (cs : List SeedCell) (counter seed : ℕ) :
    SerialNodup (activeJobs (forestJobs (seedForest originalEnclose cs counter).1 seed)) := by
  induction cs generalizing counter seed with
  | nil => simp [SerialNodup,seedForest,forestJobs,activeJobs]
  | cons c cs ih =>
      let head : Scheduled := ⟨issue originalEnclose c counter,seed,[]⟩
      let tail := forestJobs
        (seedForest originalEnclose cs (advance originalEnclose c counter)).1 (seed + 1)
      change SerialNodup (activeJobs (head :: tail))
      by_cases ha : active head.entry
      · change ((activeJobs (head :: tail)).map fun job => job.entry.serial).Nodup
        simp only [activeJobs,List.filter_cons,decide_eq_true ha,if_true,List.map_cons]
        apply List.nodup_cons.mpr
        refine ⟨?_,ih _ _⟩
        intro hm
        obtain ⟨job,hj,he⟩ := List.mem_map.mp hm
        have hf := seed_jobs_fresh cs (advance originalEnclose c counter) (seed + 1) job hj
        have hh := issue_serial_le originalEnclose c counter
        change job.entry.serial = (issue originalEnclose c counter).serial at he
        omega
      · simpa [SerialNodup,activeJobs,ha] using ih (advance originalEnclose c counter) (seed + 1)

theorem initial_serial_nodup : SerialNodup (contents initialDriverState.queue) := by
  have hp : (contents initialDriverState.queue).Perm
      (activeJobs (forestJobs (seedForest originalEnclose initialSeeds 0).1 0)) :=
    Multiset.coe_eq_coe.mp initial_heap
  exact (hp.map (fun job => job.entry.serial)).nodup_iff.mpr (seed_jobs_nodup initialSeeds 0 0)

theorem spawnJobs_nodup (serial : ℕ) (parent : Entry) (seed : ℕ) (path : List Bool) :
    SerialNodup (activeJobs (spawnJobs serial parent seed path)) := by
  let left := issue originalEnclose (sourceLeft parent.cell) serial
  let right := issue originalEnclose (sourceRight parent.cell)
    (advance originalEnclose (sourceLeft parent.cell) serial)
  by_cases hl : active left <;> by_cases hr : active right
  · have ht := active_children_tie_order originalEnclose serial parent.cell hl hr
    have hn : left.serial ≠ right.serial := Nat.ne_of_lt ht
    simpa [SerialNodup,activeJobs,spawnJobs,left,right,hl,hr] using hn
  · simp [SerialNodup,activeJobs,spawnJobs,left,right,hl,hr]
  · simp [SerialNodup,activeJobs,spawnJobs,left,right,hl,hr]
  · simp [SerialNodup,activeJobs,spawnJobs,left,right,hl,hr]

private theorem nodup_append_of_separated (xs ys : List ℕ) (hx : xs.Nodup) (hy : ys.Nodup)
    (hsep : ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y) : (xs ++ ys).Nodup := by
  revert hx hsep
  induction xs with
  | nil => intro hx hsep; simpa using hy
  | cons x xs ih =>
      intro hx hsep
      obtain ⟨hnot,hxs⟩ := List.nodup_cons.mp hx
      apply List.nodup_cons.mpr
      refine ⟨?_,ih hxs (by intro a ha b hb; exact hsep a (by simp [ha]) b hb)⟩
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hnot hm
      · exact hsep x (by simp) x hm rfl

theorem driverStep_serial_nodup (st st' : DriverState) (h : driverStep st = .ok st')
    (hb : SerialDiscipline (contents st.queue) st.serial)
    (hi : SerialNodup (contents st.queue)) : SerialNodup (contents st'.queue) := by
  unfold driverStep at h
  cases hp : Batteries.PairingHeap.deleteMin st.queue with
  | none => simp [hp] at h
  | some result =>
      rcases result with ⟨job,rest⟩
      rw [hp] at h
      cases hs : splitForestAt st.serial st.forest job.seed job.path with
      | none => simp [hs] at h
      | some result =>
          rcases result with ⟨parent,forest'⟩
          rw [hs] at h
          by_cases he : SameEntry parent job.entry
          · simp only [if_pos he] at h
            cases h
            have hpop := deleteMin_spec st.queue job rest hp
            have hprem : (contents st.queue).Perm (job :: contents rest) :=
              Multiset.coe_eq_coe.mp (by simpa using hpop.1)
            have hr : SerialNodup (contents rest) :=
              (List.nodup_cons.mp ((hprem.map (fun x => x.entry.serial)).nodup_iff.mp hi)).2
            have hnew : (contents (putJobs rest (spawnJobs st.serial parent job.seed job.path))).Perm
                (activeJobs (spawnJobs st.serial parent job.seed job.path) ++ contents rest) :=
              Multiset.coe_eq_coe.mp (by simpa using
                putJobs_contents rest (spawnJobs st.serial parent job.seed job.path))
            apply (hnew.map (fun x => x.entry.serial)).nodup_iff.mpr
            rw [List.map_append]
            apply nodup_append_of_separated _ _ (spawnJobs_nodup _ _ _ _) hr
            intro x hx y hy hxy
            obtain ⟨fresh,hfresh,hx⟩ := List.mem_map.mp hx
            obtain ⟨old,hold,hy⟩ := List.mem_map.mp hy
            have hn := (spawnJobs_fresh st.serial parent job.seed job.path fresh hfresh).1
            have ho : old ∈ contents st.queue := by
              change old ∈ (contents st.queue : Multiset Scheduled)
              rw [hpop.1]
              simp [hold]
            have hbound := (hb.1 old ho).2
            omega
          · simp [he] at h
end ImbalancedChen.P2OriginalCompactConcreteRunSourceOnly






