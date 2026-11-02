import ImbalancedChen.P2OriginalCompactConcreteLoop
import ImbalancedChen.P2OriginalCompactQ80CacheEncloser

/-!
SOURCEONLY / UNCOMPILED / ALL FINITE RUN TERMS UNEVALUATED.

Separate extension of the frozen original driver. The entry point binds the
incrementally built array ONCE and threads it through every hot enclosure,
assertion, seed, split, and final-charge query. The fixed first/tail term is
also computed once before the loop. No original functional sourceState is
called on the cached operational path.

Equality proofs use the cache supplier's symbolic lookup refinement, not
reduction of either two-million-step run. Internal helpers accept an array;
the final cachedRun has no free array, evaluator, or Run-witness argument.
-/
namespace ImbalancedChen.P2OriginalCompactCachedRunSourceOnly

open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalAdaptiveSourceSplitSourceOnly
open P2OriginalPrioritySerialQueueSourceOnly
open P2OriginalPriorityForestLedgerSourceOnly
open P2OriginalEfficientPriorityHeapSourceOnly
open P2OriginalCompactConcreteRunSourceOnly
open P2OriginalCompactConcreteLoopSourceOnly


abbrev Nodes := Array P2OriginalCompactQ80EncloserSourceOnly.Node

/-- The array supplies all source bounds, including exact/empty evaluations. -/
def cachedSeedForest (nodes : Nodes) :
    (cs : List SeedCell) → ℕ → OriginalForest cs × ℕ
  | [],serial => (.nil,serial)
  | c :: cs,serial =>
      let rest := cachedSeedForest nodes cs (advance (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) c serial)
      (.cons (.leaf c (issueSerial (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) c serial)) rest.1,rest.2)

theorem cachedSeedForest_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) (cs : List SeedCell) (serial : ℕ) :
    cachedSeedForest nodes cs serial = seedForest originalEnclose cs serial := by
  have he : P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes = originalEnclose := P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith_eq nodes hlookup
  induction cs generalizing serial with
  | nil => rfl
  | cons c cs ih =>
      simp only [cachedSeedForest,seedForest,he,ih]

/-- Address navigation and the original width assertion are unchanged. Only
actual evaluator calls and active serial tests read the shared array. -/
def cachedSplitTreeAt (nodes : Nodes) (serial : ℕ) : {c : SeedCell} →
    OriginalTree c → List Bool → Option (Entry × OriginalTree c)
  | _, .leaf c old, [] =>
      if width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c) then
        some (⟨c,P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes c,old⟩,
          .split c width
            (.leaf (sourceLeft c) (issueSerial (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) (sourceLeft c) serial))
            (.leaf (sourceRight c)
              (issueSerial (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) (sourceRight c)
                (advance (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) (sourceLeft c) serial))))
      else none
  | _, .split c width left right, false :: path =>
      (cachedSplitTreeAt nodes serial left path).map fun result =>
        (result.1,.split c width result.2 right)
  | _, .split c width left right, true :: path =>
      (cachedSplitTreeAt nodes serial right path).map fun result =>
        (result.1,.split c width left result.2)
  | _, _, _ => none

theorem cachedSplitTreeAt_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) {c : SeedCell}
    (tree : OriginalTree c) (serial : ℕ) (path : List Bool) :
    cachedSplitTreeAt nodes serial tree path = splitTreeAt serial tree path := by
  have he : P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes = originalEnclose := P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith_eq nodes hlookup
  induction tree generalizing path with
  | leaf c old => cases path <;> simp only [cachedSplitTreeAt,splitTreeAt,he]
  | split c width left right ihL ihR =>
      cases path with
      | nil => rfl
      | cons side path =>
          cases side <;> simp only [cachedSplitTreeAt,splitTreeAt,ihL,ihR]

def cachedSplitForestAt (nodes : Nodes) (serial : ℕ) : {cs : List SeedCell} →
    OriginalForest cs → ℕ → List Bool → Option (Entry × OriginalForest cs)
  | _, .nil, _, _ => none
  | _, .cons tree rest, 0, path =>
      (cachedSplitTreeAt nodes serial tree path).map fun result =>
        (result.1,.cons result.2 rest)
  | _, .cons tree rest, seed + 1, path =>
      (cachedSplitForestAt nodes serial rest seed path).map fun result =>
        (result.1,.cons tree result.2)

theorem cachedSplitForestAt_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) {cs : List SeedCell}
    (forest : OriginalForest cs) (serial seed : ℕ) (path : List Bool) :
    cachedSplitForestAt nodes serial forest seed path = splitForestAt serial forest seed path := by
  induction forest generalizing seed with
  | nil => rfl
  | cons tree rest ih =>
      cases seed with
      | zero => simp only [cachedSplitForestAt,splitForestAt,cachedSplitTreeAt_eq nodes hlookup]
      | succ seed => simp only [cachedSplitForestAt,splitForestAt,ih]

/-- Initialization jobs use cached bounds, not the original leaf projection. -/
def cachedTreeJobs (nodes : Nodes) {c : SeedCell} (seed : ℕ) (path : List Bool) :
    OriginalTree c → List Scheduled
  | .leaf c serial => [⟨⟨c,P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes c,serial⟩,seed,path⟩]
  | .split _ _ left right =>
      cachedTreeJobs nodes seed (path ++ [false]) left ++
        cachedTreeJobs nodes seed (path ++ [true]) right

theorem cachedTreeJobs_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) {c : SeedCell}
    (tree : OriginalTree c) (seed : ℕ) (path : List Bool) :
    cachedTreeJobs nodes seed path tree = treeJobs seed path tree := by
  have he : P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes = originalEnclose := P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith_eq nodes hlookup
  induction tree generalizing path with
  | leaf c serial => simp only [cachedTreeJobs,treeJobs,he]
  | split c width left right ihL ihR =>
      simp only [cachedTreeJobs,treeJobs,ihL,ihR]

def cachedForestJobs (nodes : Nodes) : {cs : List SeedCell} →
    OriginalForest cs → ℕ → List Scheduled
  | _, .nil, _ => []
  | _, .cons tree rest, seed =>
      cachedTreeJobs nodes seed [] tree ++ cachedForestJobs nodes rest (seed + 1)

theorem cachedForestJobs_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) {cs : List SeedCell}
    (forest : OriginalForest cs) (seed : ℕ) :
    cachedForestJobs nodes forest seed = forestJobs forest seed := by
  induction forest generalizing seed with
  | nil => rfl
  | cons tree rest ih =>
      simp only [cachedForestJobs,forestJobs,cachedTreeJobs_eq nodes hlookup,ih]

/-- The decidable guard equality is independent of which computable instance
proves decidability of the original sourceAssertions proposition. -/
theorem cachedSourceCheck_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) :
    P2OriginalCompactQ80CacheEncloserSourceOnly.sourceCheckWith nodes = sourceCheck := by
  funext box
  rw [P2OriginalCompactQ80CacheEncloserSourceOnly.sourceCheckWith_eq nodes hlookup]
  by_cases hs : P2OriginalCompactQ80EncloserSourceOnly.sourceAssertions box <;> simp [sourceCheck,hs]

def cachedInitialState (nodes : Nodes) : DriverState :=
  let init := cachedSeedForest nodes initialSeeds 0
  let jobs := cachedForestJobs nodes init.1 0
  ⟨init.1,putJobs Batteries.PairingHeap.empty jobs,init.2,0,
    lowerSum (jobs.map Scheduled.entry),upperSum (jobs.map Scheduled.entry),
    P2OriginalCompactQ80CacheEncloserSourceOnly.tableAssertionsWith nodes && initialSeeds.all (P2OriginalCompactQ80CacheEncloserSourceOnly.sourceCheckWith nodes)⟩

theorem cachedInitialState_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) :
    cachedInitialState nodes = initialDriverState := by
  simp only [cachedInitialState,initialDriverState,cachedSeedForest_eq nodes hlookup,
    cachedForestJobs_eq nodes hlookup,forestJobs_entries,
    P2OriginalCompactQ80CacheEncloserSourceOnly.tableAssertionsWith_eq nodes hlookup,cachedSourceCheck_eq nodes hlookup]

/-- Side0/side1 order and all active serial allocation remain literal. -/
def cachedSpawnJobs (nodes : Nodes) (serial : ℕ) (parent : Entry)
    (seed : ℕ) (path : List Bool) : List Scheduled :=
  [⟨issue (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) (sourceLeft parent.cell) serial,seed,path ++ [false]⟩,
   ⟨issue (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) (sourceRight parent.cell)
      (advance (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) (sourceLeft parent.cell) serial),seed,path ++ [true]⟩]

theorem cachedSpawnJobs_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable)
    (serial : ℕ) (parent : Entry) (seed : ℕ) (path : List Bool) :
    cachedSpawnJobs nodes serial parent seed path = spawnJobs serial parent seed path := by
  rw [cachedSpawnJobs,P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith_eq nodes hlookup]
  rfl

/-- Every hot path, including selected source diagnostics, uses nodes. The
original source-indexed forest type itself performs no enclosure query. -/
def cachedStep (nodes : Nodes) (st : DriverState) : Except DriverFailure DriverState :=
  match Batteries.PairingHeap.deleteMin st.queue with
  | none => .error .emptyHeap
  | some (job,rest) =>
      match cachedSplitForestAt nodes st.serial st.forest job.seed job.path with
      | none => .error .badAddressOrMidpoint
      | some (parent,forest') =>
          if SameEntry parent job.entry then
            let childEntries := children (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) st.serial parent.cell
            let childJobs := cachedSpawnJobs nodes st.serial parent job.seed job.path
            .ok ⟨forest',putJobs rest childJobs,
              afterChildren (P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes) st.serial parent.cell,st.splits + 1,
              st.totalLower - job.entry.bounds.lower + lowerSum childEntries,
              st.totalUpper - job.entry.bounds.upper + upperSum childEntries,
              st.assertionsPassed && P2OriginalCompactQ80CacheEncloserSourceOnly.sourceCheckWith nodes (sourceLeft parent.cell) &&
                P2OriginalCompactQ80CacheEncloserSourceOnly.sourceCheckWith nodes (sourceRight parent.cell)⟩
          else .error .cachedParentMismatch

theorem cachedStep_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) (st : DriverState) :
    cachedStep nodes st = driverStep st := by
  simp only [cachedStep,driverStep,cachedSplitForestAt_eq nodes hlookup,
    P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith_eq nodes hlookup,cachedSpawnJobs_eq nodes hlookup,
    cachedSourceCheck_eq nodes hlookup]

/-- fixed is precomputed from the same shared array before loop entry. -/
def cachedKeepRunning (fixed : ℚ) (st : DriverState) : Prop :=
  st.splits < maxSplits ∧ target ≤ fixed + (st.totalUpper : ℚ) / 2^80

instance (fixed : ℚ) (st : DriverState) : Decidable (cachedKeepRunning fixed st) := inferInstanceAs
  (Decidable (st.splits < maxSplits ∧ target ≤ fixed + (st.totalUpper : ℚ) / 2^80))

def cachedRunFuel (nodes : Nodes) (fixed : ℚ) : ℕ → DriverState → Result
  | 0, st =>
      if cachedKeepRunning fixed st then .failed .exhaustedFuel st else stopResult st
  | fuel + 1, st =>
      if cachedKeepRunning fixed st then
        match cachedStep nodes st with
        | .error reason => .failed reason st
        | .ok next => cachedRunFuel nodes fixed fuel next
      else stopResult st

theorem cachedRunFuel_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) (fixed : ℚ)
    (hfixed : fixed = fixedUpper) (fuel : ℕ) (st : DriverState) :
    cachedRunFuel nodes fixed fuel st = runFuel fuel st := by
  subst fixed
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
      simp only [cachedRunFuel,runFuel,cachedKeepRunning,keepRunning,
        cachedStep_eq nodes hlookup]
      by_cases hg : keepRunning st
      · simp only [keepRunning] at hg
        rw [if_pos hg,if_pos hg]
        cases hs : driverStep st with
        | error reason => rfl
        | ok next => exact ih next
      · simp only [keepRunning] at hg
        rw [if_neg hg,if_neg hg]

/-- Closed entry point. Array construction and fixed first/tail evaluation
occur once and are then shared explicitly by all recursive calls. -/
def cachedRun : Result :=
  let nodes := P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray
  let fixed := P2OriginalCompactQ80CacheEncloserSourceOnly.fixedUpperWith nodes
  cachedRunFuel nodes fixed maxSplits (cachedInitialState nodes)

theorem cachedRun_eq : cachedRun = originalRun := by
  unfold cachedRun originalRun
  rw [cachedRunFuel_eq P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray_lookup
    (P2OriginalCompactQ80CacheEncloserSourceOnly.fixedUpperWith P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray)
    (P2OriginalCompactQ80CacheEncloserSourceOnly.fixedUpperWith_eq P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray_lookup),
    cachedInitialState_eq P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray_lookup]

/-- Final charge extraction also uses array lookups. It does not revert to
K.entries, whose leaf projection calls the original functional evaluator. -/
def cachedTreeEntries (nodes : Nodes) {c : SeedCell} : OriginalTree c → List Entry
  | .leaf c serial => [⟨c,P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes c,serial⟩]
  | .split _ _ left right => cachedTreeEntries nodes left ++ cachedTreeEntries nodes right

theorem cachedTreeEntries_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) {c : SeedCell}
    (tree : OriginalTree c) : cachedTreeEntries nodes tree = treeEntries tree := by
  have he : P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith nodes = originalEnclose := P2OriginalCompactQ80CacheEncloserSourceOnly.encloseWith_eq nodes hlookup
  induction tree with
  | leaf c serial => simp only [cachedTreeEntries,treeEntries,he]
  | split c width left right ihL ihR => simp only [cachedTreeEntries,treeEntries,ihL,ihR]

def cachedEntries (nodes : Nodes) : {cs : List SeedCell} → OriginalForest cs → List Entry
  | _, .nil => []
  | _, .cons tree rest => cachedTreeEntries nodes tree ++ cachedEntries nodes rest

theorem cachedEntries_eq (nodes : Nodes)
    (hlookup : P2OriginalCompactQ80CacheEncloserSourceOnly.lookup nodes = P2OriginalCompactQ80EncloserSourceOnly.sourceTable) {cs : List SeedCell}
    (forest : OriginalForest cs) : cachedEntries nodes forest = entries forest := by
  induction forest with
  | nil => rfl
  | cons tree rest ih =>
      simp only [cachedEntries,entries,cachedTreeEntries_eq nodes hlookup,ih]

/-- Reuse the SAME shared nodes for the computation and its full charge
traversal; the resulting pair is a concrete data object with no free input. -/
def cachedRunAndEntries : Result × List Entry :=
  let nodes := P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray
  let fixed := P2OriginalCompactQ80CacheEncloserSourceOnly.fixedUpperWith nodes
  let result := cachedRunFuel nodes fixed maxSplits (cachedInitialState nodes)
  (result,cachedEntries nodes result.state.forest)

theorem cachedRunAndEntries_eq :
    cachedRunAndEntries = (originalRun,entries originalRun.state.forest) := by
  unfold cachedRunAndEntries
  rw [cachedRunFuel_eq P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray_lookup
    (P2OriginalCompactQ80CacheEncloserSourceOnly.fixedUpperWith P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray)
    (P2OriginalCompactQ80CacheEncloserSourceOnly.fixedUpperWith_eq P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray_lookup),
    cachedInitialState_eq P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray_lookup,
    cachedEntries_eq P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray P2OriginalCompactQ80CacheEncloserSourceOnly.tableArray_lookup]

def cachedOrderedUpperCharges : List ℤ :=
  cachedRunAndEntries.2.map fun p => p.bounds.upper

def cachedOrderedLowerCharges : List ℤ :=
  cachedRunAndEntries.2.map fun p => p.bounds.lower

theorem cachedOrderedUpperCharges_eq : cachedOrderedUpperCharges = orderedUpperCharges := by
  rw [cachedOrderedUpperCharges,cachedRunAndEntries_eq]
  rfl

theorem cachedOrderedLowerCharges_eq : cachedOrderedLowerCharges = orderedLowerCharges := by
  rw [cachedOrderedLowerCharges,cachedRunAndEntries_eq]
  rfl

/-- Exactly the old decisive check, with the actual cached run on its data
path. It does not force the legacy slow proof-attempt module to elaborate. -/
def cachedHistoricalEndpointCheck : Bool :=
  match cachedRun with
  | .stopped .budget st =>
      decide (st.splits = maxSplits ∧ st.totalUpper = historicalUpper ∧
        Batteries.PairingHeap.size st.queue = 1852040 ∧ st.assertionsPassed = true)
  | _ => false

theorem cachedHistoricalEndpointCheck_eq :
    cachedHistoricalEndpointCheck = historicalEndpointCheck := by
  rw [cachedHistoricalEndpointCheck,cachedRun_eq]
  rfl

theorem cached_ledger : LedgerInvariant cachedRun.state := by
  rw [cachedRun_eq]
  exact originalRun_ledger

theorem cached_heap : AddressHeapInvariant cachedRun.state := by
  rw [cachedRun_eq]
  exact originalRun_heap

theorem cached_serial_nodup : SerialNodup (contents cachedRun.state.queue) := by
  rw [cachedRun_eq]
  exact originalRun_serial_nodup

theorem cached_ordered_upper_sum : cachedOrderedUpperCharges.sum = cachedRun.state.totalUpper := by
  rw [cachedOrderedUpperCharges_eq,cachedRun_eq]
  exact orderedUpperCharges_sum

theorem cached_complete_leaf_count : cachedOrderedUpperCharges.length = 21 + cachedRun.state.splits := by
  rw [cachedOrderedUpperCharges_eq,cachedRun_eq]
  exact orderedCharges_length.1


/-- Attach the complete cached charge data to its exact computed source tree.
The packet is bound once so the data path uses the same shared array run. -/
def cachedChargeTree : P4AOriginalClosedTreeStructuralAggregationSourceOnly.ChargedCutTree :=
  let packet := cachedRunAndEntries
  (P4AClosedCutTreePositionalChargeBindingSourceOnly.attachCharges
    (completeTree packet.1.state.forest)
    (packet.2.map fun p => p.bounds.upper) (by
      rw [cachedRunAndEntries_eq]
      have hlen := P4AOriginalClosedTreeStructuralAggregationSourceOnly.closedLeaves_length
        (completeTree originalRun.state.forest) OriginalThirdCompactPartitionSourceOnly.compactRegion
      rw [completeTree_closedLeaves,List.length_map] at hlen
      simpa only [List.length_map] using hlen)).val

theorem cachedChargeTree_eq : cachedChargeTree = originalChargeTree := by
  simp only [cachedChargeTree,cachedRunAndEntries_eq,originalChargeTree,orderedUpperCharges]

theorem cachedChargeTree_total :
    P4AOriginalClosedTreeStructuralAggregationSourceOnly.totalCharge cachedChargeTree =
      cachedRun.state.totalUpper := by
  rw [cachedChargeTree_eq,cachedRun_eq]
  exact originalChargeTree_total

theorem cachedChargeTree_erase :
    P4AOriginalClosedTreeStructuralAggregationSourceOnly.eraseCharges cachedChargeTree =
      completeTree cachedRun.state.forest := by
  rw [cachedChargeTree_eq,cachedRun_eq]
  exact originalChargeTree_erase
end ImbalancedChen.P2OriginalCompactCachedRunSourceOnly


