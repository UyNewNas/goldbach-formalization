import ImbalancedChen.P2OriginalCanonicalPairTentBank
import ImbalancedChen.P2ActualSameQResidualQuery

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

CapChoice.argument is not used by freeze or integer admission. A finite
code cannot store every continuous exact residual query on its box.
This receiver therefore leaves the original cap program unchanged and
computes an independent actual query from its resulting complete word,
its incoming/outgoing physical totals and the actual cutoff exponent.

Fresh source provenance is read from the real canonical bank selector;
inherit retains the previous source witness. Original physical marks
remain a separate input to a source node: a factorization SourceForm mask
must not erase old marked factors or delete factors from the multiplier.

The old/new observations of a cap replacement have different Q in
general. Same-Q applies only after one of these totals is fixed and its
descendants are formed, as in P2ActualSameQResidualQuery.
-/

namespace ImbalancedChen.P2CanonicalTentDynamicQueryReceiver

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalLowerWholeBoxBranchSelect
open P2OriginalCanonicalPairTentBank P2ActualSameQResidualQuery
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)

def annotateChoice (q : ℝ) : CapChoice → CapChoice
  | .inherit _ => .inherit q
  | .fresh cap _ => .fresh cap q

theorem annotation_does_not_change_cap (q incoming : ℝ) (c : CapChoice) :
    (annotateChoice q c).freeze incoming = c.freeze incoming := by
  cases c <;> rfl

def queryAtTrace (H : Trace) (xi : ℝ) : ℝ := (H.cap-H.word.sum)/xi

theorem actual_integerTrace_query {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seed : ℝ) (N : ℕ) (history : List ℕ) (xi : ℝ) :
    queryAtTrace (integerTrace P a b seed N history) xi =
      residualQuery N (integerTrace P a b seed N history).cap xi history := by
  simp only [queryAtTrace,integerTrace_word,residualQuery,residualExponent,prefixExponent]

/-- This is the actual canonical program's computed integer trace.
    No cap/source/query identity is passed in as a premise. -/
theorem canonical_integerTrace_cutoff {N : ℕ} (hN : (1:ℝ) < N)
    (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (history : List ℕ) (hpos : ∀ p ∈ history, 0 < p) (xi : ℝ)
    (hxi : 0 < xi)
    (hL : 0 < (integerTrace (plan R mesh buffer seed) R.epsilon ceiling seed N history).cap -
      prefixExponent N history) :
    P2EnhancedTwentyOneSameQWeighted.cutoff
      ((N:ℝ)^(integerTrace (plan R mesh buffer seed) R.epsilon ceiling seed N history).cap)
      history.prod
      (queryAtTrace (integerTrace (plan R mesh buffer seed) R.epsilon ceiling seed N history) xi) =
        (N:ℝ)^xi := by
  rw [actual_integerTrace_query]
  exact original_cutoff_of_actual_query hN _ xi history hpos hL hxi

private theorem prefix_idempotent {mesh : ℕ} (rank : Fin 6) (code : Code mesh) :
    prefixCode rank.val (prefixCode rank.val code) = prefixCode rank.val code :=
  prefixCode_nested rank.val rank.val (le_refl _) code

private theorem checked_fresh_source (R : PairRange) {mesh : ℕ}
    (B : CandidateBank mesh) (buffer : ℚ) (rank : Fin 6)
    (parent cap argument : ℝ) (code : Code mesh)
    (h : checkedChoice R B buffer rank parent code = .fresh cap argument) :
    ∃ b, select R B buffer rank (prefixCode rank.val code) = some b ∧
      sourceCheck R rank (prefixCode rank.val code) buffer b ∧
      freshCheck R rank (prefixCode rank.val code) buffer parent b ∧
      cap = (rowCap R (prefixCode rank.val code) buffer b:ℝ) ∧ argument = b.argument := by
  unfold checkedChoice at h
  cases hs : select R B buffer rank (prefixCode rank.val code) with
  | none => simp [hs] at h
  | some b =>
      by_cases hf : freshCheck R rank (prefixCode rank.val code) buffer parent b
      · have he : CapChoice.fresh (rowCap R (prefixCode rank.val code) buffer b:ℝ)
            b.argument = .fresh cap argument := by simpa [hs,hf] using h
        obtain ⟨hc,ha⟩ := CapChoice.fresh.inj he
        have hsource := (select_some_source R B buffer rank
          (prefixCode rank.val code) b hs).2
        rw [prefix_idempotent] at hsource
        exact ⟨b,hs,hsource,hf,hc.symm,ha.symm⟩
      · simp [hs,hf] at h

/-- A fresh concrete choice recovers a real original source row and mask;
    no SourceComparison, selected row or Sound assumption is supplied. -/
theorem canonical_choose_fresh_source (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (rank : Fin 6) (code : Code mesh) (cap argument : ℝ)
    (h : (plan R mesh buffer seed).choose rank code = .fresh cap argument) :
    ∃ b, select R (bank R mesh buffer seed) buffer rank (prefixCode rank.val code) = some b ∧
      sourceCheck R rank (prefixCode rank.val code) buffer b ∧
      cap = (rowCap R (prefixCode rank.val code) buffer b:ℝ) ∧ argument = b.argument := by
  have hresult {r : Fin 6} {parent : ℝ}
      (hh : checkedChoice R (bank R mesh buffer seed) buffer r parent code = .fresh cap argument) :
      ∃ b, select R (bank R mesh buffer seed) buffer r (prefixCode r.val code) = some b ∧
        sourceCheck R r (prefixCode r.val code) buffer b ∧
        cap = (rowCap R (prefixCode r.val code) buffer b:ℝ) ∧ argument = b.argument := by
    obtain ⟨b,hs,hsource,_,hc,ha⟩ := checked_fresh_source R
      (bank R mesh buffer seed) buffer r parent cap argument code hh
    exact ⟨b,hs,hsource,hc,ha⟩
  fin_cases rank
  · simp [plan,pairPlan] at h
  · simp [plan,pairPlan] at h
  · simp [plan,pairPlan] at h
  · exact hresult (by simpa [plan,pairPlan] using h)
  · exact hresult (by simpa [plan,pairPlan] using h)
  · exact hresult (by simpa [plan,pairPlan] using h)

def wordRank (word : List ℝ) : Fin 6 :=
  ⟨min word.length 5,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def wordCode (R : PairRange) (mesh : ℕ) (word : List ℝ) : Code mesh :=
  codeAt R mesh word.length word

def currentSource (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (oldSource : Option SelectedBranchData) (word : List ℝ) : Option SelectedBranchData :=
  match planChoice (plan R mesh buffer seed) R.epsilon ceiling word with
  | .inherit _ => oldSource
  | .fresh _ _ => select R (bank R mesh buffer seed) buffer (wordRank word)
      (prefixCode (wordRank word).val (wordCode R mesh word))

theorem currentSource_inherit (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (oldSource : Option SelectedBranchData) (word : List ℝ) (argument : ℝ)
    (h : planChoice (plan R mesh buffer seed) R.epsilon ceiling word = .inherit argument) :
    currentSource R mesh buffer seed oldSource word = oldSource := by
  simp [currentSource,h]

theorem currentSource_fresh (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (oldSource : Option SelectedBranchData) (word : List ℝ) (cap argument : ℝ)
    (h : planChoice (plan R mesh buffer seed) R.epsilon ceiling word = .fresh cap argument) :
    ∃ b, currentSource R mesh buffer seed oldSource word = some b ∧
      sourceCheck R (wordRank word)
        (prefixCode (wordRank word).val (wordCode R mesh word)) buffer b ∧
      cap = (rowCap R (prefixCode (wordRank word).val (wordCode R mesh word)) buffer b:ℝ) ∧
      argument = b.argument := by
  have hchoice : (plan R mesh buffer seed).choose (wordRank word) (wordCode R mesh word) =
      .fresh cap argument := by
    unfold planChoice at h
    split_ifs at h with hlength
    · simpa only [incomingChoice,wordRank,wordCode,codeAt] using h
    · simp at h
  obtain ⟨b,hs,hsource,hcap,harg⟩ :=
    canonical_choose_fresh_source R mesh buffer seed _ _ cap argument hchoice
  exact ⟨b,by simpa [currentSource,h] using hs,hsource,hcap,harg⟩

structure Observation where
  oldTotal : ℝ
  newTotal : ℝ
  completeWord : List ℝ
  cutoffExponent : ℝ
  physicalCeiling : ℝ
  oldQuery : ℝ
  newQuery : ℝ
  source : Option SelectedBranchData

structure QueryTrace where
  physical : Trace
  source : Option SelectedBranchData
  observations : List Observation

def canonicalStart (seed : ℚ) : QueryTrace := ⟨root (seed:ℝ),none,[]⟩

def observeStep (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (H : QueryTrace) (x xi : ℝ) : Observation :=
  let H' := step (plan R mesh buffer seed) R.epsilon ceiling H.physical x
  let word := H.physical.word++[x]
  ⟨H.physical.cap,H'.cap,word,xi,x,
    (H.physical.cap-word.sum)/xi,(H'.cap-word.sum)/xi,
    currentSource R mesh buffer seed H.source word⟩

def receiveStep (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (H : QueryTrace) (x xi : ℝ) : QueryTrace :=
  let O := observeStep R mesh buffer seed H x xi
  ⟨step (plan R mesh buffer seed) R.epsilon ceiling H.physical x,
    O.source,H.observations++[O]⟩

def receiveRun (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (H : QueryTrace) (xs : List (ℝ×ℝ)) : QueryTrace :=
  xs.foldl (fun K p => receiveStep R mesh buffer seed K p.1 p.2) H

/-- Entire raw trace equality is stronger than equality merely of its
    cap: admission, accepted flag and original historical records survive. -/
theorem receiver_erases_to_original_run (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (H : QueryTrace) (xs : List (ℝ×ℝ)) :
    (receiveRun R mesh buffer seed H xs).physical =
      run (plan R mesh buffer seed) R.epsilon ceiling H.physical (xs.map Prod.fst) := by
  induction xs generalizing H with
  | nil => rfl
  | cons p ps ih =>
      change (receiveRun R mesh buffer seed
        (receiveStep R mesh buffer seed H p.1 p.2) ps).physical = _
      rw [ih]
      rfl

theorem canonical_receiver_erasure (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (xs : List (ℝ×ℝ)) :
    (receiveRun R mesh buffer seed (canonicalStart seed) xs).physical =
      run (plan R mesh buffer seed) R.epsilon ceiling (root seed) (xs.map Prod.fst) :=
  receiver_erases_to_original_run R mesh buffer seed (canonicalStart seed) xs

theorem receiver_keeps_ancestor_observations (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (H : QueryTrace) (xs : List (ℝ×ℝ)) :
    ∃ extra, (receiveRun R mesh buffer seed H xs).observations = H.observations++extra := by
  induction xs generalizing H with
  | nil => exact ⟨[],by simp [receiveRun]⟩
  | cons p ps ih =>
      obtain ⟨extra,he⟩ := ih (receiveStep R mesh buffer seed H p.1 p.2)
      refine ⟨[observeStep R mesh buffer seed H p.1 p.2]++extra,?_⟩
      simpa [receiveRun,receiveStep,List.append_assoc] using he

theorem observation_actual_dictionary (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (H : QueryTrace) (x xi : ℝ) :
    let O := observeStep R mesh buffer seed H x xi
    O.completeWord = (receiveStep R mesh buffer seed H x xi).physical.word ∧
      O.oldQuery = (O.oldTotal-O.completeWord.sum)/O.cutoffExponent ∧
      O.newQuery = queryAtTrace (receiveStep R mesh buffer seed H x xi).physical xi ∧
      O.physicalCeiling = x := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem observation_inherit_source_and_query (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (H : QueryTrace) (x xi argument : ℝ)
    (h : planChoice (plan R mesh buffer seed) R.epsilon ceiling
      (H.physical.word++[x]) = .inherit argument) :
    (receiveStep R mesh buffer seed H x xi).source = H.source ∧
      (observeStep R mesh buffer seed H x xi).oldTotal =
        (observeStep R mesh buffer seed H x xi).newTotal ∧
      (observeStep R mesh buffer seed H x xi).oldQuery =
        (observeStep R mesh buffer seed H x xi).newQuery := by
  simp [receiveStep,observeStep,currentSource,h,step,CapChoice.freeze]

theorem observation_fresh_source (R : PairRange) (mesh : ℕ) (buffer seed : ℚ)
    (H : QueryTrace) (x xi cap argument : ℝ)
    (h : planChoice (plan R mesh buffer seed) R.epsilon ceiling
      (H.physical.word++[x]) = .fresh cap argument) :
    ∃ b, (receiveStep R mesh buffer seed H x xi).source = some b ∧
      sourceCheck R (wordRank (H.physical.word++[x]))
        (prefixCode (wordRank (H.physical.word++[x])).val
          (wordCode R mesh (H.physical.word++[x]))) buffer b ∧
      (observeStep R mesh buffer seed H x xi).newTotal = cap ∧
      (b.argument:ℝ) = argument := by
  obtain ⟨b,hsource,hcheck,_,hargument⟩ :=
    currentSource_fresh R mesh buffer seed H.source _ cap argument h
  refine ⟨b,?_,hcheck,?_,hargument.symm⟩
  · simpa [receiveStep,observeStep] using hsource
  · simp [observeStep,step,h,CapChoice.freeze]

/-- Across an ordinary cap replacement Q can change. This exact
    difference is not called a same-Q child transition. -/
theorem ordinary_endpoint_query_difference (R : PairRange) (mesh : ℕ)
    (buffer seed : ℚ) (H : QueryTrace) (x xi : ℝ) :
    let O := observeStep R mesh buffer seed H x xi
    O.newQuery-O.oldQuery = (O.newTotal-O.oldTotal)/xi := by
  dsimp [observeStep]
  ring

def observationNode (occurrence : Fin 11) (mark : ℕ → Bool)
    (O : Observation) (newEndpoint : Bool) : PhysicalNode :=
  let total := if newEndpoint then O.newTotal else O.oldTotal
  ⟨occurrence,total,tagWord mark O.completeWord,O.physicalCeiling,
    (total-O.completeWord.sum)/O.cutoffExponent⟩

theorem observationNode_complete_query (occurrence : Fin 11) (mark : ℕ → Bool)
    (O : Observation) (newEndpoint : Bool) :
    word (observationNode occurrence mark O newEndpoint) = O.completeWord ∧
      (observationNode occurrence mark O newEndpoint).argument =
        residual (observationNode occurrence mark O newEndpoint)/O.cutoffExponent := by
  simp [observationNode,word,tagWord_exponents,residual]

/-- Actual complete-prefix query bounds on the concrete original chamber.
    The old selectedMid argument is 181/1000; it is not substituted here. -/
theorem concrete_chamber_query_interval (x : Fin 5 → ℝ)
    (hx : P2OriginalLowerBufferedAffineBoxes.inBox
      (box witnessRange witnessCode) x) :
    (366/41:ℝ) ≤ ((589/1000)-(x 0+x 1+x 2))/x 2 ∧
      ((589/1000)-(x 0+x 1+x 2))/x 2 ≤ (369/40:ℝ) := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  norm_num [box,qLo,qHi,qPoint,witnessRange,witnessCode,ceiling] at h0 h1 h2
  have h := whole_box_query_interval
    (lambda := 589/1000) (lambdaLo := 589/1000) (lambdaHi := 589/1000)
    (S := x 0+x 1+x 2) (SLo := 22/100) (SHi := 223/1000)
    (xi := x 2) (xiLo := 1/25) (xiHi := 41/1000)
    ⟨le_rfl,le_rfl⟩ ⟨by linarith,by linarith⟩ h2
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem concrete_midpoint_is_not_actual_query :
    (witnessRow.argument:ℝ) = 181/1000 ∧
      ((589/1000)-(witnessPoint 0+witnessPoint 1+witnessPoint 2))/witnessPoint 2 = 369/40 ∧
      (witnessRow.argument:ℝ) ≠
        ((589/1000)-(witnessPoint 0+witnessPoint 1+witnessPoint 2))/witnessPoint 2 := by
  norm_num [witnessRow,leftRow,selectedMid,witnessRange,witnessCode,witnessMask,
    witnessPoint,qLo,qHi,qPoint,ceiling,Fin.sum_univ_succ]

end
end ImbalancedChen.P2CanonicalTentDynamicQueryReceiver
