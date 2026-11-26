import ImbalancedChen.P2OriginalPairBufferedRootProvenance

/-!
# Actual U5 last-source square provenance

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

The additional invariant records the actual last root/fresh SourceForm.
An inherited action appends an unselected prime; a fresh action uses that
exact selected row's checked mask. No square list is a provenance field.
The original trace, seed and finite CapPlan are evaluated without change.

The finite rank-three/four/five assembly reuses appendOne_gates. Beyond
rank five the existing actual_postfive_integer_gates supplies the tail.
No bank adoption, whole-box factorization or PP estimate is asserted.
-/

namespace ImbalancedChen.P3OriginalU5AllSourceSquares

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2EnhancedLowerPhysicalNode
open P2OriginalPairRootRoughProducer P2OriginalSelectedPairNativeData
open P2OriginalPairSourceReceiver
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank SelectedBranchData)
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)
open P2OriginalSelectedIntegerPrefixSquares
open P2OriginalSelectedNativeSmallExtension
open P2OriginalPostFifthRoughSquares
open P5OriginalU5CausalFinite

/-! ## General-rank PairRange point transfer

The original public PairRange transfer is restricted to rank five. The
following transfer keeps its same checked row and covers all finite ranks.
The four original endpoint/monotonicity helpers are reused by name. The
adjacent compatibility patch only makes these existing declarations public;
their statements and proof bodies are preserved byte for byte.
-/

/-- Every selected rank uses its own actual prefix code and SourceForm.
    Both point square lists follow from the whole-box source check. -/
theorem selected_prefix_point_squares (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (delta : ℚ) (rank : Fin 6)
    (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (word : List ℝ) (hword : word = [x 0, x 1, x 2, x 3, x 4].take rank.val)
    (branch : SelectedBranchData)
    (hsel : select R bank delta rank
      (prefixCode rank.val (codeAt R mesh rank.val word)) = some branch) :
    let code := prefixCode rank.val (codeAt R mesh rank.val word)
    let slots := pointSlots rank code branch.form.supportMask x
    SquareGates (rowCap R code delta branch : ℝ) 0 (slots.map Slot.exponent) ∧
      SquareGates (rowCap R code delta branch : ℝ)
        (selectedWord slots).sum (remainingWord slots) := by
  let code := prefixCode rank.val (codeAt R mesh rank.val word)
  have hsource := (select_some_source R bank delta rank code branch hsel).2
  rw [prefixCode_nested rank.val rank.val (le_refl _)] at hsource
  have hpoint := fun i => P2OriginalPairSourceReceiver.exponent_upper R mesh (hx i)
  have hupper : ∀ i, x i ≤ (qHi R mesh (code i).1 : ℝ) := by
    intro i
    have hp := hpoint i
    have hi := (hx i).2
    fin_cases rank <;> fin_cases i
    all_goals first
      | simpa [code, hword, codeAt, incomingCode, physicalCode, marked, prefixCode] using hp
      | simpa [code, hword, codeAt, incomingCode, physicalCode, marked, prefixCode,
          qHi, ceiling] using hi
  have hslots : List.Forall₂
      (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected = q.selected)
      (pointSlots rank code branch.form.supportMask x)
      (ownSlots R rank code branch.form.supportMask) := by
    fin_cases rank <;> simp [pointSlots, ownSlots, pointSlot, ownSlot, hupper]
  have hw := P2OriginalPairSourceReceiver.slot_words_mono hslots
  have hf := P2OriginalLowerSelectedCapConstructor.strictSquareGates_sound _ _ _
    hsource.2.2.1
  have hs := P2OriginalLowerSelectedCapConstructor.strictSquareGates_sound _ _ _
    hsource.2.2.2.1
  exact ⟨P2OriginalPairSourceReceiver.squareGates_mono (le_refl (0 : ℝ)) hw.1 hf,
    P2OriginalPairSourceReceiver.squareGates_mono
      (P2OriginalPairSourceReceiver.sum_le hw.2.1) hw.2.2 hs⟩

/-! ## Actual last-source data

`Origin` stores the selected row, its actual code and actual prefix prime
vector. `Provenance` admits only the root, a genuine checked fresh action,
or inheritance from that source. Square conclusions are separate outputs.
-/

inductive Origin (mesh : ℕ) where
  | root
  | row (rank : Fin 6) (code : Code mesh) (branch : SelectedBranchData)
      (primes : Fin 5 → ℕ)

def originSlots {mesh : ℕ} (t : ℕ × ℕ) : Origin mesh → List (ℕ × Bool)
  | .root => [(t.2, true), (t.1, true)]
  | .row rank code branch p => integerPrefixSlots rank code branch.form.supportMask p

def originCap (R : PairRange) {mesh : ℕ} (delta : ℚ) (seed : ℝ) : Origin mesh → ℝ
  | .root => seed
  | .row _ code branch _ => (rowCap R code delta branch : ℝ)

def actualTrace (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre : List ℕ) : Trace :=
  run (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
    (pairRoot N t seed) (pre.map (coordinate N))

def actionWord (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre : List ℕ) (q : ℕ) : List ℝ :=
  (actualTrace R bank delta seed N t pre).word ++ [coordinate N q]

def actionCode (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre : List ℕ) (q : ℕ)
    (rank : Fin 6) : Code mesh :=
  prefixCode rank.val (codeAt R mesh rank.val (actionWord R bank delta seed N t pre q))

def actionChoice (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre : List ℕ) (q : ℕ) : CapChoice :=
  planChoice (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
    (actionWord R bank delta seed N t pre q)

inductive Provenance (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) :
    List ℕ → Origin mesh → List (ℕ × Bool) → Prop
  | root : Provenance R bank delta seed N t [] .root [(t.2, true), (t.1, true)]
  | inherited {pre : List ℕ} {source : Origin mesh} {slots : List (ℕ × Bool)}
      (q : ℕ) (old : Provenance R bank delta seed N t pre source slots)
      (choice : actionChoice R bank delta seed N t pre q = .inherit 2) :
      Provenance R bank delta seed N t (pre ++ [q]) source (appendUnselected slots [q])
  | fresh (pre : List ℕ) (q : ℕ) (rank : Fin 6)
      (rank_ok : rank.val = 3 ∨ rank.val = 4 ∨ rank.val = 5)
      (p : Fin 5 → ℕ)
      (prefix_values : [p 0, p 1, p 2, p 3, p 4].take rank.val = t.2 :: t.1 :: (pre ++ [q]))
      (branch : SelectedBranchData)
      (selected : select R bank delta rank
        (actionCode R bank delta seed N t pre q rank) = some branch)
      (checked : freshCheck R rank (actionCode R bank delta seed N t pre q rank)
        delta (actualTrace R bank delta seed N t pre).cap branch)
      (choice : actionChoice R bank delta seed N t pre q =
        .fresh (rowCap R (actionCode R bank delta seed N t pre q rank) delta branch)
          branch.argument) :
      Provenance R bank delta seed N t (pre ++ [q])
        (.row rank (actionCode R bank delta seed N t pre q rank) branch p)
        (integerPrefixSlots rank (actionCode R bank delta seed N t pre q rank)
          branch.form.supportMask p)
  | postfive {pre : List ℕ} {source : Origin mesh} {slots : List (ℕ × Bool)}
      (old : Provenance R bank delta seed N t pre source slots)
      (length : pre.length = 3) (ds : List ℕ) :
      Provenance R bank delta seed N t (pre ++ ds) source (appendUnselected slots ds)

/-- Inheritance and the post-five continuation preserve this actual
    source's selected primes. An arbitrary convenient mask is unavailable. -/
theorem provenance_mask (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ)
    {pre : List ℕ} {source : Origin mesh} {slots : List (ℕ × Bool)}
    (h : Provenance R bank delta seed N t pre source slots) :
    selectedPrimes slots = selectedPrimes (originSlots t source) := by
  induction h with
  | root => rfl
  | inherited q old choice ih => exact (appendUnselected_selected _ _).trans ih
  | fresh => rfl
  | postfive old length ds ih => exact (appendUnselected_selected _ _).trans ih

structure PrefixSupply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre : List ℕ)
    (source : Origin mesh) (slots : List (ℕ × Bool)) : Prop where
  provenance : Provenance R bank delta seed N t pre source slots
  cap : (actualTrace R bank delta seed N t pre).cap = originCap R delta seed source
  values : slots.map Prod.fst = t.2 :: t.1 :: pre
  full : SquareGates (actualTrace R bank delta seed N t pre).cap 0
    ((logSlots N slots).map Slot.exponent)
  selected : SquareGates (actualTrace R bank delta seed N t pre).cap
    (selectedWord (logSlots N slots)).sum (remainingWord (logSlots N slots))

@[simp] theorem actualTrace_word (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre : List ℕ) :
    (actualTrace R bank delta seed N t pre).word =
      [coordinate N t.2, coordinate N t.1] ++ pre.map (coordinate N) := by
  exact run_word _ _ _ _ _

theorem actualTrace_snoc (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre : List ℕ) (q : ℕ) :
    actualTrace R bank delta seed N t (pre ++ [q]) =
      step (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
        (actualTrace R bank delta seed N t pre) (coordinate N q) := by
  unfold actualTrace
  rw [List.map_append, run_append]
  rfl

private theorem supply_word (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ)
    {pre : List ℕ} {source : Origin mesh} {slots : List (ℕ × Bool)}
    (h : PrefixSupply R bank delta seed N t pre source slots) :
    (logSlots N slots).map Slot.exponent = (actualTrace R bank delta seed N t pre).word := by
  have heq : (logSlots N slots).map Slot.exponent = (slots.map Prod.fst).map (coordinate N) := by
    simp [logSlots, List.map_map, Function.comp_def]
  rw [heq, h.values, actualTrace_word]
  rfl

private theorem prefix_slots_values {mesh : ℕ} (rank : Fin 6)
    (hr : rank.val = 3 ∨ rank.val = 4 ∨ rank.val = 5)
    (code : Code mesh) (mask : Finset (Fin 5)) (p : Fin 5 → ℕ) :
    (integerPrefixSlots rank code mask p).map Prod.fst =
      [p 0, p 1, p 2, p 3, p 4].take rank.val := by
  fin_cases rank <;> simp_all [integerPrefixSlots, integerPointSlot]

private theorem prefix_slots_log {mesh : ℕ} (N : ℕ) (rank : Fin 6)
    (hr : rank.val = 3 ∨ rank.val = 4 ∨ rank.val = 5)
    (code : Code mesh) (mask : Finset (Fin 5)) (p : Fin 5 → ℕ) :
    logSlots N (integerPrefixSlots rank code mask p) =
      pointSlots rank code mask (fun i => coordinate N (p i)) := by
  fin_cases rank <;> simp_all [logSlots, integerPrefixSlots, integerPointSlot, pointSlots, pointSlot]

/-! `advance_source` handles the one actual finite source action. Its
square premise is discharged at rank three by the original root reserve,
at rank four by the actual cube, and at rank five by that preceding cube.
-/

private theorem advance_source (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ)
    (pre : List ℕ) (q : ℕ) (rank : Fin 6)
    (hr : rank.val = 3 ∨ rank.val = 4 ∨ rank.val = 5)
    (p : Fin 5 → ℕ)
    (hvec : [p 0, p 1, p 2, p 3, p 4].take rank.val = t.2 :: t.1 :: (pre ++ [q]))
    (hx : ∀ i, coordinate N (p i) ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (hlookup : actionChoice R bank delta seed N t pre q =
      checkedChoice R bank delta rank (actualTrace R bank delta seed N t pre).cap
        (codeAt R mesh rank.val (actionWord R bank delta seed N t pre q)))
    {source : Origin mesh} {slots : List (ℕ × Bool)}
    (old : PrefixSupply R bank delta seed N t pre source slots)
    (hsquare : (actualTrace R bank delta seed N t pre).word.sum + 2 * coordinate N q ≤
      (actualTrace R bank delta seed N t pre).cap) :
    ∃ nextSource nextSlots,
      PrefixSupply R bank delta seed N t (pre ++ [q]) nextSource nextSlots ∧
      (actualTrace R bank delta seed N t pre).cap ≤
        (actualTrace R bank delta seed N t (pre ++ [q])).cap := by
  let H := actualTrace R bank delta seed N t pre
  let code := actionCode R bank delta seed N t pre q rank
  have hstep : (actualTrace R bank delta seed N t (pre ++ [q])).cap =
      (actionChoice R bank delta seed N t pre q).freeze H.cap := by
    rw [actualTrace_snoc]
    rfl
  have hinherit (hchoice : actionChoice R bank delta seed N t pre q = .inherit 2) :
      ∃ nextSource nextSlots,
        PrefixSupply R bank delta seed N t (pre ++ [q]) nextSource nextSlots ∧
        H.cap ≤ (actualTrace R bank delta seed N t (pre ++ [q])).cap := by
    have hc : (actualTrace R bank delta seed N t (pre ++ [q])).cap = H.cap := by
      rw [hstep, hchoice]
      rfl
    let node : PhysicalNode := ⟨0, H.cap, logSlots N slots, 0, 2⟩
    have hword := supply_word R bank delta seed N t old
    have hgate := appendOne_gates (n := node) (x := coordinate N q) (s := 2)
      old.full old.selected (by
        change 2 * coordinate N q ≤ H.cap - ((logSlots N slots).map Slot.exponent).sum
        rw [hword]
        linarith [hsquare])
    have hlog : logSlots N (appendUnselected slots [q]) =
        logSlots N slots ++ [unselected (coordinate N q)] := by
      simp [logSlots, appendUnselected, unselected]
    refine ⟨source, appendUnselected slots [q], ?_, hc.ge⟩
    refine ⟨Provenance.inherited q old.provenance hchoice, hc.trans old.cap, ?_, ?_, ?_⟩
    · rw [appendUnselected_values, old.values]
      rfl
    · rw [hc, hlog]
      exact hgate.1
    · rw [hc, hlog]
      exact hgate.2
  cases hsel : select R bank delta rank code with
  | none =>
      apply hinherit
      rw [hlookup]
      simp only [checkedChoice, show prefixCode rank.val
        (codeAt R mesh rank.val (actionWord R bank delta seed N t pre q)) = code from rfl, hsel]
  | some branch =>
      by_cases hcheck : freshCheck R rank code delta
          (actualTrace R bank delta seed N t pre).cap branch
      · have hchoice : actionChoice R bank delta seed N t pre q =
            .fresh (rowCap R code delta branch) branch.argument := by
          rw [hlookup]
          simp only [checkedChoice, show prefixCode rank.val
            (codeAt R mesh rank.val (actionWord R bank delta seed N t pre q)) = code from rfl,
            hsel, if_pos hcheck]
        have hc : (actualTrace R bank delta seed N t (pre ++ [q])).cap =
            (rowCap R code delta branch : ℝ) := by rw [hstep, hchoice]; rfl
        have hpointWord : actionWord R bank delta seed N t pre q =
            [coordinate N (p 0), coordinate N (p 1), coordinate N (p 2),
              coordinate N (p 3), coordinate N (p 4)].take rank.val := by
          have hm := congrArg (List.map (coordinate N)) hvec
          simpa [List.map_take, actionWord, actualTrace_word, List.map_append, List.append_assoc]
            using hm.symm
        have hpoint := selected_prefix_point_squares R bank delta rank
          (fun i => coordinate N (p i)) hx _ hpointWord branch hsel
        refine ⟨.row rank code branch p,
          integerPrefixSlots rank code branch.form.supportMask p, ?_, ?_⟩
        · refine ⟨Provenance.fresh pre q rank hr p hvec branch hsel hcheck hchoice,
            hc, ?_, ?_, ?_⟩
          · exact (prefix_slots_values rank hr code _ p).trans hvec
          · rw [hc, prefix_slots_log N rank hr]
            exact hpoint.1
          · rw [hc, prefix_slots_log N rank hr]
            exact hpoint.2
        · rw [hc]
          exact hcheck.1.le
      · apply hinherit
        rw [hlookup]
        simp only [checkedChoice, show prefixCode rank.val
          (codeAt R mesh rank.val (actionWord R bank delta seed N t pre q)) = code from rfl,
          hsel, if_neg hcheck]

/-! ## The three finite source actions bind to the actual frozen parent

These are prefix-code identities, not a replacement trace evaluator.
The complete fifth cap identity already exists as pair_run_three_cap;
the extra identities here expose the first two intermediate states.
-/

private theorem prefix_vector_code (R : PairRange) (mesh : ℕ)
    (rank : Fin 6) (x : Fin 5 → ℝ) :
    codeAt R mesh rank.val ([x 0, x 1, x 2, x 3, x 4].take rank.val) =
      prefixCode rank.val (codeAt R mesh 5 [x 0, x 1, x 2, x 3, x 4]) := by
  fin_cases rank <;> funext i <;> fin_cases i <;>
    simp [codeAt, incomingCode, physicalCode, marked, prefixCode, exponentCode, ceiling]

private theorem finite_lookups (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ) :
    actionChoice R bank delta seed N t [] q₀ =
      checkedChoice R bank delta 3 (actualTrace R bank delta seed N t []).cap
        (codeAt R mesh 3 (actionWord R bank delta seed N t [] q₀)) ∧
    actionChoice R bank delta seed N t [q₀] q₁ =
      checkedChoice R bank delta 4 (actualTrace R bank delta seed N t [q₀]).cap
        (codeAt R mesh 4 (actionWord R bank delta seed N t [q₀] q₁)) ∧
    actionChoice R bank delta seed N t [q₀, q₁] q₂ =
      checkedChoice R bank delta 5 (actualTrace R bank delta seed N t [q₀, q₁]).cap
        (codeAt R mesh 5 (actionWord R bank delta seed N t [q₀, q₁] q₂)) := by
  let x : Fin 5 → ℝ := ![coordinate N t.2, coordinate N t.1, coordinate N q₀,
    coordinate N q₁, coordinate N q₂]
  let c3 := codeAt R mesh 3 [x 0, x 1, x 2]
  let c4 := codeAt R mesh 4 [x 0, x 1, x 2, x 3]
  let c5 := codeAt R mesh 5 [x 0, x 1, x 2, x 3, x 4]
  have hp3 : c3 = prefixCode 3 c5 := by
    simpa [c3, c5] using prefix_vector_code R mesh 3 x
  have hp4 : c4 = prefixCode 4 c5 := by
    simpa [c4, c5] using prefix_vector_code R mesh 4 x
  have h3raw : (actualTrace R bank delta seed N t [q₀]).cap =
      checkedCap R bank delta 3 seed c3 := by
    simp [actualTrace, run, pairRoot, step, planChoice, incomingChoice, pairPlan,
      checkedCap, c3, x, codeAt]
  have h3 : (actualTrace R bank delta seed N t [q₀]).cap =
      cap3 R bank delta seed c5 := by
    rw [h3raw, hp3]
    simp only [cap3, checkedCap, checkedChoice,
      prefixCode_nested (3 : Fin 6).val 3 (by decide)]
  have h34 : cap3 R bank delta seed c4 = cap3 R bank delta seed c5 := by
    rw [hp4]
    simp only [cap3, checkedCap, checkedChoice,
      prefixCode_nested (3 : Fin 6).val 4 (by decide)]
  have lookup3 : actionChoice R bank delta seed N t [] q₀ =
      checkedChoice R bank delta 3 (actualTrace R bank delta seed N t []).cap
        (codeAt R mesh 3 (actionWord R bank delta seed N t [] q₀)) := by
    simp [actionChoice, actionWord, actualTrace, run, pairRoot,
      planChoice, incomingChoice, pairPlan, codeAt]
  have lookup4 : actionChoice R bank delta seed N t [q₀] q₁ =
      checkedChoice R bank delta 4 (actualTrace R bank delta seed N t [q₀]).cap
        (codeAt R mesh 4 (actionWord R bank delta seed N t [q₀] q₁)) := by
    change checkedChoice R bank delta 4 (cap3 R bank delta seed c4) c4 =
      checkedChoice R bank delta 4 (actualTrace R bank delta seed N t [q₀]).cap c4
    rw [h3, h34]
  have h4 : (actualTrace R bank delta seed N t [q₀, q₁]).cap =
      cap4 R bank delta seed c5 := by
    have hs := actualTrace_snoc R bank delta seed N t [q₀] q₁
    change (actualTrace R bank delta seed N t ([q₀] ++ [q₁])).cap = _
    rw [hs]
    change (actionChoice R bank delta seed N t [q₀] q₁).freeze
      (actualTrace R bank delta seed N t [q₀]).cap = _
    rw [lookup4, h3]
    change (checkedChoice R bank delta 4 (cap3 R bank delta seed c5) c4).freeze
      (cap3 R bank delta seed c5) = _
    rw [hp4]
    simp only [cap4, checkedCap, checkedChoice,
      prefixCode_nested (4 : Fin 6).val 4 (by decide)]
  have lookup5 : actionChoice R bank delta seed N t [q₀, q₁] q₂ =
      checkedChoice R bank delta 5 (actualTrace R bank delta seed N t [q₀, q₁]).cap
        (codeAt R mesh 5 (actionWord R bank delta seed N t [q₀, q₁] q₂)) := by
    change checkedChoice R bank delta 5 (cap4 R bank delta seed c5) c5 =
      checkedChoice R bank delta 5 (actualTrace R bank delta seed N t [q₀, q₁]).cap c5
    rw [h4]
  exact ⟨lookup3, lookup4, lookup5⟩

def primeVector (t : ℕ × ℕ) (q₀ q₁ q₂ : ℕ) : Fin 5 → ℕ :=
  ![t.2, t.1, q₀, q₁, q₂]

private theorem original_root_supply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    PrefixSupply R bank (2 * buffer) (rootSeed false buffer N t) N t [] .root
      [(t.2, true), (t.1, true)] ∧
    (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t []).word.sum +
      2 * (417/5000 : ℝ) < rootSeed false buffer N t := by
  have hxy : coordinates N t = P2OriginalPairBufferedRootProvenance.pairPoint N t := by
    funext i
    fin_cases i <;> rfl
  have hp := coordinates_mem_triangle hN ht
  rw [hxy] at hp
  have hs := P2OriginalPairBufferedRootProvenance.fifth_buffered_root_squares hp buffer hb
  have hroot : 2 * coordinate N t.2 < rootSeed false buffer N t ∧
      coordinate N t.2 + 2 * coordinate N t.1 < rootSeed false buffer N t ∧
      coordinate N t.2 + coordinate N t.1 + 2 * (417/5000 : ℝ) < rootSeed false buffer N t := by
    simpa [P2OriginalPairBufferedRootProvenance.pairPoint, rootSeed, rootLevel] using hs
  refine ⟨⟨Provenance.root, rfl, rfl, ?_, ?_⟩, ?_⟩
  · simpa [actualTrace, run, pairRoot, logSlots, SquareGates] using
      And.intro hroot.1.le (And.intro hroot.2.1.le True.intro)
  · simp [actualTrace, run, pairRoot, logSlots, selectedWord, remainingWord, SquareGates]
  · simpa using hroot.2.2

private theorem rank_three_supply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (q₀ q₁ q₂ : ℕ)
    (hx : ∀ i, coordinate N (primeVector t q₀ q₁ q₂ i) ∈
      Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (hq₀ : coordinate N q₀ ≤ (417/5000 : ℝ)) :
    ∃ source slots, PrefixSupply R bank (2 * buffer) (rootSeed false buffer N t)
      N t [q₀] source slots := by
  have hroot := original_root_supply R bank buffer hb hN ht
  have hlookup := (finite_lookups R bank (2 * buffer) (rootSeed false buffer N t)
    N t q₀ q₁ q₂).1
  have hsquare :
      (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t []).word.sum +
        2 * coordinate N q₀ ≤
      (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t []).cap := by
    change _ ≤ rootSeed false buffer N t
    linarith [hroot.2]
  obtain ⟨source, slots, hs, _⟩ := advance_source R bank (2 * buffer)
    (rootSeed false buffer N t) N t [] q₀ 3 (Or.inl rfl)
    (primeVector t q₀ q₁ q₂) rfl hx hlookup hroot.1 hsquare
  exact ⟨source, slots, hs⟩

private theorem rank_four_supply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (q₀ q₁ q₂ : ℕ)
    (hx : ∀ i, coordinate N (primeVector t q₀ q₁ q₂ i) ∈
      Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (hq₀ : coordinate N q₀ ≤ (417/5000 : ℝ))
    (haccept : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t [q₀, q₁]).accepted = true) :
    ∃ source slots, PrefixSupply R bank (2 * buffer) (rootSeed false buffer N t)
      N t [q₀, q₁] source slots ∧
      (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t [q₀, q₁]).word.sum +
        2 * coordinate N q₁ <
      (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t [q₀, q₁]).cap := by
  let delta := 2 * buffer
  let seed := rootSeed false buffer N t
  obtain ⟨source, slots, old⟩ := rank_three_supply R bank buffer hb hN ht q₀ q₁ q₂ hx hq₀
  have hstepacc : (step (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
      (actualTrace R bank delta seed N t [q₀]) (coordinate N q₁)).accepted = true := by
    have ha : (actualTrace R bank delta seed N t ([q₀] ++ [q₁])).accepted = true := haccept
    rw [actualTrace_snoc] at ha
    exact ha
  have hadm := ((step_accepted_iff (pairPlan R bank delta seed) (R.epsilon : ℝ)
    (ceiling : ℝ) (actualTrace R bank delta seed N t [q₀]) (coordinate N q₁)).mp hstepacc).2
  have hcube : (actualTrace R bank delta seed N t [q₀]).word.sum +
      3 * coordinate N q₁ < (actualTrace R bank delta seed N t [q₀]).cap := by
    simpa [admission, actualTrace_word] using hadm
  have hpos : 0 ≤ coordinate N q₁ := by
    have he : 0 < (R.epsilon : ℝ) := by exact_mod_cast R.epsilon_pos
    exact he.le.trans (hx 3).1
  have hsquare : (actualTrace R bank delta seed N t [q₀]).word.sum +
      2 * coordinate N q₁ ≤ (actualTrace R bank delta seed N t [q₀]).cap := by
    linarith
  obtain ⟨nextSource, nextSlots, hs, hmono⟩ := advance_source R bank delta seed N t [q₀] q₁ 4
    (Or.inr (Or.inl rfl)) (primeVector t q₀ q₁ q₂) rfl hx
    (finite_lookups R bank delta seed N t q₀ q₁ q₂).2.1 old hsquare
  refine ⟨nextSource, nextSlots, hs, ?_⟩
  have hsum : (actualTrace R bank delta seed N t [q₀, q₁]).word.sum =
      (actualTrace R bank delta seed N t [q₀]).word.sum + coordinate N q₁ := by
    simp [actualTrace_word]; ring
  change (actualTrace R bank delta seed N t [q₀]).cap ≤
    (actualTrace R bank delta seed N t [q₀, q₁]).cap at hmono
  change (actualTrace R bank delta seed N t [q₀, q₁]).word.sum + 2 * coordinate N q₁ <
    (actualTrace R bank delta seed N t [q₀, q₁]).cap
  rw [hsum]
  linarith only [hcube, hmono]

private theorem rank_five_supply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (q₀ q₁ q₂ : ℕ)
    (hx : ∀ i, coordinate N (primeVector t q₀ q₁ q₂ i) ∈
      Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (hq₀ : coordinate N q₀ ≤ (417/5000 : ℝ))
    (horder : coordinate N q₂ ≤ coordinate N q₁)
    (haccept : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t [q₀, q₁, q₂]).accepted = true) :
    ∃ source slots, PrefixSupply R bank (2 * buffer) (rootSeed false buffer N t)
      N t [q₀, q₁, q₂] source slots := by
  let delta := 2 * buffer
  let seed := rootSeed false buffer N t
  have hstepacc : (step (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
      (actualTrace R bank delta seed N t [q₀, q₁]) (coordinate N q₂)).accepted = true := by
    have ha : (actualTrace R bank delta seed N t ([q₀, q₁] ++ [q₂])).accepted = true := haccept
    rw [actualTrace_snoc] at ha
    exact ha
  have hacc4 := ((step_accepted_iff (pairPlan R bank delta seed) (R.epsilon : ℝ)
    (ceiling : ℝ) (actualTrace R bank delta seed N t [q₀, q₁]) (coordinate N q₂)).mp hstepacc).1
  obtain ⟨source, slots, old, hcarry⟩ :=
    rank_four_supply R bank buffer hb hN ht q₀ q₁ q₂ hx hq₀ hacc4
  have hsquare : (actualTrace R bank delta seed N t [q₀, q₁]).word.sum +
      2 * coordinate N q₂ ≤ (actualTrace R bank delta seed N t [q₀, q₁]).cap := by
    linarith
  obtain ⟨nextSource, nextSlots, hs, _⟩ := advance_source R bank delta seed N t [q₀, q₁] q₂ 5
    (Or.inr (Or.inr rfl)) (primeVector t q₀ q₁ q₂) rfl hx
    (finite_lookups R bank delta seed N t q₀ q₁ q₂).2.2 old hsquare
  exact ⟨nextSource, nextSlots, hs⟩

/-! ## Original carriers and the existing arbitrary-tail consumer -/

structure IntegerSupply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (chosen : List ℕ)
    (source : Origin mesh) (slots : List (ℕ × Bool)) : Prop where
  provenance : Provenance R bank delta seed N t chosen source slots
  cap : (actualTrace R bank delta seed N t chosen).cap = originCap R delta seed source
  values : slots.map Prod.fst = t.2 :: t.1 :: chosen
  full : IntegerSquareGates N (actualTrace R bank delta seed N t chosen).cap 1
    (slots.map Prod.fst)
  selected : IntegerSquareGates N (actualTrace R bank delta seed N t chosen).cap
    (selectedPrimes slots).prod (remainingPrimes slots)

private theorem prefix_integer_supply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) {N : ℕ} (hN : 1 < (N : ℝ)) (t : ℕ × ℕ)
    {pre : List ℕ} {source : Origin mesh} {slots : List (ℕ × Bool)}
    (h : PrefixSupply R bank delta seed N t pre source slots)
    (hprime : ∀ p ∈ t.2 :: t.1 :: pre, p.Prime) :
    IntegerSupply R bank delta seed N t pre source slots := by
  have hpos : ∀ v ∈ slots, 0 < v.1 := by
    intro v hv
    have hm : v.1 ∈ slots.map Prod.fst := List.mem_map.mpr ⟨v, hv, rfl⟩
    rw [h.values] at hm
    exact (hprime v.1 hm).pos
  have hs := physical_slots_to_integer hN slots hpos _ h.full h.selected
  exact ⟨h.provenance, h.cap, h.values, hs.1, hs.2⟩

theorem actualTrace_append (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (delta : ℚ) (seed : ℝ) (N : ℕ) (t : ℕ × ℕ) (pre ds : List ℕ) :
    actualTrace R bank delta seed N t (pre ++ ds) =
      run (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
        (actualTrace R bank delta seed N t pre) (ds.map (coordinate N)) := by
  unfold actualTrace
  rw [List.map_append, run_append]

/-- Once the actual first three rough primes have supplied their last
    source, reuse the old post-five proof for every retained later prime. -/
private theorem postfive_integer_supply (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (delta : ℚ) (seed : ℝ)
    {N : ℕ} (hN : 1 < (N : ℝ)) (t : ℕ × ℕ)
    (pre ds : List ℕ) (hlen : pre.length = 3)
    {source : Origin mesh} {slots : List (ℕ × Bool)}
    (old : PrefixSupply R bank delta seed N t pre source slots)
    (hprime : ∀ p ∈ t.2 :: t.1 :: pre, p.Prime)
    (hdsPrime : ∀ p ∈ ds, p.Prime) (hdsSort : ds.Pairwise (· ≥ ·))
    (haccept : (actualTrace R bank delta seed N t (pre ++ ds)).accepted = true) :
    IntegerSupply R bank delta seed N t (pre ++ ds) source (appendUnselected slots ds) := by
  let H := actualTrace R bank delta seed N t pre
  have hHlen : H.word.length = 5 := by simp [H, actualTrace_word, hlen]
  have hpos : ∀ v ∈ slots, 0 < v.1 := by
    intro v hv
    have hm : v.1 ∈ slots.map Prod.fst := List.mem_map.mpr ⟨v, hv, rfl⟩
    rw [old.values] at hm
    exact (hprime v.1 hm).pos
  have hacc : (run (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
      H (ds.map (coordinate N))).accepted = true := by
    rw [actualTrace_append] at haccept
    exact haccept
  have hs := actual_postfive_integer_gates (pairPlan R bank delta seed)
    (R.epsilon : ℝ) (ceiling : ℝ) hN H hHlen slots
    (supply_word R bank delta seed N t old) hpos old.full old.selected
    ds hdsPrime hdsSort hacc
  have hc : (actualTrace R bank delta seed N t (pre ++ ds)).cap = H.cap := by
    rw [actualTrace_append]
    exact run_cap_after_five (pairPlan R bank delta seed) (R.epsilon : ℝ) (ceiling : ℝ)
      H (by omega) (ds.map (coordinate N))
  refine ⟨Provenance.postfive old.provenance hlen ds, hc.trans old.cap, ?_, ?_, ?_⟩
  · rw [appendUnselected_values, old.values]
    rfl
  · rw [hc]
    exact hs.1
  · rw [hc]
    exact hs.2

/-- Original selector and roughUniverse membership supply the point
    range used by the finite source checker. No input square is added. -/
private theorem original_coordinate_ranges (R : PairRange) (epsilon : ℝ)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    {chosen : List ℕ}
    (hsub : chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N)) :
    coordinate N t.2 ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ) ∧
    coordinate N t.1 ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ) ∧
    (∀ p ∈ chosen, coordinate N p ∈ Set.Icc (R.epsilon : ℝ) (417/5000 : ℝ)) := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hu, hut, hh⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp
    (coordinates_mem_triangle hN ht)
  change (417/5000 : ℝ) ≤ coordinate N t.1 at hu
  change coordinate N t.1 < coordinate N t.2 at hut
  change coordinate N t.2 < (19/125 : ℝ) at hh
  have hR : (R.epsilon : ℝ) ≤ (417 / 5000 : ℝ) := by
    have hcast : (R.epsilon : ℝ) ≤ ((417 / 5000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr R.epsilon_lt_a.le
    norm_num at hcast ⊢
    exact hcast
  have hhD : (19/125 : ℝ) ≤ (ceiling : ℝ) := by norm_num [ceiling]
  refine ⟨⟨(hR.trans hu).trans hut.le, hh.le.trans hhD⟩,
    ⟨hR.trans hu, (hut.le.trans hh.le).trans hhD⟩, ?_⟩
  intro p hp
  have hmem := hsub.subset hp
  have hprime := mem_roughPrimeUniverse_prime hmem
  constructor
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [coordinate_power hNr hprime.pos]
    exact (Real.rpow_le_rpow_of_exponent_le hNr.le hgrid).trans
      (mem_roughPrimeUniverse_lower hmem)
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [coordinate_power hNr hprime.pos]
    exact (mem_roughPrimeUniverse_upper hmem).le

/-- Every actual accepted U5 rough word, including lengths zero, one and
    two, has both integer square lists at its own actual frozen cap.

The output origin is the literal root or the last actual checked source
at rank 3/4/5. Its original mask is retained through every inherited action
and through the complete post-five tail. No FreshFifth or final square,
budget, source-adoption or factorization licence is an input. -/
theorem actual_U5_all_source_integer_squares
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) (epsilon : ℝ)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (chosen : List ℕ)
    (hsub : chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N))
    (haccept : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen).accepted = true) :
    ∃ source slots, IntegerSupply R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen source slots := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hrange := original_coordinate_ranges R epsilon hgrid hN ht hsub
  obtain ⟨hc, _, _, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hc
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp ht₁).2.1
  have hp₂ := (mem_chenAdditivePrimeCarrier.mp ht₂).2.1
  have hroughPrime : ∀ p ∈ chosen, p.Prime :=
    fun p hp => mem_roughPrimeUniverse_prime (hsub.subset hp)
  have hprime : ∀ p ∈ t.2 :: t.1 :: chosen, p.Prime := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hp₂
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hp₁
    · exact hroughPrime p hp
  have haD : (417/5000 : ℝ) ≤ (ceiling : ℝ) := by norm_num [ceiling]
  have hroughRange : ∀ p ∈ chosen,
      coordinate N p ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ) := by
    intro p hp
    exact ⟨(hrange.2.2 p hp).1, (hrange.2.2 p hp).2.trans haD⟩
  cases chosen with
  | nil =>
      exact ⟨.root, [(t.2, true), (t.1, true)],
        prefix_integer_supply R bank (2 * buffer) (rootSeed false buffer N t) hNr t
          (original_root_supply R bank buffer hb hN ht).1 hprime⟩
  | cons q₀ rest =>
      have hq₀ := (hrange.2.2 q₀ (by simp)).2
      cases rest with
      | nil =>
          have hx : ∀ i, coordinate N (primeVector t q₀ q₀ q₀ i) ∈
              Set.Icc (R.epsilon : ℝ) (ceiling : ℝ) := by
            intro i
            fin_cases i
            · exact hrange.1
            · exact hrange.2.1
            all_goals exact hroughRange q₀ (by simp)
          obtain ⟨source, slots, hs⟩ := rank_three_supply R bank buffer hb hN ht
            q₀ q₀ q₀ hx hq₀
          exact ⟨source, slots,
            prefix_integer_supply R bank (2 * buffer) (rootSeed false buffer N t) hNr t hs hprime⟩
      | cons q₁ rest =>
          cases rest with
          | nil =>
              have hx : ∀ i, coordinate N (primeVector t q₀ q₁ q₁ i) ∈
                  Set.Icc (R.epsilon : ℝ) (ceiling : ℝ) := by
                intro i
                fin_cases i
                · exact hrange.1
                · exact hrange.2.1
                · exact hroughRange q₀ (by simp)
                all_goals exact hroughRange q₁ (by simp)
              obtain ⟨source, slots, hs, _⟩ := rank_four_supply R bank buffer hb hN ht
                q₀ q₁ q₁ hx hq₀ haccept
              exact ⟨source, slots,
                prefix_integer_supply R bank (2 * buffer) (rootSeed false buffer N t) hNr t hs hprime⟩
          | cons q₂ ds =>
              have hx : ∀ i, coordinate N (primeVector t q₀ q₁ q₂ i) ∈
                  Set.Icc (R.epsilon : ℝ) (ceiling : ℝ) := by
                intro i
                fin_cases i
                · exact hrange.1
                · exact hrange.2.1
                · exact hroughRange q₀ (by simp)
                · exact hroughRange q₁ (by simp)
                · exact hroughRange q₂ (by simp)
              have hgt := (roughPrimeUniverse_pairwise_gt N (Nat.ceil (cutoff N))
                (smallCutoff N epsilon) (cutoff N)).sublist hsub
              have hgt₁ := (List.pairwise_cons.mp hgt).2
              have hq₂q₁ : q₂ < q₁ := (List.pairwise_cons.mp hgt₁).1 q₂ (by simp)
              have horder : coordinate N q₂ ≤ coordinate N q₁ := by
                apply (Real.rpow_le_rpow_left_iff hNr).mp
                rw [coordinate_power hNr (hroughPrime q₂ (by simp)).pos,
                  coordinate_power hNr (hroughPrime q₁ (by simp)).pos]
                exact_mod_cast hq₂q₁.le
              have hdsGT := (List.pairwise_cons.mp (List.pairwise_cons.mp hgt₁).2).2
              have hdsSort : ds.Pairwise (· ≥ ·) := by
                apply List.pairwise_iff_getElem.mpr
                intro i j hi hj hij
                exact ((List.pairwise_iff_getElem.mp hdsGT) i j hi hj hij).le
              have haccTail : (run (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
                  (R.epsilon : ℝ) (ceiling : ℝ)
                  (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t [q₀, q₁, q₂])
                  (ds.map (coordinate N))).accepted = true := by
                have heq := actualTrace_append R bank (2 * buffer) (rootSeed false buffer N t)
                  N t [q₀, q₁, q₂] ds
                rw [← heq]
                exact haccept
              have hacc5 := P2LowerIntegerRetainedSupport.run_accepted_incoming
                (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
                (R.epsilon : ℝ) (ceiling : ℝ) _ _ haccTail
              obtain ⟨source, slots, hs⟩ := rank_five_supply R bank buffer hb hN ht
                q₀ q₁ q₂ hx hq₀ horder hacc5
              have hprefixPrime : ∀ p ∈ t.2 :: t.1 :: [q₀, q₁, q₂], p.Prime := by
                intro p hp
                have hm : p ∈ [t.2, t.1, q₀, q₁, q₂] ++ ds :=
                  List.mem_append.mpr (Or.inl hp)
                exact hprime p (by simpa using hm)
              exact ⟨source, appendUnselected slots ds,
                postfive_integer_supply R bank (2 * buffer) (rootSeed false buffer N t)
                  hNr t [q₀, q₁, q₂] ds rfl hs hprefixPrime
                  (fun p hp => hroughPrime p (by simp [hp])) hdsSort haccept⟩

/-- The actual nonzero native U5 coefficient supplies its own accepted
    word. All source cases, including short and inherited words, are
    handled internally. This is rough square support, not full (F). -/
theorem native_U5_nonzero_all_source_squares
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : buffer ≤ 1/1000) (epsilon : ℝ)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0) :
    ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon),
      ∃ chosen : List ℕ,
        chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
          (smallCutoff N epsilon) (cutoff N) ∧ k = s * chosen.prod ∧
        (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t chosen).accepted = true ∧
        ∃ source slots, IntegerSupply R bank (2 * buffer) (rootSeed false buffer N t)
          N t chosen source slots := by
  obtain ⟨s, hs, r, _hr, chosen, hsub, hprod, hkprod, haccept⟩ :=
    native_U5_nonzero_word R bank buffer epsilon N t hk
  refine ⟨s, hs, chosen, hsub, ?_, haccept, ?_⟩
  · simpa only [hprod] using hkprod
  · exact actual_U5_all_source_integer_squares R bank buffer hb epsilon hgrid hN ht chosen hsub haccept

end
end ImbalancedChen.P3OriginalU5AllSourceSquares
