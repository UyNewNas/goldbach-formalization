import ImbalancedChen.P2Selected430W1ScalarTargets
import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual integer BH/W1/W2-singleton edges are the production singleChildren.
The only added compact-policy restrictions are rank, physical mesh and the
original own-cube test against the already frozen incoming H.cap. Admission,
prime-word alignment, unchanged Q, full/selected gates and a uniform positive
residual are conclusions of this source-path induction, not ParentTests fields.
Every step's query is computed from its original rule and integer prime.

The reverse theorem concerns a real selected W1 triple at such a constructed
parent, with the exact recursively frozen admittedChildPredicate. It proves
that the exporter contains the same occurrence and exact receiver/triple
family; therefore the exporter cannot be empty when that source term exists.
The full eleven-root instance and pair-child routes remain separate work.
-/
namespace ImbalancedChen.P2Selected430ActualW1SourceCoverage
noncomputable section
open Set
open scoped Classical
open P2Selected430CausalOccurrenceExporter
open P2Selected430W1ScalarTargets
open P2EnhancedW1FiniteActionBankPayment (W1Occurrence)
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry
open P2PhysicalFrozenPrefixHistory
open P2PhysicalIncomingPrefixCells (CapPlan)
open P5OriginalActionMassBound (W1Anchor originalW2At)
open P2EnhancedW1R2ActualCarrierBranch (admittedChildPredicate)
open P2EnhancedW1OrderedPositiveTripleWord
  (TripleLabel positiveTripleWords repeatedTripleWords)

structure IntegerStep (N : ℕ) where
  rule : SingleRule
  prime : Fin (N+1)

def query (Q : ℝ) (old : List ℕ) (e : IntegerStep N) : ℝ :=
  match e.rule with
  | .buchstab _ _ => buchstabArgument Q old e.prime.val
  | .w1 _ j => W1Anchor j * (1-relativePrime Q old e.prime.val)
  | .w2 bank _ => (originalW2At bank).s0 * (1-relativePrime Q old e.prime.val)

def childHistory {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) (H : History) (old : List ℕ) (e : IntegerStep N) : History :=
  step plan lo hi H (physicalPrime N e.prime.val) (query Q old e)

def encode (Q : ℝ) : List ℕ → List (IntegerStep N) → List (ℕ × ℝ)
  | _,[] => []
  | old,e::es => (e.prime.val,query Q old e) :: encode Q (singleWord old e.prime.val) es

def finishWord : List ℕ → List (IntegerStep N) → List ℕ
  | old,[] => old
  | old,e::es => finishWord (singleWord old e.prime.val) es

def finishHistory {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) : History → List ℕ → List (IntegerStep N) → History
  | H,_,[] => H
  | H,old,e::es => finishHistory plan N Q lo hi
      (childHistory plan N Q lo hi H old e) (singleWord old e.prime.val) es

structure IntegerState (N : ℕ) (Q : ℝ) (H : History) (old : List ℕ) : Prop where
  word_eq : word H.node = old.map (physicalPrime N)
  total_eq : H.node.total = Real.log Q / Real.log (N : ℝ)
  primes : ∀ p ∈ old, p.Prime

/-- Production integer source membership plus exactly the physical
compact-policy cap/rank/mesh gates, not exporter acceptance. -/
structure SourceEdge {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) (H : History) (old : List ℕ)
    (e : IntegerStep N) : Prop where
  member : e.prime ∈ singleChildren e.rule N Q old H.node.ceiling
  rank : H.node.slots.length+1 ≤ depth
  physicalBox : physicalPrime N e.prime.val ∈ Icc lo hi
  incomingCube : (word H.node).sum + 3*physicalPrime N e.prime.val < H.cap

def SourceSteps {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) : History → List ℕ → List (IntegerStep N) → Prop
  | _,_,[] => True
  | H,old,e::es => SourceEdge plan N Q lo hi H old e ∧
      SourceSteps plan N Q lo hi (childHistory plan N Q lo hi H old e)
        (singleWord old e.prime.val) es

private theorem step_integer_state {depth mesh : ℕ} {plan : CapPlan depth mesh}
    {N : ℕ} {Q chi lo hi : ℝ} {H : History} {old : List ℕ} {e : IntegerStep N}
    (hs : IntegerState N Q H old) (hw : parentWindow N Q old chi)
    (he : SourceEdge plan N Q lo hi H old e) :
    IntegerState N Q (childHistory plan N Q lo hi H old e)
        (singleWord old e.prime.val) ∧
      parentWindow N Q (singleWord old e.prime.val) chi := by
  have hp := mem_singleChildren.mp he.member
  have hnewPrime := singleWord_primes hs.primes he.member
  constructor
  · refine ⟨?_,?_,hnewPrime⟩
    · change word (appendOne H.node (physicalPrime N e.prime.val) (query Q old e)) = _
      rw [word_appendOne,hs.word_eq]
      simp only [singleWord,List.map_append,List.map_cons,List.map_nil]
    · exact hs.total_eq
  · have hprod : (singleWord old e.prime.val).prod = old.prod * e.prime.val :=
      (singleWord_history old e.prime.val).2.2
    refine ⟨hw.1,?_,?_,hw.2.2.2.1,hw.2.2.2.2⟩
    · rw [hprod]
      exact mul_pos hw.2.1 hp.1.1.pos
    · simpa only [hprod,parentProduct] using hp.2.2.2.2

private theorem step_admission {depth mesh : ℕ} {plan : CapPlan depth mesh}
    {N : ℕ} {Q chi lo hi : ℝ} {H : History} {old : List ℕ} {e : IntegerStep N}
    (haccepted : H.accepted=true) (hf : fullGates H.node) (hsel : selectedGates H.node)
    (hs : IntegerState N Q H old) (hw : parentWindow N Q old chi)
    (he : SourceEdge plan N Q lo hi H old e) :
    (childHistory plan N Q lo hi H old e).accepted=true ∧
    fullGates (childHistory plan N Q lo hi H old e).node ∧
    selectedGates (childHistory plan N Q lo hi H old e).node ∧
    residual H.node/2 ≤ residual (childHistory plan N Q lo hi H old e).node := by
  have hp := mem_singleChildren.mp he.member
  have hlevel := P2EnhancedW1RepeatedLabelClassification.physical_level_eq_parent_residual
    hw hs.primes hs.word_eq hs.total_eq
  have hsq : 2*physicalPrime N e.prime.val ≤ residual H.node := by
    rw [← hlevel]
    exact single_residual_square he.member
  have hp0 : 0 < physicalPrime N e.prime.val := by
    exact div_pos (Real.log_pos (by exact_mod_cast hp.1.1.one_lt))
      (parentWindow_logs hw).1
  have hgate : stepGate depth lo hi H (physicalPrime N e.prime.val) :=
    ⟨he.rank,he.physicalBox,hp0,hp.2.2.2.1,hsq,he.incomingCube,hf,hsel⟩
  have haccept : (childHistory plan N Q lo hi H old e).accepted=true :=
    (step_accepted_iff plan lo hi H _ _).mpr ⟨haccepted,hgate⟩
  have hg := admitted_step_gates plan lo hi H _ _ haccept
  refine ⟨haccept,hg.1,hg.2.1,?_⟩
  change residual H.node/2 ≤
    residual (appendOne H.node (physicalPrime N e.prime.val) (query Q old e))
  rw [residual_appendOne]
  linarith only [hsq]

/-- Real integer-domain membership produces all physical history tests.
The residual shrinks by at most a factor2 per singleton source edge. -/
theorem source_steps_sound {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi : ℝ) (H : History) (old : List ℕ)
    (es : List (IntegerStep N))
    (haccepted : H.accepted=true) (hf : fullGates H.node) (hsel : selectedGates H.node)
    (hs : IntegerState N Q H old) (hw : parentWindow N Q old chi)
    (hsource : SourceSteps plan N Q lo hi H old es) :
    (finishHistory plan N Q lo hi H old es).accepted=true ∧
    fullGates (finishHistory plan N Q lo hi H old es).node ∧
    selectedGates (finishHistory plan N Q lo hi H old es).node ∧
    IntegerState N Q (finishHistory plan N Q lo hi H old es) (finishWord old es) ∧
    parentWindow N Q (finishWord old es) chi ∧
    residual H.node/(2 : ℝ)^es.length ≤
      residual (finishHistory plan N Q lo hi H old es).node := by
  revert H old
  induction es with
  | nil =>
      intro H old haccepted hf hsel hs hw hsource
      exact ⟨haccepted,hf,hsel,hs,hw,by simp [finishHistory]⟩
  | cons e es ih =>
      intro H old haccepted hf hsel hs hw hsource
      have hg := step_admission haccepted hf hsel hs hw hsource.1
      have hstate := step_integer_state hs hw hsource.1
      obtain ⟨ha,hf',hsel',hs',hw',hr⟩ := ih
        (childHistory plan N Q lo hi H old e) (singleWord old e.prime.val)
        hg.1 hg.2.1 hg.2.2.1 hstate.1 hstate.2 hsource.2
      refine ⟨ha,hf',hsel',hs',hw',?_⟩
      calc
        residual H.node/(2 : ℝ)^(e::es).length =
            (residual H.node/2)/(2 : ℝ)^es.length := by
          simp only [List.length_cons,pow_succ]
          ring
        _ ≤ residual (childHistory plan N Q lo hi H old e).node /
            (2 : ℝ)^es.length :=
          div_le_div_of_nonneg_right hg.2.2.2 (by positivity)
        _ ≤ _ := hr

theorem encode_word (Q : ℝ) (old : List ℕ) (es : List (IntegerStep N)) :
    old ++ (encode Q old es).map Prod.fst = finishWord old es := by
  induction es generalizing old with
  | nil => simp [encode,finishWord]
  | cons e es ih =>
      simpa only [encode,finishWord,List.map_cons,singleWord,
        List.append_assoc,List.singleton_append] using ih (singleWord old e.prime.val)

theorem encode_history {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) (H : History) (old : List ℕ) (es : List (IntegerStep N)) :
    advance plan lo hi H
      ((encode Q old es).map (fun p => (physicalPrime N p.1,p.2))) =
      finishHistory plan N Q lo hi H old es := by
  induction es generalizing H old with
  | nil => rfl
  | cons e es ih =>
      simpa only [encode,List.map_cons,advance,List.foldl_cons,finishHistory,
        childHistory] using
          ih (childHistory plan N Q lo hi H old e) (singleWord old e.prime.val)

def input (Q : ℝ) (n : PhysicalNode) (old : List ℕ) (seedCap : ℝ)
    (E : ℕ → ℕ → Prop) (es : List (IntegerStep N)) : ParentInput :=
  ⟨n,old,seedCap,encode Q old es,E⟩

@[simp] theorem input_word (Q : ℝ) (n : PhysicalNode) (old : List ℕ) (seedCap : ℝ)
    (E : ℕ → ℕ → Prop) (es : List (IntegerStep N)) :
    oldWord (input Q n old seedCap E es) = finishWord old es :=
  encode_word Q old es

@[simp] theorem input_history {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) (n : PhysicalNode) (old : List ℕ) (seedCap : ℝ)
    (E : ℕ → ℕ → Prop) (es : List (IntegerStep N)) :
    parentHistory plan N lo hi (input Q n old seedCap E es) =
      finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es :=
  encode_history plan N Q lo hi _ old es

/-- Exactly the original recursively frozen child receiver, not a mask
chosen from scalar weights or from the exporter's output. -/
def sourceReceiver {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) : History → List ℕ → (ℕ → ℕ → Prop) →
      List (IntegerStep N) → ℕ → ℕ → Prop
  | _,old,E,[],_,ell => E old.prod ell
  | H,old,E,e::es,B,ell =>
      sourceReceiver plan N Q lo hi (childHistory plan N Q lo hi H old e)
        (singleWord old e.prime.val)
        (admittedChildPredicate E old.prod (childHistory plan N Q lo hi H old e))
        es B ell

/-- Admission is derived along the original integer path, so each
frozen receiver reduces to the original root E at its original root B. -/
theorem sourceReceiver_root {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi : ℝ) (H : History) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (es : List (IntegerStep N))
    (haccepted : H.accepted=true) (hf : fullGates H.node) (hsel : selectedGates H.node)
    (hs : IntegerState N Q H old) (hw : parentWindow N Q old chi)
    (hsource : SourceSteps plan N Q lo hi H old es) (B ell : ℕ) :
    sourceReceiver plan N Q lo hi H old E es B ell ↔ E old.prod ell := by
  revert H old E
  induction es with
  | nil => intro H old E haccepted hf hsel hs hw hsource; rfl
  | cons e es ih =>
      intro H old E haccepted hf hsel hs hw hsource
      have hg := step_admission haccepted hf hsel hs hw hsource.1
      have hstate := step_integer_state hs hw hsource.1
      have hrec := ih (childHistory plan N Q lo hi H old e)
        (singleWord old e.prime.val)
        (admittedChildPredicate E old.prod (childHistory plan N Q lo hi H old e))
        hg.1 hg.2.1 hg.2.2.1 hstate.1 hstate.2 hsource.2
      change sourceReceiver plan N Q lo hi _ _ _ es B ell ↔ _
      rw [hrec]
      simp only [admittedChildPredicate,hg.1,and_true]

/-- The source query attached to an original integer edge has exactly
its physical child cutoff. In particular its query is positive; alpha
and the cutoff argument are never reset to2. -/
private theorem single_child_cutoff {depth mesh : ℕ} {plan : CapPlan depth mesh}
    {N : ℕ} {Q chi lo hi : ℝ} {H : History} {old : List ℕ} {e : IntegerStep N}
    (hs : IntegerState N Q H old) (hw : parentWindow N Q old chi)
    (he : SourceEdge plan N Q lo hi H old e) :
    0 < (childHistory plan N Q lo hi H old e).node.argument ∧
    residual (childHistory plan N Q lo hi H old e).node /
        (childHistory plan N Q lo hi H old e).node.argument ≤
      (childHistory plan N Q lo hi H old e).node.ceiling := by
  let L := physicalLevel N Q old
  let u := relativePrime Q old e.prime.val
  let x := physicalPrime N e.prime.val
  have hlogs := parentWindow_logs hw
  have hL : 0 < L := hlogs.2.2
  have hx : 0 < x := by
    have hp := (mem_singleChildren.mp he.member).1.1
    exact div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) hlogs.1
  have hcoord := P2EnhancedW1RepeatedLabelClassification.physical_level_eq_parent_residual
    hw hs.primes hs.word_eq hs.total_eq
  have hLu : L*u=x := relativePrime_physical hw
  have hsq : 2*x ≤ L := single_residual_square he.member
  have hu : u < 1 := by nlinarith only [hL,hLu,hsq]
  have hone : 0 < 1-u := by linarith
  have hres : residual (childHistory plan N Q lo hi H old e).node = L*(1-u) := by
    change residual (appendOne H.node x (query Q old e)) = _
    rw [residual_appendOne,← hcoord]
    dsimp only [L] at *
    nlinarith only [hLu]
  have hbound := (single_cutoff_below_prime he.member).1
  change 0 < query Q old e ∧ residual _ / query Q old e ≤ x
  cases hr : e.rule with
  | buchstab upper target =>
      have harg : query Q old e = (L-x)/x := by
        simp only [query,hr]
        dsimp only [buchstabArgument,L,x,physicalLevel,physicalPrime]
        have hp := (mem_singleChildren.mp he.member).1.1
        have hlogp : Real.log (e.prime.val : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
        field_simp [hlogs.1.ne',hlogp]
        ring
      have hrespos : 0 < L-x := by linarith only [hL,hsq]
      refine ⟨by rw [harg]; exact div_pos hrespos hx,?_⟩
      rw [hres,harg]
      have hcut : L*(1-u)/((L-x)/x) = x := by
        field_simp [hx.ne',hrespos.ne']
        nlinarith only [hLu]
      simpa only [hcut] using (le_rfl : x ≤ x)
  | w1 i j =>
      have hA : 0 < W1Anchor j := by
        have hj := Nat.cast_nonneg (R := ℝ) j.val
        dsimp [W1Anchor]
        linarith
      have harg : query Q old e = W1Anchor j*(1-u) := by simp only [query,hr]; rfl
      refine ⟨by rw [harg]; exact mul_pos hA hone,?_⟩
      rw [hres,harg]
      have hcut : L*(1-u)/(W1Anchor j*(1-u)) = L/W1Anchor j := by
        field_simp [hA.ne',hone.ne']
        ring
      rw [hcut]
      simpa only [singleCutoff,hr] using hbound
  | w2 bank piece =>
      have hA : 0 < (originalW2At bank).s0 :=
        P5OriginalFeedbackDomains.W2_anchor_positive
          (P5OriginalActionMassBound.originalRepairedW2Bank_geometry _
            (P5OriginalActionMassBound.originalW2At_mem bank))
      have harg : query Q old e = (originalW2At bank).s0*(1-u) := by
        simp only [query,hr]; rfl
      refine ⟨by rw [harg]; exact mul_pos hA hone,?_⟩
      rw [hres,harg]
      have hcut : L*(1-u)/((originalW2At bank).s0*(1-u)) = L/(originalW2At bank).s0 := by
        field_simp [hA.ne',hone.ne']
        ring
      rw [hcut]
      simpa only [singleCutoff,hr] using hbound

theorem source_steps_cutoff_admitted {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi : ℝ) (H : History) (old : List ℕ)
    (es : List (IntegerStep N))
    (hs : IntegerState N Q H old) (hw : parentWindow N Q old chi)
    (hphysical : 0 < H.node.argument ∧ residual H.node/H.node.argument ≤ H.node.ceiling)
    (hsource : SourceSteps plan N Q lo hi H old es) :
    0 < (finishHistory plan N Q lo hi H old es).node.argument ∧
    residual (finishHistory plan N Q lo hi H old es).node /
        (finishHistory plan N Q lo hi H old es).node.argument ≤
      (finishHistory plan N Q lo hi H old es).node.ceiling := by
  revert H old
  induction es with
  | nil => intro H old hs hw hphysical hsource; exact hphysical
  | cons e es ih =>
      intro H old hs hw hphysical hsource
      have hstate := step_integer_state hs hw hsource.1
      exact ih _ _ hstate.1 hstate.2
        (single_child_cutoff hs hw hsource.1) hsource.2

private theorem source_steps_rank {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q lo hi : ℝ) (H : History) (old : List ℕ)
    (es : List (IntegerStep N)) (hroot : H.node.slots.length ≤ depth)
    (hsource : SourceSteps plan N Q lo hi H old es) :
    H.node.slots.length + es.length ≤ depth := by
  revert H old
  induction es with
  | nil => intro H old hroot hsource; simpa using hroot
  | cons e es ih =>
      intro H old hroot hsource
      have hchildRank : (childHistory plan N Q lo hi H old e).node.slots.length ≤ depth := by
        simpa only [childHistory,step,appendOne,List.length_append,List.length_singleton]
          using hsource.1.rank
      have h := ih _ _ hchildRank hsource.2
      simpa only [childHistory,step,appendOne,List.length_append,List.length_singleton,
        List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

def sourceHorizon : ℕ := 440

/-- ParentTests are SUPPLIED from the actual singleton-source prefix,
not assumed. The literal selected W1 row supplies its own target gate. -/
theorem actual_source_parent_tests {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi gamma0 : ℝ) (n : PhysicalNode) (old : List ℕ)
    (seedCap : ℝ) (E : ℕ → ℕ → Prop) (es : List (IntegerStep N))
    (g : Fin 430) (cell : Fin 200) (ij : Fin 7 × Fin 10)
    (hdepth : depth ≤ sourceHorizon) (hgamma : 0 < gamma0)
    (hroot : rootGate depth lo hi n)
    (hs : IntegerState N Q (start plan lo hi seedCap n) old)
    (hw : parentWindow N Q old chi)
    (hphysical : 0 < n.argument ∧ residual n/n.argument ≤ n.ceiling)
    (hres : gamma0 ≤ residual n)
    (hsource : SourceSteps plan N Q lo hi (start plan lo hi seedCap n) old es)
    (hselected : selectedW1 g cell = some ij)
    (hcell : (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).node.argument
      ∈ queryCell cell) :
    ParentTests plan N (finishWord old es).prod Q chi
      (gamma0/(2 : ℝ)^sourceHorizon) lo hi (input Q n old seedCap E es) ij := by
  have ha0 : (start plan lo hi seedCap n).accepted=true := by
    change decide (rootGate depth lo hi n) = true
    exact decide_eq_true hroot
  have hsound := source_steps_sound plan N Q chi lo hi _ old es ha0
    hroot.2.2.1 hroot.2.2.2 hs hw hsource
  obtain ⟨ha,hf,hsel,hs',hw',hres'⟩ := hsound
  have hlen := source_steps_rank plan N Q lo hi _ old es hroot.1 hsource
  have hlength : es.length ≤ sourceHorizon := by omega
  have hpowers : (2 : ℝ)^es.length ≤ (2 : ℝ)^sourceHorizon :=
    pow_le_pow_right₀ (by norm_num) hlength
  have hfloor : gamma0/(2 : ℝ)^sourceHorizon ≤
      residual (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).node := by
    calc
      gamma0/(2 : ℝ)^sourceHorizon ≤ gamma0/(2 : ℝ)^es.length :=
        div_le_div_of_nonneg_left hgamma.le (by positivity) hpowers
      _ ≤ residual n/(2 : ℝ)^es.length := div_le_div_of_nonneg_right hres (by positivity)
      _ ≤ _ := hres'
  have hL : 0 ≤ residual
      (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).node := by
    exact le_trans (by positivity) hfloor
  have hphysical' := source_steps_cutoff_admitted plan N Q chi lo hi _ old es
    hs hw hphysical hsource
  have htarget := selectedW1_actual_argument_target hselected hcell
  have hceiling := selectedW1_actual_ceiling hselected hcell hL hphysical'.2
  refine { accepted := ?_, product := ?_, primes := ?_, word_eq := ?_,
    total_eq := ?_, window := ?_, residualLower := ?_, target := ?_, ceiling := ?_ }
  · simpa only [input_history] using ha
  · simp only [input_word]
  · simpa only [input_word] using hs'.primes
  · simpa only [input_history,input_word] using hs'.word_eq
  · simpa only [input_history] using hs'.total_eq
  · simpa only [input_word] using hw'
  · simpa only [input_history] using hfloor
  · simpa only [input_history] using htarget
  · simpa only [input_history] using hceiling

/-- The recursively frozen ORIGINAL receiver equals the exporter's mask
as a function, with the old root multiplier retained on both sides. -/
theorem actual_source_mask_eq {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi : ℝ) (n : PhysicalNode) (old : List ℕ)
    (seedCap : ℝ) (E : ℕ → ℕ → Prop) (es : List (IntegerStep N))
    (hroot : rootGate depth lo hi n)
    (hs : IntegerState N Q (start plan lo hi seedCap n) old)
    (hw : parentWindow N Q old chi)
    (hsource : SourceSteps plan N Q lo hi (start plan lo hi seedCap n) old es) :
    sourceReceiver plan N Q lo hi (start plan lo hi seedCap n) old E es =
      computedFrozenMask plan N lo hi (input Q n old seedCap E es) := by
  have ha0 : (start plan lo hi seedCap n).accepted=true := by
    change decide (rootGate depth lo hi n) = true
    exact decide_eq_true hroot
  have ha := (source_steps_sound plan N Q chi lo hi _ old es ha0
    hroot.2.2.1 hroot.2.2.2 hs hw hsource).1
  have hm := sourceReceiver_root plan N Q chi lo hi _ old E es ha0
    hroot.2.2.1 hroot.2.2.2 hs hw hsource
  funext B ell
  apply propext
  rw [hm]
  simp only [computedFrozenMask,input_history,input,ha,and_true]

private theorem mem_exportSlots_reverse {depth mesh : ℕ}
    {plan : CapPlan depth mesh} {N B : ℕ} {Q chi gamma lo hi : ℝ}
    {a : ParentInput} {ss : List Slot} {s : Slot} {o : W1Occurrence}
    (hs : s ∈ ss) (ho : o ∈ exportSlot plan N B Q chi gamma lo hi a s) :
    o ∈ exportSlots plan N B Q chi gamma lo hi a ss := by
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
      rcases List.mem_cons.mp hs with rfl | hs
      · exact List.mem_append.mpr (Or.inl ho)
      · exact List.mem_append.mpr (Or.inr (ih hs))

/-- A real selected W1 source term forces an occurrence into the export.
All physical filter obligations have been proved from source-domain data.
The same receiver and the same strict ordered triple survive unchanged. -/
theorem actual_selected_triple_covered {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi gamma0 : ℝ) (n : PhysicalNode) (old : List ℕ)
    (seedCap : ℝ) (E : ℕ → ℕ → Prop) (es : List (IntegerStep N))
    (g : Fin 430) (cell : Fin 200) (ij : Fin 7 × Fin 10) (ell : ℕ) (t : TripleLabel)
    (hdepth : depth ≤ sourceHorizon) (hgamma : 0 < gamma0)
    (hroot : rootGate depth lo hi n)
    (hs : IntegerState N Q (start plan lo hi seedCap n) old)
    (hw : parentWindow N Q old chi)
    (hphysical : 0 < n.argument ∧ residual n/n.argument ≤ n.ceiling)
    (hres : gamma0 ≤ residual n)
    (hsource : SourceSteps plan N Q lo hi (start plan lo hi seedCap n) old es)
    (hselected : selectedW1 g cell = some ij)
    (hcell : (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).node.argument
      ∈ queryCell cell)
    (ht : t ∈ positiveTripleWords N ell Q (finishWord old es) ij.1 ij.2
      (sourceReceiver plan N Q lo hi (start plan lo hi seedCap n) old E es)) :
    ∃ o ∈ exportBank plan N (finishWord old es).prod Q chi
        (gamma0/(2 : ℝ)^sourceHorizon) lo hi [input Q n old seedCap E es],
      o.old = finishWord old es ∧ o.target = ij.1 ∧ o.anchor = ij.2 ∧
      o.frozenMask = sourceReceiver plan N Q lo hi
        (start plan lo hi seedCap n) old E es ∧
      t ∈ positiveTripleWords N ell Q o.old o.target o.anchor o.frozenMask := by
  let a := input Q n old seedCap E es
  let o : W1Occurrence :=
    ⟨finishWord old es,ij.1,ij.2,computedFrozenMask plan N lo hi a⟩
  have htests := actual_source_parent_tests plan N Q chi lo hi gamma0 n old seedCap E es
    g cell ij hdepth hgamma hroot hs hw hphysical hres hsource hselected hcell
  obtain ⟨s,hsgen,hscell⟩ := slots_cover g cell
  have hslot : o ∈ exportSlot plan N (finishWord old es).prod Q chi
      (gamma0/(2 : ℝ)^sourceHorizon) lo hi a s := by
    have hsel : selectedW1 (slotGeneration s) (slotCell s) = some ij := by
      simpa only [hsgen,hscell] using hselected
    have hguard : ParentTests plan N (finishWord old es).prod Q chi
        (gamma0/(2 : ℝ)^sourceHorizon) lo hi a ij ∧
        (parentHistory plan N lo hi a).node.argument ∈ queryCell (slotCell s) := by
      refine ⟨htests,?_⟩
      simpa only [a,input_history,hscell] using hcell
    simp only [exportSlot,hsel,if_pos hguard,List.mem_singleton]
    simp only [o,a,input_word]
  have hparent : o ∈ exportParent plan N (finishWord old es).prod Q chi
      (gamma0/(2 : ℝ)^sourceHorizon) lo hi a :=
    mem_exportSlots_reverse (by simp : s ∈ List.finRange (430*200)) hslot
  refine ⟨o,?_,rfl,rfl,rfl,?_,?_⟩
  · simpa only [exportBank,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hparent
  · exact (actual_source_mask_eq plan N Q chi lo hi n old seedCap E es
      hroot hs hw hsource).symm
  · have hmask := actual_source_mask_eq plan N Q chi lo hi n old seedCap E es
      hroot hs hw hsource
    simpa only [o,a,← hmask] using ht

/-- The actual repeated-label source mass is exactly the exported
occurrence mass at outer weight1, not merely a comparison of masks or
real measure-zero sets. All integer receiver and triple multiplicities
remain in the same repeatedTripleMass definition. -/
theorem actual_source_occurrence_mass {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi : ℝ) (n : PhysicalNode) (old : List ℕ)
    (seedCap : ℝ) (E : ℕ → ℕ → Prop) (es : List (IntegerStep N))
    (ij : Fin 7 × Fin 10)
    (hroot : rootGate depth lo hi n)
    (hs : IntegerState N Q (start plan lo hi seedCap n) old)
    (hw : parentWindow N Q old chi)
    (hsource : SourceSteps plan N Q lo hi (start plan lo hi seedCap n) old es) :
    P2EnhancedW1FiniteActionBankPayment.occurrenceMass N Q (fun _ _ => True)
      ⟨finishWord old es,ij.1,ij.2,
        computedFrozenMask plan N lo hi (input Q n old seedCap E es)⟩ =
    P2EnhancedW1OrderedTripleGlobalPayment.repeatedTripleMass N Q
      (finishWord old es) ij.1 ij.2
      (sourceReceiver plan N Q lo hi (start plan lo hi seedCap n) old E es) := by
  have hmask := actual_source_mask_eq plan N Q chi lo hi n old seedCap E es
    hroot hs hw hsource
  simp only [P2EnhancedW1FiniteActionBankPayment.occurrenceMass,true_and,← hmask]


end
end ImbalancedChen.P2Selected430ActualW1SourceCoverage
