import ImbalancedChen.P2PhysicalIncomingPrefixCells
import ImbalancedChen.FirstExitPresieveProjection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Integer-prime histories are mapped to the original chronological physical
word before the finite cap plan is evaluated. The own-lower audit tests
the initial square and EVEN full-rank cubes. Odd ranks after the first
have no new cube test. In particular rank5 is not tested with S4+3t5.
Only ranks3,4,5 may freeze a new branch cap, and the new choice is read
AFTER the current test against the incoming frozen cap.

This is deliberately separate from the stricter all-rank geometric
stepGate constructor. It gives the actual computed integer retainEven
predicate, including the complete earlier test/cap trace. Proving that a
particular finite CapPlan is the original certified branch plan, with its
selected-subset gates, margins and cap monotonicity, remains OPEN.
-/

namespace ImbalancedChen.P2LowerCapPlanIntegerRetention

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells

def coordinate (N p : ℕ) : ℝ := Real.log (p:ℝ)/Real.log N

/-- firstExit stores its newest selected prime at the head; physical
chronology therefore reads the reverse list. -/
def physicalWord (N : ℕ) (history : List ℕ) : List ℝ :=
  history.reverse.map (coordinate N)

@[simp] theorem physicalWord_cons (N p : ℕ) (history : List ℕ) :
    physicalWord N (p::history)=physicalWord N history++[coordinate N p] := by
  simp only [physicalWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]

theorem coordinate_power {N p : ℕ} (hN : 1<(N:ℝ)) (hp : 0<p) :
    (N:ℝ)^(coordinate N p)=(p:ℝ) := by
  unfold coordinate
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hN),
    mul_div_cancel₀ _ (Real.log_pos hN).ne',Real.exp_log (Nat.cast_pos.mpr hp)]

theorem physicalWord_power {N : ℕ} (hN : 1<(N:ℝ)) (history : List ℕ)
    (hp : ∀p∈history,0<p) :
    (N:ℝ)^((physicalWord N history).sum)=(history.prod:ℝ) := by
  revert hp
  induction history with
  | nil => intro hp; simp [physicalWord]
  | cons p ps ih =>
      intro hp
      rw [physicalWord_cons,List.sum_append]
      simp only [List.sum_cons,List.sum_nil,add_zero]
      rw [Real.rpow_add (zero_lt_one.trans hN),
        ih (fun q hq=>hp q (List.mem_cons_of_mem p hq)),
        coordinate_power hN (hp p (List.mem_cons_self p ps))]
      simp only [List.prod_cons,Nat.cast_mul]
      ring

/-- Literal natural multiplier and selected-prime cube, with the actual
product retained even when a selected factor repeats elsewhere. -/
theorem cube_test_integer_iff {N p : ℕ} (hN : 1<(N:ℝ)) (hp : 0<p)
    (history : List ℕ) (hpos : ∀q∈history,0<q) (cap : ℝ) :
    (physicalWord N history).sum+3*coordinate N p<cap ↔
      (history.prod:ℝ)*(p:ℝ)^3<(N:ℝ)^cap := by
  have hpow : (N:ℝ)^((physicalWord N history).sum+3*coordinate N p)=
      (history.prod:ℝ)*(p:ℝ)^3 := by
    rw [Real.rpow_add (zero_lt_one.trans hN),physicalWord_power hN history hpos,
      mul_comm (3:ℝ) (coordinate N p),Real.rpow_mul (zero_lt_one.trans hN).le,
      coordinate_power hN hp]
    norm_num
  rw [←hpow,Real.rpow_lt_rpow_left_iff hN]

def marked (word : List ℝ) : List MarkedExponent := word.map (fun x=>(x,false))

structure Frame where
  prefix : List ℝ
  incomingCap : ℝ
  tested : Prop
  choice : CapChoice
  frozenCap : ℝ

structure Trace where
  word : List ℝ
  cap : ℝ
  frames : List Frame
  accepted : Bool

def root (seedCap : ℝ) : Trace := ⟨[],seedCap,[],true⟩

/-- Literal own-lower initial square / even-cube / odd-bypass tests. -/
def admission (H : Trace) (x : ℝ) : Prop :=
  if H.word.length=0 then 2*x<H.cap
  else if (H.word.length+1)%2=0 then H.word.sum+3*x<H.cap else True

def planChoice {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (word : List ℝ) : CapChoice :=
  if word.length=3 ∨ word.length=4 ∨ word.length=5 then
    incomingChoice P a b word.length (marked word)
  else .inherit 2

def step {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : Trace) (x : ℝ) : Trace :=
  let word:=H.word++[x]
  let choice:=planChoice P a b word
  let frozen:=choice.freeze H.cap
  { word:=word
    cap:=frozen
    frames:=H.frames++[⟨word,H.cap,admission H x,choice,frozen⟩]
    accepted:=H.accepted && decide (admission H x) }

def run {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : Trace) (word : List ℝ) : Trace := word.foldl (step P a b) H

def integerTrace {depth m : ℕ} (P : CapPlan depth m) (a b seedCap : ℝ)
    (N : ℕ) (history : List ℕ) : Trace :=
  run P a b (root seedCap) (physicalWord N history)

def retainEven {depth m : ℕ} (P : CapPlan depth m) (a b seedCap : ℝ)
    (N : ℕ) (history : List ℕ) : Bool :=
  (integerTrace P a b seedCap N history).accepted

@[simp] theorem step_accepted_iff {depth m : ℕ} (P : CapPlan depth m)
    (a b : ℝ) (H : Trace) (x : ℝ) :
    (step P a b H x).accepted=true ↔ H.accepted=true ∧ admission H x := by
  simp only [step,Bool.and_eq_true,decide_eq_true_eq]

theorem run_append {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : Trace) (xs ys : List ℝ) : run P a b H (xs++ys)=run P a b (run P a b H xs) ys :=
  List.foldl_append

theorem run_word {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : Trace) (xs : List ℝ) : (run P a b H xs).word=H.word++xs := by
  induction xs generalizing H with
  | nil => simp only [run,List.foldl_nil,List.append_nil]
  | cons x xs ih =>
      simpa only [run,List.foldl_cons,step,List.singleton_append,List.append_assoc] using
        ih (step P a b H x)

@[simp] theorem integerTrace_word {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N : ℕ) (history : List ℕ) :
    (integerTrace P a b seedCap N history).word=physicalWord N history := by
  exact run_word P a b (root seedCap) (physicalWord N history)

theorem integerTrace_cons {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N p : ℕ) (history : List ℕ) :
    integerTrace P a b seedCap N (p::history)=
      step P a b (integerTrace P a b seedCap N history) (coordinate N p) := by
  unfold integerTrace
  rw [physicalWord_cons,run_append]
  rfl

/-- The raw integer predicate is computed from the same incoming trace;
its new cap cannot replace the cap used in the current cube test. -/
theorem retainEven_cons_iff {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N p : ℕ) (history : List ℕ) :
    retainEven P a b seedCap N (p::history)=true ↔
      retainEven P a b seedCap N history=true ∧
        admission (integerTrace P a b seedCap N history) (coordinate N p) := by
  unfold retainEven
  rw [integerTrace_cons,step_accepted_iff]

theorem even_rank_cube {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N p : ℕ) (history : List ℕ)
    (hpos : 0<history.length) (heven : (history.length+1)%2=0) :
    admission (integerTrace P a b seedCap N history) (coordinate N p) ↔
      (physicalWord N history).sum+3*coordinate N p<
        (integerTrace P a b seedCap N history).cap := by
  have hlen : (physicalWord N history).length=history.length := by simp [physicalWord]
  simp only [admission,integerTrace_word,hlen,show history.length≠0 by omega,
    if_false,heven,if_true]

/-- Positive incoming history at an odd full rank receives no extra own
cube exclusion. The wrapper also retains ALL odd first-exit tests. -/
theorem odd_rank_bypass {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N p : ℕ) (history : List ℕ)
    (hpos : 0<history.length) (hodd : (history.length+1)%2≠0) :
    retainEven P a b seedCap N (p::history)=true ↔
      retainEven P a b seedCap N history=true := by
  rw [retainEven_cons_iff]
  have hlen : (physicalWord N history).length=history.length := by simp [physicalWord]
  simp only [admission,integerTrace_word,hlen,show history.length≠0 by omega,
    if_false,hodd,and_true]

theorem raw_policy_odd_retained {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (N : ℕ) (history : List ℕ) :
    evenFirstExitPolicy (retainEven P a b seedCap N) false history=true := rfl

theorem no_new_cap_outside_345 {depth m : ℕ} (P : CapPlan depth m)
    (a b : ℝ) (H : Trace) (x : ℝ)
    (h : ¬((H.word++[x]).length=3 ∨ (H.word++[x]).length=4 ∨ (H.word++[x]).length=5)) :
    (step P a b H x).cap=H.cap := by
  simp only [step,planChoice,if_neg h,CapChoice.freeze]

/-- Later primes append records; every original incoming cap and its
tested proposition remains literally present at the same prefix rank. -/
theorem run_frames_extend {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : Trace) (xs : List ℝ) : ∃extra,(run P a b H xs).frames=H.frames++extra := by
  induction xs generalizing H with
  | nil => exact ⟨[],by simp only [run,List.foldl_nil,List.append_nil]⟩
  | cons x xs ih =>
      obtain ⟨extra,he⟩ := ih (step P a b H x)
      refine ⟨[⟨H.word++[x],H.cap,admission H x,planChoice P a b (H.word++[x]),
        (planChoice P a b (H.word++[x])).freeze H.cap⟩]++extra,?_⟩
      simpa only [run,List.foldl_cons,step,List.append_assoc] using he

end
end ImbalancedChen.P2LowerCapPlanIntegerRetention
