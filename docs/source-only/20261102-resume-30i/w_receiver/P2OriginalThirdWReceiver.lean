import ImbalancedChen.P2OriginalFreshWArithmetic
import ImbalancedChen.P2OriginalCanonicalTentFrozenChambers

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A concrete original W-third subfamily, with an independent endpoint source
and a primitive rescue screen. This does NOT identify its policy with the
entire adopted W/tent bank. The literal original pair root is untouched.
Only the actual third arrival can improve it; every later frame inherits.
-/
namespace ImbalancedChen.P2OriginalThirdWReceiver
noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)
open P2OriginalFreshWArithmetic P2EnhancedLowerPhysicalNode
open P2OriginalPairRootRoughProducer

def endpoint (R : PairRange) {mesh : ℕ} (code : Code mesh) (i : Fin 5) : ℝ :=
  qHi R mesh (code i).1

def eligible (R : PairRange) {mesh : ℕ} (buffer : ℚ) (seed : ℝ)
    (code : Code mesh) : Prop :=
  Geometry (endpoint R code 0) (endpoint R code 1) (endpoint R code 2) buffer ∧
    seed<physical (endpoint R code 2) buffer

def choice (R : PairRange) {mesh : ℕ} (buffer : ℚ) (seed : ℝ)
    (code : Code mesh) : CapChoice :=
  let pre := prefixCode 3 code
  if eligible R buffer seed pre then
    .fresh (physical (endpoint R pre 2) buffer) 2 else .inherit 2

def plan (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ) : CapPlan 5 mesh :=
  ⟨fun rank code => if rank.val=3 then choice R buffer seed code else .inherit 2⟩

def firstCode (R : PairRange) (mesh : ℕ) (t u z : ℝ) : Code mesh :=
  codeAt R mesh 3 [t,u,z]

/-- The actual W source, evaluated on the frozen upper endpoints. The
source has an empty mask; its third input is the real first rough slot. -/
theorem source_identity (R : PairRange) {mesh : ℕ} (code : Code mesh) :
    (SourceForm.wSlot 2).affine.eval (endpoint R code)=value (endpoint R code 2) ∧
      (SourceForm.wSlot 2).supportMask=∅ := by
  constructor
  · norm_num [SourceForm.affine,P2OriginalLowerAffineTieSelector.AffineBranch.eval,
      value,Fin.sum_univ_succ]
  · rfl

theorem choice_fresh (R : PairRange) {mesh : ℕ} (buffer : ℚ) (seed : ℝ)
    (code : Code mesh) (q argument : ℝ)
    (hc : choice R buffer seed code=.fresh q argument) :
    eligible R buffer seed (prefixCode 3 code) ∧
      q=physical (endpoint R (prefixCode 3 code) 2) buffer ∧ argument=2 := by
  unfold choice at hc
  split_ifs at hc with he
  · injection hc with hq ha
    exact ⟨he,hq.symm,ha.symm⟩
  · cases hc

theorem choice_inherit_iff (R : PairRange) {mesh : ℕ} (buffer : ℚ) (seed : ℝ)
    (code : Code mesh) :
    choice R buffer seed code=.inherit 2 ↔ ¬eligible R buffer seed (prefixCode 3 code) := by
  simp [choice]

theorem source_geometry {R : PairRange} {mesh : ℕ} {buffer : ℚ} {seed : ℝ}
    {code : Code mesh} (he : eligible R buffer seed code) {t u : ℝ}
    (ht : t≤endpoint R code 0) (hu : u≤endpoint R code 1) :
    Geometry t u (endpoint R code 2) buffer := by
  rcases he.1 with ⟨hb,hbhi,hz,hzhi,htop,utop,hgap⟩
  exact ⟨hb,hbhi,hz,hzhi,ht.trans htop,hu.trans utop,by linarith⟩

/-- A finite source whose test succeeds receives its full and empty-mask
complement squares and its arithmetic initialization geometry as outputs. -/
theorem received_source (R : PairRange) {mesh : ℕ} (buffer : ℚ) (seed : ℝ)
    (code : Code mesh) (q argument : ℝ)
    (hc : choice R buffer seed code=.fresh q argument) :
    let pre := prefixCode 3 code
    let e := endpoint R pre
    let slots := [unselected (e 0),unselected (e 1),unselected (e 2)]
    (SourceForm.wSlot 2).affine.eval e=q+2*(buffer:ℝ) ∧
      (SourceForm.wSlot 2).supportMask=∅ ∧ seed<q ∧
      SquareGates q 0 (slots.map Slot.exponent) ∧
      SquareGates q (selectedWord slots).sum (remainingWord slots) ∧
      Geometry (e 0) (e 1) (e 2) buffer := by
  obtain ⟨he,hq,ha⟩ := choice_fresh R buffer seed code q argument hc
  dsimp only
  rw [hq]
  have hs := source_identity R (prefixCode 3 code)
  refine ⟨by rw [hs.1]; dsimp [physical]; ring,hs.2,he.2,?_,?_,he.1⟩
  · simpa [unselected] using first_three_squares he.1
  · simpa [unselected,selectedWord,remainingWord] using first_three_squares he.1

theorem firstCode_prefix (R : PairRange) (mesh : ℕ) (t u z : ℝ) :
    prefixCode 3 (firstCode R mesh t u z)=firstCode R mesh t u z := by
  funext i
  fin_cases i <;> simp [firstCode,codeAt,incomingCode,physicalCode,marked,prefixCode,exponentCode]

/-- Actual coordinates, not an assumed abstract endpoint association. -/
theorem firstCode_upper (R : PairRange) (mesh : ℕ) (t u z : ℝ)
    (ht : t∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ))
    (hu : u∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ))
    (hz : z∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ)) :
    t≤endpoint R (firstCode R mesh t u z) 0 ∧
      u≤endpoint R (firstCode R mesh t u z) 1 ∧
      z≤endpoint R (firstCode R mesh t u z) 2 := by
  let x : Fin 5 → ℝ := ![t,u,z,ceiling,ceiling]
  have hD : (R.epsilon:ℝ)≤(ceiling:ℝ) := by
    exact_mod_cast (R.epsilon_lt_a.le.trans (by norm_num [ceiling] : (417:ℚ)/5000≤ceiling))
  have hx : ∀ i, x i∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) := by
    intro i; fin_cases i
    · exact ht
    · exact hu
    · exact hz
    · exact ⟨hD,le_refl _⟩
    · exact ⟨hD,le_refl _⟩
  have hb := P2OriginalCanonicalTentFrozenChambers.actualCode_point_in_box R mesh 3 x hx
  refine ⟨?_,?_,?_⟩
  all_goals
    first
    | simpa [P2OriginalCanonicalTentFrozenChambers.actualCode,
        P2OriginalCanonicalTentFrozenChambers.actualPoint,box,endpoint,firstCode,
        codeAt,incomingCode,physicalCode,marked,x] using (hb 0).2
    | simpa [P2OriginalCanonicalTentFrozenChambers.actualCode,
        P2OriginalCanonicalTentFrozenChambers.actualPoint,box,endpoint,firstCode,
        codeAt,incomingCode,physicalCode,marked,x] using (hb 1).2
    | simpa [P2OriginalCanonicalTentFrozenChambers.actualCode,
        P2OriginalCanonicalTentFrozenChambers.actualPoint,box,endpoint,firstCode,
        codeAt,incomingCode,physicalCode,marked,x] using (hb 2).2

theorem first_step (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed t u z : ℝ) :
    (step (plan R mesh buffer seed) R.epsilon ceiling ⟨[t,u],seed,[],true⟩ z).cap=
      (choice R buffer seed (firstCode R mesh t u z)).freeze seed := by
  simp [step,planChoice,incomingChoice,plan,firstCode,codeAt]

/-- The frozen source is below the independent original W at the REAL
third prime. Source equality is not replaced by candidate/adopted equality. -/
theorem original_point_source (R : PairRange) (mesh : ℕ) (t u z : ℝ)
    (ht : t∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ))
    (hu : u∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ))
    (hz : z∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ)) :
    (SourceForm.wSlot 2).affine.eval (![t,u,z,0,0] : Fin 5 → ℝ)=VariableEnvelope.B z ∧
      value (endpoint R (firstCode R mesh t u z) 2)≤VariableEnvelope.B z := by
  have hupper := (firstCode_upper R mesh t u z ht hu hz).2.2
  constructor
  · norm_num [SourceForm.affine,P2OriginalLowerAffineTieSelector.AffineBranch.eval,
      VariableEnvelope.B,VariableEnvelope.cap,Fin.sum_univ_succ]
    <;> ring
  · dsimp [value,VariableEnvelope.B,VariableEnvelope.cap]
    linarith

theorem after_third_inherits (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ)
    (word : List ℝ) (hw : 4≤word.length) :
    planChoice (plan R mesh buffer seed) R.epsilon ceiling word=.inherit 2 := by
  unfold planChoice
  split_ifs with h
  · rcases h with h3 | h4 | h5
    · omega
    · simp [incomingChoice,plan,h4]
    · simp [incomingChoice,plan,h5]
  · rfl

theorem step_cap (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ)
    (H : Trace) (hH : 3≤H.word.length) (x : ℝ) :
    (step (plan R mesh buffer seed) R.epsilon ceiling H x).cap=H.cap := by
  change (planChoice (plan R mesh buffer seed) R.epsilon ceiling (H.word++[x])).freeze H.cap=H.cap
  rw [after_third_inherits R mesh buffer seed _ (by simp only [List.length_append,List.length_singleton]; omega)]
  rfl

theorem run_cap (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ)
    (H : Trace) (hH : 3≤H.word.length) (xs : List ℝ) :
    (run (plan R mesh buffer seed) R.epsilon ceiling H xs).cap=H.cap := by
  induction xs generalizing H with
  | nil => rfl
  | cons x xs ih =>
      change (run (plan R mesh buffer seed) R.epsilon ceiling
        (step (plan R mesh buffer seed) R.epsilon ceiling H x) xs).cap=H.cap
      rw [ih _ (by simp only [step,List.length_append,List.length_singleton]; omega),
        step_cap R mesh buffer seed H hH x]

/-- Every later even cube and odd carry uses the actual frozen third cap.
No final support estimate or inherited-history premise is supplied. -/
private theorem suffix_squares (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ)
    (xs : List ℝ) : ∀ (H : Trace) (top : ℝ), 3≤H.word.length →
      (H.word.length%2=0 → H.word.sum+2*top<H.cap) →
      (H.word.length%2=0 → ∀ x∈xs, x≤top) →
      xs.Pairwise (· ≥ ·) → (∀ x∈xs, 0≤x) →
      (run (plan R mesh buffer seed) R.epsilon ceiling H xs).accepted=true →
      SquareGates H.cap H.word.sum xs := by
  let P := plan R mesh buffer seed
  induction xs with
  | nil => intros; trivial
  | cons x xs ih =>
      intro H top hlen hcarry hceil hsort hnonneg haccept
      have htailacc : (run P R.epsilon ceiling (step P R.epsilon ceiling H x) xs).accepted=true := haccept
      have hstepacc := run_accepted_incoming P R.epsilon ceiling _ _ htailacc
      have hadm := ((step_accepted_iff P R.epsilon ceiling H x).mp hstepacc).2
      have hcap := step_cap R mesh buffer seed H hlen x
      have hx0 := hnonneg x (List.mem_cons_self x xs)
      have hcube (he : (H.word.length+1)%2=0) : H.word.sum+3*x<H.cap := by
        simpa only [admission,if_neg (show H.word.length≠0 by omega),if_pos he] using hadm
      have hsq : H.word.sum+2*x≤H.cap := by
        by_cases he : (H.word.length+1)%2=0
        · linarith [hcube he]
        · have hp : H.word.length%2=0 := by omega
          have hc := hcarry hp
          have hx := hceil hp x (List.mem_cons_self x xs)
          linarith
      have hlen' : 3≤(step P R.epsilon ceiling H x).word.length := by
        simp only [step,List.length_append,List.length_singleton]; omega
      have hc' : (step P R.epsilon ceiling H x).word.length%2=0 →
          (step P R.epsilon ceiling H x).word.sum+2*x<(step P R.epsilon ceiling H x).cap := by
        intro he
        have he' : (H.word.length+1)%2=0 := by simpa [step] using he
        have hh := hcube he'
        rw [hcap]
        simpa only [step,List.sum_append,List.sum_cons,List.sum_nil,add_zero] using
          (show H.word.sum+x+2*x<H.cap by linarith)
      have ht := ih (step P R.epsilon ceiling H x) x hlen' hc'
        (fun _ y hy => (List.pairwise_cons.mp hsort).1 y hy)
        (List.pairwise_cons.mp hsort).2
        (fun y hy => hnonneg y (List.mem_cons_of_mem x hy)) htailacc
      rw [hcap] at ht
      exact ⟨hsq,by simpa only [step,List.sum_append,List.sum_cons,List.sum_nil,add_zero] using ht⟩

theorem accepted_third_continuation (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ)
    (H : Trace) (hH : H.word.length=3) (xs : List ℝ)
    (hfull : SquareGates H.cap 0 H.word) (hsort : xs.Pairwise (· ≥ ·))
    (hnonneg : ∀ x∈xs, 0≤x)
    (haccept : (run (plan R mesh buffer seed) R.epsilon ceiling H xs).accepted=true) :
    SquareGates H.cap 0 (run (plan R mesh buffer seed) R.epsilon ceiling H xs).word := by
  rw [run_word,P2EnhancedLowerPhysicalNode.squareGates_append_iff]
  refine ⟨hfull,?_⟩
  simpa only [zero_add] using suffix_squares R mesh buffer seed xs H 0 (by omega)
    (by intro he; omega) (by intro he; omega) hsort hnonneg haccept

end
end ImbalancedChen.P2OriginalThirdWReceiver
