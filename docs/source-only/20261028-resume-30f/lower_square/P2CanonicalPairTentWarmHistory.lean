import ImbalancedChen.P2OriginalCanonicalPairTentBank
import ImbalancedChen.P2OriginalSelectedPairNativeData

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The canonical finite TENT SUBBANK is connected to its computed warm
history. The rational comparison floor remains distinct from the real
original L5/L6 root seed. Source selection, its own mask and the actual
parent fresh check are recovered from the computed choice, never supplied
as an arithmetic licence. No W/adopted full-bank identity is claimed.
-/
namespace ImbalancedChen.P2CanonicalPairTentWarmHistory
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)
open P2OriginalFiniteTentBankSelectorMargins (tentMasks)

/-- Concrete canonical tent source constructor, with the actual incoming
    seed passed separately. The fixed rational comparison floor only ranks
    source rows; it does not replace the original physical root cap. -/
def warmPlan (R : PairRange) (mesh : ℕ) (buffer comparisonFloor : ℚ)
    (seed : ℝ) : CapPlan 5 mesh :=
  pairPlan R (P2OriginalCanonicalPairTentBank.bank R mesh buffer comparisonFloor) buffer seed

private theorem select_prefix (R : PairRange) {mesh : ℕ}
    (buffer floor : ℚ) (rank : Fin 6) (code : Code mesh) :
    select R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer rank
      (prefixCode rank.val code) =
    select R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer rank code := by
  simp only [select,prefixCode_nested rank.val rank.val (le_refl _)]

/-- Exhaustive computed fresh/inherit classification, for the CONCRETE
    original-mask tent bank. Every fresh source and primitive arrival test
    is an output. Failed selection/check inherits the actual parent exactly. -/
theorem checked_choice_cases (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (rank : Fin 6) (parent : ℝ) (code : Code mesh) :
    let B := P2OriginalCanonicalPairTentBank.bank R mesh buffer floor
    (checkedChoice R B buffer rank parent code = .inherit 2 ∧
      checkedCap R B buffer rank parent code = parent ∧
      (select R B buffer rank code = none ∨
        ∃ b, select R B buffer rank code = some b ∧
          ¬ freshCheck R rank (prefixCode rank.val code) buffer parent b)) ∨
    ∃ b mask, mask ∈ tentMasks rank ∧
      select R B buffer rank code = some b ∧
      P2OriginalCanonicalPairTentBank.lowerSide R (prefixCode rank.val code) mask = some b ∧
      sourceCheck R rank (prefixCode rank.val code) buffer b ∧
      b.form.supportMask = mask ∧
      (b.form = .tentLeft mask ∨ b.form = .tentRight mask) ∧
      freshCheck R rank (prefixCode rank.val code) buffer parent b ∧
      checkedChoice R B buffer rank parent code =
        .fresh (rowCap R (prefixCode rank.val code) buffer b) b.argument ∧
      checkedCap R B buffer rank parent code =
        (rowCap R (prefixCode rank.val code) buffer b : ℝ) := by
  dsimp only
  let B := P2OriginalCanonicalPairTentBank.bank R mesh buffer floor
  cases hs : select R B buffer rank code with
  | none =>
      have hchoice : checkedChoice R B buffer rank parent code = .inherit 2 := by
        simp [checkedChoice,B,select_prefix,hs]
      exact Or.inl ⟨hchoice,by rw [checkedCap,hchoice]; rfl,Or.inl hs⟩
  | some b =>
      by_cases hf : freshCheck R rank (prefixCode rank.val code) buffer parent b
      · obtain ⟨mask,hm,hside,hsource,hmask⟩ :=
          P2OriginalCanonicalPairTentBank.selected_source R mesh buffer floor rank code b hs
        have hforms := (P2OriginalCanonicalPairTentBank.lowerSide_source
          R (prefixCode rank.val code) mask b hside).1
        have hform : b.form = .tentLeft mask ∨ b.form = .tentRight mask := by
          rcases hforms with hb | hb
          · exact Or.inl (by rw [hb]; rfl)
          · exact Or.inr (by rw [hb]; rfl)
        have hchoice : checkedChoice R B buffer rank parent code =
            .fresh (rowCap R (prefixCode rank.val code) buffer b) b.argument := by
          simp [checkedChoice,B,select_prefix,hs,hf]
        exact Or.inr ⟨b,mask,hm,hs,hside,hsource,hmask,hform,hf,hchoice,
          by rw [checkedCap,hchoice]; rfl⟩
      · have hchoice : checkedChoice R B buffer rank parent code = .inherit 2 := by
          simp [checkedChoice,B,select_prefix,hs,hf]
        exact Or.inl ⟨hchoice,by rw [checkedCap,hchoice]; rfl,Or.inr ⟨b,hs,hf⟩⟩

/-- Read a genuinely computed fresh cap backwards to its independent
    canonical source. No selector/check/source licence is a caller premise. -/
theorem fresh_choice_source (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (rank : Fin 6) (parent : ℝ) (code : Code mesh) (q argument : ℝ)
    (h : checkedChoice R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor)
      buffer rank parent code = .fresh q argument) :
    ∃ b mask, mask ∈ tentMasks rank ∧
      select R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor)
        buffer rank (prefixCode rank.val code) = some b ∧
      sourceCheck R rank (prefixCode rank.val code) buffer b ∧
      b.form.supportMask = mask ∧
      (b.form = .tentLeft mask ∨ b.form = .tentRight mask) ∧
      freshCheck R rank (prefixCode rank.val code) buffer parent b ∧
      q = (rowCap R (prefixCode rank.val code) buffer b : ℝ) ∧
      argument = (b.argument : ℝ) := by
  rcases checked_choice_cases R mesh buffer floor rank parent code with hi | hf
  · rw [hi.1] at h
    cases h
  · obtain ⟨b,mask,hm,hs,hside,hsource,hmask,hform,hcheck,hchoice,hcap⟩ := hf
    have heq := hchoice.symm.trans h
    injection heq with hq ha
    have hsel : select R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor)
        buffer rank (prefixCode rank.val code) = some b := by
      simpa only [select_prefix] using hs
    exact ⟨b,mask,hm,hsel,hsource,hmask,hform,hcheck,hq.symm,ha.symm⟩

private theorem code_three_four (R : PairRange) (mesh : ℕ) (x0 x1 x2 x3 : ℝ) :
    prefixCode 3 (codeAt R mesh 4 [x0,x1,x2,x3]) = codeAt R mesh 3 [x0,x1,x2] := by
  funext i
  fin_cases i <;> simp [codeAt,incomingCode,physicalCode,marked,prefixCode,exponentCode,ceiling]

private theorem cap_three_prefix (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed : ℝ) (code : Code mesh) :
    cap3 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
      (prefixCode 3 code) =
    cap3 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed code := by
  simp only [cap3,checkedCap,checkedChoice,prefixCode_nested 3 3 (le_refl _)]

/-- The third state reads the original real pair seed, independently of
    the bank's rational comparison floor. -/
theorem warm_third_cap (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed x0 x1 x2 : ℝ) :
    (run (warmPlan R mesh buffer floor seed) R.epsilon ceiling
      ⟨[x0,x1],seed,[],true⟩ [x2]).cap =
    cap3 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
      (codeAt R mesh 3 [x0,x1,x2]) := by
  simp [run,warmPlan,step,planChoice,incomingChoice,pairPlan,codeAt,cap3,checkedCap]

/-- Actual fourth frozen cap; it cannot read the ideal or initial seed
    after the third state has selected a different cap. -/
theorem warm_fourth_cap (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed x0 x1 x2 x3 : ℝ) :
    (run (warmPlan R mesh buffer floor seed) R.epsilon ceiling
      ⟨[x0,x1],seed,[],true⟩ [x2,x3]).cap =
    cap4 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
      (codeAt R mesh 4 [x0,x1,x2,x3]) := by
  let B := P2OriginalCanonicalPairTentBank.bank R mesh buffer floor
  let P := warmPlan R mesh buffer floor seed
  let H3 := step P R.epsilon ceiling ⟨[x0,x1],seed,[],true⟩ x2
  have h3 : H3.cap = cap3 R B buffer seed (codeAt R mesh 3 [x0,x1,x2]) :=
    warm_third_cap R mesh buffer floor seed x0 x1 x2
  have h34 : cap3 R B buffer seed (codeAt R mesh 3 [x0,x1,x2]) =
      cap3 R B buffer seed (codeAt R mesh 4 [x0,x1,x2,x3]) := by
    rw [← code_three_four R mesh x0 x1 x2 x3]
    exact cap_three_prefix R mesh buffer floor seed _
  change (planChoice P R.epsilon ceiling (H3.word++[x3])).freeze H3.cap = _
  rw [h3,h34]
  simp [H3,P,B,warmPlan,step,planChoice,incomingChoice,pairPlan,codeAt,cap4,checkedCap]

/-- The original even arrival is tested BEFORE the fourth cap is frozen,
    against precisely the actual third cap. -/
theorem fourth_arrival_actual_parent (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed x0 x1 x2 x3 : ℝ) :
    admission (run (warmPlan R mesh buffer floor seed) R.epsilon ceiling
      ⟨[x0,x1],seed,[],true⟩ [x2]) x3 ↔
    x0+x1+x2+3*x3 <
      cap3 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
        (codeAt R mesh 3 [x0,x1,x2]) := by
  have hw := run_word (warmPlan R mesh buffer floor seed) R.epsilon ceiling
    (⟨[x0,x1],seed,[],true⟩ : Trace) [x2]
  simp only [admission,hw,List.length_append,List.length_cons,List.length_nil,
    show (2+1 : ℕ) ≠ 0 by omega,if_false,show ((2+1)+1 : ℕ)%2=0 by omega,if_true]
  rw [warm_third_cap]
  simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero]

/-- Real incoming original root and rational ranking floor stay distinct
    throughout the monotone third/fourth/fifth frozen-parent chain. -/
theorem original_warm_parent_chain (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (hbuffer : 0 ≤ buffer) (sixth : Bool) (N : ℕ) (p : ℕ × ℕ) (code : Code mesh) :
    let B := P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor
    let seed := P2OriginalSelectedPairNativeData.rootSeed sixth buffer N p
    seed ≤ cap3 R B (2*buffer) seed code ∧
      cap3 R B (2*buffer) seed code ≤ cap4 R B (2*buffer) seed code ∧
      cap4 R B (2*buffer) seed code ≤ cap5 R B (2*buffer) seed code ∧
      cap5 R B (2*buffer) seed code ≤ 153/256 := by
  dsimp only
  let B := P2OriginalCanonicalPairTentBank.bank R mesh (2*buffer) floor
  let seed := P2OriginalSelectedPairNativeData.rootSeed sixth buffer N p
  exact ⟨P2OriginalCanonicalPairTentBank.checked_cap_mono R mesh (2*buffer) floor 3 code seed,
    P2OriginalCanonicalPairTentBank.checked_cap_mono R mesh (2*buffer) floor 4 code _,
    P2OriginalCanonicalPairTentBank.checked_cap_mono R mesh (2*buffer) floor 5 code _,
    (caps_bounded R B (2*buffer) seed
      (P2OriginalSelectedPairNativeData.original_root_seed_bounded sixth buffer hbuffer N p)
      code).2.2⟩

/-- Exhaustive short-word lane: zero, one or two actual rough slots.
    These identities do not pretend that a missing fifth source fired. -/
theorem short_warm_cap_cases (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed x0 x1 : ℝ) (xs : List ℝ) (hlen : xs.length < 3) :
    let H := run (warmPlan R mesh buffer floor seed) R.epsilon ceiling
      ⟨[x0,x1],seed,[],true⟩ xs
    (xs=[] ∧ H.cap=seed) ∨
      (∃ x2, xs=[x2] ∧ H.cap=
        cap3 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
          (codeAt R mesh 3 [x0,x1,x2])) ∨
      (∃ x2 x3, xs=[x2,x3] ∧ H.cap=
        cap4 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
          (codeAt R mesh 4 [x0,x1,x2,x3])) := by
  cases xs with
  | nil => exact Or.inl ⟨rfl,rfl⟩
  | cons x xs =>
      cases xs with
      | nil => exact Or.inr (Or.inl ⟨x,rfl,warm_third_cap R mesh buffer floor seed x0 x1 x⟩)
      | cons y ys =>
          cases ys with
          | nil => exact Or.inr (Or.inr ⟨x,y,rfl,warm_fourth_cap R mesh buffer floor seed x0 x1 x y⟩)
          | cons z zs => simp only [List.length_cons] at hlen; omega

end
end ImbalancedChen.P2CanonicalPairTentWarmHistory
