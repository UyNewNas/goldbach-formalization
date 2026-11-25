import ImbalancedChen.P2OriginalSelectedFifthRoughBudget
import ImbalancedChen.P2OriginalLowerNestedBufferedStages

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A marked-pair receiver uses the ORIGINAL D=59/250 ceiling for external
pair coordinates. The ordinary CompactStart cutoff a/h is not reused
as a false bound on the larger L6 external prime. Rough descendants keep
their separate original a ceiling in their actual carrier.

The SourceForm, its supportMask, its whole-box winner gaps, and inherited
priority are reused. This receiver handles the existing tent-licensed
source bank; it does not silently add a W arithmetic licence or complete
all original pair branches. The actual seed is a parameter of the finite
plan, so a pair root is never reset to an ordinary baselineCap.
-/
namespace ImbalancedChen.P2OriginalPairSourceReceiver
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code prefixCode strictSquareGates)
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)

structure PairRange where
  epsilon : ℚ
  epsilon_pos : 0 < epsilon
  epsilon_lt_a : epsilon < 417/5000

def ceiling : ℚ := 59/250

def qPoint (R : PairRange) (mesh j : ℕ) : ℚ :=
  R.epsilon + j * ((ceiling - R.epsilon)/(mesh+1))

def qLo (R : PairRange) (mesh : ℕ) : CellCode mesh → ℚ
  | none => ceiling
  | some j => qPoint R mesh j.val

def qHi (R : PairRange) (mesh : ℕ) : CellCode mesh → ℚ
  | none => ceiling
  | some j => qPoint R mesh (j.val+1)

def box (R : PairRange) {mesh : ℕ} (code : Code mesh) : RationalBox :=
  ⟨fun i => qLo R mesh (code i).1, fun i => qHi R mesh (code i).1⟩

def codeAt (R : PairRange) (mesh rank : ℕ) (word : List ℝ) : Code mesh :=
  incomingCode (R.epsilon : ℝ) (ceiling : ℝ) 5 mesh rank (marked word)

def ownSlot (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) (i : Fin 5) : Slot :=
  ⟨(qHi R mesh (code i).1 : ℝ), (code i).2 || decide (i ∈ mask)⟩

def ownSlots (R : PairRange) {mesh : ℕ} (rank : Fin 6)
    (code : Code mesh) (mask : Finset (Fin 5)) : List Slot :=
  ([ownSlot R code mask 0, ownSlot R code mask 1, ownSlot R code mask 2,
    ownSlot R code mask 3, ownSlot R code mask 4]).take rank.val

def rowCap (R : PairRange) {mesh : ℕ} (code : Code mesh)
    (buffer : ℚ) (branch : SelectedBranchData) : ℚ :=
  wholeBoxInfimum branch.cap.constant branch.cap.slope (box R code) - buffer

/-- Exact finite full/selected square checks on this source's own mask. -/
def sourceCheck (R : PairRange) {mesh : ℕ} (rank : Fin 6)
    (code : Code mesh) (buffer : ℚ) (branch : SelectedBranchData) : Prop :=
  formRankEligible rank branch.form ∧ sideCheck branch (box R code) ∧
    strictSquareGates (rowCap R code buffer branch : ℝ) 0
      ((ownSlots R rank code branch.form.supportMask).map Slot.exponent) ∧
    strictSquareGates (rowCap R code buffer branch : ℝ)
      (selectedWord (ownSlots R rank code branch.form.supportMask)).sum
      (remainingWord (ownSlots R rank code branch.form.supportMask)) ∧
    (∀ i ∈ branch.form.supportMask, i.val < rank.val)

def stableAlternative (R : PairRange) {mesh : ℕ} (rank : Fin 6)
    (code : Code mesh) (buffer : ℚ) (base : LabeledBranch 5)
    (rest : List SelectedBranchData) (branch : SelectedBranchData) : Prop :=
  sourceCheck R rank code buffer branch ∧
    (branch.cap = base.cap ∨ 0 < gapLower branch.cap base.cap (box R code)) ∧
    ∀ c ∈ rest, branch.cap = c.cap ∨ 0 < gapLower branch.cap c.cap (box R code)

/-- Same winner and inherited-tie logic as the original SourceForm bank;
    the changed receiver range is explicit. Source identity is retained. -/
def select (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (rank : Fin 6) (code : Code mesh) : Option SelectedBranchData :=
  let pcode := prefixCode rank.val code
  let base := bank.inherited rank pcode
  let rest := bank.alternatives rank pcode
  if stableBase (box R pcode) base rest then none
  else firstStable (stableAlternative R rank pcode buffer base rest) rest

theorem select_some_source (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (rank : Fin 6) (code : Code mesh) (branch : SelectedBranchData)
    (hsel : select R bank buffer rank code = some branch) :
    branch ∈ bank.alternatives rank (prefixCode rank.val code) ∧
      sourceCheck R rank (prefixCode rank.val code) buffer branch := by
  unfold select at hsel
  split_ifs at hsel with hb
  · simp at hsel
  · have h := firstStable_some hsel
    exact ⟨h.1, h.2.1⟩

def pointSlot {mesh : ℕ} (code : Code mesh) (mask : Finset (Fin 5))
    (x : Fin 5 → ℝ) (i : Fin 5) : Slot :=
  ⟨x i, (code i).2 || decide (i ∈ mask)⟩

def pointSlots {mesh : ℕ} (rank : Fin 6) (code : Code mesh)
    (mask : Finset (Fin 5)) (x : Fin 5 → ℝ) : List Slot :=
  ([pointSlot code mask x 0, pointSlot code mask x 1, pointSlot code mask x 2,
    pointSlot code mask x 3, pointSlot code mask x 4]).take rank.val

private theorem qPoint_cast (R : PairRange) (mesh j : ℕ) :
    (qPoint R mesh j : ℝ) =
      logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh j := by
  unfold qPoint logPrimeMeshPoint logPrimeMeshStep
  push_cast
  ring

private theorem exponent_upper (R : PairRange) (mesh : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ)) :
    x ≤ (qHi R mesh (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh x) : ℝ) := by
  have hm := exponentCode_membership hx
  cases hc : exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh x with
  | none =>
      have heq : x = (ceiling : ℝ) := by simpa [hc, exponentCell] using hm
      simpa [hc, qHi] using heq.le
  | some j =>
      have hm' : x ∈ Set.Ico
          (logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh j.val)
          (logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh (j.val+1)) := by
        simpa only [hc, exponentCell] using hm
      simpa only [qHi, qPoint_cast] using hm'.2.le

private theorem squareGates_mono {cap T U : ℝ} {xs ys : List ℝ}
    (hTU : T ≤ U) (hxy : List.Forall₂ (· ≤ ·) xs ys)
    (hy : SquareGates cap U ys) : SquareGates cap T xs := by
  induction hxy generalizing T U with
  | nil => trivial
  | @cons x y xs ys hxy htail ih =>
      exact ⟨by linarith [hy.1], ih (add_le_add hTU hxy) hy.2⟩

private theorem sum_le {xs ys : List ℝ} (h : List.Forall₂ (· ≤ ·) xs ys) :
    xs.sum ≤ ys.sum := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy htail ih => simp only [List.sum_cons]; linarith

private theorem slot_words_mono {xs ys : List Slot}
    (h : List.Forall₂ (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected=q.selected) xs ys) :
    List.Forall₂ (· ≤ ·) (xs.map Slot.exponent) (ys.map Slot.exponent) ∧
      List.Forall₂ (· ≤ ·) (selectedWord xs) (selectedWord ys) ∧
      List.Forall₂ (· ≤ ·) (remainingWord xs) (remainingWord ys) := by
  induction h with
  | nil => exact ⟨.nil,.nil,.nil⟩
  | @cons p q xs ys hp htail ih =>
      have hf := List.Forall₂.cons hp.1 ih.1
      by_cases hs : p.selected = true
      · have ht : q.selected = true := hp.2 ▸ hs
        refine ⟨hf, ?_, ?_⟩
        · simpa [selectedWord,hs,ht] using List.Forall₂.cons hp.1 ih.2.1
        · simpa [remainingWord,hs,ht] using ih.2.2
      · have ht : q.selected ≠ true := by intro hq; exact hs (hp.2.trans hq)
        refine ⟨hf, ?_, ?_⟩
        · simpa [selectedWord,hs,ht] using ih.2.1
        · simpa [remainingWord,hs,ht] using List.Forall₂.cons hp.1 ih.2.2

/-- The actual range includes both external L6 primes up to D. This is
    a proved point-to-box transfer, not a re-used a/h receiver premise. -/
theorem selected_fifth_point_squares (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (branch : SelectedBranchData)
    (hsel : select R bank buffer 5 (codeAt R mesh 5 [x 0,x 1,x 2,x 3,x 4]) = some branch) :
    let code := prefixCode 5 (codeAt R mesh 5 [x 0,x 1,x 2,x 3,x 4])
    let pts := pointSlots 5 code branch.form.supportMask x
    SquareGates (rowCap R code buffer branch : ℝ) 0 (pts.map Slot.exponent) ∧
      SquareGates (rowCap R code buffer branch : ℝ) (selectedWord pts).sum (remainingWord pts) := by
  have hsource := (select_some_source R bank buffer 5 _ branch hsel).2
  let code := prefixCode 5 (codeAt R mesh 5 [x 0,x 1,x 2,x 3,x 4])
  have hpoint : ∀ i, x i ≤ (qHi R mesh
      (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh (x i)) : ℝ) :=
    fun i => exponent_upper R mesh (hx i)
  have hupper : ∀ i, x i ≤ (qHi R mesh (code i).1 : ℝ) := by
    intro i
    fin_cases i
    · simpa [code,codeAt,incomingCode,physicalCode,marked,prefixCode] using hpoint 0
    · simpa [code,codeAt,incomingCode,physicalCode,marked,prefixCode] using hpoint 1
    · simpa [code,codeAt,incomingCode,physicalCode,marked,prefixCode] using hpoint 2
    · simpa [code,codeAt,incomingCode,physicalCode,marked,prefixCode] using hpoint 3
    · simpa [code,codeAt,incomingCode,physicalCode,marked,prefixCode] using hpoint 4
  have hslots : List.Forall₂
      (fun p q : Slot => p.exponent ≤ q.exponent ∧ p.selected=q.selected)
      (pointSlots 5 code branch.form.supportMask x)
      (ownSlots R 5 code branch.form.supportMask) := by
    simp [pointSlots,ownSlots,pointSlot,ownSlot,hupper]
  have hwords := slot_words_mono hslots
  have hfull := P2OriginalLowerSelectedCapConstructor.strictSquareGates_sound _ _ _ hsource.2.2.1
  have hselected := P2OriginalLowerSelectedCapConstructor.strictSquareGates_sound _ _ _ hsource.2.2.2.1
  exact ⟨squareGates_mono (le_refl (0 : ℝ)) hwords.1 hfull,
    squareGates_mono (sum_le hwords.2.1) hwords.2.2 hselected⟩

/-- The current even full-rank arrival is tested against its actual
    incoming parent; rank three/five receive no extra odd cube. -/
def arrivalGate (R : PairRange) {mesh : ℕ} (rank : Fin 6)
    (code : Code mesh) (parent : ℝ) : Prop :=
  if rank.val = 4 then
    (qHi R mesh (code 0).1 : ℝ) + (qHi R mesh (code 1).1 : ℝ) +
      (qHi R mesh (code 2).1 : ℝ) + 3*(qHi R mesh (code 3).1 : ℝ) < parent
  else True

def freshCheck (R : PairRange) {mesh : ℕ} (rank : Fin 6) (code : Code mesh)
    (buffer : ℚ) (parent : ℝ) (branch : SelectedBranchData) : Prop :=
  parent < (rowCap R code buffer branch : ℝ) ∧
    (rowCap R code buffer branch : ℝ) ≤ (153/256 : ℝ) ∧
    arrivalGate R rank code parent

def checkedChoice (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (rank : Fin 6) (parent : ℝ) (code : Code mesh) : CapChoice :=
  let pcode := prefixCode rank.val code
  match select R bank buffer rank pcode with
  | none => .inherit 2
  | some branch => if freshCheck R rank pcode buffer parent branch then
      .fresh (rowCap R pcode buffer branch) branch.argument else .inherit 2

def checkedCap (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (rank : Fin 6) (parent : ℝ) (code : Code mesh) : ℝ :=
  (checkedChoice R bank buffer rank parent code).freeze parent

def cap3 (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seed : ℝ) (code : Code mesh) : ℝ :=
  checkedCap R bank buffer 3 seed code

def cap4 (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seed : ℝ) (code : Code mesh) : ℝ :=
  checkedCap R bank buffer 4 (cap3 R bank buffer seed code) code

def cap5 (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seed : ℝ) (code : Code mesh) : ℝ :=
  checkedCap R bank buffer 5 (cap4 R bank buffer seed code) code

def pairPlan (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seed : ℝ) : CapPlan 5 mesh :=
  ⟨fun rank code => match rank.val with
    | 3 => checkedChoice R bank buffer 3 seed code
    | 4 => checkedChoice R bank buffer 4 (cap3 R bank buffer seed code) code
    | 5 => checkedChoice R bank buffer 5 (cap4 R bank buffer seed code) code
    | _ => .inherit 2⟩

theorem checkedChoice_fresh (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (rank : Fin 6) (parent : ℝ) (code : Code mesh)
    (branch : SelectedBranchData)
    (hsel : select R bank buffer rank (prefixCode rank.val code) = some branch)
    (hcheck : freshCheck R rank (prefixCode rank.val code) buffer parent branch) :
    checkedChoice R bank buffer rank parent code =
      .fresh (rowCap R (prefixCode rank.val code) buffer branch) branch.argument := by
  simp [checkedChoice, hsel, hcheck]

theorem checkedChoice_freeze_bounded (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (rank : Fin 6)
    (parent incoming : ℝ) (code : Code mesh)
    (hincoming : incoming ≤ (153/256 : ℝ)) :
    (checkedChoice R bank buffer rank parent code).freeze incoming ≤ (153/256 : ℝ) := by
  unfold checkedChoice
  cases hs : select R bank buffer rank (prefixCode rank.val code) with
  | none => simpa [hs, CapChoice.freeze] using hincoming
  | some branch =>
      by_cases hc : freshCheck R rank (prefixCode rank.val code) buffer parent branch
      · simpa [hs, hc, CapChoice.freeze] using hc.2.1
      · simpa [hs, hc, CapChoice.freeze] using hincoming

theorem checkedChoice_bounded (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (rank : Fin 6) (parent : ℝ) (code : Code mesh)
    (hparent : parent ≤ (153/256 : ℝ)) :
    (checkedChoice R bank buffer rank parent code).freeze parent ≤ (153/256 : ℝ) :=
  checkedChoice_freeze_bounded R bank buffer rank parent parent code hparent

theorem caps_bounded (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seed : ℝ) (hseed : seed ≤ (153/256 : ℝ)) (code : Code mesh) :
    cap3 R bank buffer seed code ≤ (153/256 : ℝ) ∧
      cap4 R bank buffer seed code ≤ (153/256 : ℝ) ∧
      cap5 R bank buffer seed code ≤ (153/256 : ℝ) := by
  have h3 := checkedChoice_bounded R bank buffer 3 seed code hseed
  have h4 := checkedChoice_bounded R bank buffer 4 _ code h3
  have h5 := checkedChoice_bounded R bank buffer 5 _ code h4
  exact ⟨h3,h4,h5⟩

/-- Fresh-cap bound supplied to the actual raw/rounded support consumer. -/
theorem pairPlan_fresh_cap_bound (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (seed : ℝ)
    (rank : Fin 6) (code : Code mesh)
    (incoming : ℝ) (hincoming : incoming ≤ (153/256 : ℝ)) :
    ((pairPlan R bank buffer seed).choose rank code).freeze incoming ≤ (153/256 : ℝ) := by
  fin_cases rank <;> simp only [pairPlan]
  all_goals first
  | simpa [CapChoice.freeze] using hincoming
  | exact checkedChoice_freeze_bounded R bank buffer _ _ incoming code hincoming

private theorem checkedChoice_prefix (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (rank : Fin 6) (parent : ℝ)
    (code : Code mesh) (r : ℕ) (hr : rank.val ≤ r) :
    checkedChoice R bank buffer rank parent (prefixCode r code) =
      checkedChoice R bank buffer rank parent code := by
  simp only [checkedChoice, prefixCode_nested rank.val r hr]

private theorem cap3_prefix (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (seed : ℝ)
    (code : Code mesh) (r : ℕ) (hr : 3 ≤ r) :
    cap3 R bank buffer seed (prefixCode r code) = cap3 R bank buffer seed code := by
  simp only [cap3, checkedCap, checkedChoice_prefix R bank buffer 3 seed code r hr]

private theorem cap4_prefix (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (seed : ℝ)
    (code : Code mesh) (r : ℕ) (hr : 4 ≤ r) :
    cap4 R bank buffer seed (prefixCode r code) = cap4 R bank buffer seed code := by
  unfold cap4
  rw [cap3_prefix R bank buffer seed code r (by omega)]
  simp only [checkedCap, checkedChoice_prefix R bank buffer 4 _ code r hr]

private theorem code_prefix_three_four (R : PairRange) (mesh : ℕ) (x0 x1 x2 x3 : ℝ) :
    prefixCode 3 (codeAt R mesh 4 [x0,x1,x2,x3]) = codeAt R mesh 3 [x0,x1,x2] := by
  funext i
  fin_cases i <;> simp [codeAt, incomingCode, physicalCode, marked,
    prefixCode, exponentCode, ceiling]

private theorem code_prefix_four_five (R : PairRange) (mesh : ℕ) (x0 x1 x2 x3 x4 : ℝ) :
    prefixCode 4 (codeAt R mesh 5 [x0,x1,x2,x3,x4]) =
      codeAt R mesh 4 [x0,x1,x2,x3] := by
  funext i
  fin_cases i <;> simp [codeAt, incomingCode, physicalCode, marked,
    prefixCode, exponentCode, ceiling]

/-- The actual full fifth state reads the TRUE pair seed and the same
    earlier frozen rows. No row-to-Trace cap equality is an assumption. -/
theorem pair_run_three_cap (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seed x0 x1 x2 x3 x4 : ℝ) :
    (run (pairPlan R bank buffer seed) (R.epsilon : ℝ) (ceiling : ℝ)
      ⟨[x0,x1],seed,[],true⟩ [x2,x3,x4]).cap =
      cap5 R bank buffer seed (codeAt R mesh 5 [x0,x1,x2,x3,x4]) := by
  let P := pairPlan R bank buffer seed
  let H2 : Trace := ⟨[x0,x1],seed,[],true⟩
  let H3 := step P (R.epsilon : ℝ) (ceiling : ℝ) H2 x2
  let H4 := step P (R.epsilon : ℝ) (ceiling : ℝ) H3 x3
  let H5 := step P (R.epsilon : ℝ) (ceiling : ℝ) H4 x4
  let c3 := codeAt R mesh 3 [x0,x1,x2]
  let c4 := codeAt R mesh 4 [x0,x1,x2,x3]
  let c5 := codeAt R mesh 5 [x0,x1,x2,x3,x4]
  have h3 : H3.cap = cap3 R bank buffer seed c3 := by
    simp [H3,H2,P,step,planChoice,incomingChoice,pairPlan,codeAt,cap3,checkedCap]
  have h34 : cap3 R bank buffer seed c3 = cap3 R bank buffer seed c4 := by
    rw [← code_prefix_three_four R mesh x0 x1 x2 x3]
    exact cap3_prefix R bank buffer seed c4 3 (by omega)
  have h4 : H4.cap = cap4 R bank buffer seed c4 := by
    change (planChoice P (R.epsilon : ℝ) (ceiling : ℝ)
      (H3.word++[x3])).freeze H3.cap = _
    rw [h3,h34]
    simp [H3,H2,P,step,planChoice,incomingChoice,pairPlan,codeAt,cap4,checkedCap,c4]
  have h45 : cap4 R bank buffer seed c4 = cap4 R bank buffer seed c5 := by
    rw [← code_prefix_four_five R mesh x0 x1 x2 x3 x4]
    exact cap4_prefix R bank buffer seed c5 4 (by omega)
  have h5 : H5.cap = cap5 R bank buffer seed c5 := by
    change (planChoice P (R.epsilon : ℝ) (ceiling : ℝ)
      (H4.word++[x4])).freeze H4.cap = _
    rw [h4,h45]
    simp [H4,H3,H2,P,step,planChoice,incomingChoice,pairPlan,codeAt,cap5,checkedCap,c5]
  exact h5

/-- The same finite source selection supplies the actual fifth frozen
    cap. Unlike the previous batch, this is not an hcap input. -/
theorem actual_fifth_source_cap (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seed x0 x1 x2 x3 x4 : ℝ) (branch : SelectedBranchData)
    (hsel : select R bank buffer 5
      (prefixCode 5 (codeAt R mesh 5 [x0,x1,x2,x3,x4])) = some branch)
    (hcheck : freshCheck R 5
      (prefixCode 5 (codeAt R mesh 5 [x0,x1,x2,x3,x4])) buffer
      (cap4 R bank buffer seed (codeAt R mesh 5 [x0,x1,x2,x3,x4])) branch) :
    (run (pairPlan R bank buffer seed) (R.epsilon : ℝ) (ceiling : ℝ)
      ⟨[x0,x1],seed,[],true⟩ [x2,x3,x4]).cap =
      (rowCap R (prefixCode 5 (codeAt R mesh 5 [x0,x1,x2,x3,x4])) buffer branch : ℝ) := by
  rw [pair_run_three_cap]
  unfold cap5 checkedCap
  rw [checkedChoice_fresh R bank buffer 5 _ _ branch hsel hcheck]
  rfl

end
end ImbalancedChen.P2OriginalPairSourceReceiver
