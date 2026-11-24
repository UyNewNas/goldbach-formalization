import ImbalancedChen.P2OriginalLowerAffineTieSelector
import ImbalancedChen.P2OriginalLowerCompactStartCapConstructor

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- A finite rational whole-box selector for the corrected [epsilon,w]
-- lower starts. The branch bank is explicit data, not a final certificate.
-- Each tent candidate carries its own literal selected-subproduct support mask.
-- The scalar BranchTable does not encode this mask, so support is checked
-- here before the scalar row is passed to boxedTable. These are necessary
-- support gates, not the full factorization licence. The W_j branch
-- needs its distinct source licence and is excluded here. No selected bank,
-- density endpoint, or final lower coefficient is assumed.

namespace ImbalancedChen.P2OriginalLowerWholeBoxBranchSelect

noncomputable section
open scoped Classical BigOperators
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerSelectedCapConstructor
open P2PhysicalIncomingPrefixCells
open P2EnhancedLowerPhysicalNode

abbrev Code (mesh : ℕ) := P2OriginalLowerSelectedCapConstructor.Code mesh

-- These are the original affine pieces: v(s)=min((1+s)/2,
-- 57/64-3s/2), and the W_j branch Lambda-3*t_j/8.
inductive SourceForm where
  | tentLeft (mask : Finset (Fin 5))
  | tentRight (mask : Finset (Fin 5))
  | wSlot (j : Fin 5)

def SourceForm.affine : SourceForm → AffineBranch 5
  | .tentLeft mask =>
      ⟨1 / 2, fun i => if i ∈ mask then 1 / 2 else 0⟩
  | .tentRight mask =>
      ⟨57 / 64, fun i => if i ∈ mask then -(3 / 2) else 0⟩
  | .wSlot j =>
      ⟨153 / 256, fun i => if i = j then -(3 / 8) else 0⟩

def SourceForm.supportMask : SourceForm → Finset (Fin 5)
  | .tentLeft mask => mask
  | .tentRight mask => mask
  | .wSlot _ => ∅

def SourceForm.otherTent : SourceForm → Option (AffineBranch 5)
  | .tentLeft mask => some (SourceForm.affine (.tentRight mask))
  | .tentRight mask => some (SourceForm.affine (.tentLeft mask))
  | .wSlot _ => none

structure SelectedBranchData where
  label : ℕ
  form : SourceForm
  argument : ℚ

def SelectedBranchData.cap (b : SelectedBranchData) : AffineBranch 5 :=
  b.form.affine

def SelectedBranchData.asLabeled (b : SelectedBranchData) : LabeledBranch 5 :=
  ⟨b.label, b.cap, b.argument⟩

def SelectedBranchData.asBranchData (b : SelectedBranchData) :
    BranchData :=
  (b.cap.constant, b.cap.slope, b.argument)

def gapLower (a b : AffineBranch 5) (box : RationalBox) : ℚ :=
  wholeBoxInfimum (a.constant - b.constant)
    (fun i => a.slope i - b.slope i) box

theorem gapLower_le_eval_gap (a b : AffineBranch 5)
    (box : RationalBox) (x : Fin 5 → ℝ)
    (hx : inBox box x) :
    (gapLower a b box : ℝ) ≤ a.eval x - b.eval x := by
  have h := wholeBoxInfimum_le_affine
    (a.constant - b.constant)
    (fun i => a.slope i - b.slope i) box x hx
  have heq : affineValue (a.constant - b.constant)
      (fun i => a.slope i - b.slope i) x =
        a.eval x - b.eval x := by
    simp [affineValue, AffineBranch.eval, Rat.cast_sub,
      sub_mul, Finset.sum_sub_distrib]
    ring
  simpa only [gapLower, heq] using h

def sideCheck (b : SelectedBranchData) (box : RationalBox) : Prop :=
  match b.form.otherTent with
  | none => True
  | some other => 0 ≤ gapLower other b.cap box

theorem sideCheck_sound (b : SelectedBranchData)
    (box : RationalBox) (x : Fin 5 → ℝ)
    (hside : sideCheck b box) (hx : inBox box x) :
    ∀ other, b.form.otherTent = some other →
      b.cap.eval x ≤ other.eval x := by
  intro other hother
  unfold sideCheck at hside
  rw [hother] at hside
  have h := gapLower_le_eval_gap other b.cap box x hx
  have hzero : (0 : ℝ) ≤ gapLower other b.cap box := by
    exact_mod_cast hside
  linarith

-- The tent candidate support mask is recorded separately from Code's inherited
-- selected bits. A marked factor is retained if either source marks it.
-- This conservative union is visible to the gate checker, never erased by
-- passing only the scalar cap/argument row to BranchTable.
def ownSlot (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (mask : Finset (Fin 5)) (i : Fin 5) : Slot :=
  ⟨P2OriginalLowerCompactStartCapConstructor.cellUpper S mesh (code i).1,
    (code i).2 || decide (i ∈ mask)⟩

def ownPrefixSlots (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (code : Code mesh)
    (mask : Finset (Fin 5)) : List Slot :=
  match rank.val with
  | 3 => [ownSlot S code mask 0, ownSlot S code mask 1,
      ownSlot S code mask 2]
  | 4 => [ownSlot S code mask 0, ownSlot S code mask 1,
      ownSlot S code mask 2, ownSlot S code mask 3]
  | 5 => [ownSlot S code mask 0, ownSlot S code mask 1,
      ownSlot S code mask 2, ownSlot S code mask 3,
      ownSlot S code mask 4]
  | _ => []

def bufferedCap (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (buffer : ℚ)
    (b : SelectedBranchData) : ℚ :=
  wholeBoxInfimum b.cap.constant b.cap.slope
    (P2OriginalLowerCompactStartCapConstructor.boxOfCode S code) - buffer

-- The third ideal cap contains W_j for j<3, but its factorization
-- gate is separate. This selected-subproduct mask checker does not
-- license W_j, so a W candidate cannot become a fresh table row. Fresh
-- fourth/fifth tent branches must contain their newest physical slot.
-- This is structural eligibility, not the external factorization proof.
def formRankEligible (rank : Fin 6) (form : SourceForm) : Prop :=
  match rank.val, form with
  | 3, .tentLeft mask => mask.Nonempty ∧ ∀ i ∈ mask, i.val < 3
  | 3, .tentRight mask => mask.Nonempty ∧ ∀ i ∈ mask, i.val < 3
  | 3, .wSlot _ => False
  | 4, .tentLeft mask => 3 ∈ mask ∧ ∀ i ∈ mask, i.val < 4
  | 4, .tentRight mask => 3 ∈ mask ∧ ∀ i ∈ mask, i.val < 4
  | 5, .tentLeft mask => 4 ∈ mask
  | 5, .tentRight mask => 4 ∈ mask
  | _, _ => False

def supportCheck (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (code : Code mesh)
    (buffer : ℚ) (b : SelectedBranchData) : Prop :=
  let box := P2OriginalLowerCompactStartCapConstructor.boxOfCode S code
  let cap := (bufferedCap S code buffer b : ℝ)
  formRankEligible rank b.form ∧ sideCheck b box ∧
    strictSquareGates cap 0
      ((ownPrefixSlots S rank code b.form.supportMask).map Slot.exponent) ∧
    strictSquareGates cap
      (selectedWord (ownPrefixSlots S rank code b.form.supportMask)).sum
      (remainingWord (ownPrefixSlots S rank code b.form.supportMask)) ∧
    (∀ i ∈ b.form.supportMask, i.val < rank.val)

theorem supportCheck_has_own_mask_gates (S : CompactStart)
    {mesh : ℕ} (rank : Fin 6) (code : Code mesh)
    (buffer : ℚ) (b : SelectedBranchData)
    (h : supportCheck S rank code buffer b) :
    strictSquareGates (bufferedCap S code buffer b : ℝ) 0
      ((ownPrefixSlots S rank code b.form.supportMask).map Slot.exponent) ∧
    strictSquareGates (bufferedCap S code buffer b : ℝ)
      (selectedWord (ownPrefixSlots S rank code b.form.supportMask)).sum
      (remainingWord (ownPrefixSlots S rank code b.form.supportMask)) := by
  exact ⟨h.2.2.1, h.2.2.2.1⟩

def stableBase (box : RationalBox) (base : LabeledBranch 5)
    (rest : List SelectedBranchData) : Prop :=
  ∀ b ∈ rest, b.cap = base.cap ∨ 0 < gapLower base.cap b.cap box

def stableAlternative (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (code : Code mesh) (buffer : ℚ)
    (box : RationalBox) (base : LabeledBranch 5)
    (rest : List SelectedBranchData) (b : SelectedBranchData) : Prop :=
  supportCheck S rank code buffer b ∧
    (b.cap = base.cap ∨ 0 < gapLower b.cap base.cap box) ∧
    ∀ c ∈ rest, b.cap = c.cap ∨ 0 < gapLower b.cap c.cap box

def firstStable (P : SelectedBranchData → Prop) :
    List SelectedBranchData → Option SelectedBranchData
  | [] => none
  | b :: rest => if P b then some b else firstStable P rest

theorem firstStable_some {P : SelectedBranchData → Prop}
    {rest : List SelectedBranchData} {b : SelectedBranchData}
    (h : firstStable P rest = some b) :
    b ∈ rest ∧ P b := by
  induction rest with
  | nil => simp [firstStable] at h
  | cons head tail ih =>
      by_cases hp : P head
      · simp [firstStable, hp] at h
        subst b
        exact ⟨List.mem_cons_self, hp⟩
      · simp [firstStable, hp] at h
        obtain ⟨hm, hs⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hm, hs⟩

structure CandidateBank (mesh : ℕ) where
  inherited : Fin 6 → Code mesh → LabeledBranch 5
  alternatives : Fin 6 → Code mesh → List SelectedBranchData

-- All lookups use prefixCode before reading a bank row. The inherited
-- branch is first, so identical expressions and ties keep inherit.
def select (S : CompactStart) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ)
    (rank : Fin 6) (code : Code mesh) : Option BranchData :=
  let pcode := prefixCode rank.val code
  let base := bank.inherited rank pcode
  let rest := bank.alternatives rank pcode
  let box := P2OriginalLowerCompactStartCapConstructor.boxOfCode S pcode
  if stableBase box base rest then none
  else (firstStable
    (stableAlternative S rank pcode buffer box base rest) rest).map
      SelectedBranchData.asBranchData

theorem select_future_invariant (S : CompactStart) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ)
    (rank : Fin 6) {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < rank.val → code₁ i = code₂ i) :
    select S bank buffer rank code₁ = select S bank buffer rank code₂ := by
  have hp := prefixCode_future_invariant heq
  simp only [select, hp]

theorem select_none_of_identical (S : CompactStart) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ)
    (rank : Fin 6) (code : Code mesh)
    (h : ∀ b ∈ bank.alternatives rank (prefixCode rank.val code),
      b.cap = (bank.inherited rank (prefixCode rank.val code)).cap) :
    select S bank buffer rank code = none := by
  unfold select
  have hs : stableBase (P2OriginalLowerCompactStartCapConstructor.boxOfCode S (prefixCode rank.val code))
      (bank.inherited rank (prefixCode rank.val code))
      (bank.alternatives rank (prefixCode rank.val code)) := by
    intro b hb
    exact Or.inl (h b hb)
  simp [hs]

-- A selected row comes from one literal source form and retains its
-- argument and selected-subproduct mask. It has passed the separate
-- support-mask gate, not merely the scalar BranchTable check.
theorem select_some_source (S : CompactStart) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ)
    (rank : Fin 6) (code : Code mesh) (data : BranchData)
    (hsel : select S bank buffer rank code = some data) :
    ∃ b ∈ bank.alternatives rank (prefixCode rank.val code),
      supportCheck S rank (prefixCode rank.val code) buffer b ∧
        data = b.asBranchData := by
  unfold select at hsel
  let pcode := prefixCode rank.val code
  let base := bank.inherited rank pcode
  let rest := bank.alternatives rank pcode
  let box := P2OriginalLowerCompactStartCapConstructor.boxOfCode S pcode
  by_cases hb : stableBase box base rest
  · simp [hb] at hsel
  · simp only [if_neg hb] at hsel
    cases hf : firstStable
        (stableAlternative S rank pcode buffer box base rest) rest with
    | none => simp [hf] at hsel
    | some b =>
        have hs := firstStable_some hf
        simp [hf] at hsel
        subst data
        exact ⟨b, hs.1, hs.2.1, rfl⟩

-- The scalar cap row is exactly the source branch's rational affine lower
-- vertex minus the fixed buffer, with its original query argument.
theorem boxedTable_row_of_source (S : CompactStart) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ)
    (rank : Fin 6) (code : Code mesh)
    (data : BranchData)
    (hsel : select S bank buffer rank
      (prefixCode rank.val code) = some data) :
    (P2OriginalLowerCompactStartCapConstructor.boxedTable S (select S bank buffer) buffer).row rank code =
      some (wholeBoxInfimum data.1 data.2.1
        (P2OriginalLowerCompactStartCapConstructor.boxOfCode S (prefixCode rank.val code)) - buffer,
        data.2.2) := by
  simp [P2OriginalLowerCompactStartCapConstructor.boxedTable, hsel]

-- The actual parent/history gate is checked after this finite label
-- selection. When it holds, checkedChoice freezes this exact row.
theorem checkedChoice_fresh_from_source (S : CompactStart) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ)
    (rank : Fin 6) (code : Code mesh) (data : BranchData)
    (parent : ℝ)
    (hsel : select S bank buffer rank
      (prefixCode rank.val code) = some data)
    (hgate : P2OriginalLowerCompactStartCapConstructor.branchGates S rank parent
      (wholeBoxInfimum data.1 data.2.1
        (P2OriginalLowerCompactStartCapConstructor.boxOfCode S (prefixCode rank.val code)) - buffer)
      (prefixCode rank.val code)) :
    P2OriginalLowerCompactStartCapConstructor.checkedChoice S (P2OriginalLowerCompactStartCapConstructor.boxedTable S (select S bank buffer) buffer)
      rank parent code =
      .fresh
        (wholeBoxInfimum data.1 data.2.1
          (P2OriginalLowerCompactStartCapConstructor.boxOfCode S (prefixCode rank.val code)) - buffer)
        data.2.2 := by
  unfold P2OriginalLowerCompactStartCapConstructor.checkedChoice
  rw [boxedTable_row_of_source S bank buffer rank code data hsel]
  simp [hgate]

end
end ImbalancedChen.P2OriginalLowerWholeBoxBranchSelect
