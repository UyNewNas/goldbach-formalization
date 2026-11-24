import ImbalancedChen.P2OriginalLowerBufferedAffineBoxes

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Corrected compact lower grid. The original L1 and L2 starts contain
-- exponents below a, so the physical mesh must begin at epsilon, not a.
-- Earlier fixed-[a,h] CapPlan/box drafts are superseded and held.

namespace ImbalancedChen.P2OriginalLowerCompactStartCapConstructor

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor

inductive LowerStart where
  | first | second
  deriving DecidableEq

def startCutoff : LowerStart → ℚ
  | .first => 417 / 5000
  | .second => 19 / 125

def baselineCap (rho : ℝ) : ℝ := 249 / 448 - rho
def topCap : ℝ := 153 / 256

-- A chosen positive epsilon is fixed before N, strictly below the
-- particular starting rough cutoff w. In particular epsilon may be < a.
structure CompactStart where
  start : LowerStart
  epsilon : ℚ
  epsilon_pos : 0 < epsilon
  epsilon_lt_start : epsilon < startCutoff start

def cellUpper (S : CompactStart) (mesh : ℕ) : CellCode mesh → ℝ
  | none => startCutoff S.start
  | some j => logPrimeMeshPoint (S.epsilon : ℝ)
      (startCutoff S.start : ℝ) mesh (j.val + 1)

def cellLower (S : CompactStart) (mesh : ℕ) : CellCode mesh → ℝ
  | none => startCutoff S.start
  | some j => logPrimeMeshPoint (S.epsilon : ℝ)
      (startCutoff S.start : ℝ) mesh j.val

theorem mem_exponentCell_le_upper (S : CompactStart) (mesh : ℕ)
    {code : CellCode mesh} {x : ℝ}
    (hx : x ∈ exponentCell (S.epsilon : ℝ)
      (startCutoff S.start : ℝ) mesh code) :
    x ≤ cellUpper S mesh code := by
  cases code with
  | none =>
      change x = (startCutoff S.start : ℝ) at hx
      subst x
      exact le_rfl
  | some j =>
      exact hx.2.le

theorem cellLower_le_of_mem (S : CompactStart) (mesh : ℕ)
    {code : CellCode mesh} {x : ℝ}
    (hx : x ∈ exponentCell (S.epsilon : ℝ)
      (startCutoff S.start : ℝ) mesh code) :
    cellLower S mesh code ≤ x := by
  cases code with
  | none =>
      change x = (startCutoff S.start : ℝ) at hx
      subst x
      exact le_rfl
  | some j =>
      exact hx.1

def upperSlot (S : CompactStart) {mesh : ℕ}
    (code : CellCode mesh × Bool) : Slot :=
  ⟨cellUpper S mesh code.1, code.2⟩

def prefixSlots (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (code : Code mesh) : List Slot :=
  match rank.val with
  | 3 => [upperSlot S (code 0), upperSlot S (code 1),
      upperSlot S (code 2)]
  | 4 => [upperSlot S (code 0), upperSlot S (code 1),
      upperSlot S (code 2), upperSlot S (code 3)]
  | 5 => [upperSlot S (code 0), upperSlot S (code 1),
      upperSlot S (code 2), upperSlot S (code 3),
      upperSlot S (code 4)]
  | _ => []

-- The third action inherits the second historical cube; the fourth
-- action tests its own cube at the incoming third cap; rank five bypasses
-- a new cube exactly as in the paper.
def historicalGate (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (parent : ℝ) (code : Code mesh) : Prop :=
  if rank.val = 3 then
    cellUpper S mesh (code 0).1 + 3 * cellUpper S mesh (code 1).1 < parent
  else if rank.val = 4 then
    cellUpper S mesh (code 0).1 + cellUpper S mesh (code 1).1 +
      cellUpper S mesh (code 2).1 + 3 * cellUpper S mesh (code 3).1 < parent
  else True

def branchGates (S : CompactStart) {mesh : ℕ}
    (rank : Fin 6) (parent candidate : ℝ)
    (code : Code mesh) : Prop :=
  parent < candidate ∧ candidate ≤ topCap ∧
    historicalGate S rank parent code ∧
    strictSquareGates candidate 0
      ((prefixSlots S rank code).map Slot.exponent) ∧
    strictSquareGates candidate
      (selectedWord (prefixSlots S rank code)).sum
      (remainingWord (prefixSlots S rank code))

def checkedChoice (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6)
    (parent : ℝ) (code : Code mesh) : CapChoice :=
  match table.row rank (prefixCode rank.val code) with
  | none => .inherit 2
  | some (candidate, argument) =>
      if branchGates S rank parent candidate
          (prefixCode rank.val code) then
        .fresh candidate argument else .inherit 2

def checkedCap (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6)
    (parent : ℝ) (code : Code mesh) : ℝ :=
  (checkedChoice S table rank parent code).freeze parent

theorem checkedCap_monotone (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6)
    (parent : ℝ) (code : Code mesh) :
    parent ≤ checkedCap S table rank parent code := by
  unfold checkedCap checkedChoice
  cases hr : table.row rank (prefixCode rank.val code) with
  | none => simp [CapChoice.freeze]
  | some pair =>
      rcases pair with ⟨candidate, argument⟩
      by_cases hg : branchGates S rank parent candidate
          (prefixCode rank.val code)
      · simp [hg, CapChoice.freeze]
        exact hg.1.le
      · simp [hg, CapChoice.freeze]

theorem checkedCap_bounded (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6)
    (parent : ℝ) (code : Code mesh)
    (hparent : parent ≤ topCap) :
    checkedCap S table rank parent code ≤ topCap := by
  unfold checkedCap checkedChoice
  cases hr : table.row rank (prefixCode rank.val code) with
  | none => simpa [CapChoice.freeze] using hparent
  | some pair =>
      rcases pair with ⟨candidate, argument⟩
      by_cases hg : branchGates S rank parent candidate
          (prefixCode rank.val code)
      · simp [hg, CapChoice.freeze]
        exact hg.2.1
      · simpa [hg, CapChoice.freeze] using hparent

def cap3 (S : CompactStart) {mesh : ℕ} (table : BranchTable mesh)
    (rho : ℝ) (code : Code mesh) : ℝ :=
  checkedCap S table 3 (baselineCap rho) code

def cap4 (S : CompactStart) {mesh : ℕ} (table : BranchTable mesh)
    (rho : ℝ) (code : Code mesh) : ℝ :=
  checkedCap S table 4 (cap3 S table rho code) code

def cap5 (S : CompactStart) {mesh : ℕ} (table : BranchTable mesh)
    (rho : ℝ) (code : Code mesh) : ℝ :=
  checkedCap S table 5 (cap4 S table rho code) code

theorem cap_chain (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) (code : Code mesh)
    (hbase : baselineCap rho ≤ topCap) :
    baselineCap rho ≤ cap3 S table rho code ∧
      cap3 S table rho code ≤ cap4 S table rho code ∧
      cap4 S table rho code ≤ cap5 S table rho code ∧
      cap5 S table rho code ≤ topCap := by
  have h3 := checkedCap_monotone S table 3 (baselineCap rho) code
  have h3b := checkedCap_bounded S table 3 (baselineCap rho) code hbase
  have h4 := checkedCap_monotone S table 4 (cap3 S table rho code) code
  have h4b := checkedCap_bounded S table 4 (cap3 S table rho code) code h3b
  have h5 := checkedCap_monotone S table 5 (cap4 S table rho code) code
  have h5b := checkedCap_bounded S table 5 (cap4 S table rho code) code h4b
  exact ⟨h3,h4,h5,h5b⟩

def compactPlan (S : CompactStart) {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) : CapPlan 5 mesh :=
  ⟨fun rank code =>
    match rank.val with
    | 3 => checkedChoice S table 3 (baselineCap rho) code
    | 4 => checkedChoice S table 4 (cap3 S table rho code) code
    | 5 => checkedChoice S table 5 (cap4 S table rho code) code
    | _ => .inherit 2⟩

-- Rational box geometry matching the actual compact interval [epsilon,w].
def qGridPoint (S : CompactStart) (mesh index : ℕ) : ℚ :=
  S.epsilon + index *
    ((startCutoff S.start - S.epsilon) / (mesh + 1))

theorem qGridPoint_cast (S : CompactStart) (mesh index : ℕ) :
    (qGridPoint S mesh index : ℝ) =
      logPrimeMeshPoint (S.epsilon : ℝ)
        (startCutoff S.start : ℝ) mesh index := by
  unfold qGridPoint logPrimeMeshPoint logPrimeMeshStep
  push_cast
  ring

def qCellLo (S : CompactStart) (mesh : ℕ) : CellCode mesh → ℚ
  | none => startCutoff S.start
  | some j => qGridPoint S mesh j.val

theorem qCellLo_cast (S : CompactStart) (mesh : ℕ)
    (code : CellCode mesh) :
    (qCellLo S mesh code : ℝ) = cellLower S mesh code := by
  cases code with
  | none => rfl
  | some j => exact qGridPoint_cast S mesh j.val

def qCellHi (S : CompactStart) (mesh : ℕ) : CellCode mesh → ℚ
  | none => startCutoff S.start
  | some j => qGridPoint S mesh (j.val + 1)

theorem qCellHi_cast (S : CompactStart) (mesh : ℕ)
    (code : CellCode mesh) :
    (qCellHi S mesh code : ℝ) = cellUpper S mesh code := by
  cases code with
  | none => rfl
  | some j => exact qGridPoint_cast S mesh (j.val + 1)

def boxOfCode (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) :
    P2OriginalLowerBufferedAffineBoxes.RationalBox :=
  { lo := fun i => qCellLo S mesh (code i).1
    hi := fun i => qCellHi S mesh (code i).1 }

theorem inBox_of_exponentCodes (S : CompactStart) {mesh : ℕ}
    (code : Code mesh) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ exponentCell (S.epsilon : ℝ)
      (startCutoff S.start : ℝ) mesh (code i).1) :
    P2OriginalLowerBufferedAffineBoxes.inBox (boxOfCode S code) x := by
  intro i
  constructor
  · rw [qCellLo_cast]
    exact cellLower_le_of_mem S mesh (hx i)
  · rw [qCellHi_cast]
    exact mem_exponentCell_le_upper S mesh (hx i)

def boxedTable (S : CompactStart) {mesh : ℕ}
    (select : Fin 6 → Code mesh → Option
      P2OriginalLowerBufferedAffineBoxes.BranchData)
    (buffer : ℚ) : BranchTable mesh :=
  ⟨fun rank code =>
    (select rank (prefixCode rank.val code)).map (fun branch =>
      (P2OriginalLowerBufferedAffineBoxes.wholeBoxInfimum
          branch.1 branch.2.1
          (boxOfCode S (prefixCode rank.val code)) - buffer,
        branch.2.2))⟩

def boxedPlan (S : CompactStart) {mesh : ℕ}
    (select : Fin 6 → Code mesh → Option
      P2OriginalLowerBufferedAffineBoxes.BranchData)
    (buffer : ℚ) (rho : ℝ) : CapPlan 5 mesh :=
  compactPlan S (boxedTable S select buffer) rho

end
end ImbalancedChen.P2OriginalLowerCompactStartCapConstructor
