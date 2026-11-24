import ImbalancedChen.P2PhysicalIncomingPrefixCells
import ImbalancedChen.P2EnhancedLowerPhysicalNode

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Finite selected-cap constructor for the original lower chronological
-- ranks. Literal certified branch rows must be supplied independently.
-- A branch is frozen only after its finite endpoint gates have been checked.

namespace ImbalancedChen.P2OriginalLowerSelectedCapConstructor

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2EnhancedLowerPhysicalNode

def a : ℝ := 417 / 5000
def h : ℝ := 19 / 125
def nu : ℝ := 249 / 448
def Lambda : ℝ := 153 / 256
def seedCap (rho : ℝ) : ℝ := nu - rho

abbrev Code (mesh : ℕ) := Fin 5 → CellCode mesh × Bool

-- The physical code pads unused slots by (none,false). Masking is essential:
-- a later prime can neither alter a parent cap nor choose its branch label.
def prefixCode {mesh : ℕ} (rank : ℕ) (code : Code mesh) : Code mesh :=
  fun i => if i.val < rank then code i else (none,false)

theorem prefixCode_future_invariant {mesh : ℕ} {rank : ℕ}
    {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < rank → code₁ i = code₂ i) :
    prefixCode rank code₁ = prefixCode rank code₂ := by
  funext i
  by_cases hi : i.val < rank
  · simp [prefixCode, hi, heq i hi]
  · simp [prefixCode, hi]

def cellUpper (mesh : ℕ) : CellCode mesh → ℝ
  | none => h
  | some j => logPrimeMeshPoint a h mesh (j.val + 1)

def upperSlot {mesh : ℕ} (code : CellCode mesh × Bool) : Slot :=
  ⟨cellUpper mesh code.1, code.2⟩

def prefixSlots {mesh : ℕ} (rank : Fin 6) (code : Code mesh) : List Slot :=
  match rank.val with
  | 3 => [upperSlot (code 0), upperSlot (code 1), upperSlot (code 2)]
  | 4 => [upperSlot (code 0), upperSlot (code 1),
      upperSlot (code 2), upperSlot (code 3)]
  | 5 => [upperSlot (code 0), upperSlot (code 1),
      upperSlot (code 2), upperSlot (code 3), upperSlot (code 4)]
  | _ => []

def strictSquareGates (cap T : ℝ) : List ℝ → Prop
  | [] => True
  | x :: xs => T + 2*x < cap ∧ strictSquareGates cap (T+x) xs

theorem strictSquareGates_sound (cap T : ℝ) (xs : List ℝ)
    (hgates : strictSquareGates cap T xs) : SquareGates cap T xs := by
  induction xs generalizing T with
  | nil => trivial
  | cons x rest ih =>
      rcases hgates with ⟨hfirst,hrest⟩
      exact ⟨hfirst.le, ih (T+x) hrest⟩

-- At rank three the historical even test is the second cube. At rank four
-- the fourth cube is tested against the incoming third cap. Rank five is
-- odd and has no new cube test; its full square is checked separately.
def historicalGate {mesh : ℕ} (rank : Fin 6) (parent : ℝ)
    (code : Code mesh) : Prop :=
  if rank.val = 3 then
    cellUpper mesh (code 0).1 + 3 * cellUpper mesh (code 1).1 < parent
  else if rank.val = 4 then
    cellUpper mesh (code 0).1 + cellUpper mesh (code 1).1 +
      cellUpper mesh (code 2).1 + 3 * cellUpper mesh (code 3).1 < parent
  else True

-- This finite check uses the whole cell's upper endpoints, including each
-- original selected bit. It preserves the strict compact margins required
-- before the physical coefficient is compiled.
def branchGates {mesh : ℕ} (rank : Fin 6) (parent candidate : ℝ)
    (code : Code mesh) : Prop :=
  parent < candidate ∧ candidate ≤ Lambda ∧
    historicalGate rank parent code ∧
    strictSquareGates candidate 0 ((prefixSlots rank code).map Slot.exponent) ∧
    strictSquareGates candidate (selectedWord (prefixSlots rank code)).sum
      (remainingWord (prefixSlots rank code))

theorem branchGates_closed_squares {mesh : ℕ}
    (rank : Fin 6) (parent candidate : ℝ) (code : Code mesh)
    (hgates : branchGates rank parent candidate code) :
    SquareGates candidate 0 ((prefixSlots rank code).map Slot.exponent) ∧
      SquareGates candidate (selectedWord (prefixSlots rank code)).sum
        (remainingWord (prefixSlots rank code)) := by
  exact ⟨strictSquareGates_sound candidate 0 _ hgates.2.2.2.1,
    strictSquareGates_sound candidate _ _ hgates.2.2.2.2⟩

-- Rows may be read from an exact rational certificate. They are primitive
-- proposed branch endpoints and arguments, not a proof of selected gains.
structure BranchTable (mesh : ℕ) where
  row : Fin 6 → Code mesh → Option (ℚ × ℚ)

def checkedChoice {mesh : ℕ} (table : BranchTable mesh)
    (rank : Fin 6) (parent : ℝ) (code : Code mesh) : CapChoice :=
  match table.row rank (prefixCode rank.val code) with
  | none => .inherit 2
  | some (candidate, argument) =>
      if branchGates rank parent candidate (prefixCode rank.val code) then
        .fresh candidate argument else .inherit 2

def checkedCap {mesh : ℕ} (table : BranchTable mesh)
    (rank : Fin 6) (parent : ℝ) (code : Code mesh) : ℝ :=
  (checkedChoice table rank parent code).freeze parent

theorem checkedChoice_prefix_invariant {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6) (parent : ℝ)
    {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < rank.val → code₁ i = code₂ i) :
    checkedChoice table rank parent code₁ =
      checkedChoice table rank parent code₂ := by
  have hp := prefixCode_future_invariant heq
  simp only [checkedChoice, hp]

theorem checkedCap_prefix_invariant {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6) (parent : ℝ)
    {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < rank.val → code₁ i = code₂ i) :
    checkedCap table rank parent code₁ =
      checkedCap table rank parent code₂ := by
  simp only [checkedCap, checkedChoice_prefix_invariant table rank parent heq]

theorem checkedChoice_fresh_has_finite_gates {mesh : ℕ}
    (table : BranchTable mesh) (rank : Fin 6) (parent : ℝ)
    (code : Code mesh)
    (hfresh : ∃ c s : ℝ, checkedChoice table rank parent code = .fresh c s) :
    ∃ c s : ℚ,
      table.row rank (prefixCode rank.val code) = some (c,s) ∧
      branchGates rank parent c (prefixCode rank.val code) := by
  rcases hfresh with ⟨c,s,hfresh⟩
  cases hr : table.row rank (prefixCode rank.val code) with
  | none => simp [checkedChoice, hr] at hfresh
  | some pair =>
      rcases pair with ⟨candidate, argument⟩
      by_cases hg : branchGates rank parent candidate (prefixCode rank.val code)
      · exact ⟨candidate, argument, hr, hg⟩
      · simp [checkedChoice, hr, hg] at hfresh

theorem checkedCap_monotone {mesh : ℕ} (table : BranchTable mesh)
    (rank : Fin 6) (parent : ℝ) (code : Code mesh) :
    parent ≤ checkedCap table rank parent code := by
  unfold checkedCap checkedChoice
  cases hr : table.row rank (prefixCode rank.val code) with
  | none => simp [CapChoice.freeze]
  | some pair =>
      rcases pair with ⟨candidate, argument⟩
      by_cases hg : branchGates rank parent candidate (prefixCode rank.val code)
      · simp [hg, CapChoice.freeze]
        exact hg.1.le
      · simp [hg, CapChoice.freeze]

theorem checkedCap_bounded {mesh : ℕ} (table : BranchTable mesh)
    (rank : Fin 6) (parent : ℝ) (code : Code mesh)
    (hparent : parent ≤ Lambda) :
    checkedCap table rank parent code ≤ Lambda := by
  unfold checkedCap checkedChoice
  cases hr : table.row rank (prefixCode rank.val code) with
  | none => simpa [CapChoice.freeze] using hparent
  | some pair =>
      rcases pair with ⟨candidate, argument⟩
      by_cases hg : branchGates rank parent candidate (prefixCode rank.val code)
      · simp [hg, CapChoice.freeze]
        exact hg.2.1
      · simpa [hg, CapChoice.freeze] using hparent

def cap3 {mesh : ℕ} (table : BranchTable mesh) (rho : ℝ)
    (code : Code mesh) : ℝ :=
  checkedCap table 3 (seedCap rho) code

def cap4 {mesh : ℕ} (table : BranchTable mesh) (rho : ℝ)
    (code : Code mesh) : ℝ :=
  checkedCap table 4 (cap3 table rho code) code

def cap5 {mesh : ℕ} (table : BranchTable mesh) (rho : ℝ)
    (code : Code mesh) : ℝ :=
  checkedCap table 5 (cap4 table rho code) code

theorem cap3_prefix_invariant {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < 3 → code₁ i = code₂ i) :
    cap3 table rho code₁ = cap3 table rho code₂ :=
  checkedCap_prefix_invariant table 3 (seedCap rho) heq

theorem cap4_prefix_invariant {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < 4 → code₁ i = code₂ i) :
    cap4 table rho code₁ = cap4 table rho code₂ := by
  have h3 : cap3 table rho code₁ = cap3 table rho code₂ :=
    cap3_prefix_invariant table rho (fun i hi => heq i (by omega))
  unfold cap4
  rw [h3]
  exact checkedCap_prefix_invariant table 4 (cap3 table rho code₂) heq

theorem cap_chain {mesh : ℕ} (table : BranchTable mesh) (rho : ℝ)
    (code : Code mesh) (hseed : seedCap rho ≤ Lambda) :
    seedCap rho ≤ cap3 table rho code ∧
      cap3 table rho code ≤ cap4 table rho code ∧
      cap4 table rho code ≤ cap5 table rho code ∧
      cap5 table rho code ≤ Lambda := by
  have h3 := checkedCap_monotone table 3 (seedCap rho) code
  have h3b := checkedCap_bounded table 3 (seedCap rho) code hseed
  have h4 := checkedCap_monotone table 4 (cap3 table rho code) code
  have h4b := checkedCap_bounded table 4 (cap3 table rho code) code h3b
  have h5 := checkedCap_monotone table 5 (cap4 table rho code) code
  have h5b := checkedCap_bounded table 5 (cap4 table rho code) code h4b
  exact ⟨h3,h4,h5,h5b⟩

-- The same code-level plan is used for every actual N. Its selected rows
-- still require a separate exact extraction from the original certificate.
def selectedPlan {mesh : ℕ} (table : BranchTable mesh)
    (rho : ℝ) : CapPlan 5 mesh :=
  ⟨fun rank code =>
    match rank.val with
    | 3 => checkedChoice table 3 (seedCap rho) code
    | 4 => checkedChoice table 4 (cap3 table rho code) code
    | 5 => checkedChoice table 5 (cap4 table rho code) code
    | _ => .inherit 2⟩

theorem selectedPlan_third_future_invariant {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < 3 → code₁ i = code₂ i) :
    (selectedPlan table rho).choose 3 code₁ =
      (selectedPlan table rho).choose 3 code₂ := by
  exact checkedChoice_prefix_invariant table 3 (seedCap rho) heq

theorem selectedPlan_fourth_future_invariant {mesh : ℕ}
    (table : BranchTable mesh) (rho : ℝ) {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < 4 → code₁ i = code₂ i) :
    (selectedPlan table rho).choose 4 code₁ =
      (selectedPlan table rho).choose 4 code₂ := by
  have h3 : cap3 table rho code₁ = cap3 table rho code₂ :=
    cap3_prefix_invariant table rho (fun i hi => heq i (by omega))
  change checkedChoice table 4 (cap3 table rho code₁) code₁ =
    checkedChoice table 4 (cap3 table rho code₂) code₂
  rw [h3]
  exact checkedChoice_prefix_invariant table 4 (cap3 table rho code₂) heq

end
end ImbalancedChen.P2OriginalLowerSelectedCapConstructor
