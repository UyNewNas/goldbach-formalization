import ImbalancedChen.P2OriginalLowerCompactStartCapConstructor
import ImbalancedChen.P2FiniteActiveBranchBuffer

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- A finite nested prefix partition and stagewise common-buffer constructor.
-- The finite licensed chamber cover, its mask witness, and strict primitive
-- rational gate gaps are explicit inputs. No selected integral or final
-- lower estimate is a premise or conclusion.

namespace ImbalancedChen.P2OriginalLowerNestedBufferedStages

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells
open P2OriginalLowerSelectedCapConstructor
open P2OriginalLowerCompactStartCapConstructor

-- One compact cutoff works for both original lower starts. The cutoff is
-- fixed before the finite mesh and before the arithmetic target N grows.
structure JointCompactStarts where
  epsilon : ℚ
  epsilon_pos : 0 < epsilon
  epsilon_lt_first : epsilon < 417 / 5000

def JointCompactStarts.at (J : JointCompactStarts) (i : Fin 2) : CompactStart :=
  if i.val = 0 then
    ⟨.first, J.epsilon, J.epsilon_pos, J.epsilon_lt_first⟩
  else
    ⟨.second, J.epsilon, J.epsilon_pos,
      lt_trans J.epsilon_lt_first (by norm_num)⟩

-- A rank-r cell is the first r coded exponent/mark slots. Its higher
-- coordinate refinements cannot change this parent cell.
theorem prefixCode_nested {mesh : ℕ} (r s : ℕ) (hrs : r ≤ s)
    (code : Code mesh) :
    prefixCode r (prefixCode s code) = prefixCode r code := by
  funext i
  by_cases hir : i.val < r
  · have his : i.val < s := lt_of_lt_of_le hir hrs
    simp [prefixCode, hir, his]
  · simp [prefixCode, hir]

def children {mesh : ℕ} (rank : ℕ) (parent : Code mesh) :
    Finset (Code mesh) :=
  Finset.univ.filter (fun code => prefixCode rank code = parent)

@[simp] theorem mem_children {mesh : ℕ} (rank : ℕ)
    (parent child : Code mesh) :
    child ∈ children rank parent ↔ prefixCode rank child = parent := by
  simp [children]

theorem child_parent_three_of_four {mesh : ℕ}
    (parent4 child5 : Code mesh)
    (hchild : child5 ∈ children 4 parent4) :
    prefixCode 3 child5 = prefixCode 3 parent4 := by
  have h4 := (mem_children 4 parent4 child5).mp hchild
  calc
    prefixCode 3 child5 = prefixCode 3 (prefixCode 4 child5) :=
      (prefixCode_nested 3 4 (by omega) child5).symm
    _ = prefixCode 3 parent4 := by rw [h4]

-- The active set is finite because it is a Finset of the two starts and
-- their finite physical code cells. Its parent/gate/endpoint quantities
-- are rational primitive geometry after the preceding cap is frozen.
structure StageSpec (mesh : ℕ) (rank : Fin 6) where
  active : Finset (Fin 2 × Code mesh)
  parent : Fin 2 × Code mesh → ℚ
  gate : Fin 2 × Code mesh → ℚ
  endpoint : Fin 2 × Code mesh → ℚ
  argument : Fin 2 × Code mesh → ℚ
  parent_le_gate : ∀ cell ∈ active, parent cell ≤ gate cell
  strict_gap : ∀ cell ∈ active, gate cell < endpoint cell

def stageRow {mesh : ℕ} {rank : Fin 6}
    (stage : StageSpec mesh rank) (buffer : ℚ)
    (start : Fin 2) (code : Code mesh) : Option (ℚ × ℚ) :=
  let cell := (start, prefixCode rank.val code)
  if cell ∈ stage.active then
    some (stage.endpoint cell - buffer, stage.argument cell)
  else none

theorem stageRow_inherit {mesh : ℕ} {rank : Fin 6}
    (stage : StageSpec mesh rank) (buffer : ℚ)
    (start : Fin 2) (code : Code mesh)
    (hinactive : (start, prefixCode rank.val code) ∉ stage.active) :
    stageRow stage buffer start code = none := by
  simp [stageRow, hinactive]

theorem stageRow_parent_invariant {mesh : ℕ} {rank : Fin 6}
    (stage : StageSpec mesh rank) (buffer : ℚ)
    (start : Fin 2) {code₁ code₂ : Code mesh}
    (heq : ∀ i : Fin 5, i.val < rank.val → code₁ i = code₂ i) :
    stageRow stage buffer start code₁ =
      stageRow stage buffer start code₂ := by
  have hp := prefixCode_future_invariant heq
  simp only [stageRow, hp]

-- Astra's finite common-buffer lemma is applied to every active cell at
-- one rank after its rational parent has been frozen. Inactive cells keep
-- the inherit label exactly; active candidate caps retain strict gaps.
theorem exists_stage_buffer {mesh : ℕ} {rank : Fin 6}
    (stage : StageSpec mesh rank) (eta : ℚ) (heta : 0 < eta) :
    ∃ buffer : ℚ, 0 < buffer ∧ buffer < eta ∧
      (∀ cell ∈ stage.active,
        stage.parent cell < stage.endpoint cell - buffer ∧
        stage.gate cell < stage.endpoint cell - buffer ∧
        stage.endpoint cell - buffer < stage.endpoint cell) := by
  obtain ⟨buffer, hb, hbe, _, hactive⟩ :=
    P2FiniteActiveBranchBuffer.exists_buffered_caps_preserving_inherit
      stage.active stage.parent stage.gate stage.endpoint
      stage.parent_le_gate stage.strict_gap eta heta
  refine ⟨buffer, hb, hbe, ?_⟩
  intro cell hcell
  have h := hactive cell hcell
  simpa [P2FiniteActiveBranchBuffer.bufferedCap, hcell] using
    And.intro h.1 (And.intro h.2.1 h.2.2.1)

-- The three stages are chosen in chronological order. A stage-four/five
-- primitive parent quantity must be supplied from the already frozen
-- preceding stage; this datatype does not claim such data were serialized.
structure JointStageData (mesh : ℕ) where
  third : StageSpec mesh 3
  fourth : StageSpec mesh 4
  fifth : StageSpec mesh 5

def rowsForStart {mesh : ℕ} (stages : JointStageData mesh)
    (buffer3 buffer4 buffer5 : ℚ) (start : Fin 2) :
    BranchTable mesh :=
  ⟨fun rank code =>
    match rank.val with
    | 3 => stageRow stages.third buffer3 start code
    | 4 => stageRow stages.fourth buffer4 start code
    | 5 => stageRow stages.fifth buffer5 start code
    | _ => none⟩

theorem exists_joint_buffered_rows {mesh : ℕ}
    (stages : JointStageData mesh) (eta : ℚ) (heta : 0 < eta) :
    ∃ buffer3 buffer4 buffer5 : ℚ,
      0 < buffer3 ∧ buffer3 < eta ∧
      0 < buffer4 ∧ buffer4 < eta ∧
      0 < buffer5 ∧ buffer5 < eta ∧
      (∀ start : Fin 2, ∃ table : BranchTable mesh,
        table = rowsForStart stages buffer3 buffer4 buffer5 start) := by
  obtain ⟨buffer3,h3,h3eta,_⟩ := exists_stage_buffer stages.third eta heta
  obtain ⟨buffer4,h4,h4eta,_⟩ := exists_stage_buffer stages.fourth eta heta
  obtain ⟨buffer5,h5,h5eta,_⟩ := exists_stage_buffer stages.fifth eta heta
  exact ⟨buffer3,buffer4,buffer5,h3,h3eta,h4,h4eta,h5,h5eta,
    fun start => ⟨rowsForStart stages buffer3 buffer4 buffer5 start,rfl⟩⟩

def planForStart {mesh : ℕ} (J : JointCompactStarts)
    (stages : JointStageData mesh) (buffer3 buffer4 buffer5 : ℚ)
    (rho : ℝ) (start : Fin 2) : CapPlan 5 mesh :=
  compactPlan (J.at start)
    (rowsForStart stages buffer3 buffer4 buffer5 start) rho

end
end ImbalancedChen.P2OriginalLowerNestedBufferedStages
