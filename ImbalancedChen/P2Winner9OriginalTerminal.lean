import ImbalancedChen.P2Winner9OriginalSourceGates

/-!
The 97 ordered literal half-spaces of the original eighth-stage
terminal `.remaining (.nine 11)`, global index 41. The tagged entries are
from `P4AOriginalSeed7Unequal15Literal.nineRows 11`. The comparison
below checks every coefficient against the formula-derived gates.
-/

namespace ImbalancedChen.P2Winner9OriginalTerminal

open scoped BigOperators
open Set MeasureTheory
open P2Winner9OriginalSourceGates P2Winner9PhysicalAffineTransfer

noncomputable section

def terminal41Rows : Fin 97 → String × (Fin 9 → ℚ) := ![
  ("largest below mu", ![25/128, -1, 0, 0, 0, 0, 0, 0, 0]),
  ("third original cutoff", ![-1/100, 0, 0, 1, 0, 0, 0, 0, 0]),
  ("eighth compact cutoff", ![-53/13824, 0, 0, 0, 0, 0, 0, 0, 1]),
  ("order 1", ![0, 1, -1, 0, 0, 0, 0, 0, 0]),
  ("order 2", ![0, 0, 1, -1, 0, 0, 0, 0, 0]),
  ("order 3", ![0, 0, 0, 1, -1, 0, 0, 0, 0]),
  ("order 4", ![0, 0, 0, 0, 1, -1, 0, 0, 0]),
  ("order 5", ![0, 0, 0, 0, 0, 1, -1, 0, 0]),
  ("order 6", ![0, 0, 0, 0, 0, 0, 1, -1, 0]),
  ("order 7", ![0, 0, 0, 0, 0, 0, 0, 1, -1]),
  ("old first history below B3", ![57/64, -3, -3/2, -3/2, 0, 0, 0, 0, 0]),
  ("old H3 below B3", ![57/64, -1, -5/2, -9/2, 0, 0, 0, 0, 0]),
  ("old H5 below B3", ![57/64, -1, -5/2, -5/2, -1, -3, 0, 0, 0]),
  ("old H7 below B3", ![57/64, -1, -5/2, -5/2, -1, -1, -1, -3, 0]),
  ("raw R6 strictly above raw B3", ![-25/64, 1/2, 3/2, 3/2, 1/2, 0, 0, 0, 0]),
  ("old winner9 ascending below descending", ![25/64, -2, 0, 0, -2, 0, 0, 0, 0]),
  ("third winner6 descending below ascending", ![-25/64, 0, 2, 2, 0, 0, 0, 0, 0]),
  ("old W below R6", ![-25/256, 1/2, 0, 3/8, 1/2, 0, 0, 0, 0]),
  ("new cap improvement", ![-1/1000000, -1/2, 1/2, 0, 0, 0, 0, 0, 1/2]),
  ("new descending license buffered", ![25/64, 0, -2, 0, -2, 0, 0, 0, -2]),
  ("full square 1", ![499999/1000000, -2, 1/2, 0, 1/2, 0, 0, 0, 1/2]),
  ("selected138 remaining square 1", ![499999/1000000, -2, -1/2, 0, -1/2, 0, 0, 0, -1/2]),
  ("full square 2", ![499999/1000000, -1, -3/2, 0, 1/2, 0, 0, 0, 1/2]),
  ("full square 3", ![499999/1000000, -1, -1/2, -2, 1/2, 0, 0, 0, 1/2]),
  ("selected138 remaining square 3", ![499999/1000000, -1, -1/2, -2, -1/2, 0, 0, 0, -1/2]),
  ("full square 4", ![499999/1000000, -1, -1/2, -1, -3/2, 0, 0, 0, 1/2]),
  ("full square 5", ![499999/1000000, -1, -1/2, -1, -1/2, -2, 0, 0, 1/2]),
  ("selected138 remaining square 5", ![499999/1000000, -1, -1/2, -1, -1/2, -2, 0, 0, -1/2]),
  ("full square 6", ![499999/1000000, -1, -1/2, -1, -1/2, -1, -2, 0, 1/2]),
  ("selected138 remaining square 6", ![499999/1000000, -1, -1/2, -1, -1/2, -1, -2, 0, -1/2]),
  ("full square 7", ![499999/1000000, -1, -1/2, -1, -1/2, -1, -1, -2, 1/2]),
  ("selected138 remaining square 7", ![499999/1000000, -1, -1/2, -1, -1/2, -1, -1, -2, -1/2]),
  ("full square 8", ![499999/1000000, -1, -1/2, -1, -1/2, -1, -1, -1, -3/2]),
  ("old R6 residual above t8", ![1/2, -1/2, -1, -1, -1/2, -1, -1, -1, -2]),
  ("new residual below3t8", ![-499999/1000000, 1, 1/2, 1, 1/2, 1, 1, 1, 7/2]),
  ("old subset 1 chosen plane 0 below R6", ![0, 0, 0, 0, 1/2, 0, 0, 0, 0]),
  ("old subset 2 chosen plane 0 below R6", ![0, 1/2, -1/2, 0, 1/2, 0, 0, 0, 0]),
  ("old subset 3 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 1/2, 0, 0, 0, 0]),
  ("old subset 4 chosen plane 0 below R6", ![0, 1/2, 0, -1/2, 1/2, 0, 0, 0, 0]),
  ("old subset 5 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 1/2, 0, 0, 0, 0]),
  ("old subset 6 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 1/2, 0, 0, 0, 0]),
  ("old subset 7 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 1/2, 0, 0, 0, 0]),
  ("old subset 8 chosen plane 0 below R6", ![0, 1/2, 0, 0, 0, 0, 0, 0, 0]),
  ("old subset 10 chosen plane 0 below R6", ![0, 1/2, -1/2, 0, 0, 0, 0, 0, 0]),
  ("old subset 11 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 2, 0, 0, 0, 0]),
  ("old subset 12 chosen plane 0 below R6", ![0, 1/2, 0, -1/2, 0, 0, 0, 0, 0]),
  ("old subset 13 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 2, 0, 0, 0, 0]),
  ("old subset 14 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 2, 0, 0, 0, 0]),
  ("old subset 15 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 2, 0, 0, 0, 0]),
  ("old subset 16 chosen plane 0 below R6", ![0, 1/2, 0, 0, 1/2, -1/2, 0, 0, 0]),
  ("old subset 17 chosen plane 0 below R6", ![0, 0, 0, 0, 1/2, -1/2, 0, 0, 0]),
  ("old subset 18 chosen plane 0 below R6", ![0, 1/2, -1/2, 0, 1/2, -1/2, 0, 0, 0]),
  ("old subset 19 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 1/2, 3/2, 0, 0, 0]),
  ("old subset 20 chosen plane 0 below R6", ![0, 1/2, 0, -1/2, 1/2, -1/2, 0, 0, 0]),
  ("old subset 21 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 1/2, 3/2, 0, 0, 0]),
  ("old subset 22 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 1/2, 3/2, 0, 0, 0]),
  ("old subset 23 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 1/2, 3/2, 0, 0, 0]),
  ("old subset 24 chosen plane 0 below R6", ![0, 1/2, 0, 0, 0, -1/2, 0, 0, 0]),
  ("old subset 25 chosen plane 1 below R6", ![-25/64, 2, 0, 0, 2, 3/2, 0, 0, 0]),
  ("old subset 26 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 0, 2, 3/2, 0, 0, 0]),
  ("old subset 27 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 2, 3/2, 0, 0, 0]),
  ("old subset 28 chosen plane 1 below R6", ![-25/64, 1/2, 0, 3/2, 2, 3/2, 0, 0, 0]),
  ("old subset 29 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 2, 3/2, 0, 0, 0]),
  ("old subset 30 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 2, 3/2, 0, 0, 0]),
  ("old subset 31 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 2, 3/2, 0, 0, 0]),
  ("old subset 32 chosen plane 0 below R6", ![0, 1/2, 0, 0, 1/2, 0, -1/2, 0, 0]),
  ("old subset 33 chosen plane 0 below R6", ![0, 0, 0, 0, 1/2, 0, -1/2, 0, 0]),
  ("old subset 34 chosen plane 0 below R6", ![0, 1/2, -1/2, 0, 1/2, 0, -1/2, 0, 0]),
  ("old subset 35 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 1/2, 0, 3/2, 0, 0]),
  ("old subset 36 chosen plane 0 below R6", ![0, 1/2, 0, -1/2, 1/2, 0, -1/2, 0, 0]),
  ("old subset 37 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 1/2, 0, 3/2, 0, 0]),
  ("old subset 38 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 1/2, 0, 3/2, 0, 0]),
  ("old subset 39 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 1/2, 0, 3/2, 0, 0]),
  ("old subset 40 chosen plane 0 below R6", ![0, 1/2, 0, 0, 0, 0, -1/2, 0, 0]),
  ("old subset 41 chosen plane 1 below R6", ![-25/64, 2, 0, 0, 2, 0, 3/2, 0, 0]),
  ("old subset 42 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 0, 2, 0, 3/2, 0, 0]),
  ("old subset 43 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 2, 0, 3/2, 0, 0]),
  ("old subset 44 chosen plane 1 below R6", ![-25/64, 1/2, 0, 3/2, 2, 0, 3/2, 0, 0]),
  ("old subset 45 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 2, 0, 3/2, 0, 0]),
  ("old subset 46 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 2, 0, 3/2, 0, 0]),
  ("old subset 47 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 2, 0, 3/2, 0, 0]),
  ("old subset 48 chosen plane 0 below R6", ![0, 1/2, 0, 0, 1/2, -1/2, -1/2, 0, 0]),
  ("old subset 49 chosen plane 1 below R6", ![-25/64, 2, 0, 0, 1/2, 3/2, 3/2, 0, 0]),
  ("old subset 50 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 0, 1/2, 3/2, 3/2, 0, 0]),
  ("old subset 51 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 1/2, 3/2, 3/2, 0, 0]),
  ("old subset 52 chosen plane 1 below R6", ![-25/64, 1/2, 0, 3/2, 1/2, 3/2, 3/2, 0, 0]),
  ("old subset 53 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 1/2, 3/2, 3/2, 0, 0]),
  ("old subset 54 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 1/2, 3/2, 3/2, 0, 0]),
  ("old subset 55 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 1/2, 3/2, 3/2, 0, 0]),
  ("old subset 56 chosen plane 0 below R6", ![0, 1/2, 0, 0, 0, -1/2, -1/2, 0, 0]),
  ("old subset 57 chosen plane 1 below R6", ![-25/64, 2, 0, 0, 2, 3/2, 3/2, 0, 0]),
  ("old subset 58 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 0, 2, 3/2, 3/2, 0, 0]),
  ("old subset 59 chosen plane 1 below R6", ![-25/64, 2, 3/2, 0, 2, 3/2, 3/2, 0, 0]),
  ("old subset 60 chosen plane 1 below R6", ![-25/64, 1/2, 0, 3/2, 2, 3/2, 3/2, 0, 0]),
  ("old subset 61 chosen plane 1 below R6", ![-25/64, 2, 0, 3/2, 2, 3/2, 3/2, 0, 0]),
  ("old subset 62 chosen plane 1 below R6", ![-25/64, 1/2, 3/2, 3/2, 2, 3/2, 3/2, 0, 0]),
  ("old subset 63 chosen plane 1 below R6", ![-25/64, 2, 3/2, 3/2, 2, 3/2, 3/2, 0, 0])
]

def terminalGateIndex : Gate → Fin 97
  | .largest => 0
  | .third => 1
  | .eighth => 2
  | .order j => ⟨3 + j.val, by omega⟩
  | .history j => ⟨10 + j.val, by omega⟩
  | .minorantGap => 14
  | .winnerSide => 15
  | .thirdSide => 16
  | .oldW => 17
  | .improvement => 18
  | .selectedDescending => 19
  | .fullSquare j => ![20, 22, 23, 25, 26, 28, 30, 32] j
  | .complementSquare j => ![21, 0, 24, 0, 27, 29, 31, 0] j.val
  | .oldResidual => 33
  | .newResidual => 34
  | .oldSubset m => ⟨if m.val.val < 8 then 35 + m.val.val else 34 + m.val.val, by
      have hm := m.val.isLt
      split <;> omega⟩

def terminal41Gate (j : Fin 97) : Row :=
  ⟨(terminal41Rows j).2 0, fun k => (terminal41Rows j).2 k.succ⟩

private def terminalGateAt : Fin 97 → Gate := ![
  .largest, .third, .eighth, .order 0, .order 1,
  .order 2, .order 3, .order 4, .order 5, .order 6,
  .history 0, .history 1, .history 2, .history 3, .minorantGap,
  .winnerSide, .thirdSide, .oldW, .improvement, .selectedDescending,
  .fullSquare 0, .complementSquare ⟨0, by decide⟩, .fullSquare 1, .fullSquare 2, .complementSquare ⟨2, by decide⟩,
  .fullSquare 3, .fullSquare 4, .complementSquare ⟨4, by decide⟩, .fullSquare 5, .complementSquare ⟨5, by decide⟩,
  .fullSquare 6, .complementSquare ⟨6, by decide⟩, .fullSquare 7, .oldResidual, .newResidual,
  .oldSubset ⟨0, by decide⟩, .oldSubset ⟨1, by decide⟩, .oldSubset ⟨2, by decide⟩, .oldSubset ⟨3, by decide⟩, .oldSubset ⟨4, by decide⟩,
  .oldSubset ⟨5, by decide⟩, .oldSubset ⟨6, by decide⟩, .oldSubset ⟨7, by decide⟩, .oldSubset ⟨9, by decide⟩, .oldSubset ⟨10, by decide⟩,
  .oldSubset ⟨11, by decide⟩, .oldSubset ⟨12, by decide⟩, .oldSubset ⟨13, by decide⟩, .oldSubset ⟨14, by decide⟩, .oldSubset ⟨15, by decide⟩,
  .oldSubset ⟨16, by decide⟩, .oldSubset ⟨17, by decide⟩, .oldSubset ⟨18, by decide⟩, .oldSubset ⟨19, by decide⟩, .oldSubset ⟨20, by decide⟩,
  .oldSubset ⟨21, by decide⟩, .oldSubset ⟨22, by decide⟩, .oldSubset ⟨23, by decide⟩, .oldSubset ⟨24, by decide⟩, .oldSubset ⟨25, by decide⟩,
  .oldSubset ⟨26, by decide⟩, .oldSubset ⟨27, by decide⟩, .oldSubset ⟨28, by decide⟩, .oldSubset ⟨29, by decide⟩, .oldSubset ⟨30, by decide⟩,
  .oldSubset ⟨31, by decide⟩, .oldSubset ⟨32, by decide⟩, .oldSubset ⟨33, by decide⟩, .oldSubset ⟨34, by decide⟩, .oldSubset ⟨35, by decide⟩,
  .oldSubset ⟨36, by decide⟩, .oldSubset ⟨37, by decide⟩, .oldSubset ⟨38, by decide⟩, .oldSubset ⟨39, by decide⟩, .oldSubset ⟨40, by decide⟩,
  .oldSubset ⟨41, by decide⟩, .oldSubset ⟨42, by decide⟩, .oldSubset ⟨43, by decide⟩, .oldSubset ⟨44, by decide⟩, .oldSubset ⟨45, by decide⟩,
  .oldSubset ⟨46, by decide⟩, .oldSubset ⟨47, by decide⟩, .oldSubset ⟨48, by decide⟩, .oldSubset ⟨49, by decide⟩, .oldSubset ⟨50, by decide⟩,
  .oldSubset ⟨51, by decide⟩, .oldSubset ⟨52, by decide⟩, .oldSubset ⟨53, by decide⟩, .oldSubset ⟨54, by decide⟩, .oldSubset ⟨55, by decide⟩,
  .oldSubset ⟨56, by decide⟩, .oldSubset ⟨57, by decide⟩, .oldSubset ⟨58, by decide⟩, .oldSubset ⟨59, by decide⟩, .oldSubset ⟨60, by decide⟩,
  .oldSubset ⟨61, by decide⟩, .oldSubset ⟨62, by decide⟩
]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem terminalGateAt_index : ∀ i : Fin 97, terminalGateIndex (terminalGateAt i) = i := by
  decide +kernel

theorem terminalGateIndex_surjective : Function.Surjective terminalGateIndex :=
  fun j => ⟨terminalGateAt j, terminalGateAt_index j⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem terminal41_gate_fields (g : Gate) :
    (terminal41Gate (terminalGateIndex g)).constant = (gate g).constant ∧
      ∀ j : Fin 8, (terminal41Gate (terminalGateIndex g)).coefficient j =
        (gate g).coefficient j := by
  cases g with
  | order j =>
      revert j
      decide +kernel
  | history j =>
      revert j
      decide +kernel
  | oldSubset m =>
      rcases m with ⟨m, hm⟩
      revert m
      decide +kernel
  | fullSquare j =>
      revert j
      decide +kernel
  | complementSquare j =>
      rcases j with ⟨j, hj⟩
      revert j
      decide +kernel
  | _ => decide +kernel

theorem terminal41_gate_eq (g : Gate) : terminal41Gate (terminalGateIndex g) = gate g := by
  obtain ⟨hc, hf⟩ := terminal41_gate_fields g
  exact congrArg₂ Row.mk hc (funext hf)

def terminal41Source : Set Ambient :=
  {x | ∀ j : Fin 97, 0 < (terminal41Gate j).eval x}

theorem terminal41_source_eq : terminal41Source = originalPhysicalSource := by
  ext x
  change (∀ j : Fin 97, 0 < (terminal41Gate j).eval x) ↔
    (∀ g : Gate, 0 < (gate g).eval x)
  constructor
  · intro h g
    simpa only [terminal41_gate_eq] using h (terminalGateIndex g)
  · intro h j
    obtain ⟨g, rfl⟩ := terminalGateIndex_surjective j
    simpa only [terminal41_gate_eq] using h g

def terminal41Comparison (t : Ambient) : ℝ := (1 + (t 0 + t 3)) / 2

def terminal41NewCap (t : Ambient) : ℝ :=
  (1 + (t 1 + t 3 + t 7)) / 2 - 1 / 1000000

def terminal41Kernel (t : Ambient) : ℝ :=
  4 * (terminal41NewCap t - terminal41Comparison t) /
    ((terminal41Comparison t - ∑ j : Fin 8, t j) *
      (terminal41NewCap t - ∑ j : Fin 8, t j) * ∏ j : Fin 8, t j)

theorem terminal41_kernel_eq (t : Ambient) :
    terminal41Kernel t = physicalUpperIntegrand t := by
  have hf : (∏ j : Fin 10, physicalFactor j t) =
      (physicalR t - coordinateSum t) * (physicalM t - coordinateSum t) *
        ∏ j : Fin 8, t j := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have hone : (0 : Fin 9).succ = (1 : Fin 10) := rfl
    simp only [hone, physicalFactor_zero, physicalFactor_one, physicalFactor_succ_succ]
    ring
  have hr : terminal41Comparison t = physicalR t := by
    unfold terminal41Comparison physicalR
    ring
  have hm : terminal41NewCap t = physicalM t := by
    unfold terminal41NewCap physicalM
    ring
  rw [physicalUpperIntegrand, hf, physicalGap, terminal41Kernel, hr, hm, coordinateSum]

def terminal41Integral : ℝ := ∫ t in terminal41Source, terminal41Kernel t

theorem terminal41_integral_eq :
    terminal41Integral = ∫ t in originalPhysicalSource, physicalUpperIntegrand t := by
  simp only [terminal41Integral, terminal41_source_eq, terminal41_kernel_eq]

end

end ImbalancedChen.P2Winner9OriginalTerminal
