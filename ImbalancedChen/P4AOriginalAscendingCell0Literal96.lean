import ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal 96-row transcription of the immutable navigation cell 0. The
recorded finite LP navigation describes an open real cell. No half-open
physical carrier-to-rows bridge is supplied by that JSON or by the
cell-00 simplex witness. This module proves only the four named rows
used by the chronological slot-16 source action. It does not assume or
claim that a retained rough-prime prefix satisfies all 96 rows.
-/

namespace ImbalancedChen.P4AOriginalAscendingCell0Literal96
noncomputable section
open scoped Classical BigOperators
open P4AOriginalAscendingCell0AfterSeed7
open P4AOriginalSeed7Unequal15Literal

abbrev Point := Fin 8 → ℝ

def rows : Fin 96 → (String × (Fin 9 → ℚ)) :=
  ![
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
    ("old first history", ![57/64, -3, -3/2, -3/2, 0, 0, 0, 0, 0]),
    ("old H3 below L3", ![57/64, -1, -5/2, -9/2, 0, 0, 0, 0, 0]),
    ("old H5 below L3", ![57/64, -1, -5/2, -5/2, -1, -3, 0, 0, 0]),
    ("old H7 below L3", ![57/64, -1, -5/2, -5/2, -1, -1, -1, -3, 0]),
    ("old winner6 descending below ascending", ![-25/64, 0, 2, 2, 0, 0, 0, 0, 0]),
    ("old W below R6", ![75/256, 0, -3/2, -9/8, 0, 0, 0, 0, 0]),
    ("new cap improvement", ![-195313/500000, 1/2, 3/2, 3/2, 0, 0, 0, 0, 1/2]),
    ("new descending license buffered", ![25/64, -2, 0, 0, 0, 0, 0, 0, -2]),
    ("full square 1", ![499999/1000000, -3/2, 0, 0, 0, 0, 0, 0, 1/2]),
    ("full square 2", ![499999/1000000, -1/2, -2, 0, 0, 0, 0, 0, 1/2]),
    ("selected129 remaining square 2", ![499999/1000000, -1/2, -2, 0, 0, 0, 0, 0, -1/2]),
    ("full square 3", ![499999/1000000, -1/2, -1, -2, 0, 0, 0, 0, 1/2]),
    ("selected129 remaining square 3", ![499999/1000000, -1/2, -1, -2, 0, 0, 0, 0, -1/2]),
    ("full square 4", ![499999/1000000, -1/2, -1, -1, -2, 0, 0, 0, 1/2]),
    ("selected129 remaining square 4", ![499999/1000000, -1/2, -1, -1, -2, 0, 0, 0, -1/2]),
    ("full square 5", ![499999/1000000, -1/2, -1, -1, -1, -2, 0, 0, 1/2]),
    ("selected129 remaining square 5", ![499999/1000000, -1/2, -1, -1, -1, -2, 0, 0, -1/2]),
    ("full square 6", ![499999/1000000, -1/2, -1, -1, -1, -1, -2, 0, 1/2]),
    ("selected129 remaining square 6", ![499999/1000000, -1/2, -1, -1, -1, -1, -2, 0, -1/2]),
    ("full square 7", ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -2, 1/2]),
    ("selected129 remaining square 7", ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -2, -1/2]),
    ("full square 8", ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -1, -3/2]),
    ("old residual above t8", ![57/64, -1, -5/2, -5/2, -1, -1, -1, -1, -2]),
    ("new residual below3t8", ![-499999/1000000, 1/2, 1, 1, 1, 1, 1, 1, 7/2]),
    ("old subset 1 chosen plane 0 below R6", ![25/64, -1/2, -3/2, -3/2, 0, 0, 0, 0, 0]),
    ("old subset 2 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, 0, 0, 0, 0, 0]),
    ("old subset 3 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 0, 0, 0, 0, 0]),
    ("old subset 4 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, 0, 0, 0, 0, 0]),
    ("old subset 5 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 0, 0, 0, 0, 0]),
    ("old subset 7 chosen plane 1 below R6", ![0, 3/2, 0, 0, 0, 0, 0, 0, 0]),
    ("old subset 8 chosen plane 0 below R6", ![25/64, 0, -3/2, -3/2, -1/2, 0, 0, 0, 0]),
    ("old subset 9 chosen plane 1 below R6", ![0, 3/2, -3/2, -3/2, 3/2, 0, 0, 0, 0]),
    ("old subset 10 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, -1/2, 0, 0, 0, 0]),
    ("old subset 11 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 3/2, 0, 0, 0, 0]),
    ("old subset 12 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, -1/2, 0, 0, 0, 0]),
    ("old subset 13 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 3/2, 0, 0, 0, 0]),
    ("old subset 14 chosen plane 1 below R6", ![0, 0, 0, 0, 3/2, 0, 0, 0, 0]),
    ("old subset 15 chosen plane 1 below R6", ![0, 3/2, 0, 0, 3/2, 0, 0, 0, 0]),
    ("old subset 16 chosen plane 0 below R6", ![25/64, 0, -3/2, -3/2, 0, -1/2, 0, 0, 0]),
    ("old subset 17 chosen plane 1 below R6", ![0, 3/2, -3/2, -3/2, 0, 3/2, 0, 0, 0]),
    ("old subset 18 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, 0, -1/2, 0, 0, 0]),
    ("old subset 19 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 0, 3/2, 0, 0, 0]),
    ("old subset 20 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, 0, -1/2, 0, 0, 0]),
    ("old subset 21 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 0, 3/2, 0, 0, 0]),
    ("old subset 22 chosen plane 1 below R6", ![0, 0, 0, 0, 0, 3/2, 0, 0, 0]),
    ("old subset 23 chosen plane 1 below R6", ![0, 3/2, 0, 0, 0, 3/2, 0, 0, 0]),
    ("old subset 24 chosen plane 0 below R6", ![25/64, 0, -3/2, -3/2, -1/2, -1/2, 0, 0, 0]),
    ("old subset 25 chosen plane 1 below R6", ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 0, 0, 0]),
    ("old subset 26 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, -1/2, -1/2, 0, 0, 0]),
    ("old subset 27 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 3/2, 3/2, 0, 0, 0]),
    ("old subset 28 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0]),
    ("old subset 29 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 3/2, 3/2, 0, 0, 0]),
    ("old subset 30 chosen plane 1 below R6", ![0, 0, 0, 0, 3/2, 3/2, 0, 0, 0]),
    ("old subset 31 chosen plane 1 below R6", ![0, 3/2, 0, 0, 3/2, 3/2, 0, 0, 0]),
    ("old subset 32 chosen plane 0 below R6", ![25/64, 0, -3/2, -3/2, 0, 0, -1/2, 0, 0]),
    ("old subset 33 chosen plane 1 below R6", ![0, 3/2, -3/2, -3/2, 0, 0, 3/2, 0, 0]),
    ("old subset 34 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, 0, 0, -1/2, 0, 0]),
    ("old subset 35 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 0, 0, 3/2, 0, 0]),
    ("old subset 36 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, 0, 0, -1/2, 0, 0]),
    ("old subset 37 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 0, 0, 3/2, 0, 0]),
    ("old subset 38 chosen plane 1 below R6", ![0, 0, 0, 0, 0, 0, 3/2, 0, 0]),
    ("old subset 39 chosen plane 1 below R6", ![0, 3/2, 0, 0, 0, 0, 3/2, 0, 0]),
    ("old subset 40 chosen plane 0 below R6", ![25/64, 0, -3/2, -3/2, -1/2, 0, -1/2, 0, 0]),
    ("old subset 41 chosen plane 1 below R6", ![0, 3/2, -3/2, -3/2, 3/2, 0, 3/2, 0, 0]),
    ("old subset 42 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, -1/2, 0, -1/2, 0, 0]),
    ("old subset 43 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 3/2, 0, 3/2, 0, 0]),
    ("old subset 44 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, -1/2, 0, -1/2, 0, 0]),
    ("old subset 45 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 3/2, 0, 3/2, 0, 0]),
    ("old subset 46 chosen plane 1 below R6", ![0, 0, 0, 0, 3/2, 0, 3/2, 0, 0]),
    ("old subset 47 chosen plane 1 below R6", ![0, 3/2, 0, 0, 3/2, 0, 3/2, 0, 0]),
    ("old subset 48 chosen plane 0 below R6", ![25/64, 0, -3/2, -3/2, 0, -1/2, -1/2, 0, 0]),
    ("old subset 49 chosen plane 1 below R6", ![0, 3/2, -3/2, -3/2, 0, 3/2, 3/2, 0, 0]),
    ("old subset 50 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, 0, -1/2, -1/2, 0, 0]),
    ("old subset 51 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 0, 3/2, 3/2, 0, 0]),
    ("old subset 52 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, 0, -1/2, -1/2, 0, 0]),
    ("old subset 53 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 0, 3/2, 3/2, 0, 0]),
    ("old subset 54 chosen plane 1 below R6", ![0, 0, 0, 0, 0, 3/2, 3/2, 0, 0]),
    ("old subset 55 chosen plane 1 below R6", ![0, 3/2, 0, 0, 0, 3/2, 3/2, 0, 0]),
    ("old subset 56 chosen plane 0 below R6", ![25/64, 0, -3/2, -3/2, -1/2, -1/2, -1/2, 0, 0]),
    ("old subset 57 chosen plane 1 below R6", ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 3/2, 0, 0]),
    ("old subset 58 chosen plane 0 below R6", ![25/64, 0, -2, -3/2, -1/2, -1/2, -1/2, 0, 0]),
    ("old subset 59 chosen plane 1 below R6", ![0, 3/2, 0, -3/2, 3/2, 3/2, 3/2, 0, 0]),
    ("old subset 60 chosen plane 0 below R6", ![25/64, 0, -3/2, -2, -1/2, -1/2, -1/2, 0, 0]),
    ("old subset 61 chosen plane 1 below R6", ![0, 3/2, -3/2, 0, 3/2, 3/2, 3/2, 0, 0]),
    ("old subset 62 chosen plane 1 below R6", ![0, 0, 0, 0, 3/2, 3/2, 3/2, 0, 0]),
    ("old subset 63 chosen plane 1 below R6", ![0, 3/2, 0, 0, 3/2, 3/2, 3/2, 0, 0])
  ]

def sourceRows (t : Point) : Prop :=
  ∀ k : Fin 96, 0 < evalAffine (rows k).2 t

private theorem row14 : (rows 14).2 = cell0Row14 := by
  funext j
  fin_cases j <;> decide

private theorem row16 : (rows 16).2 = cell0Row16 := by
  funext j
  fin_cases j <;> decide

private theorem row17 : (rows 17).2 = cell0Row17 := by
  funext j
  fin_cases j <;> decide

private theorem row58 : (rows 58).2 = cell0Row58 := by
  funext j
  fin_cases j <;> decide

theorem sourceRows_core (t : Point) (h : sourceRows t) : Cell0Affine t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [row14] using h 14
  · simpa only [row16] using h 16
  · simpa only [row17] using h 17
  · simpa only [row58] using h 58

end
end ImbalancedChen.P4AOriginalAscendingCell0Literal96
