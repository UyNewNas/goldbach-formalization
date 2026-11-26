import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
noncomputable section
open scoped Classical BigOperators
abbrev Point := Fin 8 → ℝ
def oldSum (m : ℕ) (t : Point) := ∑ j ∈ (Finset.univ.filter (fun j : Fin 8 => j.val < 6 ∧ m.testBit j.val = true)), t j
def newSum (m : ℕ) (t : Point) := ∑ j : Fin 6, if decide (m / 2^j.val % 2 = 1) then t j.castSucc.castSucc else 0
def testRow : Fin 9 → ℚ := ![25/64, -2, 0, 0, -2, 0, 0, 0, 0]
def evaluate (a : Fin 9 → ℚ) (t : Point) : ℝ := (a 0 : ℝ) + ∑ j : Fin 8, (a j.succ : ℝ) * t j
example (t : Point) (hh : 0 < evaluate testRow t) : t 0+t 3 < 25/128 := by
  simp only [evaluate, Fin.sum_univ_succ, Fin.sum_univ_zero] at hh
  dsimp [testRow] at hh
  norm_num at hh
  linarith
