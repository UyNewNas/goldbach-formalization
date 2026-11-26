import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
noncomputable section
open scoped Classical BigOperators
abbrev Point := Fin 8 → ℝ
def mu : ℝ := 25/128
def C (s : ℝ) : ℝ := 57/64 -3/2*s
def history (t : Point) : Fin 4 → ℝ :=
  ![3*t 0, t 0+t 1+3*t 2, t 0+t 1+t 2+t 3+3*t 4,
    t 0+t 1+t 2+t 3+t 4+t 5+3*t 6]
def KindRows (k : Fin 9) (t : Point) : Prop :=
  match k.val with
  | 0 => t 0+t 7 < mu
  | 1 => mu < t 0+t 7
  | 2 => mu < t 1+t 2 ∧ ∀ j : Fin 4, history t j < C (t 1+t 2)
  | 3 => t 1+t 4+t 5 < mu
  | 4 => mu < t 1+t 4+t 5
  | 5 => t 1+t 2 < mu
  | 6 => mu < t 1+t 2 ∧ C (t 1+t 2) < history t 1
  | 7 => mu < t 1+t 2 ∧ history t 1 < C (t 1+t 2) ∧ C (t 1+t 2) < history t 2
  | _ => mu < t 1+t 2 ∧ history t 1 < C (t 1+t 2) ∧
      history t 2 < C (t 1+t 2) ∧ C (t 1+t 2) < history t 3

def kindWinner (k : Fin 9) : ℕ := if k.val ≤ 1 then 6 else if k.val = 3 ∨ k.val = 4 then 50 else 9

example (i j : Fin 9) (t : Point)
    (hw : kindWinner i = kindWinner j)
    (hkc : KindRows i t) (hkd : KindRows j t) : i = j := by
  fin_cases i
  all_goals fin_cases j
  all_goals try rfl
  all_goals norm_num [kindWinner] at hw
  all_goals simp only [KindRows] at hkc hkd
  all_goals first
    | linarith
    | linarith [hkc.1]
    | linarith [hkd.1]
    | linarith [hkc.2 (1 : Fin 4),hkd.2]
    | linarith [hkd.2 (1 : Fin 4),hkc.2]
    | linarith [hkc.2 (2 : Fin 4),hkd.2.2]
    | linarith [hkd.2 (2 : Fin 4),hkc.2.2]
    | linarith [hkc.2 (3 : Fin 4),hkd.2.2.2]
    | linarith [hkd.2 (3 : Fin 4),hkc.2.2.2]


def oldSum (m : ℕ) (t : Point) := ∑ j ∈ (Finset.univ.filter (fun j : Fin 8 => j.val < 6 ∧ m.testBit j.val = true)), t j
def newSum (m : ℕ) (t : Point) := ∑ j : Fin 6, if decide (m / 2^j.val % 2 = 1) then t j.castSucc.castSucc else 0
example (m : Fin 64) (t : Point) : oldSum m.val t = newSum m.val t := by
  norm_num [oldSum, newSum, Finset.sum_filter, Fin.sum_univ_succ,
    Nat.testBit_eq_decide_div_mod_eq, Fin.ofNat, Fin.succ]
