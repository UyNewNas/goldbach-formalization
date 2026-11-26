import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/- Exact existing declaration slices; diagnostic starts at the already-proved source_common_pos h 17 conclusion. No Source premise is altered in the candidate module. -/
namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
namespace VariableEnvelope

def mu : ℝ := 25 / 128

def cap : ℝ := 153 / 256

def A (t : ℝ) : ℝ := (1 + t) / 2

def C (t : ℝ) : ℝ := 57 / 64 - 3 / 2 * t

def B (t : ℝ) : ℝ := cap - 3 / 8 * t

end VariableEnvelope
open VariableEnvelope

def prefixSquareExpr {n : ℕ} {α : Type*} [CommSemiring α]
    (t : Fin n → α) (j : Fin n) : α :=
  (∑ k ∈ Finset.univ.filter (fun k => k < j), t k) + 2 * t j

def selectedSquareExpr {n : ℕ} {α : Type*} [CommSemiring α]
    (I : Finset (Fin n)) (t : Fin n → α) (j : Fin n) : α :=
  (∑ k ∈ I, t k) +
    (∑ k ∈ Finset.univ.filter (fun k => k < j ∧ k ∉ I), t k) + 2 * t j

namespace P4AOriginalRemainingEighthSources

abbrev Point := Fin 8 → ℝ

inductive Cell where
  | ascending (i : Fin 14)
  | seed
  | nine (i : Fin 13)
  | fiftyA
  | fiftyD
  | h5 (i : Fin 7)
  | h7 (i : Fin 10)
  deriving DecidableEq, Fintype

def selected : Cell → Finset (Fin 8)
  | .ascending _ | .seed => {0,7}
  | .fiftyA => {3,4,5,7}
  | .fiftyD => {1,2,7}
  | _ => {1,3,7}

def selectedSum (c : Cell) (t : Point) : ℝ := ∑ j ∈ selected c, t j

def eta : ℝ := 1 / 1000000

def comparison : Cell → Point → ℝ
  | .ascending _, t | .seed, t => C (t 1 + t 2)
  | .fiftyA, t => A (t 1 + t 4 + t 5)
  | .fiftyD, t => C (t 1 + t 4 + t 5)
  | _, t => A (t 0 + t 3)

def descendingNew : Cell → Bool
  | .fiftyD => true
  | _ => false

def newCap (c : Cell) (t : Point) : ℝ :=
  (if descendingNew c then C (selectedSum c t) else A (selectedSum c t)) - eta

def minorant : Cell → Point → ℝ
  | .ascending _, t | .seed, t | .nine _, t => C (t 1 + t 2)
  | .fiftyA, t => A (t 1 + t 2)
  | _, t => A (t 0)

def otherPlane (c : Cell) (s : ℝ) : ℝ :=
  if descendingNew c then A s else C s

def history (t : Point) : Fin 4 → ℝ :=
  ![3*t 0, t 0+t 1+3*t 2, t 0+t 1+t 2+t 3+3*t 4,
    t 0+t 1+t 2+t 3+t 4+t 5+3*t 6]

def total (t : Point) : ℝ := ∑ j, t j

def sideSlack : Cell → Point → ℝ
  | .ascending _, t | .seed, t | .nine _, t => 2*(t 1+t 2-mu)
  | .fiftyA, t => 2*(mu-t 1-t 2)
  | _, t => mu-t 0

def commonSlack (c : Cell) (t : Point) : Fin 35 → ℝ :=
  ![mu-t 0, t 2-1/100, t 7-53/13824,
    t 0-t 1, t 1-t 2, t 2-t 3, t 3-t 4, t 4-t 5, t 5-t 6, t 6-t 7,
    minorant c t-history t 0, minorant c t-history t 1,
    minorant c t-history t 2, minorant c t-history t 3,
    comparison c t-VariableEnvelope.B (t 2), newCap c t-comparison c t,
    total t+3*t 7-newCap c t,
    otherPlane c (selectedSum c t)-eta-newCap c t,
    newCap c t-prefixSquareExpr t 0, newCap c t-prefixSquareExpr t 1,
    newCap c t-prefixSquareExpr t 2, newCap c t-prefixSquareExpr t 3,
    newCap c t-prefixSquareExpr t 4, newCap c t-prefixSquareExpr t 5,
    newCap c t-prefixSquareExpr t 6, newCap c t-prefixSquareExpr t 7,
    if 0 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 0,
    if 1 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 1,
    if 2 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 2,
    if 3 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 3,
    if 4 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 4,
    if 5 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 5,
    if 6 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 6,
    if 7 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 7,
    sideSlack c t]

end P4AOriginalRemainingEighthSources
namespace P4AOriginalFull87SourceDictionary

abbrev Point := Fin 8 → ℝ

inductive Cell where
  | remaining (c : P4AOriginalRemainingEighthSources.Cell)
  | descending (i : Fin 15)
  | ascendingPair (i : Fin 13)
  | h3 (i : Fin 12)
  deriving DecidableEq, Fintype

end P4AOriginalFull87SourceDictionary
namespace P4AOriginalFull87Ownership
open P4AOriginalFull87SourceDictionary

abbrev history := P4AOriginalRemainingEighthSources.history

def kind : Cell → Fin 9
  | .remaining (.ascending _) | .remaining .seed => 0
  | .descending _ => 1
  | .remaining (.nine _) => 2
  | .remaining .fiftyA => 3
  | .remaining .fiftyD => 4
  | .ascendingPair _ => 5
  | .h3 _ => 6
  | .remaining (.h5 _) => 7
  | .remaining (.h7 _) => 8

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

set_option maxHeartbeats 0 in


example (i : Fin 14) {t : Point} (h : 0 < P4AOriginalRemainingEighthSources.commonSlack (.ascending i) t 17) :
    KindRows (kind (.remaining (.ascending i))) t := by
  have hh := h
  dsimp only [P4AOriginalRemainingEighthSources.commonSlack] at hh
  norm_num [
    P4AOriginalRemainingEighthSources.otherPlane,
    P4AOriginalRemainingEighthSources.newCap,
    P4AOriginalRemainingEighthSources.descendingNew,
    P4AOriginalRemainingEighthSources.selectedSum,
    P4AOriginalRemainingEighthSources.selected,A,C,KindRows,kind,mu] at hh ⊢
  linarith


example  {t : Point} (h : 0 < P4AOriginalRemainingEighthSources.commonSlack .seed t 17) :
    KindRows (kind (.remaining .seed)) t := by
  have hh := h
  dsimp only [P4AOriginalRemainingEighthSources.commonSlack] at hh
  norm_num [
    P4AOriginalRemainingEighthSources.otherPlane,
    P4AOriginalRemainingEighthSources.newCap,
    P4AOriginalRemainingEighthSources.descendingNew,
    P4AOriginalRemainingEighthSources.selectedSum,
    P4AOriginalRemainingEighthSources.selected,A,C,KindRows,kind,mu] at hh ⊢
  linarith


end P4AOriginalFull87Ownership
end
end ImbalancedChen
