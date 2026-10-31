import ImbalancedChen.P2HistoricSieveCore
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast

/-!
Draft only: exact finite replay of the ORIGINAL historical Q80 recurrence.
No analytic estimate is assumed or changed. A finite recurrence witness is
used only to prove equality to the existing functional-state interpreter.
-/
namespace ImbalancedChen.P2HistoricSieveFiniteReplay

open P2HistoricSieveTableSemantics
open Certificates.P2HistoricQ80DefectLookup

/-- An update reads only strictly earlier nodes when the grid is positive. -/
theorem update_congr_prefix {g i : ℕ} (hg : 0 < g)
    {old new : ℕ → HistoricNode}
    (h : ∀ j, j < i → old j = new j) :
    update g i old = update g i new := by
  by_cases hi : i ≤ 2 * g
  · simp only [update, if_pos hi]
  · simp only [update, if_neg hi]
    rw [h (i - 1) (by omega), h (i - g - 1) (by omega),
      h (i - g) (by omega)]

/-- Once an index is written, later state updates never change it. -/
theorem state_stable (g : ℕ) {i k : ℕ} (hi : i ≤ k) :
    state g k i = state g i i := by
  revert hi
  induction k with
  | zero =>
      intro hi
      have : i = 0 := by omega
      subst i
      rfl
  | succ k ih =>
      intro hi
      by_cases he : i = k + 1
      · subst i
        rfl
      · change (if i = k + 1 then update g (k + 1) (state g k)
          else state g k i) = state g i i
        rw [if_neg he]
        exact ih (by omega)

/-- Finite literal recurrence checks imply equality, not merely an enclosure. -/
theorem state_eq_replay {g N : ℕ} (hg : 0 < g)
    (nodes : ℕ → HistoricNode) (hzero : nodes 0 = initial)
    (hstep : ∀ i, 0 < i → i ≤ N → nodes i = update g i nodes)
    {k : ℕ} (hk : k ≤ N) :
    ∀ i, i ≤ k → state g k i = nodes i := by
  revert hk
  induction k with
  | zero =>
      intro hk i hi
      have : i = 0 := by omega
      subst i
      exact hzero.symm
  | succ k ih =>
      intro hk i hi
      by_cases he : i = k + 1
      · subst i
        change (if k + 1 = k + 1 then update g (k + 1) (state g k)
          else state g k (k + 1)) = nodes (k + 1)
        rw [if_pos rfl]
        calc
          update g (k + 1) (state g k) = update g (k + 1) nodes :=
            update_congr_prefix hg (fun j hj => ih (by omega) j (by omega))
          _ = nodes (k + 1) := (hstep _ (by omega) hk).symm
      · change (if i = k + 1 then update g (k + 1) (state g k)
          else state g k i) = nodes i
        rw [if_neg he]
        exact ih (by omega) i (by omega)

/-- The original maximum-eight table may be read from a shorter certified
prefix. No table values after that prefix are assumed or substituted. -/
theorem table_eq_replay {g maximum N i : ℕ} (hg : 0 < g)
    (nodes : ℕ → HistoricNode) (hzero : nodes 0 = initial)
    (hstep : ∀ j, 0 < j → j ≤ N → nodes j = update g j nodes)
    (hi : i ≤ N) (himax : i ≤ maximum * g) :
    table g maximum i = nodes i := by
  calc
    table g maximum i = state g i i := state_stable g himax
    _ = state g N i := (state_stable g hi).symm
    _ = nodes i := state_eq_replay hg nodes hzero hstep le_rfl i hi

/-- The original integer interpolation with a separately supplied node reader. -/
def numeratorWith (g : ℕ) (nodes : ℕ → HistoricNode) (a b : ℤ) : I80 :=
  numerator g a b (fun i => (nodes i).ll) (fun i => (nodes i).lh)

/-- Interpolation only reads q and, for a nonzero residual, q+1. -/
theorem numeratorWith_eq {g maximum : ℕ} (nodes : ℕ → HistoricNode)
    (a b : ℤ)
    (h0 : nodes (queryIndex g a b) = table g maximum (queryIndex g a b))
    (h1 : queryResidual g a b ≠ 0 →
      nodes (queryIndex g a b + 1) = table g maximum (queryIndex g a b + 1)) :
    numeratorWith g nodes a b =
      numerator g a b (fun i => (table g maximum i).ll)
        (fun i => (table g maximum i).lh) := by
  unfold numeratorWith numerator
  by_cases hr : queryResidual g a b = 0
  · simp only [hr, if_pos, h0]
  · simp only [hr, if_false, h0, h1 hr]

/-- A bounded reader keeps the original table outside the certified prefix.
Thus it is extensionally equal to the source table on *all* indices. -/
def prefixReader (g maximum N : ℕ) (nodes : ℕ → HistoricNode) (i : ℕ) : HistoricNode :=
  if i ≤ N then nodes i else table g maximum i

theorem prefixReader_eq {g maximum N : ℕ} (hg : 0 < g)
    (hN : N ≤ maximum * g) (nodes : ℕ → HistoricNode)
    (hzero : nodes 0 = initial)
    (hstep : ∀ j, 0 < j → j ≤ N → nodes j = update g j nodes) :
    prefixReader g maximum N nodes = table g maximum := by
  funext i
  unfold prefixReader
  split_ifs with hi
  · exact (table_eq_replay hg nodes hzero hstep hi (hi.trans hN)).symm
  · rfl

/-- Literal source point query, parameterized only by its table reader. -/
def pointWith (g maximum : ℕ) (nodes : ℕ → HistoricNode) (a b : ℤ) : I80 :=
  if a ≤ 2 * b then ⟨0, 0⟩ else
  if a > (maximum : ℤ) * b then
    ⟨(nodes (maximum * g)).ll / (maximum : ℤ),
      ceilDiv (nodes (maximum * g)).hh (maximum : ℤ)⟩ else
  let p := numeratorWith g nodes a b
  ⟨p.lo * b / a, ceilDiv (p.hi * b) a⟩

theorem pointWith_source (g maximum : ℕ) (a b : ℤ) :
    pointWith g maximum (table g maximum) a b = point g maximum a b := rfl

/-- Exact sf interpreter equality. All source guards, rounding and tails
are unchanged, including queries outside the replayed prefix. -/
theorem sf_prefixReader_eq {g maximum N : ℕ} (hg : 0 < g)
    (hN : N ≤ maximum * g) (nodes : ℕ → HistoricNode)
    (hzero : nodes 0 = initial)
    (hstep : ∀ j, 0 < j → j ≤ N → nodes j = update g j nodes)
    (q : ℚ) :
    pointWith g maximum (prefixReader g maximum N nodes) q.num (q.den : ℤ) =
      sf g maximum q := by
  rw [prefixReader_eq hg hN nodes hzero hstep]
  rfl

end ImbalancedChen.P2HistoricSieveFiniteReplay
