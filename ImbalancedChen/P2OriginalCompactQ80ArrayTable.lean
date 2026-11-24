import ImbalancedChen.P2OriginalCompactQ80Encloser
import Init.Data.Array.Lemmas

/-!
SOURCE ONLY / UNCOMPILED / NO FINITE COMPUTATION PERFORMED.

An incremental pure Array implementation of the ORIGINAL Q80 table. Each
iteration appends exactly one node, computed from the already built array.
Neither `Array.ofFn` nor the functional sourceState evaluator occurs in the
executable builder. The full functional sourceState appears only in proofs.
The initial node is also the out-of-range default, so refinement is an
equality of total lookup functions, without an input-range hypothesis.
-/
namespace ImbalancedChen.P2OriginalCompactQ80ArrayTableSourceOnly

open P2OriginalCompactQ80EncloserSourceOnly

/-- Total array lookup with the original untouched-node value. -/
def lookup (nodes : Array Node) (i : ℕ) : Node :=
  nodes[i]?.getD initialNode

theorem lookup_push (nodes : Array Node) (next : Node) :
    lookup (nodes.push next) =
      fun i => if i = nodes.size then next else lookup nodes i := by
  funext i
  by_cases hi : i = nodes.size <;>
    simp only [lookup, Array.getElem?_push, hi, if_true, if_false,
      Option.getD_some]

/-- The invariant includes every natural lookup, not just stored indices. -/
def Represents (g n : ℕ) (nodes : Array Node) : Prop :=
  nodes.size = n + 1 ∧ lookup nodes = sourceState g n

theorem singleton_represents (g : ℕ) :
    Represents g 0 #[initialNode] := by
  constructor
  · rfl
  · funext i
    by_cases hi : i = 0 <;>
      simp only [lookup, Array.getElem?_singleton, hi, if_true, if_false,
        Option.getD_some, Option.getD_none, sourceState]

/-- A single source update is read entirely from the existing array and
written once, at its previous size. No sourceState call is evaluated. -/
def appendNode (g : ℕ) (nodes : Array Node) : Array Node :=
  nodes.push (nodeUpdate g nodes.size (lookup nodes))

theorem appendNode_represents (g n : ℕ) (nodes : Array Node)
    (h : Represents g n nodes) : Represents g (n + 1) (appendNode g nodes) := by
  constructor
  · simp only [appendNode, Array.size_push, h.1]
  · unfold appendNode
    rw [lookup_push, h.1, h.2]
    rfl

/-- Tail-recursive incremental construction. At each iteration the only
live table argument is the Array from the preceding iteration. -/
def buildFrom (g : ℕ) : ℕ → Array Node → Array Node
  | 0, nodes => nodes
  | remaining + 1, nodes => buildFrom g remaining (appendNode g nodes)

theorem buildFrom_represents (g remaining n : ℕ) (nodes : Array Node)
    (h : Represents g n nodes) :
    Represents g (n + remaining) (buildFrom g remaining nodes) := by
  induction remaining generalizing n nodes with
  | zero => simpa only [buildFrom, Nat.add_zero] using h
  | succ remaining ih =>
      rw [show n + (remaining + 1) = (n + 1) + remaining by omega]
      exact ih (n + 1) (appendNode g nodes) (appendNode_represents g n nodes h)

/-- Actual original parameters, with one slot for index zero. This term has
not been evaluated while authoring this source-only proposal. -/
def tableArray : Array Node := buildFrom 16384 (12 * 16384) #[initialNode]

theorem tableArray_represents : Represents 16384 (12 * 16384) tableArray := by
  simpa only [Nat.zero_add] using
    buildFrom_represents 16384 (12 * 16384) 0 #[initialNode]
      (singleton_represents 16384)

theorem tableArray_size : tableArray.size = 12 * 16384 + 1 :=
  tableArray_represents.1

theorem tableArray_lookup : lookup tableArray = sourceTable :=
  tableArray_represents.2

theorem tableArray_lookup_historical :
    lookup tableArray = P2HistoricSieveTableSemantics.table 16384 12 :=
  tableArray_lookup.trans sourceTable_eq_historical

/-- Exactness holds also beyond the stored prefix, using the same initial
default as the original functional state. This is a symbolic consequence
of the recurrence proof, rather than a finite table acceptance guard. -/
theorem tableArray_lookup_apply (i : ℕ) : lookup tableArray i = sourceTable i :=
  congrFun tableArray_lookup i

/-- Transport the already proved actual Q80 node enclosure through exact
cache refinement. This does not execute or assume a table acceptance test. -/
theorem tableArray_encloses_actual (i : ℕ) (hi : 16384 ≤ i) (hmax : i ≤ 196608) :
    P2HistoricSieveStateInduction.Encloses (lookup tableArray i) i := by
  rw [tableArray_lookup_historical]
  exact P2OriginalCompactQ80TableSourceOnly.table12_encloses_actual i hi hmax

end ImbalancedChen.P2OriginalCompactQ80ArrayTableSourceOnly
