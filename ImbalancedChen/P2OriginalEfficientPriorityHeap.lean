import ImbalancedChen.P2OriginalPrioritySerialQueue
import Batteries.Data.PairingHeap

/-!
SOURCEONLY / UNCOMPILED. No finite heap or enclosure evaluation is run here.
The manifest-pinned Batteries pairing heap supplies the actual efficient pure
operations. Its structural WF predicate is not silently treated as a content
or minimum theorem: both missing semantic facts are proved below.
-/
namespace ImbalancedChen.P2OriginalEfficientPriorityHeapSourceOnly

open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalPrioritySerialQueueSourceOnly
open Batteries.PairingHeapImp

/-- An address is administrative. It does not enter the original priority key.
`false` is side0; `true` is side1; paths run from the seed root downward. -/
structure Scheduled where
  entry : Entry
  seed : ℕ
  path : List Bool

def keyLe (p q : Scheduled) : Bool := decide (Before p.entry q.entry)

instance : Batteries.TotalBLE keyLe where
  total := by
    intro p q
    simpa only [keyLe,decide_eq_true_eq] using before_total p.entry q.entry

abbrev Queue := Batteries.PairingHeap Scheduled keyLe

def nodes : Heap Scheduled → List Scheduled
  | .nil => []
  | .node a c s => a :: (nodes c ++ nodes s)

def bag (h : Heap Scheduled) : Multiset Scheduled := (nodes h : Multiset Scheduled)

def rootBag : Heap Scheduled → Multiset Scheduled
  | .nil => 0
  | .node a c _ => {a} + bag c

theorem bag_nil : bag .nil = 0 := rfl

theorem bag_node (a : Scheduled) (c s : Heap Scheduled) :
    bag (.node a c s) = {a} + bag c + bag s := by
  simp [bag,nodes,add_assoc]

theorem rootBag_eq {h : Heap Scheduled} (hs : h.NoSibling) : rootBag h = bag h := by
  cases hs <;> simp [rootBag,bag_node,bag_nil]

/-- `merge` ignores root siblings in the API. The statement accounts for that
explicitly; the public queue uses only NoSibling roots. -/
theorem bag_merge_roots (h k : Heap Scheduled) :
    bag (h.merge keyLe k) = rootBag h + rootBag k := by
  cases h with
  | nil => cases k <;> simp [Heap.merge,rootBag,bag_node,bag_nil]
  | node a c s =>
      cases k with
      | nil => simp [Heap.merge,rootBag,bag_node,bag_nil]
      | node b d t =>
          simp only [Heap.merge]
          split <;> simp [rootBag,bag_node,bag_nil,add_assoc,add_left_comm,add_comm]

theorem bag_combine (h : Heap Scheduled) : bag (h.combine keyLe) = bag h := by
  match h with
  | .nil => rfl
  | .node a c .nil => rfl
  | .node a c (.node b d s) =>
      rw [Heap.combine,bag_merge_roots,
        rootBag_eq (Heap.noSibling_merge _ _ _),
        rootBag_eq (Heap.noSibling_combine _ _),bag_merge_roots,
        bag_combine s]
      simp [rootBag,bag_node,add_assoc,add_left_comm,add_comm]
termination_by h.size
decreasing_by simp [Heap.size]; omega

def contents (q : Queue) : List Scheduled := nodes q.val

theorem contents_empty : contents (Batteries.PairingHeap.empty : Queue) = [] := rfl

/-- Exact multiplicities, not mere membership or size preservation. -/
theorem contents_insert (p : Scheduled) (q : Queue) :
    (contents (Batteries.PairingHeap.insert p q) : Multiset Scheduled) =
      {p} + (contents q : Multiset Scheduled) := by
  change bag ((Heap.singleton p).merge keyLe q.val) = {p} + bag q.val
  rw [bag_merge_roots]
  have hs : q.val.NoSibling := by cases q.property <;> constructor
  simp [rootBag,Heap.singleton,bag_nil,rootBag_eq hs]

/-- Every descendant of a root is later in the literal error/serial order. -/
theorem nodeWF_priority (h : Heap Scheduled) (p : Scheduled)
    (hw : h.NodeWF keyLe p) (q : Scheduled) (hq : q ∈ nodes h) :
    Before p.entry q.entry := by
  induction h generalizing p q with
  | nil => simp [nodes] at hq
  | node a c s ihc ihs =>
      rcases hw with ⟨ha,hc,hs⟩
      have hpa : Before p.entry a.entry := by
        simpa only [keyLe,decide_eq_true_eq] using ha
      simp only [nodes,List.mem_cons,List.mem_append] at hq
      rcases hq with rfl | hq | hq
      · exact hpa
      · exact before_trans hpa (ihc a hc q hq)
      · exact ihs p hs q hq

/-- Deletion returns one minimum and every other queued job once. The source
uses unique positive serials, so addresses never introduce an extra tie key. -/
theorem deleteMin_spec (q : Queue) (p : Scheduled) (rest : Queue)
    (hd : Batteries.PairingHeap.deleteMin q = some (p,rest)) :
    (contents q : Multiset Scheduled) = {p} + (contents rest : Multiset Scheduled) ∧
      p ∈ contents q ∧ ∀ r ∈ contents q, Before p.entry r.entry := by
  rcases q with ⟨h,hw⟩
  cases hw with
  | nil => simp [Batteries.PairingHeap.deleteMin,Heap.deleteMin] at hd
  | @node a c hc =>
      simp only [Batteries.PairingHeap.deleteMin,Heap.deleteMin] at hd
      cases hd
      refine ⟨?_,by simp [contents,nodes],?_⟩
      · change bag (.node a c .nil) = {a} + bag (c.combine keyLe)
        rw [bag_combine]
        simp [bag_node,bag_nil]
      · intro r hr
        simp only [contents,nodes,List.append_nil,List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact before_refl _
        · exact nodeWF_priority c a hc r hr

/-- The heap's returned key is exactly Python's negative-error/serial key. -/
theorem deleteMin_original_key (q : Queue) (p : Scheduled) (rest : Queue)
    (hd : Batteries.PairingHeap.deleteMin q = some (p,rest))
    (r : Scheduled) (hr : r ∈ contents q) :
    -error p.entry < -error r.entry ∨
      (-error p.entry = -error r.entry ∧ p.entry.serial ≤ r.entry.serial) :=
  (before_key_iff _ _).mp ((deleteMin_spec q p rest hd).2.2 r hr)

end ImbalancedChen.P2OriginalEfficientPriorityHeapSourceOnly


