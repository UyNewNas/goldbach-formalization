import ImbalancedChen.P2OriginalCompactQ80Leaf
import ImbalancedChen.P2OriginalPriorityForestLedger

/-!
SOURCE ONLY / UNCOMPILED.
Actual normalized21 roots and the exact original midpoint children imply
the primitive Geometry of EVERY complete forest entry. There is no external
leaf-geometry premise at the State interface. Entries with zero uncertainty
and empty source-domain intersections are included, as in K's full forest.
-/
namespace ImbalancedChen.P2OriginalCompactQ80ReachabilitySourceOnly

noncomputable section
open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalPrioritySerialQueueSourceOnly
open P2OriginalPriorityForestLedgerSourceOnly
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80LeafSourceOnly

theorem geometry_mem_initialSeeds (box : SeedCell) (h : box ∈ initialSeeds) : Geometry box := by
  have hm : box ∈ records := by simpa only [initialSeeds_eq_records] using h
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hm
  have hi21 : i < 21 := by simpa only [records_length] using hi
  have hr : recordAt ⟨i,hi21⟩ = box := by simpa only [recordAt] using he
  rw [←hr]
  exact geometry_recordAt ⟨i,hi21⟩

theorem treeEntry_geometry {evaluator : SeedCell → Bounds} {root : SeedCell}
    (tree : SourceTree evaluator root) : Geometry root →
      ∀ p ∈ treeEntries tree, Geometry p.cell := by
  induction tree with
  | leaf cell serial =>
      intro g p hp
      have he : p = ⟨cell,evaluator cell,serial⟩ := by simpa only [treeEntries,List.mem_singleton] using hp
      simpa only [he] using g
  | split cell width left right ihL ihR =>
      intro g p hp
      rcases List.mem_append.mp hp with hl | hr
      · exact ihL (geometry_sourceLeft g width) p hl
      · exact ihR (geometry_sourceRight g width) p hr

theorem forestEntry_geometry {evaluator : SeedCell → Bounds} {roots : List SeedCell}
    (forest : SourceForest evaluator roots) :
    (∀ box ∈ roots, Geometry box) → ∀ p ∈ entries forest, Geometry p.cell := by
  induction forest with
  | nil => intro _ p hp; simp only [entries,List.not_mem_nil] at hp
  | @cons cell cells tree rest ih =>
      intro hg p hp
      rcases List.mem_append.mp hp with ht | hr
      · exact treeEntry_geometry tree (hg cell (by simp)) p ht
      · exact ih (fun box hb => hg box (by simp [hb])) p hr

/-- The run owner can use this directly, with no assumed Run witness and no
caller-supplied geometry on individual cached entries. The dependent forest
itself records original roots, literal children and successful midpoint guards. -/
theorem stateEntry_geometry (st : State enclose) (p : Entry) (hp : p ∈ entries st.forest) :
    Geometry p.cell :=
  forestEntry_geometry st.forest geometry_mem_initialSeeds p hp

theorem stateEntry_residual (st : State enclose) (p : Entry) (hp : p ∈ entries st.forest) :
    p.cell.2 0+p.cell.2 1 < (phiRange p.cell).lo :=
  (stateEntry_geometry st p hp).residual

theorem stateEntry_muCut (st : State enclose) (p : Entry) (hp : p ∈ entries st.forest) :
    p.cell.2 0 ≤ muInteger ∨ muInteger ≤ p.cell.1 0 :=
  (stateEntry_geometry st p hp).muCut

end
end ImbalancedChen.P2OriginalCompactQ80ReachabilitySourceOnly
