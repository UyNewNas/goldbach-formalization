import ImbalancedChen.P2OriginalSaving16PullingFaceInduction
import ImbalancedChen.P2OriginalSaving19Archive

/-! The max-pulling certificate for one projected seven-dimensional
chamber of the original radial reduction. A separating row still has
only the seven projected coordinates after the existing affine
induction is applied. The last physical coordinate can vary freely. -/
namespace ImbalancedChen.P2OriginalRadialBasePulling
open scoped BigOperators
open P2OriginalSaving16OriginalArchive (QPoint evalQ)
open P2OriginalSaving16PullingFaceInduction (Shape pull pull_pair_separated)

abbrev QPoint7 := Fin 7 → ℚ
abbrev Affine7 := Fin 8 → ℚ
def eval7 (a : Affine7) (x : QPoint7) : ℚ := a 0 + ∑ i, a i.succ * x i

structure Data where
  vertices : Array (Array ℚ)
  facets : Array (Array ℕ)
  faces : Array P2OriginalSaving19Archive.FaceRecord
  rows : Array (Array ℕ)
  gates : Array (Array ℚ)
  deriving Inhabited

def vertex (d : Data) (v : ℕ) : QPoint7 := fun j => (d.vertices.getD v #[]).getD j.val 0
def vertexId (d : Data) (s : Fin d.rows.size) (i : Fin 8) := d.rows[s].getD i.val 0
def rowVertices (d : Data) (s : Fin d.rows.size) (i : Fin 8) : QPoint7 := vertex d (vertexId d s i)
def gate (d : Data) (g : Fin d.gates.size) : Affine7 := fun k => d.gates[g].getD k.val 0
def facet (d : Data) (f : Fin d.facets.size) := d.facets[f].toList
def faceRecord (d : Data) (face : List ℕ) :=
  (d.faces.toList.find? (fun f => f.vertices.toList == face)).getD default
def pivot (d : Data) (face : List ℕ) := (faceRecord d face).pivot
def children (d : Data) (face : List ℕ) : List (List ℕ) :=
  ((faceRecord d face).facetSets.toList.map Array.toList).filter (fun z => !(z.contains (pivot d face)))
def whole (d : Data) := List.range d.vertices.size
def saved (d : Data) := d.rows.toList.map Array.toList

/-- The producer uses max pivot and lexicographic child order. Its
original chamber inequalities supply the supporting affine rows. -/
def Checks (d : Data) : Prop :=
  (∀ v : Fin d.vertices.size, d.vertices[v].size = 7) ∧
  (∀ s : Fin d.rows.size, d.rows[s].size = 8 ∧ ∀ i, vertexId d s i < d.vertices.size) ∧
  (∀ g : Fin d.gates.size, d.gates[g].size = 8 ∧
    ∀ v : Fin d.vertices.size, 0 ≤ eval7 (gate d g) (vertex d v)) ∧
  (∀ f : Fin d.facets.size, ∃ g : Fin d.gates.size, ∀ v : Fin d.vertices.size,
    v.val ∈ facet d f ↔ eval7 (gate d g) (vertex d v) = 0) ∧
  Shape (facet d) (pivot d) (children d) 8 (whole d) ∧
  pull (pivot d) (children d) 8 (whole d) = saved d ∧ (saved d).Nodup

instance (d : Data) : Decidable (Checks d) := by unfold Checks; infer_instance

def embed (x : QPoint7) : QPoint := ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,0]
def lift7 (a : Affine7) : Fin 9 → ℚ := ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,a 7,0]
def restrict7 (a : Fin 9 → ℚ) : Affine7 := fun j => a j.castSucc

theorem restrict7_lift7 (a : Affine7) : restrict7 (lift7 a) = a := by
  funext j
  fin_cases j <;> rfl

theorem eval_embed (a : Fin 9 → ℚ) (x : QPoint7) :
    evalQ a (embed x) = eval7 (restrict7 a) x := by
  norm_num [evalQ,embed,eval7,restrict7,Fin.sum_univ_succ]

theorem eval_lift7 (a : Affine7) (x : QPoint) :
    evalQ (lift7 a) x = eval7 a (fun j => x j.castSucc) := by
  norm_num [evalQ,lift7,eval7,Fin.sum_univ_succ]

private theorem id_mem {d : Data} (h : Checks d) (s : Fin d.rows.size) (i : Fin 8) :
    vertexId d s i ∈ d.rows[s].toList := by
  have hi : i.val < d.rows[s].size := (h.2.1 s).1.symm ▸ i.isLt
  change d.rows[s].getD i.val 0 ∈ _
  rw [← Array.getElem_eq_getD (h := hi) 0]
  exact Array.getElem_mem_toList hi

private theorem row_mem {d : Data} (h : Checks d) (s : Fin d.rows.size) :
    d.rows[s].toList ∈ pull (pivot d) (children d) 8 (whole d) := by
  rw [h.2.2.2.2.2.1]
  exact List.mem_map.mpr ⟨d.rows[s],Array.getElem_mem_toList s.isLt,rfl⟩

private theorem row_ne {d : Data} (h : Checks d) (s t : Fin d.rows.size) (hst : s ≠ t) :
    d.rows[s].toList ≠ d.rows[t].toList := by
  intro he
  have hs : s.val < (saved d).length := by simpa [saved] using s.isLt
  have ht : t.val < (saved d).length := by simpa [saved] using t.isLt
  have he' : (saved d)[s.val] = (saved d)[t.val] := by simpa [saved] using he
  apply hst
  exact Fin.ext ((List.getElem_inj (h₀ := hs) (h₁ := ht) h.2.2.2.2.2.2).mp he')

/-- Every distinct pair of actual base simplices has a vertical
separating wall. Nontriviality is witnessed on an original projected
vertex of this same chamber. No volume or separation input is needed. -/
theorem separated {d : Data} (h : Checks d) (s t : Fin d.rows.size) (hst : s ≠ t) :
    ∃ a : Affine7, (∀ i : Fin 8, eval7 a (rowVertices d s i) ≤ 0) ∧
      (∀ i : Fin 8, 0 ≤ eval7 a (rowVertices d t i)) ∧
      ∃ v : Fin d.vertices.size, eval7 a (vertex d v) ≠ 0 := by
  classical
  choose g hgate using h.2.2.2.1
  let V := fun v : ℕ => embed (vertex d v)
  let G := fun f : Fin d.facets.size => lift7 (gate d (g f))
  have he (f : Fin d.facets.size) (v : ℕ) :
      evalQ (G f) (V v) = eval7 (gate d (g f)) (vertex d v) := by
    rw [show G f = lift7 (gate d (g f)) from rfl,show V v = embed (vertex d v) from rfl,
      eval_embed,restrict7_lift7]
  have hp f v (hv : v ∈ whole d) : 0 ≤ evalQ (G f) (V v) := by
    rw [he]
    exact (h.2.2.1 (g f)).2 ⟨v,by simpa [whole] using hv⟩
  have hf f v (hv : v ∈ whole d) : v ∈ facet d f ↔ evalQ (G f) (V v) = 0 := by
    rw [he]
    exact hgate f ⟨v,by simpa [whole] using hv⟩
  obtain ⟨a,hs,ht,v,hv,hav⟩ := pull_pair_separated V G (facet d) (whole d)
    (pivot d) (children d) hp hf (fun _ hz => hz) h.2.2.2.2.1
    (row_mem h s) (row_mem h t) (row_ne h s t hst)
  refine ⟨restrict7 a,?_,?_,⟨v,by simpa [whole] using hv⟩,?_⟩
  · intro i
    simpa only [V,eval_embed,rowVertices] using hs _ (id_mem h s i)
  · intro i
    simpa only [V,eval_embed,rowVertices] using ht _ (id_mem h t i)
  · simpa only [V,eval_embed] using hav

end ImbalancedChen.P2OriginalRadialBasePulling
