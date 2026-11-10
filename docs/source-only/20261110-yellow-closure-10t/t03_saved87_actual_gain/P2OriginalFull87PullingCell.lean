import ImbalancedChen.P2OriginalSaving16PullingFaceInduction
import ImbalancedChen.P2OriginalSaving16SimplexBinding
import ImbalancedChen.P2OriginalSaving19OwnedSource
import ImbalancedChen.P4AOriginalFull87EighthKernelControl

/-! The inner-union argument common to the original unequal-parent and
first-failure moment witnesses. It reads their ordered max-pulling rows.
The finite source checks concern vertices, source gates and face IDs. -/
namespace ImbalancedChen.P2OriginalFull87PullingCell
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87EighthKernelControl (kernel integrableOn_kernel kernel_bounds)
open P2OriginalSaving16OriginalArchive (QPoint evalQ castPoint edgeMatrix)
open P2OriginalSaving16SimplexBinding (edgeEquiv edge_vertices)
open P2OriginalSaving16PullingFaceInduction (pull Shape pull_pair_separated)
open P2OriginalSaving19OwnedSource (AffineRow eval eval_cast eval_interpolate affine_zero_volume)
open P2OriginalSaving19SimplexMoments
  (support support_measurable vertices_interpolate bary_nonneg interpolate)

structure Data where
  vertices : Array (Array ℚ)
  facets : Array (Array ℕ)
  faces : Array P2OriginalSaving19Archive.FaceRecord
  rows : Array (Array ℕ)
  deriving Inhabited

def originalGate : (c : Cell) → Fin (rowCount c) → AffineRow
  | .remaining c, g => P4AOriginalRemainingEighthSources.row c g
  | .descending i, g => OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i g
  | .ascendingPair i, g => OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i g
  | .h3 i, g => (P4AOriginalFirstFailureH3Literal.sourceAffineRows i g).2

theorem gate_eval (c : Cell) (g : Fin (rowCount c)) (t : Point) :
    eval (originalGate c g) t = rowValue c g t := by cases c <;> rfl

def vertex (d : Data) (v : ℕ) : QPoint := fun j => (d.vertices.getD v #[]).getD j.val 0
def idAt (d : Data) (s : Fin d.rows.size) (k : Fin 9) := d.rows[s].getD k.val 0
def rowVertices (d : Data) (s : Fin d.rows.size) (k : Fin 9) : QPoint := vertex d (idAt d s k)
def facet (d : Data) (f : Fin d.facets.size) := d.facets[f].toList
def faceRecord (d : Data) (face : List ℕ) :=
  (d.faces.toList.find? (fun f => f.vertices.toList == face)).getD default
def pivot (d : Data) (face : List ℕ) := (faceRecord d face).pivot
def children (d : Data) (face : List ℕ) : List (List ℕ) :=
  ((faceRecord d face).facetSets.toList.map Array.toList).filter
    (fun s => !(s.contains (pivot d face)))
def whole (d : Data) := List.range d.vertices.size
def savedRows (d : Data) := d.rows.toList.map Array.toList

/-- Actual row IDs, vertices and supporting original gates. The
potentially heterogeneous facet ordinals need only bind their vertex
sets to literal original gates on this cell. -/
def Checks (c : Cell) (d : Data) : Prop :=
  (∀ v : Fin d.vertices.size, d.vertices[v].size = 8) ∧
  (∀ s : Fin d.rows.size, d.rows[s].size = 9 ∧
    (∀ k : Fin 9, idAt d s k < d.vertices.size) ∧ (edgeMatrix (rowVertices d s)).det ≠ 0) ∧
  (∀ (g : Fin (rowCount c)) (v : Fin d.vertices.size), 0 ≤ evalQ (originalGate c g) (vertex d v)) ∧
  (∀ g : Fin (rowCount c), ∃ v : Fin d.vertices.size, 0 < evalQ (originalGate c g) (vertex d v)) ∧
  (∀ f : Fin d.facets.size, ∃ g : Fin (rowCount c), ∀ v : Fin d.vertices.size,
    v.val ∈ facet d f ↔ evalQ (originalGate c g) (vertex d v) = 0) ∧
  Shape (facet d) (pivot d) (children d) 9 (whole d) ∧
  pull (pivot d) (children d) 9 (whole d) = savedRows d ∧ (savedRows d).Nodup

instance (c : Cell) (d : Data) : Decidable (Checks c d) := by unfold Checks; infer_instance

theorem row_det {c d} (h : Checks c d) (s : Fin d.rows.size) :
    (edgeMatrix (rowVertices d s)).det ≠ 0 := (h.2.1 s).2.2

def rowSupport (d : Data) (s : Fin d.rows.size) (hd : (edgeMatrix (rowVertices d s)).det ≠ 0) : Set Point :=
  support (edgeEquiv (rowVertices d s) hd) (castPoint (rowVertices d s 0))

private theorem id_mem {c d} (h : Checks c d) (s : Fin d.rows.size) (k : Fin 9) :
    idAt d s k ∈ d.rows[s].toList := by
  have hk : k.val < d.rows[s].size := (h.2.1 s).1.symm ▸ k.isLt
  change d.rows[s].getD k.val 0 ∈ _
  rw [← Array.getElem_eq_getD (h := hk) 0]
  exact Array.getElem_mem_toList hk

private theorem row_mem {c d} (h : Checks c d) (s : Fin d.rows.size) :
    d.rows[s].toList ∈ pull (pivot d) (children d) 9 (whole d) := by
  rw [h.2.2.2.2.2.2.1]
  exact List.mem_map.mpr ⟨d.rows[s], Array.getElem_mem_toList s.isLt,rfl⟩

private theorem row_ne {c d} (h : Checks c d) (s t : Fin d.rows.size) (hne : s ≠ t) :
    d.rows[s].toList ≠ d.rows[t].toList := by
  intro he
  have hs : s.val < (savedRows d).length := by simpa [savedRows] using s.isLt
  have ht : t.val < (savedRows d).length := by simpa [savedRows] using t.isLt
  exact hne (Fin.ext ((List.getElem_inj (h₀ := hs) (h₁ := ht) h.2.2.2.2.2.2.2).mp
    (by simpa [savedRows] using he)))

private theorem separator {c d} (h : Checks c d) (s t : Fin d.rows.size) (hne : s ≠ t) :
    ∃ a : AffineRow, (∀ k, evalQ a (rowVertices d s k) ≤ 0) ∧
      (∀ k, 0 ≤ evalQ a (rowVertices d t k)) ∧ ∃ x : Point, eval a x ≠ 0 := by
  choose g hg using h.2.2.2.2.1
  have hn f v (hv : v ∈ whole d) : 0 ≤ evalQ (originalGate c (g f)) (vertex d v) :=
    h.2.2.1 (g f) ⟨v, by simpa [whole] using hv⟩
  have hf f v (hv : v ∈ whole d) : v ∈ facet d f ↔ evalQ (originalGate c (g f)) (vertex d v) = 0 :=
    hg f ⟨v, by simpa [whole] using hv⟩
  obtain ⟨a,hs,ht,v,_,ha⟩ := pull_pair_separated (vertex d) (fun f => originalGate c (g f))
    (facet d) (whole d) (pivot d) (children d) hn hf (fun _ z => z)
    h.2.2.2.2.2.1 (row_mem h s) (row_mem h t) (row_ne h s t hne)
  exact ⟨a, fun k => hs _ (id_mem h s k), fun k => ht _ (id_mem h t k),
    castPoint (vertex d v), by rw [eval_cast]; exact_mod_cast ha⟩

private theorem eval_on {d : Data} {s : Fin d.rows.size} {hd} (a : AffineRow)
    {x : Point} (hx : x ∈ rowSupport d s hd) :
    ∃ y ∈ P2OriginalSaving19SimplexMoments.canonical,
      eval a x = interpolate (fun k => (evalQ a (rowVertices d s k) : ℝ)) y := by
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨y,hy,?_⟩
  rw [← vertices_interpolate (edgeEquiv (rowVertices d s) hd) (castPoint (rowVertices d s 0)),
    edge_vertices, eval_interpolate]
  simp only [eval_cast]

private theorem nonneg_on {d : Data} {s : Fin d.rows.size} {hd} {a : AffineRow}
    (h : ∀ k, 0 ≤ evalQ a (rowVertices d s k)) {x : Point} (hx : x ∈ rowSupport d s hd) :
    0 ≤ eval a x := by
  obtain ⟨y,hy,he⟩ := eval_on a hx
  rw [he]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (bary_nonneg hy k) (by exact_mod_cast h k)

private theorem nonpos_on {d : Data} {s : Fin d.rows.size} {hd} {a : AffineRow}
    (h : ∀ k, evalQ a (rowVertices d s k) ≤ 0) {x : Point} (hx : x ∈ rowSupport d s hd) :
    eval a x ≤ 0 := by
  obtain ⟨y,hy,he⟩ := eval_on a hx
  rw [he]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (bary_nonneg hy k) (by exact_mod_cast h k)

theorem within_cell_null {c d} (h : Checks c d) {s t : Fin d.rows.size} (hne : s ≠ t) :
    volume (rowSupport d s (row_det h s) ∩ rowSupport d t (row_det h t)) = 0 := by
  obtain ⟨a,hs,ht,ha⟩ := separator h s t hne
  exact measure_mono_null (fun _ hx => le_antisymm (nonpos_on hs hx.1) (nonneg_on ht hx.2))
    (affine_zero_volume a ha)

private def walls (c : Cell) : Set Point := ⋃ g : Fin (rowCount c), {x | eval (originalGate c g) x = 0}

private theorem walls_null {c d} (h : Checks c d) : volume (walls c) = 0 := by
  apply measure_iUnion_null
  intro g
  obtain ⟨v,hv⟩ := h.2.2.2.1 g
  apply affine_zero_volume
  refine ⟨castPoint (vertex d v),?_⟩
  rw [eval_cast]
  exact_mod_cast hv.ne'

private theorem support_off_walls {c d} (h : Checks c d) (s : Fin d.rows.size) :
    rowSupport d s (row_det h s) \ walls c ⊆ sourceSet c := by
  rintro x ⟨hx,hw⟩
  apply (source_iff_rows c x).mpr
  intro g
  rw [← gate_eval]
  have hz : eval (originalGate c g) x ≠ 0 := fun z => hw (mem_iUnion.mpr ⟨g,z⟩)
  exact (nonneg_on (fun k => h.2.2.1 g ⟨_,(h.2.1 s).2.1 k⟩) hx).lt_of_ne hz.symm

/-- The true integral of the original kernel on the complete pulling
row list is bounded by the true integral on this very original cell. -/
theorem sum_support_integrals_le (c : Cell) (d : Data) (h : Checks c d) :
    (∑ s : Fin d.rows.size, ∫ x in rowSupport d s (row_det h s), kernel c x) ≤
      ∫ x in sourceSet c, kernel c x := by
  let A := fun s : Fin d.rows.size => rowSupport d s (row_det h s)
  let overlap := ⋃ s : Fin d.rows.size, ⋃ t : Fin d.rows.size, if s = t then ∅ else A s ∩ A t
  let exc := walls c ∪ overlap
  let good := fun s => A s \ exc
  have hn : volume overlap = 0 := by
    apply measure_iUnion_null
    intro s
    apply measure_iUnion_null
    intro t
    by_cases hm : s = t
    · simp [hm]
    · simp only [if_neg hm]; exact within_cell_null h hm
  have he : volume exc = 0 := measure_union_null (walls_null h) hn
  have ha (s : Fin d.rows.size) : MeasurableSet (A s) := support_measurable _ _
  have hmeas : MeasurableSet exc := by
    apply MeasurableSet.union
    · apply MeasurableSet.iUnion
      intro g
      exact (isClosed_eq (P2OriginalSaving19OwnedSource.eval_continuous _) continuous_const).measurableSet
    · apply MeasurableSet.iUnion
      intro s
      apply MeasurableSet.iUnion
      intro t
      by_cases hm : s = t
      · simp [hm]
      · simp only [if_neg hm]; exact (ha s).inter (ha t)
  have hg (s : Fin d.rows.size) : good s ⊆ sourceSet c :=
    fun _ hx => support_off_walls h s ⟨hx.1,fun hw => hx.2 (Or.inl hw)⟩
  have hd : Pairwise (fun s t => Disjoint (good s) (good t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    rintro x ⟨hs,hs'⟩ ⟨ht,_⟩
    apply hs'
    right
    exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨t,by simpa only [if_neg hst] using And.intro hs ht⟩⟩
  have hae (s : Fin d.rows.size) : good s =ᵐ[volume] A s := by
    have hne : ∀ᵐ x : Point ∂volume, x ∉ exc := by rw [ae_iff]; simpa only [not_not] using he
    filter_upwards [hne] with x hx
    simp [good,hx]
  have hU := integral_iUnion_fintype (fun s => (ha s).diff hmeas) hd
    (fun s => (integrableOn_kernel c).mono_set (hg s))
  change (∫ x in ⋃ s, good s, kernel c x) = ∑ s, ∫ x in good s, kernel c x at hU
  have hE : (∑ s, ∫ x in good s, kernel c x) = ∑ s, ∫ x in A s, kernel c x :=
    Finset.sum_congr rfl (fun s _ => setIntegral_congr_set (hae s))
  rw [← hE,← hU]
  apply setIntegral_mono_set (integrableOn_kernel c)
  · filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with x hx
    exact (kernel_bounds hx).1
  · exact Filter.Eventually.of_forall (iUnion_subset hg)

end
end ImbalancedChen.P2OriginalFull87PullingCell
