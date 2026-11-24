import ImbalancedChen.P2OriginalSaving16OriginalArchive
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Reverse pulling needs only supporting faces and an antichain of children
for its nonoverlap conclusion. Coverage and face dimensions are not inputs.
The induction constructs a separating rational affine row. At a common
pivot p it extends a child separator a by g(p)*a-a(p)*g, where g=0 on the
child and g(p)>0. At different children it uses h(p)*g-g(p)*h.

The finite archive checks are in the next module; this module does not
decide a finite geometric consequence or accept disjointness as a premise.
-/
namespace ImbalancedChen.P2OriginalSaving16PullingFaceInduction

open scoped BigOperators
open P2OriginalSaving16OriginalArchive (QPoint evalQ)

abbrev AffineRow := Fin 9 → ℚ

/-- The source's ordered max-pivot recursion. Fuel nine is dimension+one
at the original root, and is used only to make recursion structural. -/
def pull (pivot : List Nat → Nat) (children : List Nat → List (List Nat)) :
    Nat → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, face =>
      if face.length = 1 then [face]
      else (children face).flatMap fun child =>
        (pull pivot children n child).map (fun row => pivot face :: row)

/-- Finite incidence conditions, all at the vertex-ID level. The children
need not exhaust the boundary: a legal inner family is sufficient.
`facet` is the original global facet-vertex incidence list. -/
def Shape {m : Nat} (facet : Fin m → List Nat)
    (pivot : List Nat → Nat) (children : List Nat → List (List Nat)) :
    Nat → List Nat → Prop
  | 0, _ => True
  | n + 1, face =>
      if face.length = 1 then True else
        pivot face ∈ face ∧
        (∀ v ∈ face, v ≤ pivot face) ∧
        (∀ child ∈ children face,
          child ⊆ face ∧ pivot face ∉ child ∧
          ∃ g : Fin m, ∀ v ∈ face, (v ∈ child ↔ v ∈ facet g)) ∧
        (∀ child ∈ children face, ∀ other ∈ children face,
          child ≠ other → ¬ child ⊆ other) ∧
        (∀ child ∈ children face, Shape facet pivot children n child)

instance shapeDecidable {m : Nat} (facet : Fin m → List Nat)
    (pivot : List Nat → Nat) (children : List Nat → List (List Nat))
    (n : Nat) (face : List Nat) : Decidable (Shape facet pivot children n face) := by
  induction n generalizing face with
  | zero => unfold Shape; infer_instance
  | succ n ih =>
      unfold Shape
      letI := ih
      infer_instance

theorem pull_row_subset {m : Nat} (facet : Fin m → List Nat)
    (pivot : List Nat → Nat) (children : List Nat → List (List Nat))
    {n : Nat} {face row : List Nat}
    (hshape : Shape facet pivot children n face)
    (hrow : row ∈ pull pivot children n face) : row ⊆ face := by
  induction n generalizing face row with
  | zero => simp [pull] at hrow
  | succ n ih =>
      by_cases hsingle : face.length = 1
      · have he : row = face := by simpa [pull, hsingle] using hrow
        simpa [he]
      · simp only [Shape, hsingle, if_false] at hshape
        simp only [pull, hsingle, if_false, List.mem_flatMap, List.mem_map] at hrow
        obtain ⟨child, hc, tail, ht, rfl⟩ := hrow
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hshape.1
        · exact (hshape.2.2.1 child hc).1
            (ih (hshape.2.2.2.2 child hc) ht hv)

/-- Rational affine combinations commute with evaluation. -/
theorem evalQ_combine (r s : ℚ) (a b : AffineRow) (x : QPoint) :
    evalQ (fun j => r * a j - s * b j) x =
      r * evalQ a x - s * evalQ b x := by
  simp only [evalQ, sub_mul, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum]
  ring

/-- The first genuinely geometric step: facet incidence and weak support
at the original vertices make an omitted pivot strictly positive. -/
theorem supporting_child {m : Nat} (vertex : Nat → QPoint)
    (gate : Fin m → AffineRow) (facet : Fin m → List Nat) (whole face child : List Nat)
    (pivot : Nat) (hface : face ⊆ whole) (hp : pivot ∈ face)
    (hc : child ⊆ face) (hpc : pivot ∉ child)
    (hinc : ∃ g : Fin m, ∀ v ∈ face, (v ∈ child ↔ v ∈ facet g))
    (hnonneg : ∀ g v, v ∈ whole → 0 ≤ evalQ (gate g) (vertex v))
    (hfacet : ∀ g v, v ∈ whole → (v ∈ facet g ↔ evalQ (gate g) (vertex v) = 0)) :
    ∃ g : Fin m,
      0 < evalQ (gate g) (vertex pivot) ∧
      (∀ v ∈ child, evalQ (gate g) (vertex v) = 0) ∧
      (∀ v ∈ face, 0 ≤ evalQ (gate g) (vertex v)) ∧
      (∀ v ∈ face, v ∉ child → 0 < evalQ (gate g) (vertex v)) := by
  obtain ⟨g, hg⟩ := hinc
  have hz (v : Nat) (hv : v ∈ face) :
      v ∈ child ↔ evalQ (gate g) (vertex v) = 0 :=
    (hg v hv).trans (hfacet g v (hface hv))
  have hpos (v : Nat) (hv : v ∈ face) (hn : v ∉ child) :
      0 < evalQ (gate g) (vertex v) :=
    lt_of_le_of_ne (hnonneg g v (hface hv))
      (fun he => hn ((hz v hv).2 he.symm))
  exact ⟨g, hpos pivot hp hpc,
    fun v hv => (hz v (hc hv)).1 hv,
    fun v hv => hnonneg g v (hface hv), hpos⟩

/-- Separating-wall induction for max-pivot reverse pulling. Every
separator is nonzero on an original vertex of the current face. Thus its
eventual ambient wall is proper, even though coverage is never asserted.
The max condition authenticates the producer; the geometric argument
works for any one common pivot at each face. -/
theorem pull_pair_separated {m : Nat} (vertex : Nat → QPoint)
    (gate : Fin m → AffineRow) (facet : Fin m → List Nat)
    (whole : List Nat) (pivot : List Nat → Nat)
    (children : List Nat → List (List Nat))
    (hnonneg : ∀ g v, v ∈ whole → 0 ≤ evalQ (gate g) (vertex v))
    (hfacet : ∀ g v, v ∈ whole → (v ∈ facet g ↔ evalQ (gate g) (vertex v) = 0))
    {n : Nat} {face left right : List Nat}
    (hface : face ⊆ whole) (hshape : Shape facet pivot children n face)
    (hl : left ∈ pull pivot children n face)
    (hr : right ∈ pull pivot children n face) (hne : left ≠ right) :
    ∃ a : AffineRow,
      (∀ v ∈ left, evalQ a (vertex v) ≤ 0) ∧
      (∀ v ∈ right, 0 ≤ evalQ a (vertex v)) ∧
      ∃ v ∈ face, evalQ a (vertex v) ≠ 0 := by
  classical
  induction n generalizing face left right with
  | zero => simp [pull] at hl
  | succ n ih =>
      by_cases hsingle : face.length = 1
      · have hle : left = face := by simpa [pull, hsingle] using hl
        have hre : right = face := by simpa [pull, hsingle] using hr
        exact False.elim (hne (hle.trans hre.symm))
      · simp only [Shape, hsingle, if_false] at hshape
        simp only [pull, hsingle, if_false, List.mem_flatMap, List.mem_map] at hl hr
        obtain ⟨child, hc, ls, hls, rfl⟩ := hl
        obtain ⟨other, hd, rs, hrs, rfl⟩ := hr
        have hcs := (hshape.2.2.1 child hc).1
        have hds := (hshape.2.2.1 other hd).1
        have hls_sub := pull_row_subset facet pivot children
          (hshape.2.2.2.2 child hc) hls
        have hrs_sub := pull_row_subset facet pivot children
          (hshape.2.2.2.2 other hd) hrs
        obtain ⟨g, hgp, hgz, hgn, hgt⟩ := supporting_child vertex gate facet
          whole face child (pivot face) hface hshape.1 hcs
          (hshape.2.2.1 child hc).2.1 (hshape.2.2.1 child hc).2.2 hnonneg hfacet
        by_cases hcd : child = other
        · subst other
          have htne : ls ≠ rs := fun he => hne (congrArg (List.cons (pivot face)) he)
          obtain ⟨a, hal, har, v, hv, hav⟩ := ih
            (fun v hv => hface (hcs hv)) (hshape.2.2.2.2 child hc) hls hrs htne
          let b : AffineRow := fun j =>
            evalQ (gate g) (vertex (pivot face)) * a j -
              evalQ a (vertex (pivot face)) * gate g j
          have hb (w : Nat) : evalQ b (vertex w) =
              evalQ (gate g) (vertex (pivot face)) * evalQ a (vertex w) -
                evalQ a (vertex (pivot face)) * evalQ (gate g) (vertex w) :=
            evalQ_combine _ _ _ _ _
          refine ⟨b, ?_, ?_, v, hcs hv, ?_⟩
          · intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · rw [hb]; ring_nf
            · rw [hb, hgz w (hls_sub hw), mul_zero, sub_zero]
              exact mul_nonpos_of_nonneg_of_nonpos hgp.le (hal w hw)
          · intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · rw [hb]; ring_nf
            · rw [hb, hgz w (hrs_sub hw), mul_zero, sub_zero]
              exact mul_nonneg hgp.le (har w hw)
          · rw [hb, hgz v hv, mul_zero, sub_zero]
            exact mul_ne_zero hgp.ne' hav
        · obtain ⟨h, hhp, hhz, hhn, hht⟩ := supporting_child vertex gate facet
            whole face other (pivot face) hface hshape.1 hds
            (hshape.2.2.1 other hd).2.1 (hshape.2.2.1 other hd).2.2 hnonneg hfacet
          have hnot := hshape.2.2.2.1 child hc other hd hcd
          obtain ⟨v, hv, hnv⟩ : ∃ v, v ∈ child ∧ v ∉ other := by
            by_contra h
            apply hnot
            intro v hv
            by_contra hnv
            exact h ⟨v, hv, hnv⟩
          let a : AffineRow := fun j =>
            evalQ (gate h) (vertex (pivot face)) * gate g j -
              evalQ (gate g) (vertex (pivot face)) * gate h j
          have ha (w : Nat) : evalQ a (vertex w) =
              evalQ (gate h) (vertex (pivot face)) * evalQ (gate g) (vertex w) -
                evalQ (gate g) (vertex (pivot face)) * evalQ (gate h) (vertex w) :=
            evalQ_combine _ _ _ _ _
          refine ⟨a, ?_, ?_, v, hcs hv, ?_⟩
          · intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · rw [ha]; ring_nf
            · rw [ha, hgz w (hls_sub hw), mul_zero, zero_sub]
              exact neg_nonpos.mpr (mul_nonneg hgp.le (hhn w (hcs (hls_sub hw))))
          · intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · rw [ha]; ring_nf
            · rw [ha, hhz w (hrs_sub hw), mul_zero, sub_zero]
              exact mul_nonneg hhp.le (hgn w (hds (hrs_sub hw)))
          · rw [ha, hgz v hv, mul_zero, zero_sub]
            exact neg_ne_zero.mpr (mul_ne_zero hgp.ne' (hht v (hcs hv) hnv).ne')

end ImbalancedChen.P2OriginalSaving16PullingFaceInduction
