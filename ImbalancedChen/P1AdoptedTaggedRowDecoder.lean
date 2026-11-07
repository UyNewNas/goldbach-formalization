import ImbalancedChen.P1AdoptedE0E1ActualSupport
import Mathlib.Data.Fintype.BigOperators

/-!
SOURCE ONLY. No Lean invocation, kernel replay, or numerical checker was run.

The import is the proposed integration name of the sibling source-only file
e0-e1-actual-support/P1AdoptedE0E1ActualSupport.lean.txt.

The frozen JSON has E0 first (6091 entries), then E1 (11481 entries), each
lexicographically ordered by actual (t_index,u_index). FullMask.Row instead
has all 186 t-strips together, with u increasing in each strip. These orders
are different. The equivalence below preserves actual coordinates and tags;
it does not silently identify the original JSON ordinal with a Row ordinal.

There is no w_index field in the frozen JSON. The local indices here are
integer u offsets. The inner-fibre variables z,w are not outer row indices.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P1E0E1.TaggedDecoder

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A literal finite-data check, separate from every analytic certificate. -/
theorem split_bounds (i : Fin 186) :
    firstU i ≤ e0FirstU i ∧ e0FirstU i ≤ 512 := by
  have h : ∀ k : Fin 186, firstU k ≤ e0FirstU k ∧ e0FirstU k ≤ 512 := by
    decide +kernel
  exact h i

/-- The E0 terminal portion of each of the actual 186 strips. Empty strips
remain empty; no uniform strip length is introduced. -/
abbrev E0Local := (i : Fin 186) × Fin (512 - e0FirstU i)

/-- The E1 initial portion of each actual strip. -/
abbrev E1Local := (i : Fin 186) × Fin (e0FirstU i - firstU i)

def ofE0 (q : E0Local) : Row :=
  ⟨q.1, ⟨e0FirstU q.1 - firstU q.1 + q.2.val, by
    have hb := split_bounds q.1
    have hq := q.2.isLt
    omega⟩⟩

def ofE1 (q : E1Local) : Row :=
  ⟨q.1, ⟨q.2.val, by
    have hb := split_bounds q.1
    have hq := q.2.isLt
    omega⟩⟩

@[simp] theorem indices_ofE0 (q : E0Local) :
    indices (ofE0 q) = (326 + q.1.val, e0FirstU q.1 + q.2.val) := by
  apply Prod.ext
  · rfl
  · have hb := split_bounds q.1
    dsimp [indices, ofE0]
    omega

@[simp] theorem indices_ofE1 (q : E1Local) :
    indices (ofE1 q) = (326 + q.1.val, firstU q.1 + q.2.val) := by
  rfl

theorem ofE0_label (q : E0Local) : IsE0 (ofE0 q) := by
  change e0FirstU q.1 ≤ (indices (ofE0 q)).2
  rw [indices_ofE0]
  omega

theorem ofE1_label (q : E1Local) : IsE1 (ofE1 q) := by
  change firstU q.1 + q.2.val < e0FirstU q.1
  have hq := q.2.isLt
  omega

theorem ofE0_injective : Function.Injective ofE0 := by
  rintro ⟨i,j⟩ ⟨k,l⟩ he
  have hi : i = k := congrArg (fun r : Row => r.1) he
  subst k
  have hu := congrArg (fun r : Row => (indices r).2) he
  rw [indices_ofE0, indices_ofE0] at hu
  have hj : j = l := Fin.ext (Nat.add_left_cancel hu)
  subst l
  rfl

theorem ofE1_injective : Function.Injective ofE1 := by
  rintro ⟨i,j⟩ ⟨k,l⟩ he
  have hi : i = k := congrArg (fun r : Row => r.1) he
  subst k
  have hu := congrArg (fun r : Row => (indices r).2) he
  rw [indices_ofE1, indices_ofE1] at hu
  have hj : j = l := Fin.ext (Nat.add_left_cancel hu)
  subst l
  rfl

def toE0 (r : Row) (h : IsE0 r) : E0Local :=
  ⟨r.1, ⟨(indices r).2 - e0FirstU r.1, by
    have hu := (indices_bounds r).2.2
    dsimp [IsE0] at h
    omega⟩⟩

def toE1 (r : Row) (h : IsE1 r) : E1Local :=
  ⟨r.1, ⟨r.2.val, by
    dsimp [IsE1, indices] at h
    omega⟩⟩

theorem ofE0_toE0 (r : Row) (h : IsE0 r) : ofE0 (toE0 r h) = r := by
  apply indices_injective
  rw [indices_ofE0]
  apply Prod.ext
  · rfl
  · dsimp [toE0]
    dsimp [IsE0] at h
    omega

theorem ofE1_toE1 (r : Row) (h : IsE1 r) : ofE1 (toE1 r h) = r := by
  apply indices_injective
  rw [indices_ofE1]
  rfl

/-- Executable tag test and integer local-u decoder. -/
def splitRow (r : Row) : E0Local ⊕ E1Local :=
  if h : IsE0 r then Sum.inl (toE0 r h)
  else Sum.inr (toE1 r (by exact lt_of_not_ge h))

def mergeRow : E0Local ⊕ E1Local → Row := Sum.elim ofE0 ofE1

theorem merge_split (r : Row) : mergeRow (splitRow r) = r := by
  unfold splitRow
  split_ifs with h
  · exact ofE0_toE0 r h
  · exact ofE1_toE1 r (by exact lt_of_not_ge h)

theorem mergeRow_injective : Function.Injective mergeRow := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact congrArg Sum.inl (ofE0_injective h)
    | inr y =>
      change ofE0 x = ofE1 y at h
      have hx := ofE0_label x
      rw [h] at hx
      exact False.elim (row_labels_disjoint (ofE1 y) ⟨hx, ofE1_label y⟩)
  | inr x =>
    cases y with
    | inl y =>
      change ofE1 x = ofE0 y at h
      have hx := ofE1_label x
      rw [h] at hx
      exact False.elim (row_labels_disjoint (ofE0 y) ⟨ofE0_label y, hx⟩)
    | inr y =>
      exact congrArg Sum.inr (ofE1_injective h)

theorem tagged_indices_injective :
    Function.Injective (fun q : E0Local ⊕ E1Local => indices (mergeRow q)) := by
  exact indices_injective.comp mergeRow_injective

/-- A coordinate-preserving, explicit E0/E1 decomposition of every actual
adopted row. Both inverse laws are proved, with the real strip lengths. -/
def rowEquiv : Row ≃ E0Local ⊕ E1Local where
  toFun := splitRow
  invFun := mergeRow
  left_inv := merge_split
  right_inv := by
    intro q
    apply mergeRow_injective
    exact merge_split (mergeRow q)

@[simp] theorem rowEquiv_symm_inl (q : E0Local) :
    rowEquiv.symm (Sum.inl q) = ofE0 q := by
  rfl

@[simp] theorem rowEquiv_symm_inr (q : E1Local) :
    rowEquiv.symm (Sum.inr q) = ofE1 q := by
  rfl

theorem e0_membership_iff (r : Row) :
    (∃ q : E0Local, ofE0 q = r) ↔ IsE0 r := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ofE0_label q
  · intro h
    exact ⟨toE0 r h, ofE0_toE0 r h⟩

theorem e1_membership_iff (r : Row) :
    (∃ q : E1Local, ofE1 q = r) ↔ IsE1 r := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ofE1_label q
  · intro h
    exact ⟨toE1 r h, ofE1_toE1 r h⟩

/-- Exact decoder membership using actual t and u integer grid coordinates. -/
theorem e0_indices_cover (t u : ℕ) :
    (∃ q : E0Local, indices (ofE0 q) = (t,u)) ↔
      ∃ i : Fin 186, t = 326 + i.val ∧ e0FirstU i ≤ u ∧ u < 512 := by
  constructor
  · rintro ⟨⟨i,j⟩, h⟩
    rw [indices_ofE0] at h
    have ht := congrArg Prod.fst h
    have hu := congrArg Prod.snd h
    have hj := j.isLt
    have hb := split_bounds i
    exact ⟨i, ht.symm, by omega, by omega⟩
  · rintro ⟨i, ht, hlo, hhi⟩
    refine ⟨⟨i, ⟨u - e0FirstU i, by omega⟩⟩, ?_⟩
    rw [indices_ofE0]
    apply Prod.ext
    · exact ht.symm
    · dsimp
      omega

theorem e1_indices_cover (t u : ℕ) :
    (∃ q : E1Local, indices (ofE1 q) = (t,u)) ↔
      ∃ i : Fin 186, t = 326 + i.val ∧ firstU i ≤ u ∧ u < e0FirstU i := by
  constructor
  · rintro ⟨⟨i,j⟩, h⟩
    rw [indices_ofE1] at h
    have ht := congrArg Prod.fst h
    have hu := congrArg Prod.snd h
    have hj := j.isLt
    exact ⟨i, ht.symm, by omega, by omega⟩
  · rintro ⟨i, ht, hlo, hhi⟩
    refine ⟨⟨i, ⟨u - firstU i, by omega⟩⟩, ?_⟩
    rw [indices_ofE1]
    apply Prod.ext
    · exact ht.symm
    · dsimp
      omega

/-- The following cardinal checks inspect only 186 small strip lengths.
They do not evaluate any gain, logarithm, cutoff, saved floor, or integral. -/
theorem e0_card : Fintype.card E0Local = 6091 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  decide +kernel

theorem e1_card : Fintype.card E1Local = 11481 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  decide +kernel

theorem cardinality_preserved :
    Fintype.card Row = Fintype.card E0Local + Fintype.card E1Local := by
  rw [Fintype.card_congr rowEquiv, Fintype.card_sum]

/-- Reindex any finite assembly by the actual E0/E1 local rows. This also
applies to row integrals without adding an analytic hypothesis. -/
theorem sum_rows_split {M : Type*} [AddCommMonoid M] (f : Row → M) :
    (∑ r : Row, f r) =
      (∑ q : E0Local, f (ofE0 q)) + ∑ q : E1Local, f (ofE1 q) := by
  calc
    (∑ r : Row, f r) =
        ∑ q : E0Local ⊕ E1Local, f (rowEquiv.symm q) :=
      (rowEquiv.symm.sum_comp f).symm
    _ = (∑ q : E0Local, f (ofE0 q)) + ∑ q : E1Local, f (ofE1 q) := by
      rw [Fintype.sum_sum_type]
      rfl

/-- Prefix offsets for the original JSON order, with E0 first and E1
second. Their source provenance is recorded in the companion manifest;
no assertion of JSON parsing inside Lean is made. -/
def e0Offset (i : Fin 186) : ℕ :=
  ∑ k : Fin 186, if k.val < i.val then 512 - e0FirstU k else 0

def e1Offset (i : Fin 186) : ℕ :=
  ∑ k : Fin 186, if k.val < i.val then e0FirstU k - firstU k else 0

def sourceOrdinal : E0Local ⊕ E1Local → ℕ
  | .inl q => e0Offset q.1 + q.2.val
  | .inr q => 6091 + e1Offset q.1 + q.2.val

def sortedOffset (i : Fin 186) : ℕ :=
  ∑ k : Fin 186, if k.val < i.val then 512 - firstU k else 0

def sortedOrdinal (r : Row) : ℕ := sortedOffset r.1 + r.2.val

end ImbalancedChen.Certificates.PairedV2.FullMask.P1E0E1.TaggedDecoder
