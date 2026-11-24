import ImbalancedChen.P2Winner9RationalSimplexData

/-! Positivity and bound certificates for the decoder's finite rational cap formulas. -/

namespace ImbalancedChen.P2Winner9RationalSimplexCaps

open ImbalancedChen.P2Winner9RationalSimplexData
open ImbalancedChen.P2Winner9Row22Arithmetic
  (RationalVertices VertexNormalization rawGap rawP rawFactor)

private theorem le_foldl_max_initial {α : Type*} [LinearOrder α] (l : List α) (x : α) :
    x ≤ l.foldl max x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => exact le_trans (le_max_left x a) (ih (max x a))

private theorem le_foldl_max_of_mem {α : Type*} [LinearOrder α]
    (l : List α) (x : α) {a : α} (ha : a ∈ l) : a ≤ l.foldl max x := by
  induction l generalizing x with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst b
      exact le_trans (le_max_right x a) (le_foldl_max_initial l (max x a))
    · exact ih (max x b) h

private theorem foldl_min_le_of_mem {α : Type*} [LinearOrder α]
    (l : List α) (x : α) {a : α} (ha : a ∈ l) : l.foldl min x ≤ a :=
  le_foldl_max_of_mem (α := αᵒᵈ) l x ha

/-- The common upper bound in the archived decoder. -/
def upper (v : RationalVertices) (means : Fin 10 → ℚ) : ℚ :=
  (List.ofFn (rawP v means)).foldl max 0

/-- The positive lower bound in the archived decoder. -/
def lower (v : RationalVertices) (means : Fin 10 → ℚ) : ℚ :=
  (List.ofFn (rawP v means)).foldl min 1

/-- The factorwise upper bound is taken across the common P bound
and the normalized factors on every original vertex. -/
def transverseUpper (v : RationalVertices) (means : Fin 10 → ℚ) (j : Fin 10) : ℚ :=
  (List.ofFn (fun i : Fin 9 => rawFactor v i j / means j)).foldl max (upper v means)

theorem rawP_le_upper (v : RationalVertices) (means : Fin 10 → ℚ) (i : Fin 9) :
    rawP v means i ≤ upper v means :=
  le_foldl_max_of_mem _ 0 (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem upper_pos (v : RationalVertices) (means : Fin 10 → ℚ)
    (h : 0 < rawP v means 0) : 0 < upper v means :=
  lt_of_lt_of_le h (rawP_le_upper v means 0)

theorem lower_le_rawP (v : RationalVertices) (means : Fin 10 → ℚ) (i : Fin 9) :
    lower v means ≤ rawP v means i :=
  foldl_min_le_of_mem _ 1 (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem lower_pos (v : RationalVertices) (means : Fin 10 → ℚ)
    (hp : ∀ i : Fin 9, 0 < rawP v means i) : 0 < lower v means := by
  have haux (l : List ℚ) (x : ℚ) (hx : 0 < x) (hl : ∀ b ∈ l, 0 < b) :
      0 < l.foldl min x := by
    induction l generalizing x with
    | nil => exact hx
    | cons b l ih =>
      exact ih (min x b) (lt_min hx (hl b (List.mem_cons_self ..)))
        (fun c hc => hl c (List.mem_cons_of_mem b hc))
  refine haux _ 1 (by norm_num) (fun b hb => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact hp i

theorem upper_le_transverseUpper (v : RationalVertices) (means : Fin 10 → ℚ) (j : Fin 10) :
    upper v means ≤ transverseUpper v means j :=
  le_foldl_max_initial _ _

theorem normalizedFactor_le_transverseUpper (v : RationalVertices) (means : Fin 10 → ℚ)
    (i : Fin 9) (j : Fin 10) :
    rawFactor v i j / means j ≤ transverseUpper v means j :=
  le_foldl_max_of_mem _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem rawP_le_transverseUpper (v : RationalVertices) (means : Fin 10 → ℚ) (i : Fin 9)
    (j : Fin 10) : rawP v means i ≤ transverseUpper v means j :=
  (rawP_le_upper v means i).trans (upper_le_transverseUpper v means j)

/-- The archived cap choices supply the upper-bound normalization guards
directly from rational P positivity, with the original ordered vertices. -/
def ofPhysicalVertices (v : RationalVertices) (means : Fin 10 → ℚ) (jensen : ℚ)
    (hgap : ∀ i, 0 ≤ rawGap v i) (hgapSum : 0 < ∑ i, rawGap v i)
    (hP : 0 < rawP v means 0) (hjensen : 0 ≤ jensen) : Input :=
  ofRawVertices v means (upper v means) (transverseUpper v means) jensen hgap hgapSum
    (upper_pos v means hP) (rawP_le_upper v means)
    (fun j => lt_of_lt_of_le (upper_pos v means hP) (upper_le_transverseUpper v means j)) hjensen

theorem ofPhysicalVertices_normalization (v : RationalVertices) (means : Fin 10 → ℚ)
    (jensen : ℚ) (hgap : ∀ i, 0 ≤ rawGap v i) (hgapSum : 0 < ∑ i, rawGap v i)
    (hP : 0 < rawP v means 0) (hjensen : 0 ≤ jensen) :
    let a := ofPhysicalVertices v means jensen hgap hgapSum hP hjensen
    VertexNormalization v means (upper v means) (toSimplexData a) (gapDen a) := by
  exact ofRawVertices_normalization ..

end ImbalancedChen.P2Winner9RationalSimplexCaps
