import ImbalancedChen.P4AClosedTreeCoordinatePropagation
import ImbalancedChen.VariableEnvelope
import Mathlib.Data.Finset.Sort

/-!
SOURCE_WRITTEN / UNCOMPILED / MAIN OPEN30.

Original producer: numerical-third-compact-independent-20261010.py,
SHA256 005fcc24c3431753e2530ab90f70e80d2256b3691cd45d14e13eb9191b0caa7c.
cap_bounds asserts x1<=M or M<=x0. seeds uses sorted({z0,M,R}) for z0<M
and [z0,R] otherwise. Every later split changes an integer upper endpoint
by min, or an integer lower endpoint by max. These exact source operations
prove the guard without requiring a nonempty child or historical tree bytes.
-/
namespace ImbalancedChen.P4AOriginalMuSplitInvariantSourceOnly

noncomputable section
open Set OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly

abbrev IntegerPoint := Fin 3 → ℤ

def noCrossMu (M : ℤ) (axis : Fin 3) (a b : IntegerPoint) : Prop :=
  b axis ≤ M ∨ M ≤ a axis

theorem leftIntegerUpper_le (b : IntegerPoint) (axis i : Fin 3) (cut : ℤ) :
    leftIntegerUpper b axis cut i ≤ b i := by
  by_cases hi : i = axis
  · subst i
    simpa only [leftIntegerUpper, Function.update_same] using min_le_left (b axis) cut
  · simp [leftIntegerUpper, hi]

theorem le_rightIntegerLower (a : IntegerPoint) (axis i : Fin 3) (cut : ℤ) :
    a i ≤ rightIntegerLower a axis cut i := by
  by_cases hi : i = axis
  · subst i
    simpa only [rightIntegerLower, Function.update_same] using le_max_left (a axis) cut
  · simp [rightIntegerLower, hi]

/-- Arbitrary integer left cuts inherit either side of the original guard. -/
theorem noCrossMu_left {M : ℤ} {i : Fin 3} {a b : IntegerPoint}
    (h : noCrossMu M i a b) (axis : Fin 3) (cut : ℤ) :
    noCrossMu M i a (leftIntegerUpper b axis cut) := by
  rcases h with hb | ha
  · exact Or.inl ((leftIntegerUpper_le b axis i cut).trans hb)
  · exact Or.inr ha

/-- Arbitrary integer right cuts inherit either side, even if the child is empty. -/
theorem noCrossMu_right {M : ℤ} {i : Fin 3} {a b : IntegerPoint}
    (h : noCrossMu M i a b) (axis : Fin 3) (cut : ℤ) :
    noCrossMu M i (rightIntegerLower a axis cut) b := by
  rcases h with hb | ha
  · exact Or.inl hb
  · exact Or.inr (ha.trans (le_rightIntegerLower a axis i cut))

/-- Every descendant endpoint pair from the actual original tree inherits
the seed interval guard. There is no nonemptiness or valid-midpoint premise. -/
theorem integerLeafBoxes_noCrossMu (tree : ClosedCutTree) (M : ℤ) (i : Fin 3)
    (a b : IntegerPoint) (h : noCrossMu M i a b)
    (bounds : IntegerPoint × IntegerPoint) (hb : bounds ∈ integerLeafBoxes tree a b) :
    noCrossMu M i bounds.1 bounds.2 := by
  induction tree generalizing a b with
  | leaf =>
      have he : bounds = (a,b) := by simpa only [integerLeafBoxes, List.mem_singleton] using hb
      simpa only [he] using h
  | split axis cut left right ihL ihR =>
      change bounds ∈ integerLeafBoxes left a (leftIntegerUpper b axis cut) ++
        integerLeafBoxes right (rightIntegerLower a axis cut) b at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ihL a (leftIntegerUpper b axis cut) (noCrossMu_left h axis cut) hb
      · exact ihR (rightIntegerLower a axis cut) b (noCrossMu_right h axis cut) hb

/-- Literal zip(cuts,cuts[1:]) used by the seed producer. -/
def consecutivePairs (cuts : List ℤ) : List (ℤ × ℤ) := cuts.zip cuts.tail

theorem consecutivePairs_mem_endpoints (cuts : List ℤ) :
    ∀ {x y : ℤ}, (x,y) ∈ consecutivePairs cuts → x ∈ cuts ∧ y ∈ cuts := by
  induction cuts with
  | nil => intro x y h; simp [consecutivePairs] at h
  | cons a tail ih =>
      intro x y h
      cases tail with
      | nil => simp [consecutivePairs] at h
      | cons b rest =>
          change (x,y) ∈ (a,b) :: consecutivePairs (b::rest) at h
          rcases List.mem_cons.mp h with h | h
          · have he : x=a ∧ y=b := by simpa only [Prod.mk.injEq] using h
            rcases he with ⟨rfl,rfl⟩
            simp
          · have he := ih h
            exact ⟨List.mem_cons_of_mem a he.1, List.mem_cons_of_mem a he.2⟩

/-- A true finite ordered cut list containing M cannot have M strictly
inside one of its adjacent intervals. Repeated cuts are allowed. -/
theorem ordered_cutList_consecutive_noCross (cuts : List ℤ) (M : ℤ) :
    cuts.Pairwise (· ≤ ·) → M ∈ cuts →
      ∀ {x y : ℤ}, (x,y) ∈ consecutivePairs cuts → y ≤ M ∨ M ≤ x := by
  induction cuts with
  | nil => intro _ hM; simp at hM
  | cons a tail ih =>
      intro horder hM x y hpair
      cases tail with
      | nil => simp [consecutivePairs] at hpair
      | cons b rest =>
          have ho := List.pairwise_cons.mp horder
          change (x,y) ∈ (a,b) :: consecutivePairs (b::rest) at hpair
          rcases List.mem_cons.mp hpair with hpair | hpair
          · have he : x=a ∧ y=b := by simpa only [Prod.mk.injEq] using hpair
            rcases he with ⟨rfl,rfl⟩
            rcases List.mem_cons.mp hM with hM | hM
            · subst M
              exact Or.inr le_rfl
            · rcases List.mem_cons.mp hM with hM | hM
              · subst M
                exact Or.inl le_rfl
              · exact Or.inl ((List.pairwise_cons.mp ho.2).1 M hM)
          · rcases List.mem_cons.mp hM with hM | hM
            · subst M
              exact Or.inr (ho.1 x (consecutivePairs_mem_endpoints (b::rest) hpair).1)
            · exact ih ho.2 hM hpair

/-- Exact Python seed xy-list: sorted set when z0<M; plain pair otherwise. -/
def sourceSeedXYCuts (z0 M R : ℤ) : List ℤ :=
  if z0 < M then ({z0,M,R} : Finset ℤ).sort (· ≤ ·) else [z0,R]

/-- The actual source seed construction supplies the guard from integer
membership/order, without taking that desired guard as an input. -/
theorem sourceSeedXYCuts_noCross (z0 M R x0 x1 : ℤ)
    (h : (x0,x1) ∈ consecutivePairs (sourceSeedXYCuts z0 M R)) :
    x1 ≤ M ∨ M ≤ x0 := by
  by_cases hz : z0 < M
  · apply ordered_cutList_consecutive_noCross
      (({z0,M,R} : Finset ℤ).sort (· ≤ ·)) M
    · exact Finset.pairwise_sort _ _
    · simp
    · simpa only [sourceSeedXYCuts, if_pos hz] using h
  · have he : x0=z0 ∧ x1=R := by
      simpa [sourceSeedXYCuts, hz, consecutivePairs] using h
    exact Or.inr ((le_of_not_gt hz).trans he.1.ge)

def seedLower (x0 y0 z0 : ℤ) : IntegerPoint := ![x0,y0,z0]
def seedUpper (x1 y1 z1 : ℤ) : IntegerPoint := ![x1,y1,z1]

theorem source_seed_noCross_xy (z0 z1 M R x0 x1 y0 y1 : ℤ)
    (hx : (x0,x1) ∈ consecutivePairs (sourceSeedXYCuts z0 M R))
    (hy : (y0,y1) ∈ consecutivePairs (sourceSeedXYCuts z0 M R)) :
    noCrossMu M 0 (seedLower x0 y0 z0) (seedUpper x1 y1 z1) ∧
      noCrossMu M 1 (seedLower x0 y0 z0) (seedUpper x1 y1 z1) := by
  constructor
  · simpa only [noCrossMu, seedLower, seedUpper, Matrix.cons_val_zero] using
      sourceSeedXYCuts_noCross z0 M R x0 x1 hx
  · simpa only [noCrossMu, seedLower, seedUpper, Matrix.cons_val_one] using
      sourceSeedXYCuts_noCross z0 M R y0 y1 hy

/-- Direct seed-to-all-descendants API for both x and y intervals. -/
theorem source_seed_descendants_noCross_xy (tree : ClosedCutTree)
    (z0 z1 M R x0 x1 y0 y1 : ℤ)
    (hx : (x0,x1) ∈ consecutivePairs (sourceSeedXYCuts z0 M R))
    (hy : (y0,y1) ∈ consecutivePairs (sourceSeedXYCuts z0 M R))
    (bounds : IntegerPoint × IntegerPoint)
    (hb : bounds ∈ integerLeafBoxes tree (seedLower x0 y0 z0) (seedUpper x1 y1 z1)) :
    noCrossMu M 0 bounds.1 bounds.2 ∧ noCrossMu M 1 bounds.1 bounds.2 := by
  have hs := source_seed_noCross_xy z0 z1 M R x0 x1 y0 y1 hx hy
  exact ⟨integerLeafBoxes_noCrossMu tree M 0 _ _ hs.1 bounds hb,
    integerLeafBoxes_noCrossMu tree M 1 _ _ hs.2 bounds hb⟩

/-- Exact original M=int((25/128)*D), with the original D divisible by 128. -/
def originalMuInteger : ℤ := (25 * (48000 * 2^24)) / 128

theorem originalMuInteger_decode :
    (originalMuInteger : ℝ) / coordinateDenominator = VariableEnvelope.mu := by
  norm_num [originalMuInteger, coordinateDenominator, VariableEnvelope.mu]

theorem noCrossMu_real_guard (a b : IntegerPoint) (i : Fin 3)
    (h : noCrossMu originalMuInteger i a b) :
    decodeCoordinates b i ≤ VariableEnvelope.mu ∨
      VariableEnvelope.mu ≤ decodeCoordinates a i := by
  rcases h with hb | ha
  · have hc : (b i : ℝ) ≤ (originalMuInteger : ℝ) := by exact_mod_cast hb
    left
    exact (div_le_div_of_nonneg_right hc original_coordinateDenominator_pos.le).trans_eq
      originalMuInteger_decode
  · have hc : (originalMuInteger : ℝ) ≤ (a i : ℝ) := by exact_mod_cast ha
    right
    exact originalMuInteger_decode.symm.trans_le
      (div_le_div_of_nonneg_right hc original_coordinateDenominator_pos.le)

/-- The producer dispatches above first at x0=M. If that test fails,
the inherited seed invariant supplies the required below-mu upper endpoint. -/
theorem original_cap_bounds_dispatch_guard (a b : IntegerPoint)
    (h : noCrossMu originalMuInteger 0 a b) :
    if originalMuInteger ≤ a 0 then VariableEnvelope.mu ≤ decodeCoordinates a 0
    else decodeCoordinates b 0 ≤ VariableEnvelope.mu := by
  split_ifs with ha
  · have hc : (originalMuInteger : ℝ) ≤ (a 0 : ℝ) := by exact_mod_cast ha
    exact originalMuInteger_decode.symm.trans_le
      (div_le_div_of_nonneg_right hc original_coordinateDenominator_pos.le)
  · rcases h with hb | hx
    · have hc : (b 0 : ℝ) ≤ (originalMuInteger : ℝ) := by exact_mod_cast hb
      exact (div_le_div_of_nonneg_right hc original_coordinateDenominator_pos.le).trans_eq
        originalMuInteger_decode
    · exact False.elim (ha hx)

/-- End-to-end guard supplier from literal seed zip-membership to every
actual descendant box. No noCrossMu or desired dispatch guard is an input. -/
theorem source_seed_descendants_cap_bounds_guard (tree : ClosedCutTree)
    (z0 z1 R x0 x1 y0 y1 : ℤ)
    (hx : (x0,x1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger R))
    (hy : (y0,y1) ∈ consecutivePairs (sourceSeedXYCuts z0 originalMuInteger R))
    (bounds : IntegerPoint × IntegerPoint)
    (hb : bounds ∈ integerLeafBoxes tree (seedLower x0 y0 z0) (seedUpper x1 y1 z1)) :
    (bounds.2 0 ≤ originalMuInteger ∨ originalMuInteger ≤ bounds.1 0) ∧
      (bounds.2 1 ≤ originalMuInteger ∨ originalMuInteger ≤ bounds.1 1) ∧
      (if originalMuInteger ≤ bounds.1 0 then
        VariableEnvelope.mu ≤ decodeCoordinates bounds.1 0
       else decodeCoordinates bounds.2 0 ≤ VariableEnvelope.mu) := by
  have hs := source_seed_descendants_noCross_xy tree z0 z1 originalMuInteger R
    x0 x1 y0 y1 hx hy bounds hb
  exact ⟨hs.1, hs.2, original_cap_bounds_dispatch_guard bounds.1 bounds.2 hs.1⟩

end
end ImbalancedChen.P4AOriginalMuSplitInvariantSourceOnly
