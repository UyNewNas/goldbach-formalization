import ImbalancedChen.Part5OriginalCausalSmoothAtlas
import ImbalancedChen.Part5OriginalH430FullMemberMeasurable

/-! Finite smooth lower/upper *functions* for the actual prefix pullback,
not a claim that a partition of unity alone approximates a discontinuity.
The undecided weight is exposed exactly. No boundary is dismissed because
it is called an equality. All upper/lower coefficients are chosen before N.
Source only; no assertion that the original arithmetic controls every mixed box. -/
namespace ImbalancedChen.Part5OriginalH430JointQueryEnclosure
noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalCausalSmoothAtlas
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430NativeQueryPaths Part5OriginalH430FullMemberStrips
open Part5OriginalUpsilon5CausalDictionary

variable {ι : Type*} [Fintype ι]

def Cube (x : ι → ℝ) : Prop := ∀ i, x i ∈ Icc (0:ℝ) 1
def hit (P : Plan) (D : Set (ι → ℝ)) (j : ι → Code P) : Prop :=
  ∃ x, Cube x ∧ atom P j x ≠ 0 ∧ x ∈ D
def sure (P : Plan) (D : Set (ι → ℝ)) (j : ι → Code P) : Prop :=
  hit P D j ∧ ¬hit P Dᶜ j
def mixed (P : Plan) (D : Set (ι → ℝ)) (j : ι → Code P) : Prop :=
  hit P D j ∧ hit P Dᶜ j
def readout (P : Plan) (accept : (ι → Code P) → Prop) (x : ι → ℝ) : ℝ :=
  ∑ j : ι → Code P, if accept j then atom P j x else 0

theorem readout_smooth (P : Plan) (accept : (ι → Code P) → Prop) :
    ContDiff ℝ ∞ (readout P accept) := by
  classical
  unfold readout
  apply ContDiff.sum
  intro j _
  by_cases h : accept j
  · simpa only [if_pos h] using atom_smooth P j
  · simp only [if_neg h]; exact contDiff_const

theorem gap_exact (P : Plan) (D : Set (ι → ℝ)) (x : ι → ℝ) :
    readout P (hit P D) x = readout P (sure P D) x + readout P (mixed P D) x := by
  classical
  unfold readout
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : hit P D j <;> by_cases h' : hit P Dᶜ j <;> simp [h,h',sure,mixed]

theorem sharp_sandwich (P : Plan) (D : Set (ι → ℝ)) {x : ι → ℝ} (hx : Cube x) :
    readout P (sure P D) x ≤ (if x ∈ D then 1 else 0) ∧
      (if x ∈ D then 1 else 0) ≤ readout P (hit P D) x := by
  classical
  have hone := atom_total P hx
  by_cases h : x ∈ D
  · rw [if_pos h, ← hone]
    constructor
    · exact Finset.sum_le_sum (fun j _ => by
        by_cases hs : sure P D j <;> simp [hs,atom_nonneg])
    · apply Finset.sum_le_sum
      intro j _
      by_cases hh : hit P D j
      · simp [hh]
      · have hz : atom P j x = 0 := by
          by_contra hn
          exact hh ⟨x,hx,hn,h⟩
        simp [hh,hz]
  · rw [if_neg h]
    constructor
    · apply le_of_eq
      apply Finset.sum_eq_zero
      intro j _
      by_cases hs : sure P D j
      · rw [if_pos hs]
        by_contra hn
        exact hs.2 ⟨x,hx,hn,h⟩
      · simp [hs]
    · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [atom_nonneg])

/-- Identical positive-mass knot / inherit faces in the chart cost zero if the
predicate is constant there. Restriction is to a *single fixed original*
stratum; this lemma itself supplies no permission to discard its complement. -/
theorem no_mixed_of_constant (P : Plan) (D : Set (ι → ℝ)) (v : Prop)
    (hc : ∀ x, Cube x → (x ∈ D ↔ v)) (j : ι → Code P) : ¬mixed P D j := by
  rintro ⟨⟨x,hx,_,hy⟩,⟨z,hz,_,hn⟩⟩
  exact hn ((hc z hz).mpr ((hc x hx).mp hy))

/-- A mixed mask for a fine grid exhibits actual opposite full-query answers
at points within its physical native-coordinate diameter. The converse and
smallness of the measure of this set are not presumed. -/
theorem mixed_neighbours (m : ℕ) (D : Set (ι → ℝ)) (j : ι → Code (.mesh m))
    (h : mixed (.mesh m) D j) :
    ∃ x y, Cube x ∧ Cube y ∧ x ∈ D ∧ y ∉ D ∧
      ∀ i, |x i-y i| < 4 * width m := by
  obtain ⟨⟨x,hx,hxj,hD⟩,⟨y,hy,hyj,hn⟩⟩ := h
  refine ⟨x,y,hx,hy,hD,hn,?_⟩
  intro i
  apply mesh_diameter m (j i)
  · exact fun hz => hxj (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  · exact fun hz => hyj (Finset.prod_eq_zero (Finset.mem_univ i) hz)

/-- Every actual chronological prefix has precisely the root slot and the
0/1/2 slots of its emitted shapes. Its varying canonical Program is recomputed
on the very same input to every mask; cutoff, clamp and all 401 atoms are literal. -/
def nativeQuery {d : ℕ} (n mesh : ℕ) (k : Root) (tau : ℝ)
    (sh : Fin d → StepShape) (lower : Bool) (b : FloorAtom) :
    Set (NativeSlot sh → ℝ) := {x |
      QueryMember 0 1 (frozenRoot n k tau (nativeRootCoordinate x))
        (nativeProgram mesh sh x) (nativeCoordinates sh x) lower b}

theorem every_native_query (P : Plan) {d : ℕ} (n mesh : ℕ) (k : Root) (tau : ℝ)
    (sh : Fin d → StepShape) (lower : Bool) (b : FloorAtom) :
    let D := nativeQuery n mesh k tau sh lower b
    MeasurableSet D ∧ ContDiff ℝ ∞ (readout P (sure P D)) ∧
      ContDiff ℝ ∞ (readout P (hit P D)) ∧
      ∀ x, Cube x → readout P (sure P D) x ≤ (if x ∈ D then 1 else 0) ∧
        (if x ∈ D then 1 else 0) ≤ readout P (hit P D) x ∧
        readout P (hit P D) x - readout P (sure P D) x = readout P (mixed P D) x := by
  dsimp only
  let D := nativeQuery n mesh k tau sh lower b
  refine ⟨(Part5OriginalH430FullMemberMeasurable.actual_native_QueryMember_measurable
      n mesh k tau sh lower b).2, readout_smooth _ _, readout_smooth _ _, ?_⟩
  intro x hx
  have h := sharp_sandwich P D hx
  exact ⟨h.1,h.2,by linarith only [gap_exact P D x]⟩

end
end ImbalancedChen.Part5OriginalH430JointQueryEnclosure
