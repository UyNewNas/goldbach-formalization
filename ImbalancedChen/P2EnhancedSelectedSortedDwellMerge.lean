import ImbalancedChen.P2EnhancedSortedDwellMerge

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The selected labels are the original old-prime subset. Residual primes
are unselected. Filtering the actual canonical sorted union gives EXACTLY
the sorted union of the old complement and residual; the selected list
itself is unchanged. Thus this is a statement about the actual merged
vector, not a separately postulated remainder vector.

The original selected remaining-square gates are explicit indexed
inequalities. They imply support at Q/A before merging, and the exact
identity B=A*C makes the residual level Q/B fit the SAME level Q/A after
merging. No extra order between old and residual primes is imposed.
No signed/AP, density, enhanced gain, or K licence follows from this file.
-/

namespace ImbalancedChen.P2EnhancedSelectedSortedDwellMerge

noncomputable section

open P2EnhancedSortedDwellMerge
open scoped Classical

def selected (old : List ℕ) (S : ℕ → Prop) : List ℕ :=
  old.filter (fun p => decide (S p))

def remaining (old : List ℕ) (S : ℕ → Prop) : List ℕ :=
  old.filter (fun p => decide (¬ S p))

theorem selected_mul_remaining (old : List ℕ) (S : ℕ → Prop) :
    (selected old S).prod * (remaining old S).prod = old.prod := by
  simpa only [selected, remaining, List.map_id] using
    List.prod_map_filter_mul_prod_map_filter_not S id old

theorem selected_product_pos (old : List ℕ) (S : ℕ → Prop)
    (hone : ∀ p ∈ old, 1 ≤ p) : 0 < (selected old S).prod := by
  apply List.prod_pos
  intro p hp
  exact lt_of_lt_of_le (by decide : 0 < (1 : ℕ))
    (hone p (List.mem_filter.mp hp).1)

theorem remaining_product_pos (old : List ℕ) (S : ℕ → Prop)
    (hone : ∀ p ∈ old, 1 ≤ p) : 0 < (remaining old S).prod := by
  apply List.prod_pos
  intro p hp
  exact lt_of_lt_of_le (by decide : 0 < (1 : ℕ))
    (hone p (List.mem_filter.mp hp).1)

/-- Sorting and deleting the old selected subset commute on the actual union. -/
theorem remaining_sortedUnion (old residual : List ℕ) (S : ℕ → Prop)
    (hres : ∀ q ∈ residual, ¬ S q) :
    remaining (sortedUnion old residual) S = sortedUnion (remaining old S) residual := by
  have hkeep : residual.filter (fun q => decide (¬ S q)) = residual := by
    apply List.filter_eq_self.mpr
    intro q hq
    simpa only [decide_eq_true_eq] using hres q hq
  have hperm : (remaining (sortedUnion old residual) S).Perm
      (remaining old S ++ residual) := by
    have h := (sortedUnion_perm old residual).filter (fun q => decide (¬ S q))
    simpa only [remaining, List.filter_append, hkeep] using h
  have hleft : (remaining (sortedUnion old residual) S).Pairwise (· ≥ ·) :=
    (sortedUnion_sorted old residual).filter _
  exact (hperm.trans (sortedUnion_perm (remaining old S) residual).symm).eq_of_pairwise'
    hleft (sortedUnion_sorted (remaining old S) residual)

/-- The selected original labels themselves are unchanged, including their order. -/
theorem selected_sortedUnion (old residual : List ℕ) (S : ℕ → Prop)
    (holdSort : old.Pairwise (· ≥ ·)) (hres : ∀ q ∈ residual, ¬ S q) :
    selected (sortedUnion old residual) S = selected old S := by
  have hdrop : residual.filter (fun q => decide (S q)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    simpa only [decide_eq_true_eq] using hres q hq
  have hperm : (selected (sortedUnion old residual) S).Perm (selected old S) := by
    have h := (sortedUnion_perm old residual).filter (fun q => decide (S q))
    simpa only [selected, List.filter_append, hdrop, List.append_nil] using h
  exact hperm.eq_of_pairwise'
    ((sortedUnion_sorted old residual).filter _) (holdSort.filter _)

/-- The manuscript's retained selected-complement square tests on old labels. -/
def RemainingSquares (Q : ℝ) (old : List ℕ) (S : ℕ → Prop) : Prop :=
  ∀ (i : ℕ) (hi : i < (remaining old S).length),
    ((selected old S).prod : ℝ) *
      (((remaining old S).take i).map (fun p : ℕ => (p : ℝ))).prod *
      ((remaining old S)[i] : ℝ) ^ 2 ≤ Q

theorem remaining_well_of_gates {Q : ℝ} (old : List ℕ) (S : ℕ → Prop)
    (hone : ∀ p ∈ old, 1 ≤ p) (hgates : RemainingSquares Q old S) :
    actualDwellSupport (Q / ((selected old S).prod : ℝ)) (remaining old S) := by
  have hA : (0 : ℝ) < (selected old S).prod := Nat.cast_pos.mpr (selected_product_pos old S hone)
  intro i hi
  apply (le_div_iff₀ hA).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hgates i hi

/-- The selected remaining-square gates survive the ACTUAL sorted union
at Q/A. The residual atom stays at Q/B, not a substituted residual level. -/
theorem remaining_sortedUnion_well {Q : ℝ} (old residual : List ℕ) (S : ℕ → Prop)
    (holdSort : old.Pairwise (· ≥ ·)) (holdOne : ∀ p ∈ old, 1 ≤ p)
    (hgates : RemainingSquares Q old S)
    (hres : actualDwellSupport (Q / (old.prod : ℝ)) residual)
    (hresOne : ∀ q ∈ residual, 1 ≤ q) (hresNo : ∀ q ∈ residual, ¬ S q) :
    actualDwellSupport (Q / ((selected old S).prod : ℝ))
      (remaining (sortedUnion old residual) S) := by
  rw [remaining_sortedUnion old residual S hresNo]
  have hA : (0 : ℝ) < (selected old S).prod :=
    Nat.cast_pos.mpr (selected_product_pos old S holdOne)
  have hC : (0 : ℝ) < (remaining old S).prod :=
    Nat.cast_pos.mpr (remaining_product_pos old S holdOne)
  have hprod : ((selected old S).prod : ℝ) * ((remaining old S).prod : ℝ) = old.prod := by
    exact_mod_cast selected_mul_remaining old S
  apply sortedUnion_well (remaining old S) residual
    (remaining_well_of_gates old S holdOne hgates) (holdSort.filter _)
    (fun p hp => holdOne p (List.mem_filter.mp hp).1) hres hresOne
  have heq : ((remaining old S).prod : ℝ) * (Q / (old.prod : ℝ)) =
      Q / ((selected old S).prod : ℝ) := by
    rw [← hprod]
    field_simp [hA.ne', hC.ne']
    <;> ring
  exact heq.le

/-- Full and selected support coexist on one actual merged list, with
the same original selected labels and the same total Q throughout. -/
theorem full_and_selected_sortedUnion {Q : ℝ} (old residual : List ℕ) (S : ℕ → Prop)
    (holdProd : 0 < old.prod) (hold : actualDwellSupport Q old)
    (holdSort : old.Pairwise (· ≥ ·)) (holdOne : ∀ p ∈ old, 1 ≤ p)
    (hgates : RemainingSquares Q old S)
    (hres : actualDwellSupport (Q / (old.prod : ℝ)) residual)
    (hresOne : ∀ q ∈ residual, 1 ≤ q) (hresNo : ∀ q ∈ residual, ¬ S q) :
    actualDwellSupport Q (sortedUnion old residual) ∧
      selected (sortedUnion old residual) S = selected old S ∧
      actualDwellSupport (Q / ((selected old S).prod : ℝ))
        (remaining (sortedUnion old residual) S) ∧
      (remaining (sortedUnion old residual) S).prod = (remaining old S).prod * residual.prod := by
  refine ⟨sortedUnion_at_residual_level old residual holdProd hold holdSort holdOne hres hresOne,
    selected_sortedUnion old residual S holdSort hresNo,
    remaining_sortedUnion_well old residual S holdSort holdOne hgates hres hresOne hresNo, ?_⟩
  rw [remaining_sortedUnion old residual S hresNo, sortedUnion_product]

end
end ImbalancedChen.P2EnhancedSelectedSortedDwellMerge
