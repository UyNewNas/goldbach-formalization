import ImbalancedChen.ActualTwoCapacityGreedy
import MathlibNt.Wu2008DoubleSieve.ReboxingSorted
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The primary source already proves one true sorted insertion. This file
iterates that theorem through an arbitrary residual atom at Q/B. Every
inserted coordinate is the actual natural prime label, not a replacement
upper endpoint, and the final vector is a permutation of old ++ residual.
Residual coordinates may interleave with the old prefix without a ceiling
or append-order assumption. The canonical decreasing sorted union inherits
every full square gate at the unchanged total Q.

This is geometric support only. It is not a signed AP, mean-density, K,
or enhanced native-count licence.
-/

namespace ImbalancedChen.P2EnhancedSortedDwellMerge

noncomputable section

open Finset Wu2008DoubleSieve
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open scoped Classical

/-- Exact bridge from actual natural list gates to the primary Fin API. -/
theorem dwell_ofFn_iff {n : ℕ} (Q : ℝ) (v : Fin n → ℕ) :
    actualDwellSupport Q (List.ofFn v) ↔
      boxSquaredPrefixes Q (fun j => (v j : ℝ)) := by
  constructor
  · intro h j
    have hs := h j.val (by simp)
    simpa only [List.map_take, List.map_ofFn, List.prod_take_ofFn,
      List.getElem_ofFn, Fin.lt_def] using hs
  · intro h i hi
    have hi' : i < n := by simpa only [List.length_ofFn] using hi
    have hs := h ⟨i, hi'⟩
    simpa only [List.map_take, List.map_ofFn, List.prod_take_ofFn,
      List.getElem_ofFn, Fin.lt_def] using hs

theorem cast_insertNth {n : ℕ} (p : Fin (n + 1)) (q : ℕ) (v : Fin n → ℕ) :
    (fun j => (p.insertNth q v j : ℝ)) =
      p.insertNth (q : ℝ) (fun j => (v j : ℝ)) := by
  rw [← Fin.cons_comp_cycleRange, ← Fin.cons_comp_cycleRange]
  funext j
  simp only [Function.comp_apply]
  exact Fin.cases rfl (fun _ => rfl) (p.cycleRange j)

theorem inserted_labels_perm {n : ℕ} (p : Fin (n + 1)) (q : ℕ) (v : Fin n → ℕ) :
    (List.ofFn (p.insertNth q v)).Perm (q :: List.ofFn v) := by
  have h := p.cycleRange.ofFn_comp_perm (Fin.cons q v)
  rw [Fin.cons_comp_cycleRange] at h
  simpa only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ] using h

/-- All-arity genuine sorted union construction. The primary insertion
gate is paid at each stage by the original residual square gate times B. -/
theorem exists_sorted_union {Q R : ℝ} (old : List ℕ)
    (hold : actualDwellSupport Q old) (holdSort : old.Pairwise (· ≥ ·))
    (holdOne : ∀ p ∈ old, 1 ≤ p) (hbudget : (old.prod : ℝ) * R ≤ Q)
    (residual : List ℕ) (hres : actualDwellSupport R residual)
    (hresOne : ∀ p ∈ residual, 1 ≤ p) :
    ∃ v : Fin (old.length + residual.length) → ℕ,
      Antitone (fun j => (v j : ℝ)) ∧
      boxSquaredPrefixes Q (fun j => (v j : ℝ)) ∧
      (List.ofFn v).Perm (old ++ residual) := by
  revert hres hresOne
  induction residual using List.reverseRecOn with
  | nil =>
    intro _ _
    let v : Fin old.length → ℕ := fun j => old[j.val]
    have hv : List.ofFn v = old := List.ofFn_getElem
    have hanti : Antitone (fun j => (v j : ℝ)) := by
      intro i j hij
      rcases lt_or_eq_of_le hij with hlt | heq
      · have hs := (List.pairwise_iff_getElem.mp holdSort) i.val j.val i.isLt j.isLt hlt
        exact_mod_cast hs
      · subst j
        exact le_rfl
    have hwell : boxSquaredPrefixes Q (fun j => (v j : ℝ)) :=
      (dwell_ofFn_iff Q v).mp (hv.symm ▸ hold)
    simpa only [List.length_nil, Nat.add_zero, List.append_nil] using
      (show ∃ v : Fin old.length → ℕ, Antitone (fun j => (v j : ℝ)) ∧
        boxSquaredPrefixes Q (fun j => (v j : ℝ)) ∧ (List.ofFn v).Perm old from
        ⟨v, hanti, hwell, by simpa only [hv] using List.Perm.refl old⟩)
  | append_singleton residual q ih =>
    intro hres hresOne
    obtain ⟨hprefix, hlast⟩ :=
      (prefixSquareBound_append_singleton_iff (fun p : ℕ => (p : ℝ)) R residual q).mp hres
    obtain ⟨v, hvanti, hvwell, hvperm⟩ := ih hprefix
      (fun p hp => hresOne p (List.mem_append_left _ hp))
    have hq : 1 ≤ (q : ℝ) := by
      exact_mod_cast hresOne q (by simp)
    have hvOne (j : Fin (old.length + residual.length)) : 1 ≤ (v j : ℝ) := by
      have hj : v j ∈ old ++ residual :=
        hvperm.mem_iff.mp (List.mem_ofFn.mpr ⟨j, rfl⟩)
      rcases List.mem_append.mp hj with hj | hj
      · exact_mod_cast holdOne _ hj
      · exact_mod_cast hresOne _ (List.mem_append_left _ hj)
    have hprod : (∏ j, (v j : ℝ)) = (old.prod : ℝ) * (residual.prod : ℝ) := by
      have hp := congrArg (fun n : ℕ => (n : ℝ)) hvperm.prod_eq
      simpa only [List.prod_ofFn, List.prod_append, Nat.cast_mul, Nat.cast_prod] using hp
    have hfull : (∏ j, (v j : ℝ)) * (q : ℝ) ^ 2 ≤ Q := by
      have hm := mul_le_mul_of_nonneg_left hlast (Nat.cast_nonneg old.prod : (0 : ℝ) ≤ old.prod)
      calc
        _ = (old.prod : ℝ) *
            ((residual.map (fun p : ℕ => (p : ℝ))).prod * (q : ℝ) ^ 2) := by
          rw [hprod, actualNatList_cast_prod]
          ring
        _ ≤ (old.prod : ℝ) * R := hm
        _ ≤ Q := hbudget
    obtain ⟨p, hpanti, hpwell⟩ :=
      exists_sorted_box_insertion hq hvOne hvanti hvwell hfull
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc]
    refine ⟨p.insertNth q v, ?_, ?_, ?_⟩
    · simpa only [cast_insertNth] using hpanti
    · simpa only [cast_insertNth] using hpwell
    · have hmove : (q :: (old ++ residual)).Perm ((old ++ residual) ++ [q]) := by
        simpa only [List.singleton_append] using
          (List.perm_append_comm : ([q] ++ (old ++ residual)).Perm ((old ++ residual) ++ [q]))
      simpa only [List.append_assoc] using
        (inserted_labels_perm p q v).trans ((hvperm.cons q).trans hmove)

/-- A canonical decreasing union, with actual natural occurrences retained. -/
def sortedUnion (old residual : List ℕ) : List ℕ :=
  (old ++ residual).mergeSort (fun p q => p ≥ q)

theorem sortedUnion_perm (old residual : List ℕ) :
    (sortedUnion old residual).Perm (old ++ residual) :=
  List.mergeSort_perm _ _

theorem sortedUnion_sorted (old residual : List ℕ) :
    (sortedUnion old residual).Pairwise (· ≥ ·) :=
  List.pairwise_mergeSort' (r := (· ≥ ·)) _

/-- Every complete square survives the actual sorted union, including
when residual primes interleave with arbitrary old prefix primes. -/
theorem sortedUnion_well {Q R : ℝ} (old residual : List ℕ)
    (hold : actualDwellSupport Q old) (holdSort : old.Pairwise (· ≥ ·))
    (holdOne : ∀ p ∈ old, 1 ≤ p) (hres : actualDwellSupport R residual)
    (hresOne : ∀ p ∈ residual, 1 ≤ p) (hbudget : (old.prod : ℝ) * R ≤ Q) :
    actualDwellSupport Q (sortedUnion old residual) := by
  obtain ⟨v, hvanti, hvwell, hvperm⟩ :=
    exists_sorted_union old hold holdSort holdOne hbudget residual hres hresOne
  have hsort : (List.ofFn v).Pairwise (· ≥ ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact_mod_cast hvanti hij.le
  have heq : List.ofFn v = sortedUnion old residual :=
    (hvperm.trans (sortedUnion_perm old residual).symm).eq_of_pairwise'
      hsort (sortedUnion_sorted old residual)
  simpa only [heq] using (dwell_ofFn_iff Q v).mpr hvwell

/-- The manuscript's exact residual level is Q/B, with the total Q unchanged. -/
theorem sortedUnion_at_residual_level {Q : ℝ} (old residual : List ℕ)
    (holdProd : 0 < old.prod) (hold : actualDwellSupport Q old)
    (holdSort : old.Pairwise (· ≥ ·)) (holdOne : ∀ p ∈ old, 1 ≤ p)
    (hres : actualDwellSupport (Q / (old.prod : ℝ)) residual)
    (hresOne : ∀ p ∈ residual, 1 ≤ p) :
    actualDwellSupport Q (sortedUnion old residual) := by
  apply sortedUnion_well old residual hold holdSort holdOne hres hresOne
  have heq : (old.prod : ℝ) * (Q / (old.prod : ℝ)) = Q := by
    simpa only [mul_comm] using div_mul_cancel₀ Q (Nat.cast_pos.mpr holdProd).ne'
  exact heq.le

/-- The complete arithmetic product is exactly the two original products. -/
theorem sortedUnion_product (old residual : List ℕ) :
    (sortedUnion old residual).prod = old.prod * residual.prod := by
  simpa only [List.prod_append] using (sortedUnion_perm old residual).prod_eq

end
end ImbalancedChen.P2EnhancedSortedDwellMerge
