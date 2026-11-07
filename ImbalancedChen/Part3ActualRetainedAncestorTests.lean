import ImbalancedChen.Part3ActualCompactInitialSupport
import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.FrozenRosserPolicy

/-!
# Every actual retained leaf supplies all its ancestor tests

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The main premise is membership in the actual recursive leaf generator.
Every ancestor's retention test is recovered from its causal selection
path.  For the compact policy this supplies the literal ordinary Rosser
predicate at every odd rank >= 3, at the same frozen physical cell level.
No retained-ancestor supplier or full-square support is assumed.

The rank-four application removes the previously explicit third-retention
premise from Part3ActualCompactInitialSupport.  All-rank conversion of
the resulting finite-set cubic tests into the indexed square-support
predicate, and the complete rho/tensor and spectral theorem, remain open.
-/

namespace ImbalancedChen.Part3.ActualRetainedAncestorTests

noncomputable section

open ActualCompactInitialSupport

/-- Each nonempty ancestor passed the actual policy with its actual sign. -/
def AncestorTests {α : Type*} (retained : Bool → List α → Bool)
    (history : List α) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ history.length →
    retained (evenListLength (rosserAncestor k history)) (rosserAncestor k history) = true

private theorem ancestorTests_cons {α : Type*} (retained : Bool → List α → Bool)
    (p : α) (pre : List α) (hpre : AncestorTests retained pre)
    (hpass : retained (!(evenListLength pre)) (p :: pre) = true) :
    AncestorTests retained (p :: pre) := by
  intro k hk hlen
  by_cases hold : k ≤ pre.length
  · rw [rosserAncestor_cons k p pre hold]
    exact hpre k hk hold
  · have hnew : (p :: pre).length ≤ k := by simp only [List.length_cons] at *; omega
    rw [rosserAncestor_self_of_length_le k (p :: pre) hnew]
    exact hpass

private theorem validSelection_ancestorTests {α : Type*}
    (retained : Bool → List α → Bool) (chosen : List α) :
    ∀ pre : List α, AncestorTests retained pre →
      FirstExitValidSelection retained pre (evenListLength pre) chosen →
      AncestorTests retained (chosen.reverse ++ pre) := by
  induction chosen with
  | nil =>
      intro pre hpre _
      simpa using hpre
  | cons p ps ih =>
      intro pre hpre hvalid
      have hnext := ancestorTests_cons retained p pre hpre hvalid.1
      have htail : FirstExitValidSelection retained (p :: pre)
          (evenListLength (p :: pre)) ps := hvalid.2
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (p :: pre) hnext htail

/-- Actual recursive membership supplies every ancestor test, for any
rank, any policy, any carrier, and any original signed tuple weight. -/
theorem retained_leaf_ancestor_tests {α : Type*}
    (retained : Bool → List α → Bool) (weight : α → ℝ)
    (carrier : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ firstExitRetainedLeaves retained weight [] true 1 carrier) :
    AncestorTests retained leaf.selected := by
  obtain ⟨chosen, _hsub, hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      retained weight [] carrier true 1 leaf hleaf
  have hempty : AncestorTests retained ([] : List α) := by
    intro k hk hlen
    simp only [List.length_nil] at hlen
    omega
  rw [hselected]
  exact validSelection_ancestorTests retained chosen [] hempty hvalid

private theorem evenListLength_parity {α : Type*} (history : List α) :
    evenListLength history = decide (Even history.length) := by
  induction history with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- Every odd ancestor of rank at least three reads the same actual
compact cell.  The full ordinary finite-set predicate is extracted from
the original retain decision, rather than postulated as a new supplier. -/
theorem actual_compact_leaf_odd_ancestor_admissible
    (e h : ℝ) (m N : ℕ) (weight : ℕ → ℝ) (carrier : List ℕ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1 carrier)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 leaf.selected) ∈
      actualExtendedThirdOwnedCell m j)
    (k : ℕ) (hk3 : 3 ≤ k) (hk : k ≤ leaf.selected.length) (hodd : ¬Even k) :
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j) (rosserAncestor k leaf.selected) := by
  have hpass := retained_leaf_ancestor_tests
    (actualExtendedThirdCompactUpperPolicy e h m N) weight carrier leaf hleaf k (by omega) hk
  have hlen : (rosserAncestor k leaf.selected).length = k := by
    rw [rosserAncestor_length, Nat.min_eq_left hk]
  have hsign : evenListLength (rosserAncestor k leaf.selected) = false := by
    rw [evenListLength_parity, hlen]
    simp only [hodd, decide_false]
  have hcell : primeHistoryLogCoordinates (N : ℝ) 3
      (rosserAncestor 3 (rosserAncestor k leaf.selected)) ∈ actualExtendedThirdOwnedCell m j := by
    rw [rosserAncestor_nested 3 k hk3]
    exact ht
  rw [hsign, actualExtendedThirdCompactUpperPolicy_on_cell false
    (rosserAncestor k leaf.selected) (by omega) hj hcell] at hpass
  simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
    oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using hpass

/-- Rank-three retention is recovered from any actual later leaf.  The
history equality simply names its original three selected primes. -/
theorem actual_compact_leaf_third_retention
    (e h : ℝ) (m N : ℕ) (weight : ℕ → ℝ) (carrier : List ℕ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1 carrier)
    (hrank : 3 ≤ leaf.selected.length) (p0 p1 p2 : ℕ)
    (hthird : rosserAncestor 3 leaf.selected = [p2, p1, p0]) :
    actualExtendedThirdCompactUpperPolicy e h m N false [p2, p1, p0] = true := by
  have hpass := retained_leaf_ancestor_tests
    (actualExtendedThirdCompactUpperPolicy e h m N) weight carrier leaf hleaf 3 (by omega) hrank
  rw [hthird] at hpass
  exact hpass

/-- Every actual retained leaf of any rank >= 4 supplies full original
square support on its rank-four ancestor, without a retention or support
premise.  It remains the same frozen cell and the same original primes. -/
theorem actual_compact_leaf_fourth_ancestor_support {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (weight : ℕ → ℝ) (carrier : List ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1 carrier)
    (hrank : 4 ≤ leaf.selected.length)
    (p0 p1 p2 p3 : ℕ) (hp2 : 0 < p2)
    (h32 : p3 ≤ p2) (h21 : p2 < p1) (h10 : p1 < p0)
    (hfourth : rosserAncestor 4 leaf.selected = [p3, p2, p1, p0])
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 leaf.selected) ∈
      actualExtendedThirdOwnedCell m j) :
    actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
      (rosserAncestor 4 leaf.selected).reverse := by
  have hthird : rosserAncestor 3 leaf.selected = [p2, p1, p0] := by
    rw [← rosserAncestor_nested 3 4 (by omega) leaf.selected, hfourth]
    simp [rosserAncestor]
  have hret := actual_compact_leaf_third_retention e h m N weight carrier leaf hleaf
    (by omega) p0 p1 p2 hthird
  have hcell : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈
      actualExtendedThirdOwnedCell m j := by simpa only [hthird] using ht
  have hs := (actual_compact_retained_fourth_support hN he0 he hmesh
    p0 p1 p2 p3 hp2 h32 h21 h10 hj hcell hret).2
  rw [hfourth]
  simpa using hs

end

end ImbalancedChen.Part3.ActualRetainedAncestorTests
