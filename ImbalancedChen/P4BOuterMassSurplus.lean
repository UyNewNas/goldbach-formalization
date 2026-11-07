import ImbalancedChen.ActualUpperCountingInputs

/-!
# P4B: finite outer-envelope mass surplus

YELLOW / SOURCE ONLY / UNCOMPILED.

All identities use the actual finite carrier and actual weights.  In
particular, points outside the literal source contribute their full weight.
The final theorem supplies exactly the `hsurplus` interface of the draft
`P4BActualOuterUpperAssembly`, from finite boundary-slice certificates.
It does not construct an envelope or prove a boundary lattice estimate.
-/

namespace ImbalancedChen
namespace P4B

noncomputable section
open Filter Topology
open scoped BigOperators

/-- An actual finite source indicator has its cardinality as mass on every
finite carrier containing that source. -/
theorem outerMass_indicator_eq_card
    (A S : Finset ℕ) (hAS : A ⊆ S) :
    finiteSourceMass S (fun m => if m ∈ A then (1 : ℝ) else 0) =
      (A.card : ℝ) := by
  classical
  have hsum :
      (∑ m ∈ A, if m ∈ A then (1 : ℝ) else 0) =
        ∑ m ∈ S, if m ∈ A then (1 : ℝ) else 0 := by
    apply Finset.sum_subset hAS
    intro m hmS hmA
    exact if_neg hmA
  unfold finiteSourceMass
  rw [← hsum]
  simp

/-- Exact boundary surplus: excess above one inside the actual source,
plus the complete outer weight outside the actual source. -/
theorem outerMass_sub_card_eq_boundary_surplus
    (A S : Finset ℕ) (w : ℕ → ℝ) (hAS : A ⊆ S) :
    finiteSourceMass S w - (A.card : ℝ) =
      (∑ m ∈ A, (w m - 1)) +
        ∑ m ∈ S.filter (fun m => m ∉ A), w m := by
  classical
  have hfilter : S.filter (fun m => m ∈ A) = A := by
    ext m
    constructor
    · intro hm
      exact (Finset.mem_filter.mp hm).2
    · intro hm
      exact Finset.mem_filter.mpr ⟨hAS hm, hm⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun m => m ∈ A) w
  rw [hfilter] at hsplit
  have hones : (∑ _m ∈ A, (1 : ℝ)) = (A.card : ℝ) := by simp
  unfold finiteSourceMass
  rw [Finset.sum_sub_distrib, hones]
  linarith only [hsplit]

/-- A positive outer majorant makes both terms in the preceding exact
surplus nonnegative; source containment is used for every interior point. -/
theorem outerMass_boundary_surplus_nonneg
    (A S : Finset ℕ) (w : ℕ → ℝ) (hAS : A ⊆ S)
    (houter : ∀ m ∈ S, (if m ∈ A then (1 : ℝ) else 0) ≤ w m) :
    0 ≤ finiteSourceMass S w - (A.card : ℝ) := by
  classical
  rw [outerMass_sub_card_eq_boundary_surplus A S w hAS]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro m hm
    have ho := houter m (hAS hm)
    rw [if_pos hm] at ho
    linarith only [ho]
  · apply Finset.sum_nonneg
    intro m hm
    obtain ⟨hmS, hmA⟩ := Finset.mem_filter.mp hm
    have ho := houter m hmS
    rw [if_neg hmA] at ho
    exact ho

/-- Specialization of the exact identity to the literal manuscript source.
No approximate source or prime-prefix cardinality occurs here. -/
theorem actualOuterMass_sub_source_card_eq_boundary_surplus
    (b kappa : ℝ) (N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hsource :
      realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) ⊆ S) :
    finiteSourceMass S w -
        ((realHalfProductSource b N
          (manuscriptHalfProductCutoff kappa N)).card : ℝ) =
      (∑ m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N),
        (w m - 1)) +
      ∑ m ∈ S.filter (fun m => m ∉
        realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)), w m := by
  exact outerMass_sub_card_eq_boundary_surplus
    (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)) S w hsource

/-- A pointwise nonnegative boundary majorant gives the full finite mass
bound.  Its mass includes the carrier outside the actual source. -/
theorem outerMass_le_card_add_boundary_mass
    (A S : Finset ℕ) (w u : ℕ → ℝ) (hAS : A ⊆ S)
    (hu : ∀ m ∈ S, 0 ≤ u m)
    (hupper : ∀ m ∈ S,
      w m ≤ (if m ∈ A then (1 : ℝ) else 0) + u m) :
    0 ≤ finiteSourceMass S u ∧
      finiteSourceMass S w ≤ (A.card : ℝ) + finiteSourceMass S u := by
  classical
  refine ⟨Finset.sum_nonneg hu, ?_⟩
  calc
    finiteSourceMass S w ≤
        finiteSourceMass S (fun m => if m ∈ A then (1 : ℝ) else 0) +
          finiteSourceMass S u := by
      unfold finiteSourceMass
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hupper
    _ = (A.card : ℝ) + finiteSourceMass S u := by
      rw [outerMass_indicator_eq_card A S hAS]

/-- Finite actual-source form of the boundary-majorant mass bridge. -/
theorem actualOuterMass_le_source_card_add_boundary_mass
    (b kappa : ℝ) (N : ℕ) (S : Finset ℕ) (w u : ℕ → ℝ)
    (hsource :
      realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) ⊆ S)
    (hu : ∀ m ∈ S, 0 ≤ u m)
    (hupper : ∀ m ∈ S, w m ≤
      (if m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)
        then (1 : ℝ) else 0) + u m) :
    finiteSourceMass S w ≤
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff kappa N)).card : ℝ) + finiteSourceMass S u := by
  exact (outerMass_le_card_add_boundary_mass
    (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
    S w u hsource hu hupper).2
/-- A finite label map partitions the actual carrier into disjoint fibres.
The formula is exact, so slice budgets incur no overlap multiplicity. -/
theorem outerMass_eq_sum_label_fibres {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : Finset ℕ) (tag : ℕ → ι) (u : ℕ → ℝ)
    (htag : ∀ m ∈ S, tag m ∈ I) :
    finiteSourceMass S u =
      ∑ i ∈ I, finiteSourceMass (S.filter (fun m => tag m = i)) u := by
  classical
  simp only [finiteSourceMass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  symm
  calc
    (∑ i ∈ I, if tag m = i then u m else 0) =
        (if tag m = tag m then u m else 0) := by
      apply Finset.sum_eq_single (tag m)
      · intro i hi hne
        exact if_neg (Ne.symm hne)
      · intro hnot
        exact False.elim (hnot (htag m hm))
    _ = u m := if_pos rfl

/-- Independent finite boundary budgets add to the actual outer-mass
surplus bound after a genuine partition of the carrier. -/
theorem outerMass_le_card_add_sum_partition_budgets {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A S : Finset ℕ) (tag : ℕ → ι)
    (w u : ℕ → ℝ) (budget : ι → ℝ) (hAS : A ⊆ S)
    (hu : ∀ m ∈ S, 0 ≤ u m)
    (hupper : ∀ m ∈ S,
      w m ≤ (if m ∈ A then (1 : ℝ) else 0) + u m)
    (htag : ∀ m ∈ S, tag m ∈ I)
    (hslice : ∀ i ∈ I,
      finiteSourceMass (S.filter (fun m => tag m = i)) u ≤ budget i) :
    finiteSourceMass S w ≤ (A.card : ℝ) + ∑ i ∈ I, budget i := by
  classical
  have hm := (outerMass_le_card_add_boundary_mass A S w u hAS hu hupper).2
  have hb : finiteSourceMass S u ≤ ∑ i ∈ I, budget i := by
    rw [outerMass_eq_sum_label_fibres I S tag u htag]
    exact Finset.sum_le_sum hslice
  exact hm.trans (add_le_add_left hb _)

/-- Literal `hsurplus` supplier for `P4BActualOuterUpperAssembly`, obtained
from nonnegative boundary weights and finite partition budgets.  The input
is a finite geometric certificate, not the outer source mass inequality.
The conclusion retains the exact original actual-source cardinality. -/
theorem eventually_actualOuterMass_surplus_of_partition_budgets {ι : Type*} [DecidableEq ι]
    (b kappa : ℝ)
    (S : ℝ → ℕ → Finset ℕ) (weight u : ℝ → ℕ → ℕ → ℝ)
    (I : ℝ → ℕ → Finset ι) (tag : ℝ → ℕ → ℕ → ι)
    (budget : ℝ → ℕ → ι → ℝ)
    (hcertificate : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N →
        (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) ⊆
          S delta N) ∧
        (∀ m ∈ S delta N, 0 ≤ u delta N m) ∧
        (∀ m ∈ S delta N, weight delta N m ≤
          (if m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)
            then (1 : ℝ) else 0) + u delta N m) ∧
        (∀ m ∈ S delta N, tag delta N m ∈ I delta N) ∧
        (∀ i ∈ I delta N,
          finiteSourceMass ((S delta N).filter (fun m => tag delta N m = i))
            (u delta N) ≤ budget delta N i) ∧
        (∑ i ∈ I delta N, budget delta N i) ≤
          delta * ((N : ℝ) / Real.log (N : ℝ))) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      finiteSourceMass (S delta N) (weight delta N) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)) := by
  classical
  intro delta hdelta
  filter_upwards [hcertificate delta hdelta] with N hN
  intro hEven
  obtain ⟨hsource, hu, hupper, htag, hslice, hbudget⟩ := hN hEven
  have hfinite := outerMass_le_card_add_sum_partition_budgets
    (I delta N)
    (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
    (S delta N) (tag delta N) (weight delta N) (u delta N)
    (budget delta N) hsource hu hupper htag hslice
  exact hfinite.trans (add_le_add_left hbudget _)

end
end P4B
end ImbalancedChen