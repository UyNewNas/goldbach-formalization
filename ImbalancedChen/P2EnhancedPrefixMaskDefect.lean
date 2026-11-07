import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherOriginalWindows
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The 21-term mother and its four-band count proof already exist in
`SecondFunctionalMotherFinite`. The missing finite comparison treated here
is different: its switched prefix carrier exempts the first r-2 labels
from sifting. Removing that exemption in the QUOTIENT carrier can discard
only receivers for which a selected prime divides the residual quotient.
Every discarded receiver therefore has an actual selected-prime square.

No unscaled source carrier with mask d*N is identified with a quotient
carrier. The original next-to-last-prime cutoff, all labels, and the N and
d factors of the mask are retained. Unit quotients have no defect. The
finite defect is exposed, not assumed negligible, and no enhanced count,
H/h value, product estimate, distribution statement, or numerical pass is
an input.
-/

namespace ImbalancedChen.P2EnhancedPrefixMaskDefect

noncomputable section

open Finset Wu2008DoubleSieve
open scoped Classical

/-- The physical quotient with the old d*N mask and the unchanged cutoff. -/
def quotientCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  sieveCarrier N (d * l.prod) (d * N) (l.getD (l.length - 2) 0)

/-- The precise finite event lost when the additional prefix mask is removed. -/
def defectCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  secondFunctionalMotherPrefixCarrier N d l \ quotientCarrier N d l

/-- A selected prime below the original cutoff repeats in the residual quotient. -/
def SelectedCollision (N d : ℕ) (l : List ℕ) (ell : ℕ) : Prop :=
  ∃ r : ℕ, r.Prime ∧ r ∣ (l.take (l.length - 2)).prod ∧
    (r : ℝ) < l.getD (l.length - 2) 0 ∧ r ∣ (N - ell) / (d * l.prod)

/-- This carrier retains the complete original source predicate as well. -/
def collisionCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  (secondFunctionalMotherPrefixCarrier N d l).filter (SelectedCollision N d l)

theorem take_prod_dvd_complete (d : ℕ) (l : List ℕ) :
    (l.take (l.length - 2)).prod ∣ d * l.prod := by
  have heq := congrArg (fun xs : List ℕ => xs.prod)
    (List.take_append_drop (l.length - 2) l)
  simp only [List.prod_append] at heq
  refine ⟨d * (l.drop (l.length - 2)).prod, ?_⟩
  rw [← heq]
  ring

/-- Source roughness descends to the real residual quotient at its original mask. -/
theorem prefix_quotient_sifted {N d ell : ℕ} {l : List ℕ}
    (hell : ell ∈ secondFunctionalMotherPrefixCarrier N d l) :
    Sifted (d * (l.take (l.length - 2)).prod * N)
      ((N - ell) / (d * l.prod)) (l.getD (l.length - 2) 0) := by
  change ell ∈ sourceSieveCarrier N (d * l.prod)
    (d * (l.take (l.length - 2)).prod * N) (l.getD (l.length - 2) 0) at hell
  obtain ⟨_, _, hdiv, hs⟩ := mem_filter.mp hell
  intro r hr hM hz hrd
  apply hs r hr hM hz
  have hm := dvd_mul_of_dvd_right hrd (d * l.prod)
  simpa only [Nat.mul_div_cancel' hdiv] using hm

/-- Every point in the exact finite mask difference has an explicit collision. -/
theorem defect_subset_collision (N d : ℕ) (l : List ℕ) :
    defectCarrier N d l ⊆ collisionCarrier N d l := by
  intro ell hell
  obtain ⟨hprefix, hmiss⟩ := mem_sdiff.mp hell
  have hdata := hprefix
  change ell ∈ sourceSieveCarrier N (d * l.prod)
    (d * (l.take (l.length - 2)).prod * N) (l.getD (l.length - 2) 0) at hdata
  obtain ⟨hrange, hprime, hdiv, _⟩ := mem_filter.mp hdata
  have hquot := prefix_quotient_sifted hprefix
  have hnot : ¬ Sifted (d * N) ((N - ell) / (d * l.prod))
      (l.getD (l.length - 2) 0) := by
    intro hs
    apply hmiss
    exact mem_filter.mpr ⟨hrange, hprime, hdiv, hs⟩
  simp only [Sifted, not_forall, not_imp, not_not] at hnot
  obtain ⟨r, hr, hrM, hrz, hrd⟩ := hnot
  have hrpre : r ∣ (l.take (l.length - 2)).prod := by
    by_contra hn
    have hcop := Nat.coprime_mul_iff_right.mp hrM
    have hc : r.Coprime (d * (l.take (l.length - 2)).prod * N) :=
      (hcop.1.mul_right ((hr.coprime_iff_not_dvd).mpr hn)).mul_right hcop.2
    exact hquot r hr hc hrz hrd
  exact mem_filter.mpr ⟨hprefix, r, hr, hrpre, hrz, hrd⟩

/-- The collision produces a square in the actual unscaled complement. -/
theorem collision_forces_prime_square {N d ell : ℕ} {l : List ℕ}
    (hell : ell ∈ collisionCarrier N d l) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) < l.getD (l.length - 2) 0 ∧
      r ^ 2 ∣ N - ell := by
  obtain ⟨hprefix, r, hr, hrpre, hrz, hrd⟩ := mem_filter.mp hell
  change ell ∈ sourceSieveCarrier N (d * l.prod)
    (d * (l.take (l.length - 2)).prod * N) (l.getD (l.length - 2) 0) at hprefix
  have hdiv := (mem_filter.mp hprefix).2.2.1
  have hrfull := hrpre.trans (take_prod_dvd_complete d l)
  refine ⟨r, hr, hrz, ?_⟩
  have hsquare := mul_dvd_mul hrfull hrd
  simpa only [← pow_two, Nat.mul_div_cancel' hdiv] using hsquare

/-- Exact inclusion-exclusion: the admitted intersection and the full defect. -/
theorem prefix_card_partition (N d : ℕ) (l : List ℕ) :
    (secondFunctionalMotherPrefixCarrier N d l).card =
      ((secondFunctionalMotherPrefixCarrier N d l) ∩ quotientCarrier N d l).card +
        (defectCarrier N d l).card := by
  simpa only [defectCarrier, add_comm] using
    (card_sdiff_add_card_inter (secondFunctionalMotherPrefixCarrier N d l)
      (quotientCarrier N d l)).symm

/-- The actual finite switched count is bounded by the desired quotient
count plus the explicitly retained selected-square event count. -/
theorem prefix_card_le_quotient_add_collision (N d : ℕ) (l : List ℕ) :
    (secondFunctionalMotherPrefixCarrier N d l).card ≤
      (quotientCarrier N d l).card + (collisionCarrier N d l).card := by
  rw [prefix_card_partition]
  exact Nat.add_le_add (card_le_card (inter_subset_right))
    (card_le_card (defect_subset_collision N d l))

/-- The two carriers agree on the squarefree part in the required direction. -/
theorem squarefree_prefix_subset_quotient (N d : ℕ) (l : List ℕ) :
    (secondFunctionalMotherPrefixCarrier N d l).filter
      (fun ell => Squarefree (N - ell)) ⊆ quotientCarrier N d l := by
  intro ell hell
  obtain ⟨hprefix, hsf⟩ := mem_filter.mp hell
  by_contra hmiss
  have hc := defect_subset_collision N d l (mem_sdiff.mpr ⟨hprefix, hmiss⟩)
  obtain ⟨r, hr, _, hr2⟩ := collision_forces_prime_square hc
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf r hr)
    (by simpa only [pow_two] using hr2)

/-- Quotient one is retained exactly; no unit surface is put in the error. -/
theorem collision_quotient_ne_one {N d ell : ℕ} {l : List ℕ}
    (hell : ell ∈ collisionCarrier N d l) :
    (N - ell) / (d * l.prod) ≠ 1 := by
  obtain ⟨_, r, hr, _, _, hrd⟩ := mem_filter.mp hell
  intro heq
  rw [heq] at hrd
  exact hr.not_dvd_one hrd

end
end ImbalancedChen.P2EnhancedPrefixMaskDefect
