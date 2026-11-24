import ImbalancedChen.P5ActualHBMediumBranchPartition
import Mathlib.Data.List.Forall2

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Original truncated Mobius roles cannot be long when their actual REAL
-- cutoff lies below the original medium ceiling. Selected medium support
-- is taken from the actual nonzero ordered coefficient, not supplied.
namespace ImbalancedChen.P5Z.ActualHBMediumRoleSupports
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition

theorem assigned_mobius_lower_caps {z y : ℝ} :
    ∀ rs : List Role, ∀ bs : List Block, ∀ ps : List ℕ,
      assignedWeight z y rs bs ps ≠ 0 →
      ∀ rb ∈ rs.zip bs, rb.1 = .mobius → (lower rb.2 : ℝ) ≤ y := by
  intro rs
  induction rs with
  | nil => intro bs ps hn rb hrb; simp at hrb
  | cons r rs ih =>
    intro bs ps hn
    cases bs with
    | nil => intro rb hrb; simp at hrb
    | cons b bs =>
      cases ps with
      | nil => simp [assignedWeight] at hn
      | cons p ps =>
        have hp := mul_ne_zero_iff.mp hn
        intro rb hrb hrole
        rcases List.mem_cons.mp hrb with rfl | htail
        · change r = .mobius at hrole
          subst r
          have hcut := mobius_interval_cutoff hp.1
          have hlow : (lower b : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (owns_bounds hcut.1).1
          exact hlow.trans hcut.2
        · exact ih bs ps hp.2 rb htail hrole

-- Literal roles (j+1 Mobius, j one, ONE log) are not replaced by an
-- arbitrary coefficient. Repeated occurrences remain in the zip.
theorem actual_long_role_is_unweighted {z y B : ℝ} (hz : 0 ≤ z) (hyB : y ≤ B)
    {j n : ℕ} {bs : List Block} (hn : blockCoefficient z y j n bs ≠ 0) :
    ∀ rb ∈ (roles j).zip bs, B < (lower rb.2 : ℝ) →
      rb.1 = .one ∨ rb.1 = .logarithm := by
  obtain ⟨ps,hps,ha,ho,hbounds,hcut⟩ := active_coefficient_tuple hz hn
  intro rb hrb hlong
  have hnot : rb.1 ≠ .mobius := by
    intro hm
    have hc := assigned_mobius_lower_caps (roles j) bs ps ha rb hrb hm
    linarith
  cases hrole : rb.1 with
  | mobius => exact False.elim (hnot hrole)
  | one => exact Or.inl hrole
  | logarithm => exact Or.inr hrole

-- The original medium selector gives the SAME selected occurrence in
-- every tuple. Its actual integer factor has the original dyadic support.
theorem actual_selected_medium_support {z y A B : ℝ} (hz : 0 ≤ z) (hA : 1 < A)
    {j n i : ℕ} {bs : List Block} (hn : blockCoefficient z y j n bs ≠ 0)
    (hselect : firstMedium A B bs = some i) :
    ∃ ps ∈ factorTuples (2*(j+1)) n,
      assignedWeight z y (roles j) bs ps ≠ 0 ∧
      ∃ hi : i < bs.length, ∃ hp : i < ps.length,
        Medium A B bs[i] ∧
        (lower bs[i] : ℝ) < (ps[i] : ℝ) ∧
        (ps[i] : ℝ) ≤ 2*(lower bs[i] : ℝ) ∧
        0 < ps[i] ∧ ps[i] ≤ n ∧
        (∀ p ∈ ps.take (j+1), (p : ℝ) ≤ y) := by
  obtain ⟨ps,hps,ha,ho,hbounds,hcut⟩ := active_coefficient_tuple hz hn
  obtain ⟨hi,hm,hbefore⟩ := firstMedium_some hselect
  have hp : i < ps.length := by rw [← ho.length_eq]; exact hi
  have hown : Owns bs[i] ps[i] := by
    exact ho.get hi hp
  have hnonunit : bs[i] ≠ .unit := by
    intro hu
    have hh := hm.1
    rw [hu] at hh
    simp only [lower,Nat.cast_one] at hh
    linarith
  have hstrict : lower bs[i] < ps[i] := by
    cases he : bs[i] with
    | unit => exact False.elim (hnonunit he)
    | dyadic k =>
      have hd : 2^k < ps[i] ∧ ps[i] ≤ 2^(k+1) := by
        simpa only [he,Owns] using hown
      simpa only [he,lower] using hd.1
  have hupper := (owns_bounds hown).2
  have hmem : ps[i] ∈ ps := List.getElem_mem hp
  exact ⟨ps,hps,ha,hi,hp,hm,by exact_mod_cast hstrict,
    by exact_mod_cast hupper,(hbounds _ hmem).1,(hbounds _ hmem).2,hcut⟩

-- Substitution of the original window is literal. The branch is allowed
-- to be Type I; no argument infers Medium from a largest-slot root bound.
theorem original_noMedium_actual_alternative {z y X zeta : ℝ}
    (hz : 0 ≤ z) (hA : 1 ≤ originalLower X zeta)
    (hB : 1 ≤ originalUpper X zeta) (hyB : y ≤ originalUpper X zeta)
    {j n : ℕ} {bs : List Block} (hj : j ∈ Finset.range 3)
    (hn : blockCoefficient z y j n bs ≠ 0)
    (hbranch : firstMedium (originalLower X zeta) (originalUpper X zeta) bs = none)
    (hshort : 64*(originalLower X zeta)^6 < (n : ℝ))
    (hcomplete : (n : ℝ) < (originalUpper X zeta)^3) :
    ((longBlocks (originalUpper X zeta) bs).length = 1 ∨
      (longBlocks (originalUpper X zeta) bs).length = 2) ∧
    (∀ rb ∈ (roles j).zip bs, originalUpper X zeta < (lower rb.2 : ℝ) →
      rb.1 = .one ∨ rb.1 = .logarithm) := by
  exact ⟨actual_noMedium_one_or_two_long hz hA hB hj hn hbranch hshort hcomplete,
    actual_long_role_is_unweighted hz hyB hn⟩

end
end ImbalancedChen.P5Z.ActualHBMediumRoleSupports
