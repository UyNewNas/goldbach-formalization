import ImbalancedChen.OrdinaryRosserFirstExitPolicy

/-!
# Complete ordinary tests for short inherited histories

Histories are stored in reverse processing order. Strictly decreasing
positive natural labels suffice; primality is not needed for these finite
identities. The total-product cutoff is proved from the displayed cubic
tests, rather than silently discarded. Raising the real level preserves
all inherited tests by a separate general monotonicity theorem.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- Raising the level preserves the complete history, including the total
product cutoff and every parity-selected inherited cubic test. -/
theorem ordinaryRosserPrefixAdmissible_mono
    (lower : Bool) (pre : List ℕ) {Q Q' : ℝ} (hQ : Q ≤ Q')
    (hadm : ordinaryRosserPrefixAdmissible lower Q pre) :
    ordinaryRosserPrefixAdmissible lower Q' pre := by
  refine ⟨hadm.1.trans_le hQ, ?_⟩
  cases lower with
  | false =>
      intro p hp hparity
      exact (hadm.2 p hp hparity).trans_le hQ
  | true =>
      intro p hp hparity
      exact (hadm.2 p hp hparity).trans_le hQ

/-- The provider's complete upper four-label test checks exactly ranks one
and three. This statement concerns its admissible set before the additional
strict total-product condition. -/
theorem upperRosserAdmissibleSet_four_iff
    (Q : ℝ) (p1 p2 p3 p4 : ℕ)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    UpperAdmissibleSet Q [p4, p3, p2, p1].toFinset ↔
      (p1 : ℝ) ^ 3 < Q ∧ (p1 : ℝ) * p2 * p3 ^ 3 < Q := by
  have h42 := h43.trans h32
  have h31 := h32.trans h21
  have h41 := h42.trans h21
  let S : Finset ℕ := {p4, p3, p2, p1}
  have hf1 : S.filter (fun p => p1 ≤ p) = {p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf2 : S.filter (fun p => p2 ≤ p) = {p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf3 : S.filter (fun p => p3 ≤ p) = {p3, p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf4 : S.filter (fun p => p4 ≤ p) = S := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [List.toFinset_cons, List.toFinset_nil]
  change UpperAdmissibleSet Q S ↔ _
  simp only [UpperAdmissibleSet, S, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  rw [hf1, hf2, hf3, hf4]
  norm_num [S, h43.ne, h32.ne, h21.ne, h42.ne, h31.ne, h41.ne,
    Nat.cast_mul, List.prod_cons, List.prod_nil, pow_succ, mul_comm, mul_left_comm, mul_assoc, and_comm]

/-- The complete lower four-label admissible set checks ranks two and four. -/
theorem lowerRosserAdmissibleSet_four_iff
    (Q : ℝ) (p1 p2 p3 p4 : ℕ)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    LowerAdmissibleSet Q [p4, p3, p2, p1].toFinset ↔
      (p1 : ℝ) * p2 ^ 3 < Q ∧
        (([p4, p3, p2, p1].prod : ℕ) : ℝ) * p4 ^ 2 < Q := by
  have h42 := h43.trans h32
  have h31 := h32.trans h21
  have h41 := h42.trans h21
  let S : Finset ℕ := {p4, p3, p2, p1}
  have hf1 : S.filter (fun p => p1 ≤ p) = {p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf2 : S.filter (fun p => p2 ≤ p) = {p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf3 : S.filter (fun p => p3 ≤ p) = {p3, p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf4 : S.filter (fun p => p4 ≤ p) = S := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [List.toFinset_cons, List.toFinset_nil]
  change LowerAdmissibleSet Q S ↔ _
  simp only [LowerAdmissibleSet, S, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  rw [hf1, hf2, hf3, hf4]
  norm_num [S, h43.ne, h32.ne, h21.ne, h42.ne, h31.ne, h41.ne,
    Nat.cast_mul, List.prod_cons, List.prod_nil, pow_succ, mul_comm, mul_left_comm, mul_assoc, and_comm]

/-- At rank four the third cubic test already implies the total-product
cutoff. All tests of the actual full upper predicate are displayed. -/
theorem ordinaryRosserPrefixAdmissible_upper_four_iff
    (Q : ℝ) (p1 p2 p3 p4 : ℕ) (h4 : 0 < p4)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    ordinaryRosserPrefixAdmissible false Q [p4, p3, p2, p1] ↔
      (p1 : ℝ) ^ 3 < Q ∧ (p1 : ℝ) * p2 * p3 ^ 3 < Q := by
  have hle : (p4 : ℝ) ≤ (p3 : ℝ) ^ 2 := by
    have hp3 : (1 : ℝ) ≤ p3 := by exact_mod_cast (show 1 ≤ p3 by omega)
    have hp43 : (p4 : ℝ) < p3 := by exact_mod_cast h43
    nlinarith
  have hprod : (([p4, p3, p2, p1].prod : ℕ) : ℝ) ≤
      (p1 : ℝ) * p2 * p3 ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hle
      (by positivity : (0 : ℝ) ≤ (p1 : ℝ) * p2 * p3)
    simp only [List.prod_cons, List.prod_nil, Nat.cast_mul, mul_one]
    nlinarith only [hh]
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    upperRosserAdmissibleSet_four_iff Q p1 p2 p3 p4 h43 h32 h21]
  exact ⟨fun hh => hh.2, fun hh => ⟨hprod.trans_lt hh.2, hh⟩⟩

/-- At rank four the lower own-cube test pays the total-product cutoff. -/
theorem ordinaryRosserPrefixAdmissible_lower_four_iff
    (Q : ℝ) (p1 p2 p3 p4 : ℕ) (h4 : 0 < p4)
    (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    ordinaryRosserPrefixAdmissible true Q [p4, p3, p2, p1] ↔
      (p1 : ℝ) * p2 ^ 3 < Q ∧
        (([p4, p3, p2, p1].prod : ℕ) : ℝ) * p4 ^ 2 < Q := by
  have hsq : (1 : ℝ) ≤ (p4 : ℝ) ^ 2 := by
    have hp : (1 : ℝ) ≤ p4 := by exact_mod_cast h4
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsq
    (Nat.cast_nonneg (α := ℝ) [p4, p3, p2, p1].prod)
  simp only [mul_one] at hprod
  simp only [ordinaryRosserPrefixAdmissible, if_true,
    lowerRosserAdmissibleSet_four_iff Q p1 p2 p3 p4 h43 h32 h21]
  exact ⟨fun hh => hh.2, fun hh => ⟨hprod.trans_lt hh.2, hh⟩⟩

/-- The provider's complete upper five-label test checks exactly ranks one,
three and five. The fifth test is the own-cube condition for that prefix. -/
theorem upperRosserAdmissibleSet_five_iff
    (Q : ℝ) (p1 p2 p3 p4 p5 : ℕ)
    (h54 : p5 < p4) (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    UpperAdmissibleSet Q [p5, p4, p3, p2, p1].toFinset ↔
      (p1 : ℝ) ^ 3 < Q ∧ (p1 : ℝ) * p2 * p3 ^ 3 < Q ∧
        (([p5, p4, p3, p2, p1].prod : ℕ) : ℝ) * p5 ^ 2 < Q := by
  have h42 := h43.trans h32
  have h31 := h32.trans h21
  have h41 := h42.trans h21
  have h53 := h54.trans h43
  have h52 := h53.trans h32
  have h51 := h52.trans h21
  let S : Finset ℕ := {p5, p4, p3, p2, p1}
  have hf1 : S.filter (fun p => p1 ≤ p) = {p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf2 : S.filter (fun p => p2 ≤ p) = {p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf3 : S.filter (fun p => p3 ≤ p) = {p3, p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf4 : S.filter (fun p => p4 ≤ p) = {p4, p3, p2, p1} := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf5 : S.filter (fun p => p5 ≤ p) = S := by
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [List.toFinset_cons, List.toFinset_nil]
  change UpperAdmissibleSet Q S ↔ _
  simp only [UpperAdmissibleSet, S, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  rw [hf1, hf2, hf3, hf4, hf5]
  norm_num [S, h43.ne, h32.ne, h21.ne, h42.ne, h31.ne, h41.ne,
    h54.ne, h53.ne, h52.ne, h51.ne, Nat.cast_mul, List.prod_cons, List.prod_nil,
    pow_succ, mul_comm, mul_left_comm, mul_assoc, and_comm, and_left_comm, and_assoc]

/-- Exact full upper predicate through rank five, with no remaining
total-cutoff hypothesis beyond its three displayed tests. -/
theorem ordinaryRosserPrefixAdmissible_upper_five_iff
    (Q : ℝ) (p1 p2 p3 p4 p5 : ℕ) (h5 : 0 < p5)
    (h54 : p5 < p4) (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1) :
    ordinaryRosserPrefixAdmissible false Q [p5, p4, p3, p2, p1] ↔
      (p1 : ℝ) ^ 3 < Q ∧ (p1 : ℝ) * p2 * p3 ^ 3 < Q ∧
        (([p5, p4, p3, p2, p1].prod : ℕ) : ℝ) * p5 ^ 2 < Q := by
  have hsq : (1 : ℝ) ≤ (p5 : ℝ) ^ 2 := by
    have hp : (1 : ℝ) ≤ p5 := by exact_mod_cast h5
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsq
    (Nat.cast_nonneg (α := ℝ) [p5, p4, p3, p2, p1].prod)
  simp only [mul_one] at hprod
  simp only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
    upperRosserAdmissibleSet_five_iff Q p1 p2 p3 p4 p5 h54 h43 h32 h21]
  exact ⟨fun hh => hh.2, fun hh => ⟨hprod.trans_lt hh.2.2, hh⟩⟩

/-- The accepted fifth own-cube test leaves a literal residual level
strictly above the square of the terminal prime. -/
theorem ordinaryRosserPrefixAdmissible_upper_five_residual_gt_sq
    (Q : ℝ) (p1 p2 p3 p4 p5 : ℕ) (h5 : 0 < p5)
    (h54 : p5 < p4) (h43 : p4 < p3) (h32 : p3 < p2) (h21 : p2 < p1)
    (hadm : ordinaryRosserPrefixAdmissible false Q [p5, p4, p3, p2, p1]) :
    (p5 : ℝ) ^ 2 < Q / ([p5, p4, p3, p2, p1].prod : ℝ) := by
  have hcube := ((ordinaryRosserPrefixAdmissible_upper_five_iff Q p1 p2 p3 p4 p5
    h5 h54 h43 h32 h21).mp hadm).2.2
  have hp1 : 0 < p1 := by omega
  have hp2 : 0 < p2 := by omega
  have hp3 : 0 < p3 := by omega
  have hp4 : 0 < p4 := by omega
  have hP : (0 : ℝ) < ([p5, p4, p3, p2, p1].prod : ℝ) := by
    simp only [List.prod_cons, List.prod_nil, Nat.cast_mul, Nat.cast_one]
    positivity
  exact (lt_div_iff₀ hP).mpr (by simpa only [mul_comm] using hcube)

end

end ImbalancedChen
