import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import ImbalancedChen.PrimeHistoryLogCoordinates
import ImbalancedChen.P4AOriginalFull87HistoryCore

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.
The provider's complete UPPER admissibility predicate is established from
all FOUR odd prefix cubes. The seventh cube alone is deliberately not used
to pay the earlier cubes. No analytic estimate or frontier premise occurs.
-/
namespace ImbalancedChen.P4AOriginalFull87SevenCubeAdmission
noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open P4AOriginalFull87HistoryCore

/-- Exact processing-to-storage convention used throughout this packet. -/
def pre (p : Fin 8 → ℕ) : List ℕ :=
  [p 7, p 6, p 5, p 4, p 3, p 2, p 1, p 0]

def point (N : ℝ) (p : Fin 8 → ℕ) : Fin 8 → ℝ :=
  primeHistoryLogCoordinates N 8 (pre p)

theorem pre_length (p : Fin 8 → ℕ) : (pre p).length = 8 := by simp [pre]

theorem tuple_pre (p : Fin 8 → ℕ) : primeHistoryTuple 8 (pre p) = p := by
  funext i
  fin_cases i <;> simp [pre, primeHistoryTuple]

theorem pre_ofFn (p : Fin 8 → ℕ) : pre p = (List.ofFn p).reverse := by
  have h := primeHistoryTuple_reverse_ofFn (pre_length p)
  rw [tuple_pre] at h
  exact h.symm

theorem point_rpow (N : ℝ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ i, 0 < p i) (i : Fin 8) : N ^ point N p i = (p i : ℝ) := by
  have hpos : ∀ q ∈ pre p, 0 < q := by
    intro q hq
    rw [pre_ofFn] at hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hq)
    exact hp j
  simpa only [point, tuple_pre] using
    rpow_primeHistoryLogCoordinates N hN (pre_length p) hpos i

theorem pre_pairwise (p : Fin 8 → ℕ) (hp : StrictAnti p) :
    (pre p).Pairwise (· < ·) := by
  rw [pre_ofFn, List.pairwise_reverse]
  exact List.pairwise_ofFn.mpr hp

/-- No sorting is postulated: the original source's strict adjacent rows
imply decreasing actual prime labels by the exact rpow inverse. -/
theorem source_strictAnti (N : ℝ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ i, 0 < p i) (c : P4AOriginalFull87SourceDictionary.Cell)
    (hs : P4AOriginalFull87SourceDictionary.Source c (point N p)) : StrictAnti p := by
  have ht : StrictAnti (point N p) :=
    Fin.strictAnti_iff_succ_lt.mpr
      (P4AOriginalFull87SourceDictionary.source_basic hs).2.2.2
  intro i j hij
  have h := Real.rpow_lt_rpow_of_exponent_lt hN (ht hij)
  rw [point_rpow N hN p hp, point_rpow N hN p hp] at h
  exact_mod_cast h

/-- Literal seven-prefix test of the native upper Rosser object. -/
theorem seven_admissible_of_four_cubes (p : Fin 8 → ℕ) (Q : ℝ)
    (hp : ∀ i, 0 < p i) (hord : StrictAnti p)
    (h1 : (p 0 : ℝ)^3 < Q)
    (h3 : (p 0 : ℝ) * p 1 * (p 2 : ℝ)^3 < Q)
    (h5 : (p 0 : ℝ) * p 1 * p 2 * p 3 * (p 4 : ℝ)^3 < Q)
    (h7 : (p 0 : ℝ) * p 1 * p 2 * p 3 * p 4 * p 5 * (p 6 : ℝ)^3 < Q) :
    ordinaryRosserPrefixAdmissible false Q [p 6, p 5, p 4, p 3, p 2, p 1, p 0] := by
  have h01 : p 1 < p 0 := hord (by decide : (0 : Fin 8) < 1)
  have h02 : p 2 < p 0 := hord (by decide : (0 : Fin 8) < 2)
  have h03 : p 3 < p 0 := hord (by decide : (0 : Fin 8) < 3)
  have h04 : p 4 < p 0 := hord (by decide : (0 : Fin 8) < 4)
  have h05 : p 5 < p 0 := hord (by decide : (0 : Fin 8) < 5)
  have h06 : p 6 < p 0 := hord (by decide : (0 : Fin 8) < 6)
  have h12 : p 2 < p 1 := hord (by decide : (1 : Fin 8) < 2)
  have h13 : p 3 < p 1 := hord (by decide : (1 : Fin 8) < 3)
  have h14 : p 4 < p 1 := hord (by decide : (1 : Fin 8) < 4)
  have h15 : p 5 < p 1 := hord (by decide : (1 : Fin 8) < 5)
  have h16 : p 6 < p 1 := hord (by decide : (1 : Fin 8) < 6)
  have h23 : p 3 < p 2 := hord (by decide : (2 : Fin 8) < 3)
  have h24 : p 4 < p 2 := hord (by decide : (2 : Fin 8) < 4)
  have h25 : p 5 < p 2 := hord (by decide : (2 : Fin 8) < 5)
  have h26 : p 6 < p 2 := hord (by decide : (2 : Fin 8) < 6)
  have h34 : p 4 < p 3 := hord (by decide : (3 : Fin 8) < 4)
  have h35 : p 5 < p 3 := hord (by decide : (3 : Fin 8) < 5)
  have h36 : p 6 < p 3 := hord (by decide : (3 : Fin 8) < 6)
  have h45 : p 5 < p 4 := hord (by decide : (4 : Fin 8) < 5)
  have h46 : p 6 < p 4 := hord (by decide : (4 : Fin 8) < 6)
  have h56 : p 6 < p 5 := hord (by decide : (5 : Fin 8) < 6)
  have hpeq (i j : Fin 8) : p i = p j ↔ i = j := by
    constructor
    · exact hord.injective
    · rintro rfl; rfl
  let S : Finset ℕ := {p 6, p 5, p 4, p 3, p 2, p 1, p 0}
  have hf0 : S.filter (fun q => p 0 ≤ q) = {p 0} := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf1 : S.filter (fun q => p 1 ≤ q) = {p 1, p 0} := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf2 : S.filter (fun q => p 2 ≤ q) = {p 2, p 1, p 0} := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf3 : S.filter (fun q => p 3 ≤ q) = {p 3, p 2, p 1, p 0} := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf4 : S.filter (fun q => p 4 ≤ q) = {p 4, p 3, p 2, p 1, p 0} := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf5 : S.filter (fun q => p 5 ≤ q) = {p 5, p 4, p 3, p 2, p 1, p 0} := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hf6 : S.filter (fun q => p 6 ≤ q) = {p 6, p 5, p 4, p 3, p 2, p 1, p 0} := by
    ext q
    simp only [S, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hupper : UpperAdmissibleSet Q S := by
    intro q hq hodd
    have hcases : q = p 6 ∨ q = p 5 ∨ q = p 4 ∨ q = p 3 ∨
        q = p 2 ∨ q = p 1 ∨ q = p 0 := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hf6]
      simpa [hpeq, Nat.cast_mul, pow_succ, mul_comm, mul_left_comm, mul_assoc]
        using h7
    · rw [hf5] at hodd
      norm_num [hpeq] at hodd
    · rw [hf4]
      simpa [hpeq, Nat.cast_mul, pow_succ, mul_comm, mul_left_comm, mul_assoc]
        using h5
    · rw [hf3] at hodd
      norm_num [hpeq] at hodd
    · rw [hf2]
      simpa [hpeq, Nat.cast_mul, pow_succ, mul_comm, mul_left_comm, mul_assoc]
        using h3
    · rw [hf1] at hodd
      norm_num [hpeq] at hodd
    · rw [hf0]
      simpa [hpeq, Nat.cast_mul, pow_succ, mul_comm, mul_left_comm, mul_assoc]
        using h1
  have htotal : (([p 6, p 5, p 4, p 3, p 2, p 1, p 0].prod : ℕ) : ℝ) < Q := by
    have hp6 : (1 : ℝ) ≤ p 6 := by exact_mod_cast (Nat.succ_le_of_lt (hp 6))
    have hsquare : (1 : ℝ) ≤ (p 6 : ℝ)^2 := by nlinarith
    have hnonneg : (0 : ℝ) ≤ (([p 6, p 5, p 4, p 3, p 2, p 1, p 0].prod : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    apply (le_mul_of_one_le_right hnonneg hsquare).trans_lt
    simpa only [List.prod_cons, List.prod_nil, Nat.cast_mul, Nat.cast_one,
      mul_one, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h7
  refine ⟨htotal, ?_⟩
  simpa only [S, List.toFinset_cons, List.toFinset_nil, Finset.insert_empty_eq] using hupper

/-- The four original affine H rows pay all four literal natural cubes
at one real level. No integer endpoints or null sets are discarded. -/
theorem seven_admissible_of_histories (N : ℝ) (hN : 1 < N)
    (p : Fin 8 → ℕ) (hp : ∀ i, 0 < p i) (hord : StrictAnti p) (L : ℝ)
    (hh : ∀ j : Fin 4, oldHistory (point N p) j < L) :
    ordinaryRosserPrefixAdmissible false (N^L)
      [p 6, p 5, p 4, p 3, p 2, p 1, p 0] := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hc (i : Fin 8) : N ^ (3 * point N p i) = (p i : ℝ)^3 := by
    rw [mul_comm, Real.rpow_mul_natCast hN0.le, point_rpow N hN p hp]
  have hh0 := Real.rpow_lt_rpow_of_exponent_lt hN (hh 0)
  have hh1 := Real.rpow_lt_rpow_of_exponent_lt hN (hh 1)
  have hh2 := Real.rpow_lt_rpow_of_exponent_lt hN (hh 2)
  have hh3 := Real.rpow_lt_rpow_of_exponent_lt hN (hh 3)
  norm_num only [oldHistory, P4AOriginalRemainingEighthSources.history,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at hh0 hh1 hh2 hh3
  apply seven_admissible_of_four_cubes p (N^L) hp hord
  · simpa only [hc] using hh0
  · simpa only [Real.rpow_add hN0, point_rpow N hN p hp, hc] using hh1
  · simpa only [Real.rpow_add hN0, point_rpow N hN p hp, hc] using hh2
  · simpa only [Real.rpow_add hN0, point_rpow N hN p hp, hc] using hh3

end
end ImbalancedChen.P4AOriginalFull87SevenCubeAdmission
