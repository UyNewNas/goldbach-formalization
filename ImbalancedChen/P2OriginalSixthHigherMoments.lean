import ImbalancedChen.P2OriginalSixthSimplexMoments
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardLowBoundary
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardMiddle
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK0I2
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK0I3
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK0I4
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK0I5
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK0I6
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK1I2
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK1I3
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK1I4
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK1I5
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK1I6
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK2I1
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK2I2
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK2I3
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK2I4
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK2I5
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK2I6
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK3I0
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK3I1
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK3I2
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK3I3
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK3I4
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK3I5
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK3I6
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK4I1
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK4I2
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK4I3
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK4I4
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK4I5
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK4I6
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK5I0
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK5I2
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK5I3
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK5I4
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK5I5
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK5I6
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK6I0
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK6I1
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK6I2
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK6I3
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK6I4
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK6I5
import ImbalancedChen.P2OriginalSixthHigherMomentsGuardK6I6
import ImbalancedChen.P2OriginalSixthHigherMomentsAuthorK0
import ImbalancedChen.P2OriginalSixthHigherMomentsAuthorK1
import ImbalancedChen.P2OriginalSixthHigherMomentsAuthorK2
import ImbalancedChen.P2OriginalSixthHigherMomentsAuthorK3
import ImbalancedChen.P2OriginalSixthHigherMomentsAuthorK4
import ImbalancedChen.P2OriginalSixthHigherMomentsAuthorK5
import ImbalancedChen.P2OriginalSixthHigherMomentsAuthorK6

/-! SOURCE_ONLY / UNCOMPILED.
Public facade for the original degree-zero-through-six simplex moments.
All original public fully qualified names, theorem headers, and definition
bodies are retained. Five definitions and completeH_cons_succ are imported
from Core; the other public declarations remain owned by this module.
The existing a9a4e532 proof bodies are retained; this file changes only
compilation organization. No numerical row or new evaluator is introduced.
-/
namespace ImbalancedChen.P2OriginalSixthHigherMoments
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2OriginalSixthSimplexMoments
open ProofPieces

theorem duplicateH_map {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B)
    (y : Fin 7 → A) (i : Fin 7) (k : ℕ) :
    f (duplicateH y i k) = duplicateH (fun r => f (y r)) i k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [duplicateH]
    | succ k =>
      simp only [duplicateH, map_smul, map_sum, map_mul, map_add, map_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (k - j.val) (by omega)]

def rationalMoment (g y : Fin 7 → ℚ) (k : ℕ) : ℚ :=
  (∑ i : Fin 7, g i * duplicateH y i k) /
    ((∑ i : Fin 7, g i) * ((7 + k).choose k : ℚ))

def realMoment (g y : Fin 7 → ℝ) (k : ℕ) : ℝ :=
  (∑ i : Fin 7, g i * duplicateH y i k) /
    ((∑ i : Fin 7, g i) * ((7 + k).choose k : ℝ))

theorem rationalMoment_cast (g y : Fin 7 → ℚ) (k : ℕ) :
    (rationalMoment g y k : ℝ) =
      realMoment (fun i => (g i : ℝ)) (fun i => (y i : ℝ)) k := by
  unfold rationalMoment realMoment
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hmap := duplicateH_map (Algebra.ofId ℚ ℝ) y i k
  change ((duplicateH y i k : ℚ) : ℝ) = duplicateH (fun r => (y r : ℝ)) i k at hmap
  rw [hmap]

theorem baryCoefficient_cast (e : Fin 7 → ℕ) :
    (baryCoefficient e : ℝ) = baryMoment e := by
  rw [baryMoment_eq]
  simp [baryCoefficient]

theorem bary_bumped (e : Fin 7 → ℕ) (i : Fin 7) (x : Point) :
    (∏ r : Fin 7, bary r x ^ bumped e i r) =
      bary i x * ∏ r : Fin 7, bary r x ^ e r := by
  simp only [bumped, pow_add, Finset.prod_mul_distrib, prod_unitExponent]
  ring

theorem integratedPower_newton_guard (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    integratedPower y i k = duplicateH y i k /
      ((Nat.factorial 7 : ℝ) * ((7 + k).choose k : ℝ)) := by
  interval_cases k
  · fin_cases i
    · exact integratedPower_newton_guard_0_0 y
    · exact integratedPower_newton_guard_0_1 y
    · exact integratedPower_newton_guard_0_2 y
    · exact integratedPower_newton_guard_0_3 y
    · exact integratedPower_newton_guard_0_4 y
    · exact integratedPower_newton_guard_0_5 y
    · exact integratedPower_newton_guard_0_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_1_0 y
    · exact integratedPower_newton_guard_1_1 y
    · exact integratedPower_newton_guard_1_2 y
    · exact integratedPower_newton_guard_1_3 y
    · exact integratedPower_newton_guard_1_4 y
    · exact integratedPower_newton_guard_1_5 y
    · exact integratedPower_newton_guard_1_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_2_0 y
    · exact integratedPower_newton_guard_2_1 y
    · exact integratedPower_newton_guard_2_2 y
    · exact integratedPower_newton_guard_2_3 y
    · exact integratedPower_newton_guard_2_4 y
    · exact integratedPower_newton_guard_2_5 y
    · exact integratedPower_newton_guard_2_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_3_0 y
    · exact integratedPower_newton_guard_3_1 y
    · exact integratedPower_newton_guard_3_2 y
    · exact integratedPower_newton_guard_3_3 y
    · exact integratedPower_newton_guard_3_4 y
    · exact integratedPower_newton_guard_3_5 y
    · exact integratedPower_newton_guard_3_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_4_0 y
    · exact integratedPower_newton_guard_4_1 y
    · exact integratedPower_newton_guard_4_2 y
    · exact integratedPower_newton_guard_4_3 y
    · exact integratedPower_newton_guard_4_4 y
    · exact integratedPower_newton_guard_4_5 y
    · exact integratedPower_newton_guard_4_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_5_0 y
    · exact integratedPower_newton_guard_5_1 y
    · exact integratedPower_newton_guard_5_2 y
    · exact integratedPower_newton_guard_5_3 y
    · exact integratedPower_newton_guard_5_4 y
    · exact integratedPower_newton_guard_5_5 y
    · exact integratedPower_newton_guard_5_6 y
  · fin_cases i
    · exact integratedPower_newton_guard_6_0 y
    · exact integratedPower_newton_guard_6_1 y
    · exact integratedPower_newton_guard_6_2 y
    · exact integratedPower_newton_guard_6_3 y
    · exact integratedPower_newton_guard_6_4 y
    · exact integratedPower_newton_guard_6_5 y
    · exact integratedPower_newton_guard_6_6 y

theorem completeH_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (as : List A) (k : ℕ) :
    f (completeH as k) = completeH (as.map f) k := by
  induction as generalizing k with
  | nil => by_cases hk : k = 0 <;> simp [completeH, hk]
  | cons a as ih => simp [completeH, map_sum, map_mul, map_pow, ih]

theorem duplicateH_author_guard (y : Fin 7 → ℚ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    duplicateH y i k = ∑ j : Fin (k + 1),
      completeH (List.ofFn y) (k - j.val) * y i ^ j.val := by
  interval_cases k
  · exact duplicateH_author_guard_0 y i
  · exact duplicateH_author_guard_1 y i
  · exact duplicateH_author_guard_2 y i
  · exact duplicateH_author_guard_3 y i
  · exact duplicateH_author_guard_4 y i
  · exact duplicateH_author_guard_5 y i
  · exact duplicateH_author_guard_6 y i

def authorMoment (g y : Fin 7 → ℚ) (k : ℕ) : ℚ :=
  (∑ j : Fin (k + 1), completeH (List.ofFn y) (k - j.val) *
    ∑ i : Fin 7, g i * y i ^ j.val) /
      ((∑ i : Fin 7, g i) * ((7 + k).choose k : ℚ))

theorem authorMoment_eq_rationalMoment (g y : Fin 7 → ℚ) (k : ℕ)
    (hk : k ≤ 6) : authorMoment g y k = rationalMoment g y k := by
  unfold authorMoment rationalMoment
  congr 1
  simp_rw [duplicateH_author_guard y _ k hk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def integerDuplicateH (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ) : ℤ :=
  completeH (z i :: List.ofFn z) k

theorem integerDuplicateH_cast (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    (integerDuplicateH z i k : ℚ) = duplicateH (fun r => (z r : ℚ)) i k := by
  have hm := completeH_map (Int.castRingHom ℚ) (z i :: List.ofFn z) k
  have he : (integerDuplicateH z i k : ℚ) =
      completeH ((z i : ℚ) :: List.ofFn (fun r => (z r : ℚ))) k := by
    simpa [integerDuplicateH, List.map_ofFn] using hm
  rw [he, completeH, duplicateH_author_guard _ i k hk]
  apply Finset.sum_congr rfl
  intro j _
  ring

def integerNewtonNumerator (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ) : ℤ :=
  ∑ j : Fin (k + 1),
    ((∑ r : Fin 7, z r ^ (j.val + 1)) + z i ^ (j.val + 1)) *
      integerDuplicateH z i (k - j.val)

theorem integerNewtonNumerator_spec (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ)
    (hk : k + 1 ≤ 6) :
    integerNewtonNumerator z i k = (k + 1 : ℤ) * integerDuplicateH z i (k + 1) := by
  have hc (j : Fin (k + 1)) :
      (integerDuplicateH z i (k - j.val) : ℚ) =
        duplicateH (fun r => (z r : ℚ)) i (k - j.val) :=
    integerDuplicateH_cast z i _ (by omega)
  have hQ : (integerNewtonNumerator z i k : ℚ) =
      (k + 1 : ℚ) * (integerDuplicateH z i (k + 1) : ℚ) := by
    rw [integerDuplicateH_cast z i (k + 1) hk, duplicateH]
    simp only [integerNewtonNumerator, Int.cast_sum, Int.cast_mul, Int.cast_add,
      Int.cast_pow, hc, smul_eq_mul]
    have hne : (k + 1 : ℚ) ≠ 0 := by positivity
    field_simp [hne]
  exact_mod_cast hQ

theorem integerNewtonNumerator_divisible (z : Fin 7 → ℤ) (i : Fin 7) (k : ℕ)
    (hk : k + 1 ≤ 6) : (k + 1 : ℤ) ∣ integerNewtonNumerator z i k :=
  ⟨integerDuplicateH z i (k + 1), integerNewtonNumerator_spec z i k hk⟩

theorem binomial_normalization (k : ℕ) :
    ((7 + k).choose k : ℚ) * k.factorial * (Nat.factorial 7) =
      ((7 + k).factorial : ℚ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 7 + k) (k := k) (by omega)
  have hs : 7 + k - k = 7 := by omega
  rw [hs] at h
  exact_mod_cast h

theorem integral_bary_interpolate_power (y : Fin 7 → ℝ) (i : Fin 7) (k : ℕ)
    (hk : k ≤ 6) :
    (∫ x in canonical, bary i x * interpolate y x ^ k) =
      duplicateH y i k /
        (((Nat.factorial 7) : ℝ) * ((7 + k).choose k : ℝ)) := by
  classical
  let S := Finset.piAntidiag (Finset.univ : Finset (Fin 7)) k
  let term (e : Fin 7 → ℕ) (x : Point) :=
    ((Nat.multinomial Finset.univ e : ℝ) * ∏ r : Fin 7, y r ^ e r) *
      ∏ r : Fin 7, bary r x ^ bumped e i r
  have hi (e : Fin 7 → ℕ) : IntegrableOn (term e) canonical := by
    apply ContinuousOn.integrableOn_compact canonical_compact
    apply Continuous.continuousOn
    apply continuous_const.mul
    exact continuous_finsetProd _ fun r _ => (bary_continuous r).pow _
  have he (x : Point) : bary i x * interpolate y x ^ k = ∑ e ∈ S, term e x := by
    rw [interpolate, Finset.sum_pow_eq_sum_piAntidiag, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [term, mul_pow, Finset.prod_mul_distrib, bary_bumped]
    ring
  have hint : (∫ x in canonical, bary i x * interpolate y x ^ k) =
      ∑ e ∈ S, ((Nat.multinomial Finset.univ e : ℝ) *
        (baryCoefficient (bumped e i) : ℝ)) * ∏ r : Fin 7, y r ^ e r := by
    simp_rw [he]
    rw [integral_finsetSum S (fun e _ => hi e)]
    apply Finset.sum_congr rfl
    intro e _
    rw [show term e = fun x =>
        ((Nat.multinomial Finset.univ e : ℝ) * ∏ r : Fin 7, y r ^ e r) *
          ∏ r : Fin 7, bary r x ^ bumped e i r from rfl,
      integral_const_mul]
    rw [show (∫ x in canonical, ∏ r : Fin 7, bary r x ^ bumped e i r) =
      baryMoment (bumped e i) from rfl, ← baryCoefficient_cast]
    ring
  rw [hint]
  exact integratedPower_newton_guard y i k hk

theorem integral_interpolate_mul_power (g y : Fin 7 → ℝ) (k : ℕ) (hk : k ≤ 6) :
    (∫ x in canonical, interpolate g x * interpolate y x ^ k) =
      (∑ i : Fin 7, g i * duplicateH y i k) /
        (((Nat.factorial 7) : ℝ) * ((7 + k).choose k : ℝ)) := by
  have hi (i : Fin 7) : IntegrableOn
      (fun x => g i * (bary i x * interpolate y x ^ k)) canonical :=
    (continuous_const.mul ((bary_continuous i).mul
      ((interpolate_continuous y).pow k))).continuousOn.integrableOn_compact
        canonical_compact
  have he (x : Point) : interpolate g x * interpolate y x ^ k =
      ∑ i : Fin 7, g i * (bary i x * interpolate y x ^ k) := by
    simp only [interpolate, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [integral_const_mul, integral_bary_interpolate_power y _ k hk]
  simp [mul_div_assoc, Finset.sum_div]

end
end ImbalancedChen.P2OriginalSixthHigherMoments
