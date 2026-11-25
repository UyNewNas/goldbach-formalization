import ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semiring

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The accepted physical Gamma5 extension has a complete-product gate and a
positive cutoff at every original old/fresh/tail coordinate. For a fixed
positive exponent a, the condition N^a <= b therefore forces every nonzero
physical profile to have total rank at most floor(4/a), once N exceeds the
explicit threshold below. At larger ranks the entire original function,
and consequently every original Euler word, is zero.

The accepted bounded-rank Euler budget then gives an all-rank budget. Its
constant precedes every moving scale, endpoint, cutoff, width, rank, and
physical point. The profile, its coordinate permutation, and its Euler
operators are reused without changing their definitions.

This is a smooth-support theorem. It does not supply the arithmetic claim
that an actual marked history has a common N^a floor, does not admit a
source family, and does not pay a collar or prime-product estimate.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5AllRankEulerBudget

noncomputable section
open Finset Real
open P2FiniteMarkedGamma5PhysicalExtension
open P2FiniteMarkedGamma5EulerWordBudget
open P5Z.AdmissibleAllRankIntegerGeometricFamily (eulerOne eulerWord)
open scoped Classical BigOperators

/-- A threshold fixed before every moving parameter. It ensures both
exp(1) <= N and 2 <= N^(a/2). -/
def scaleThreshold (a : ℝ) : ℝ := max (exp 1) ((2 : ℝ) ^ (2 / a))

theorem scaleThreshold_bounds {a N : ℝ} (ha : 0 < a)
    (hN : scaleThreshold a ≤ N) : 1 < N ∧ 2 ≤ N ^ (a / 2) := by
  have heN : exp 1 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 < N :=
    (Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)).trans_le heN
  refine ⟨hN1, ?_⟩
  have hbase : (2 : ℝ) ^ (2 / a) ≤ N := (le_max_right _ _).trans hN
  have hmul : (2 / a) * (a / 2) = (1 : ℝ) := by
    field_simp [ne_of_gt ha]
  calc
    2 = ((2 : ℝ) ^ (2 / a)) ^ (a / 2) := by
      rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num), hmul, Real.rpow_one]
    _ ≤ N ^ (a / 2) := Real.rpow_le_rpow
      (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) _) hbase (half_pos ha).le

/-- The original physical profile itself supplies the rank ceiling.
All slots are counted, including repeated coordinates and the two fresh
slots. No rank or complete-product assumption is imposed on the caller. -/
theorem physicalProfile_nonzero_rank_le {a N logQ width b : ℝ} {k r : ℕ}
    {x : PhysicalPoint k r} (ha : 0 < a) (hN : scaleThreshold a ≤ N)
    (hb : N ^ a ≤ b) (hw : 0 < width) (hw1 : width ≤ 1)
    (hne : physicalProfile logQ N width b x ≠ 0) :
    k + 2 + r ≤ ⌊4 / a⌋₊ := by
  obtain ⟨hN1, htwo⟩ := scaleThreshold_bounds ha hN
  have hN0 : 0 < N := zero_lt_one.trans hN1
  have hb0 : 0 < b := (Real.rpow_pos_of_pos hN0 a).trans_le hb
  have hsquare : (N ^ (a / 2)) ^ 2 = N ^ a := by
    calc
      (N ^ (a / 2)) ^ 2 = N ^ ((a / 2) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hN0.le (a / 2) 2).symm
      _ = N ^ a := by congr 1; ring
  have hhalf : N ^ (a / 2) ≤ b / 2 := by
    have hmul := mul_le_mul_of_nonneg_left htwo
      (Real.rpow_nonneg hN0.le (a / 2))
    nlinarith only [hmul, hsquare, hb]
  have hslot (i : Slot k r) : N ^ (a / 2) ≤ x i :=
    hhalf.trans (physicalProfile_nonzero_lower hb0 hne i).le
  have hprodLower : (N ^ (a / 2)) ^ (k + 2 + r) ≤ physicalProduct x := by
    calc
      (N ^ (a / 2)) ^ (k + 2 + r) = ∏ _i : Slot k r, N ^ (a / 2) := by
        simp only [prod_const, card_univ, Slot, Fintype.card_sum, Fintype.card_fin,
          Nat.add_assoc]
      _ ≤ physicalProduct x :=
        Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg hN0.le (a / 2))
          (fun i _ => hslot i)
  have hprodUpper : physicalProduct x ≤ N ^ 2 := by
    calc
      physicalProduct x ≤ exp width * N :=
        (physicalProfile_nonzero_product_lt hb0 hN0 hw hne).le
      _ ≤ exp 1 * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hw1) hN0.le
      _ ≤ N * N := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hN) hN0.le
      _ = N ^ 2 := (pow_two N).symm
  have hpow : N ^ ((a / 2) * ((k + 2 + r : ℕ) : ℝ)) ≤ N ^ (2 : ℝ) := by
    rw [Real.rpow_mul hN0.le, Real.rpow_natCast, Real.rpow_two]
    exact hprodLower.trans hprodUpper
  have hrank : (a / 2) * ((k + 2 + r : ℕ) : ℝ) ≤ (2 : ℝ) :=
    (Real.rpow_le_rpow_left_iff hN1).mp hpow
  apply (Nat.le_floor_iff (show (0 : ℝ) ≤ 4 / a from
    div_nonneg (by norm_num) ha.le)).mpr
  apply (le_div_iff₀ ha).mpr
  nlinarith only [hrank]

/-- At high rank the physical profile is zero on the entire real
coordinate space, not only on an arithmetic source. -/
theorem physicalProfile_eq_zero_of_rank_gt {a N logQ width b : ℝ} {k r : ℕ}
    (ha : 0 < a) (hN : scaleThreshold a ≤ N) (hb : N ^ a ≤ b)
    (hw : 0 < width) (hw1 : width ≤ 1) (hrank : ⌊4 / a⌋₊ < k + 2 + r) :
    physicalProfile (k := k) (r := r) logQ N width b = 0 := by
  funext x
  change physicalProfile logQ N width b x = 0
  by_contra hne
  exact (not_le_of_gt hrank) (physicalProfile_nonzero_rank_le ha hN hb hw hw1 hne)

/-- The accepted bijection to the original Fin coordinates preserves the
whole-function zero statement. -/
theorem finPhysicalProfile_eq_zero_of_rank_gt {a N logQ width b : ℝ} {k r : ℕ}
    (ha : 0 < a) (hN : scaleThreshold a ≤ N) (hb : N ^ a ≤ b)
    (hw : 0 < width) (hw1 : width ≤ 1) (hrank : ⌊4 / a⌋₊ < k + 2 + r) :
    finPhysicalProfile (k := k) (r := r) logQ N width b = 0 := by
  have hz := physicalProfile_eq_zero_of_rank_gt (logQ := logQ) ha hN hb hw hw1 hrank
  funext v
  exact congrFun hz (finToPhysical k r v)

private theorem eulerWord_zero {d : ℕ} (w : List (Fin d)) :
    eulerWord w (0 : (Fin d → ℝ) → ℝ) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change eulerOne i (eulerWord w (0 : (Fin d → ℝ) → ℝ)) = 0
    rw [ih]
    funext v
    simp [eulerOne]

/-- Public access to the existing private zero-word proof, so geometric
Family consumers need not depend on a compiler-generated private name. -/
theorem eulerWord_zero_eq {d : ℕ} (w : List (Fin d)) :
    eulerWord w (0 : (Fin d → ℝ) → ℝ) = 0 :=
  eulerWord_zero w

/-- Every original Euler word, with arbitrary repeated coordinates and
without an order restriction, vanishes at every point above the rank cap. -/
theorem finPhysicalProfile_eulerWord_eq_zero_of_rank_gt
    {a N logQ width b : ℝ} {k r : ℕ}
    (ha : 0 < a) (hN : scaleThreshold a ≤ N) (hb : N ^ a ≤ b)
    (hw : 0 < width) (hw1 : width ≤ 1) (hrank : ⌊4 / a⌋₊ < k + 2 + r)
    (w : List (Fin (k + (2 + r)))) :
    eulerWord w (finPhysicalProfile logQ N width b) = 0 := by
  rw [finPhysicalProfile_eq_zero_of_rank_gt ha hN hb hw hw1 hrank]
  exact eulerWord_zero w

/-- Uniformly in all ranks and moving parameters, the original mixed
Euler words obey the accepted inverse-width budget. One constant works
simultaneously for every derivative order q <= m, with exponent q.
The sole fixed positive floor exponent is chosen before the scale. -/
theorem finPhysicalProfile_allRank_mixedEuler_budget {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ), scaleThreshold a ≤ N →
      ∀ (logQ b width : ℝ), N ^ a ≤ b → 0 < width → width ≤ 1 →
      ∀ (k r q : ℕ), q ≤ m →
      ∀ w : List (Fin (k + (2 + r))), w.length ≤ q →
      ∀ v : Fin (k + (2 + r)) → ℝ,
        |eulerWord w (finPhysicalProfile logQ N width b) v| ≤
          C * (1 + width⁻¹) ^ q := by
  choose C hC HC using fun q : ℕ =>
    finPhysicalProfile_boundedRank_mixedEuler_budget ⌊4 / a⌋₊ q
  let Ctotal : ℝ := ∑ q ∈ range (m + 1), C q
  have htotal : 0 ≤ Ctotal := sum_nonneg (fun q _ => hC q)
  refine ⟨Ctotal, htotal, ?_⟩
  intro N hN logQ b width hb hw hw1 k r q hqm w hwq v
  have hN0 : 0 < N := zero_lt_one.trans (scaleThreshold_bounds ha hN).1
  have hb0 : 0 < b := (Real.rpow_pos_of_pos hN0 a).trans_le hb
  have hpow : 0 ≤ (1 + width⁻¹) ^ q :=
    pow_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr hw.le)) q
  by_cases hkr : k + 2 + r ≤ ⌊4 / a⌋₊
  · have hCsum : C q ≤ Ctotal :=
      single_le_sum (fun j _ => hC j) (mem_range.mpr (Nat.lt_succ_of_le hqm))
    exact (HC q k r hkr logQ N b width hb0 hw w hwq v).trans
      (mul_le_mul_of_nonneg_right hCsum hpow)
  · rw [finPhysicalProfile_eulerWord_eq_zero_of_rank_gt
      ha hN hb hw hw1 (lt_of_not_ge hkr) w]
    simp only [Pi.zero_apply, abs_zero]
    exact mul_nonneg htotal hpow

/-- The same result in eventual-uniformity form. The explicit threshold
is independent of m, and the constant is independent of all moving ranks. -/
theorem finPhysicalProfile_eventually_allRank_mixedEuler_budget
    {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ N0 C : ℝ, 1 < N0 ∧ 0 ≤ C ∧ ∀ (N : ℝ), N0 ≤ N →
      ∀ (logQ b width : ℝ), N ^ a ≤ b → 0 < width → width ≤ 1 →
      ∀ (k r q : ℕ), q ≤ m →
      ∀ w : List (Fin (k + (2 + r))), w.length ≤ q →
      ∀ v : Fin (k + (2 + r)) → ℝ,
        |eulerWord w (finPhysicalProfile logQ N width b) v| ≤
          C * (1 + width⁻¹) ^ q := by
  obtain ⟨C, hC, H⟩ := finPhysicalProfile_allRank_mixedEuler_budget ha m
  have hN0 : 1 < scaleThreshold a := (scaleThreshold_bounds ha le_rfl).1
  exact ⟨scaleThreshold a, C, hN0, hC, H⟩

end
end ImbalancedChen.P2FiniteMarkedGamma5AllRankEulerBudget
