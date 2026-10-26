import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Positive Dirichlet-coefficient multinomial comparison with the ORIGINAL
product of per-label factorials. The selected label-count term is bounded
by the total label sum, with its exact multinomial integer retained.
No gamma-unit or weighted-fibre identity is a hypothesis. The next leaf
identifies the arithmetic functions with literal weighted prime words.
-/
namespace ImbalancedChen.P5Z.WeightedLabelMultinomialComparison
noncomputable section
open scoped Classical BigOperators

def coefficient (n : ℕ) : ArithmeticFunction ℝ≥0 →+ ℝ≥0 where
  toFun F := F n
  map_zero' := rfl
  map_add' _ _ := rfl

theorem nat_mul_coefficient (k : ℕ) (F : ArithmeticFunction ℝ≥0) (n : ℕ) :
    ((k : ArithmeticFunction ℝ≥0)*F) n = (k : ℝ≥0)*F n := by
  calc
    _ = coefficient n (k • F) := by rw [nsmul_eq_mul]; rfl
    _ = k • coefficient n F := (coefficient n).map_nsmul F k
    _ = _ := by rw [nsmul_eq_mul]; rfl

theorem mul_coefficient_mono {F G H K : ArithmeticFunction ℝ≥0}
    (hFG : ∀ n, F n ≤ G n) (hHK : ∀ n, H n ≤ K n) (n : ℕ) :
    (F*H) n ≤ (G*K) n := by
  simp only [ArithmeticFunction.mul_apply]
  exact Finset.sum_le_sum (fun d hd => mul_le_mul (hFG _) (hHK _) (zero_le _) (zero_le _))

theorem pow_coefficient_mono {F G : ArithmeticFunction ℝ≥0}
    (hFG : ∀ n, F n ≤ G n) (r n : ℕ) : (F^r) n ≤ (G^r) n := by
  induction r generalizing n with
  | zero => exact le_rfl
  | succ r ih =>
    rw [pow_succ,pow_succ]
    exact mul_coefficient_mono ih hFG n

/-- Exact selected multinomial coefficient, projected to a positive
Dirichlet coefficient, is no larger than the complete expansion. -/
theorem selected_multinomial_coefficient_le {ι : Type*} (S : Finset ι)
    (F : ι → ArithmeticFunction ℝ≥0) (m : ι → ℕ) (r n : ℕ)
    (hr : ∑ i ∈ S, m i = r) (hS : ∀ i, m i ≠ 0 → i ∈ S) :
    (Nat.multinomial S m : ℝ≥0)*(∏ i ∈ S, F i ^ m i) n ≤ ((∑ i ∈ S, F i)^r) n := by
  have hm : m ∈ Finset.piAntidiag S r := Finset.mem_piAntidiag.mpr ⟨hr,hS⟩
  have hexpand : ((∑ i ∈ S, F i)^r) n =
      ∑ k ∈ Finset.piAntidiag S r,
        (Nat.multinomial S k : ℝ≥0)*(∏ i ∈ S, F i ^ k i) n := by
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    change coefficient n (∑ k ∈ Finset.piAntidiag S r,
      (Nat.multinomial S k : ArithmeticFunction ℝ≥0)*(∏ i ∈ S, F i ^ k i)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact nat_mul_coefficient _ _ n
  rw [hexpand]
  exact Finset.single_le_sum (fun k hk => zero_le _) hm

/-- ORIGINAL per-label normalization is dominated by the total prime
coefficient with total-rank factorial. This is a comparison, not a change
to the definition of the original fixed-count coefficient. -/
theorem original_normalized_coefficient_le_total {ι : Type*} (S : Finset ι)
    (F : ι → ArithmeticFunction ℝ≥0) (m : ι → ℕ) (r n : ℕ)
    (hr : ∑ i ∈ S, m i = r) (hS : ∀ i, m i ≠ 0 → i ∈ S) :
    (∏ i ∈ S, F i ^ m i) n / (∏ i ∈ S, (m i).factorial : ℕ) ≤
      ((∑ i ∈ S, F i)^r) n / (r.factorial : ℕ) := by
  have hMpos : (0 : ℝ≥0) < (∏ i ∈ S, (m i).factorial : ℕ) := by
    exact_mod_cast Nat.prod_factorial_pos S m
  have hrpos : (0 : ℝ≥0) < (r.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos r
  have hspec : ((∏ i ∈ S, (m i).factorial : ℕ) : ℝ≥0)*(Nat.multinomial S m : ℝ≥0) =
      (r.factorial : ℕ) := by
    exact_mod_cast (Nat.multinomial_spec S m).trans (congrArg Nat.factorial hr)
  apply (div_le_div_iff₀ hMpos hrpos).mpr
  calc
    _ = ((∏ i ∈ S, (m i).factorial : ℕ) : ℝ≥0)*
        ((Nat.multinomial S m : ℝ≥0)*(∏ i ∈ S, F i ^ m i) n) := by rw [← hspec]; ring
    _ ≤ ((∏ i ∈ S, (m i).factorial : ℕ) : ℝ≥0)*((∑ i ∈ S, F i)^r) n :=
      mul_le_mul_of_nonneg_left (selected_multinomial_coefficient_le S F m r n hr hS) (zero_le _)
    _ = _ := mul_comm _ _

end
end ImbalancedChen.P5Z.WeightedLabelMultinomialComparison
