import Mathlib
import ImbalancedChen.Part3TwoLongInternalP2FrequencySums
import ImbalancedChen.P0RamanujanMultiplicativeGcdBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The P2 divisor-frequency reindexing is proved on the ACTUAL filtered Z
sum, rather than only on a suggested parametrization j=d*k.
-/
namespace ImbalancedChen.Part3.TwoLongFilteredIntegerFrequency
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongInternalP2FrequencySums
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanMultiplicativeGcdBound20261025a

def baseDecay (H : ℝ) : ℤ → ℝ := multipleDecay H 1

def filteredDecay (H : ℝ) (d : ℕ) (j : ℤ) : ℝ :=
  if (d : ℤ) ∣ j then baseDecay H j else 0

theorem filtered_at_multiple {H : ℝ} {d : ℕ} (hd : 0 < d) (k : ℤ) :
    filteredDecay H d ((d : ℤ)*k) = multipleDecay H d k := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hk : k=0
  · simp [filteredDecay,baseDecay,multipleDecay,hk]
  · have hdk : (d : ℤ)*k ≠ 0 := mul_ne_zero hdZ hk
    simp [filteredDecay,baseDecay,multipleDecay,hk,hdk,Int.cast_mul]

/-- Support-level bijection proves the exact all-integer reindexing.
Zero frequencies are already exactly zero in the actual kernel. -/
theorem filtered_tsum_eq_multiple {H : ℝ} {d : ℕ} (hd : 0 < d) :
    (∑' j : ℤ, filteredDecay H d j) = ∑' k : ℤ, multipleDecay H d k := by
  let f := filteredDecay H d
  let g := multipleDecay H d
  let i : Function.support g → ℤ := fun k => (d : ℤ)*k.val
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hi : Function.Injective i := by
    intro k l h
    exact Subtype.ext (mul_left_cancel₀ hdZ h)
  have hf : Function.support f ⊆ Set.range i := by
    intro j hj
    have hdiv : (d : ℤ) ∣ j := by
      by_contra hn
      exact hj (by simp [f,filteredDecay,hn])
    obtain ⟨k,hk⟩ := hdiv
    have hg : k ∈ Function.support g := by
      intro hn
      have hfg := filtered_at_multiple (H := H) hd k
      rw [← hk] at hfg
      exact hj (hfg.trans hn)
    exact ⟨⟨k,hg⟩,hk.symm⟩
  have hfg (k : Function.support g) : f (i k) = g k := filtered_at_multiple hd k
  exact tsum_eq_tsum_of_ne_zero_bij i hi hf hfg

theorem filtered_nonneg (H : ℝ) (d : ℕ) (j : ℤ) : 0 ≤ filteredDecay H d j := by
  unfold filteredDecay
  split_ifs
  · exact multipleDecay_nonneg H 1 j
  · exact le_rfl

theorem filtered_summable {H : ℝ} (hH : 0 < H) (d : ℕ) :
    Summable (filteredDecay H d) := by
  have hbase := (multipleDecay_summable_tsum_le hH (by norm_num : 0 < (1 : ℕ))).1
  apply hbase.of_nonneg_of_le (filtered_nonneg H d)
  intro j
  unfold filteredDecay baseDecay
  split_ifs
  · exact le_rfl
  · exact multipleDecay_nonneg H 1 j

theorem filtered_tsum_le {H : ℝ} (hH : 0 < H) {d : ℕ} (hd : 0 < d) :
    (∑' j : ℤ, filteredDecay H d j) ≤ 2*H/(d : ℝ) := by
  rw [filtered_tsum_eq_multiple hd]
  exact (multipleDecay_summable_tsum_le hH hd).2

/-- The complete integer filters pay the same double-frequency budget as
D's d-multiple parametrization, with no guessed coverage assumption. -/
theorem filtered_double_sum_le {H K : ℝ} (hH : 0 < H) (hK : 0 < K)
    {d : ℕ} (hd : 0 < d) :
    (∑' j : ℤ, ∑' k : ℤ, filteredDecay H d j * filteredDecay K d k) ≤
      4*H*K/(d : ℝ)^2 := by
  calc
    _ = (∑' j : ℤ, filteredDecay H d j) * (∑' k : ℤ, filteredDecay K d k) := by
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
    _ ≤ (2*H/(d : ℝ))*(2*K/(d : ℝ)) :=
      mul_le_mul (filtered_tsum_le hH hd) (filtered_tsum_le hK hd)
        (tsum_nonneg (filtered_nonneg K d)) (by positivity)
    _ = _ := by have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'; field_simp [hdR]; ring

/-- Euler's exact divisor identity supplies the actual Ramanujan gcd
majorant in the original q-divisor filter, including negative j and j=0. -/
theorem gcd_eq_totient_filtered (q : ℕ) (hq : 0 < q) (j : ℤ) :
    (q.gcd j.natAbs : ℝ) =
      ∑ d ∈ q.divisors.filter (fun d => (d : ℤ) ∣ j), (Nat.totient d : ℝ) := by
  have hgc : 0 < q.gcd j.natAbs := Nat.gcd_pos_of_pos_left _ hq
  have hdiv (d : ℕ) : (d : ℤ) ∣ j ↔ d ∣ j.natAbs := by
    rw [← Int.dvd_natAbs,Int.natCast_dvd_natCast]
  have hset : q.divisors.filter (fun d => (d : ℤ) ∣ j) = (q.gcd j.natAbs).divisors := by
    ext d
    simp [Nat.mem_divisors,hq.ne',hgc.ne',hdiv,Nat.dvd_gcd_iff,and_assoc]
  rw [hset]
  exact_mod_cast (Nat.sum_totient (q.gcd j.natAbs)).symm

theorem ramanujan_norm_le_totient_filter (q : ℕ) (hq : 0 < q) (j : ℤ) :
    ‖ramanujan q j‖ ≤
      ∑ d ∈ q.divisors.filter (fun d => (d : ℤ) ∣ j), (Nat.totient d : ℝ) := by
  rw [← gcd_eq_totient_filtered q hq j]
  exact norm_ramanujan_le_gcd q j

end
end ImbalancedChen.Part3.TwoLongFilteredIntegerFrequency
