import ImbalancedChen.TruncatedSieveLevel
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Transfer from unweighted source discrepancies to the actual sieve error

For the literal half-product source, the residue count is at most
`N / d + 1` (with natural division), and the total cardinality is at most
`N`. Consequently its actual sieve remainder satisfies
`|R(d)| ≤ 3 * N / φ(d)` for `1 ≤ d ≤ N`. This bound is proved here,
not supplied as a distribution hypothesis.

Mathlib's finite Cauchy inequality then gives

`errSum(lambdaSquared w)^2 ≤ W^4 * (3 * N * Σ τ(d)^4 / φ(d)) * Σ |Δ(d)|`.

The first version keeps exactly the allowed divisors `d ≤ L * L`; the
second enlarges only the discrepancy sum to the moduli in `Icc 1 (L * L)`
that are coprime to `N`. The divisor moment keeps its squarefree support.
Here `Δ` is the actual coprime-normalized source discrepancy, after the
proved roughness gate. The coefficient is still mathlib's lambda-square
coefficient, and its support comes from `w n = 0` for `L < n`, so the
two input factors are at most `L` and their lcm is at most `L * L`.

All divisor losses are explicit. No estimate of the unweighted discrepancy
sum or of the fourth divisor moment is assumed or proved. This finite
transfer is not an optimized linear sieve or an asymptotic conclusion.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Positivity of every actual half-product removes zero from the inclusive
ambient interval, so there are at most `N` source elements. -/
theorem halfProductSource_card_le (num den N : ℕ) (T : ℝ) :
    (halfProductSource num den N T).card ≤ N := by
  classical
  calc
    (halfProductSource num den N T).card ≤ (Finset.range N).card := by
      apply Finset.card_le_card_of_injOn (fun m : ℕ => m - 1)
      · intro m hm
        have hm0 := halfProductSource_pos hm
        have hmN := (mem_halfProductSource.mp hm).1
        exact Finset.mem_range.mpr (by omega)
      · intro m hm n hn hmn
        have hm0 := halfProductSource_pos hm
        have hn0 := halfProductSource_pos hn
        change m - 1 = n - 1 at hmn
        omega
    _ = N := Finset.card_range N

/-- The quotient map is injective on one residue class. This proves a
literal progression bound, retaining the possible endpoint `m = N`. -/
theorem halfProductCongruenceMass_le_quotient_add_one
    (num den N d : ℕ) (T : ℝ) :
    halfProductCongruenceMass num den N T d ≤ (N / d : ℕ) + (1 : ℝ) := by
  classical
  have hcard : ((halfProductSource num den N T).filter
      (fun m : ℕ => Nat.ModEq d m N)).card ≤ N / d + 1 := by
    calc
      _ ≤ (Finset.range (N / d + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun m : ℕ => m / d)
        · intro m hm
          have hmN := (mem_halfProductSource.mp (Finset.mem_filter.mp hm).1).1
          exact Finset.mem_range.mpr
            (Nat.lt_succ_iff.mpr (Nat.div_le_div_right hmN))
        · intro m hm n hn hmn
          have hmR : m % d = N % d := (Finset.mem_filter.mp hm).2
          have hnR : n % d = N % d := (Finset.mem_filter.mp hn).2
          change m / d = n / d at hmn
          calc
            m = m % d + d * (m / d) := (Nat.mod_add_div m d).symm
            _ = n % d + d * (n / d) := by rw [hmR, hnR, hmn]
            _ = n := Nat.mod_add_div n d
      _ = N / d + 1 := Finset.card_range _
  unfold halfProductCongruenceMass
  exact_mod_cast hcard

/-- An unconditional pointwise cap for the actual cardinality-normalized
remainder. The progression count and the main term are both estimated
from the source itself; no remainder bound appears among the premises. -/
theorem abs_halfProductRemainder_le_three_mul_div_totient
    (num den N : ℕ) (T : ℝ) {d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    |halfProductCongruenceMass num den N T d -
      ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)| ≤
        3 * (N : ℝ) / (Nat.totient d : ℝ) := by
  have hA0 : 0 ≤ halfProductCongruenceMass num den N T d := Nat.cast_nonneg _
  have hphi : (0 : ℝ) < (Nat.totient d : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  have hphiD : (Nat.totient d : ℝ) ≤ (d : ℝ) :=
    Nat.cast_le.mpr (Nat.totient_le d)
  have hdN' : (d : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hdN
  have hquot : ((N / d : ℕ) : ℝ) * (d : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N d
  have hAd : halfProductCongruenceMass num den N T d * (d : ℝ) ≤
      (N : ℝ) + (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_right
      (halfProductCongruenceMass_le_quotient_add_one num den N d T)
      (Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))
    nlinarith
  have hAphi : halfProductCongruenceMass num den N T d *
      (Nat.totient d : ℝ) ≤ 2 * (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hphiD hA0
    linarith
  have hA : halfProductCongruenceMass num den N T d ≤
      2 * (N : ℝ) / (Nat.totient d : ℝ) :=
    (le_div_iff₀ hphi).mpr hAphi
  have hB0 : 0 ≤ ((halfProductSource num den N T).card : ℝ) /
      (Nat.totient d : ℝ) := div_nonneg (Nat.cast_nonneg _) hphi.le
  have hB : ((halfProductSource num den N T).card : ℝ) /
      (Nat.totient d : ℝ) ≤ (N : ℝ) / (Nat.totient d : ℝ) :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (halfProductSource_card_le num den N T))
      hphi.le
  calc
    _ ≤ halfProductCongruenceMass num den N T d +
        ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith
    _ ≤ 2 * (N : ℝ) / (Nat.totient d : ℝ) +
        (N : ℝ) / (Nat.totient d : ℝ) := add_le_add hA hB
    _ = _ := by ring

/-- Cauchy with the genuine lambda-square coefficient and the full fourth
divisor moment. The remainder is arbitrary, and no weighted estimate is
assumed. This reuses mathlib's finite Cauchy inequality without square roots. -/
theorem sum_abs_lambdaSquared_mul_sq_le_divisor_moment
    (S : Finset ℕ) (w r : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ d ∈ S, ∀ n ∈ d.divisors, |w n| ≤ W) :
    (∑ d ∈ S, |BoundingSieve.lambdaSquared w d| * |r d|) ^ 2 ≤
      W ^ 4 * (∑ d ∈ S, (d.divisors.card : ℝ) ^ 4 * |r d|) *
        (∑ d ∈ S, |r d|) := by
  have hcoeff (d : ℕ) (hd : d ∈ S) :
      |BoundingSieve.lambdaSquared w d| ^ 2 ≤ (d.divisors.card : ℝ) ^ 4 * W ^ 4 := by
    calc
      _ ≤ ((d.divisors.card : ℝ) ^ 2 * W ^ 2) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _)
          (abs_lambdaSquared_le_divisor_card_sq w d W hW (hw d hd)) 2
      _ = _ := by ring
  have hcs : (∑ d ∈ S, |BoundingSieve.lambdaSquared w d| * |r d|) ^ 2 ≤
      (∑ d ∈ S, ((d.divisors.card : ℝ) ^ 4 * W ^ 4) * |r d|) *
        (∑ d ∈ S, |r d|) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro d _hd
      exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 4)
        (pow_nonneg hW 4)) (abs_nonneg _)
    · intro d _hd
      exact abs_nonneg _
    · intro d hd
      calc
        (|BoundingSieve.lambdaSquared w d| * |r d|) ^ 2 =
            |BoundingSieve.lambdaSquared w d| ^ 2 * |r d| ^ 2 := by ring
        _ ≤ ((d.divisors.card : ℝ) ^ 4 * W ^ 4) * |r d| ^ 2 :=
          mul_le_mul_of_nonneg_right (hcoeff d hd) (sq_nonneg _)
        _ = _ := by ring
  have hsum : (∑ d ∈ S, ((d.divisors.card : ℝ) ^ 4 * W ^ 4) * |r d|) =
      W ^ 4 * (∑ d ∈ S, (d.divisors.card : ℝ) ^ 4 * |r d|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  rw [hsum] at hcs
  exact hcs

/-- The actual pointwise progression cap removes the remainder from the
fourth-moment factor. Only the literal unweighted discrepancy sum remains. -/
theorem sum_abs_lambdaSquared_mul_halfProductRemainder_sq_le
    (num den N : ℕ) (T : ℝ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
    (w : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ d ∈ S, ∀ n ∈ d.divisors, |w n| ≤ W) :
    (∑ d ∈ S, |BoundingSieve.lambdaSquared w d| *
      |halfProductCongruenceMass num den N T d -
        ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)|) ^ 2 ≤
      W ^ 4 * (3 * (N : ℝ) *
        (∑ d ∈ S, (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ))) *
        (∑ d ∈ S, |halfProductCongruenceMass num den N T d -
          ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)|) := by
  let r : ℕ → ℝ := fun d => halfProductCongruenceMass num den N T d -
    ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)
  have hmoment : (∑ d ∈ S, (d.divisors.card : ℝ) ^ 4 * |r d|) ≤
      3 * (N : ℝ) * (∑ d ∈ S, (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hdN := Finset.mem_Icc.mp (hS hd)
    calc
      (d.divisors.card : ℝ) ^ 4 * |r d| ≤ (d.divisors.card : ℝ) ^ 4 *
          (3 * (N : ℝ) / (Nat.totient d : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (abs_halfProductRemainder_le_three_mul_div_totient num den N T hdN.1 hdN.2)
          (pow_nonneg (Nat.cast_nonneg _) 4)
      _ = _ := by ring
  exact (sum_abs_lambdaSquared_mul_sq_le_divisor_moment S w r W hW hw).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmoment (pow_nonneg hW 4))
      (Finset.sum_nonneg fun d _hd => abs_nonneg (r d)))

/-- Exact level support, the actual sieve remainder, and the actual
coprime-normalized source discrepancy are joined without an analytic
hypothesis. Both sums retain precisely the allowed moduli at most `L²`. -/
theorem halfProductBoundingSieve_errSum_lambdaSquared_sq_le_unweighted
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (w : ℕ → ℝ) (L : ℕ) (hlevel : L * L ≤ N)
    (hcut : ∀ n : ℕ, L < n → w n = 0)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ n : ℕ, n ≤ L → |w n| ≤ W) :
    ((halfProductBoundingSieve num den N T z hN).errSum
      (BoundingSieve.lambdaSquared w)) ^ 2 ≤
      W ^ 4 * (3 * (N : ℝ) *
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
          (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ))) *
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
          |halfProductCongruenceMass num den N T d -
            halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) := by
  classical
  let S := (sieveProduct N z).divisors.filter (fun d => d ≤ L * L)
  have hS : S ⊆ Finset.Icc 1 N := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdiv, hdL⟩
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdiv, hdL.trans hlevel⟩
  have hwAll : ∀ n : ℕ, |w n| ≤ W := by
    intro n
    by_cases hn : n ≤ L
    · exact hw n hn
    · rw [hcut n (Nat.lt_of_not_ge hn), abs_zero]
      exact hW
  have hbound := sum_abs_lambdaSquared_mul_halfProductRemainder_sq_le
    num den N T S hS w W hW (fun _d _hd n _hn => hwAll n)
  have hsum : (∑ d ∈ S, |halfProductCongruenceMass num den N T d -
      ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)|) =
      ∑ d ∈ S, |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [halfProductCoprimeMass_eq_card_of_gate hnum hden hT hcap
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)]
  rw [hsum] at hbound
  have herr : (halfProductBoundingSieve num den N T z hN).errSum
      (BoundingSieve.lambdaSquared w) =
      ∑ d ∈ S, |BoundingSieve.lambdaSquared w d| *
        |halfProductCongruenceMass num den N T d -
          ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)| := by
    rw [boundingSieve_errSum_lambdaSquared_truncated _ w L hcut]
    apply Finset.sum_congr rfl
    intro d _hd
    rw [halfProductBoundingSieve_rem]
  rw [herr]
  exact hbound

/-- A direct consumer for a primitive-residue distribution theorem. The
discrepancy sum may be enlarged to all positive moduli at most `L²` that
are coprime to `N`, without a cardinality factor. The fourth moment keeps
the original squarefree allowed-divisor support. No estimate at a
nonprimitive residue is smuggled into the distribution input. -/
theorem halfProductBoundingSieve_errSum_lambdaSquared_sq_le_unweighted_coprime_Icc
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (w : ℕ → ℝ) (L : ℕ) (hlevel : L * L ≤ N)
    (hcut : ∀ n : ℕ, L < n → w n = 0)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ n : ℕ, n ≤ L → |w n| ≤ W) :
    ((halfProductBoundingSieve num den N T z hN).errSum
      (BoundingSieve.lambdaSquared w)) ^ 2 ≤
      W ^ 4 * (3 * (N : ℝ) *
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
          (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ))) *
        (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
          |halfProductCongruenceMass num den N T d -
            halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) := by
  classical
  let S := (sieveProduct N z).divisors.filter (fun d => d ≤ L * L)
  have hS : S ⊆ (Finset.Icc 1 (L * L)).filter (fun d => Nat.Coprime d N) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdiv, hdL⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdiv, hdL⟩,
        coprime_of_dvd_sieveProduct (Nat.dvd_of_mem_divisors hdiv)⟩
  have herr : (∑ d ∈ S, |halfProductCongruenceMass num den N T d -
      halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
      ∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun _d _hd _hnot => abs_nonneg _
  refine (halfProductBoundingSieve_errSum_lambdaSquared_sq_le_unweighted
    num den N T z hN hnum hden hT hcap w L hlevel hcut W hW hw).trans ?_
  exact mul_le_mul_of_nonneg_left herr
    (mul_nonneg (pow_nonneg hW 4)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
        (Finset.sum_nonneg fun d _hd =>
          div_nonneg (pow_nonneg (Nat.cast_nonneg _) 4) (Nat.cast_nonneg _))))

end

end ImbalancedChen
