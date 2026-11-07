import ImbalancedChen.P4BPositiveUpperLowRankClass
import ImbalancedChen.P2OriginalU5ExactNormalizedSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Attach the actual POSITIVE-UPPER modulus rank class to I's independent
whole-Gamma source at the original U5 root. There is no identification of
the outer Gamma primes with modulus slots, and no use of the ALL16 lower
coefficient. Every mother-list occurrence, repeated outer representation
and unit quotient remains in the same-modulus coprime discrepancy.

The new analytic input removed in the companion file is the low-rank
COMPLETE support/norm claim. This consumer does not assert PP or evaluate J.
-/
namespace ImbalancedChen.P2OriginalGammaUpperLowRankConsumer
noncomputable section
open scoped Classical BigOperators
open P4BPositiveUpperLowRankClass P2OriginalU5ExactNormalizedSource

private theorem list_sum_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map (fun x => f x-g x)).sum = (l.map f).sum-(l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons,List.sum_cons,ih]
      ring

theorem sourceTest_sub (N : ℕ) (t : ℕ × ℕ) (F G : ℕ → ℝ) :
    sourceTest N t (fun m => F m-G m) = sourceTest N t F-sourceTest N t G := by
  simp only [sourceTest,Finset.sum_sub_distrib,list_sum_sub]

theorem sourceTest_div (N : ℕ) (t : ℕ × ℕ) (F : ℕ → ℝ) (c : ℝ) :
    sourceTest N t (fun m => F m/c) = sourceTest N t F/c := by
  simp only [sourceTest,div_eq_mul_inv,← Finset.sum_mul,List.sum_map_mul_right]

/-- The exact coprime kernel for the COMPLETE outer integer. -/
def gammaKernel (N q m : ℕ) : ℝ :=
  (if Nat.ModEq q m N then 1 else 0)-
    (if Nat.Coprime m q then 1 else 0)/(Nat.totient q : ℝ)

def gammaDiscrepancy (N : ℕ) (t : ℕ × ℕ) (q : ℕ) : ℝ :=
  sourceTest N t (gammaKernel N q)

/-- Same q in congruence and mean; no unrestricted-mass substitution. -/
theorem gammaDiscrepancy_eq_count_sub_exact_coprime (N : ℕ) (t : ℕ × ℕ) (q : ℕ) :
    gammaDiscrepancy N t q =
      sourceTest N t (fun m => if Nat.ModEq q m N then 1 else 0)-
      sourceTest N t (fun m => if Nat.Coprime m q then 1 else 0)/(Nat.totient q : ℝ) := by
  unfold gammaDiscrepancy gammaKernel
  rw [sourceTest_sub,sourceTest_div]

/-- The q=1 discrepancy vanishes; this is unrelated to an outer unit
quotient, whose source contribution remains in the next identity. -/
theorem gammaDiscrepancy_one (N : ℕ) (t : ℕ × ℕ) :
    gammaDiscrepancy N t 1 = 0 := by
  simp [gammaDiscrepancy,gammaKernel,Nat.ModEq,sourceTest]

theorem gammaDiscrepancy_unit_nonunit (N : ℕ) (t : ℕ × ℕ) (q : ℕ) :
    gammaDiscrepancy N t q =
      unitTest N t (gammaKernel N q)+nonunitTest N t (gammaKernel N q) := by
  exact sourceTest_unit_nonunit N t (gammaKernel N q)

def fullError (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) : ℝ :=
  ∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
    attachedUpperCoefficient nu r epsilon retain cap N q*gammaDiscrepancy N t q

def lowError (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) : ℝ :=
  ∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
    rankRho (retain N) N (cap N) ((N : ℝ)^(nu*epsilon^2))
      ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 q*gammaDiscrepancy N t q

def highError (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) : ℝ :=
  ∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
    remainingRho (retain N) N (cap N) ((N : ℝ)^(nu*epsilon^2))
      ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 q*gammaDiscrepancy N t q

/-- The actual upper coefficient, before any discrepancy is inspected,
splits this entire Gamma source into low and still-unpaid high ranks. -/
theorem original_Gamma_upper_error_split (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    fullError N t nu r epsilon retain cap =
      lowError N t nu r epsilon retain cap+highError N t nu r epsilon retain cap := by
  exact signed_test_rank_split (retain N) N (cap N) ((N : ℝ)^(nu*epsilon^2))
    ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 (gammaDiscrepancy N t)

/-- A genuine finite upper-class estimate on the WHOLE Gamma discrepancy.
The coefficient costs scalar norm one, and the ceiling is the full small
times rough modulus. No factor 22, rank199 or logarithm is introduced here.
The exact remaining analytic target is the displayed absolute sum. -/
theorem original_Gamma_upper_low_error_bound
    {N : ℕ} (hN : 1 ≤ N) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (hnur : 0 ≤ nu*r) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    |lowError N t nu r epsilon retain cap| ≤
      ∑ q ∈ (Finset.range (Nat.ceil ((N : ℝ)^(nu*(2*r+epsilon))))).filter
        (fun q => 0 < q ∧ q.Coprime N), |gammaDiscrepancy N t q| := by
  have h := rankRho_absolute_test_bound (retain N) N (cap N)
    ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2
    (Real.one_le_rpow (by exact_mod_cast hN) hnur) (gammaDiscrepancy N t)
  have hpower : (N : ℝ)^(nu*epsilon)*((N : ℝ)^(nu*r))^2 =
      (N : ℝ)^(nu*(2*r+epsilon)) := by
    simpa only [Nat.cast_ofNat] using attachment_rank_power (by omega : 0 < N) nu r epsilon 2
  simpa only [lowError,attachedUpperModuli,hpower] using h

/-- Neither low-rank reduction nor exact coprime centering deletes the
unit quotient surfaces. This signed equality holds for every original mark. -/
theorem original_Gamma_upper_low_error_unit_nonunit
    (N : ℕ) (t : ℕ × ℕ) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    lowError N t nu r epsilon retain cap =
    (∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
      rankRho (retain N) N (cap N) ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 q*unitTest N t (gammaKernel N q))+
    (∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
      rankRho (retain N) N (cap N) ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*r)) ((N : ℝ)^(nu*epsilon)) 2 q*nonunitTest N t (gammaKernel N q)) := by
  unfold lowError
  simp_rw [gammaDiscrepancy_unit_nonunit,mul_add]
  rw [Finset.sum_add_distrib]

end
end ImbalancedChen.P2OriginalGammaUpperLowRankConsumer
