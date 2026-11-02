import ImbalancedChen.P5OriginalSharpPrimeSynthesis
import ImbalancedChen.ChenQuotientCentreBudget
import ImbalancedChen.CurrentChenInitialSource
import ImbalancedChen.P2LowerFiniteCellRawDensityReserve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The centre-prime deletion in the ORIGINAL ordinary lower start is a
one-sided count problem. Sum the SAME lower polynomial at each excluded
receiver first. Its value is at most one, even though it can be negative.
This pays the entire centre deletion by the number of prime divisors of N,
uniformly in all policies, meshes, beta levels and physical supports.

Both the literal even-exit rho and the actual finite-cell rounded compiler
are instantiated below. The final source is exactly 3*U1+U2 at a=417/5000
and h=19/125, with a common cap, presieve, beta level and mesh. The sharp
signed total-pi error is retained, with its sign, for each same coefficient.
Neither hstarts, its numerical endpoint, nor an enhanced h bank is a premise.
The ordinary raw-density and distribution obligations remain open.
-/

namespace ImbalancedChen.P5OriginalStartsOneSidedCentre

noncomputable section
open Filter
open scoped Classical BigOperators

/-- Exact Fubini on the excluded prime labels. This identity is valid at
zero receivers and modulus one; it uses no support-size bound. -/
theorem centre_sum_eq_divisor_polynomials (N : ℕ) (S : Finset ℕ)
    (rho : ℕ → ℝ) :
    (∑ q ∈ S, rho q * chenCentrePrimeAPCount N N q) =
      ∑ P ∈ chenCentrePrimeCarrier N, physicalDivisorSum S rho (N-P) := by
  have hcount (q : ℕ) : chenCentrePrimeAPCount N N q =
      ∑ P ∈ chenCentrePrimeCarrier N, if q ∣ N-P then (1:ℝ) else 0 := by
    rw [chenCentrePrimeAPCount_eq_filter_dvd, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  simp_rw [hcount, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  simp only [physicalDivisorSum, supportedDivisorSum, Finset.sum_filter]
  exact Finset.sum_comm

/-- The original deletion only needs an upper bound on its signed sum.
The divisor polynomial is not required to be nonnegative. -/
theorem centre_sum_le_prime_divisors (N : ℕ) (S : Finset ℕ)
    (rho : ℕ → ℝ)
    (hminor : ∀ n : ℕ, physicalDivisorSum S rho n ≤ 1) :
    (∑ q ∈ S, rho q * chenCentrePrimeAPCount N N q) ≤
      chenPrimeDivisorCount N N := by
  rw [centre_sum_eq_divisor_polynomials]
  calc
    _ ≤ ∑ _P ∈ chenCentrePrimeCarrier N, (1:ℝ) :=
      Finset.sum_le_sum (fun P _ => hminor (N-P))
    _ = chenPrimeDivisorCount N N := by
      simp only [chenCentrePrimeCarrier, chenPrimeDivisorCount,
        Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The actual indicator used by the lower compiler has values zero/one. -/
theorem actual_indicator_le_one (N : ℕ) (z : ℝ) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤ 1 := by
  unfold actualSmallRoughIndicator
  split_ifs <;> norm_num

/-- Convert the same actual lower polynomial to the literal Chen receiver
source. This intermediate lemma is immediately instantiated by proved
raw and rounded compiler minorants, not by assumed count estimates. -/
theorem lower_polynomial_le_actual_sifted (N cap : ℕ) (z : ℝ)
    (S : Finset ℕ) (rho : ℕ → ℝ) (hzcap : z ≤ (cap:ℝ))
    (hminor : ∀ n : ℤ, physicalDivisorSum S rho n.natAbs ≤
      actualSmallRoughIndicator N z n) :
    (∑ q ∈ S, rho q * (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) ≤
      ((chenSiftedPrimeSource N z).card:ℝ) := by
  rw [← P5S1OriginalLower.sum_physicalDivisorSum]
  calc
    _ ≤ ∑ n ∈ chenPrimeReceiverSource N,
        if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      have h := hminor (n:ℤ)
      have hind : actualSmallRoughIndicator N z (n:ℤ) =
          if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1:ℝ) else 0 := by
        unfold actualSmallRoughIndicator
        rw [← actualSmallPrimeProduct_coprime_natAbs_iff N cap z hzcap (n:ℤ)]
        simp only [Int.natAbs_natCast,
          currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap,
          Nat.coprime_comm]
      simpa only [Int.natAbs_natCast, hind] using h
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Total pi(N), literal density, and exact signed sharp error. The
centre deletion costs one per excluded PRIME, not one per modulus-prime
incidence. No Q or support envelope is required for this finite result. -/
theorem total_pi_mean_lower (N cap : ℕ) (z : ℝ) (S : Finset ℕ)
    (rho : ℕ → ℝ) (hzcap : z ≤ (cap:ℝ))
    (hminor : ∀ n : ℤ, physicalDivisorSum S rho n.natAbs ≤
      actualSmallRoughIndicator N z n) :
    ((chenPrimePrefix N).card:ℝ) * physicalDensitySum S rho +
        P5OriginalSharpPrime.totalPiError N S rho - chenPrimeDivisorCount N N ≤
      ((chenSiftedPrimeSource N z).card:ℝ) := by
  have hfinite := lower_polynomial_le_actual_sifted N cap z S rho hzcap hminor
  have hcentre := centre_sum_le_prime_divisors N S rho (fun n => by
    have h := (hminor (n:ℤ)).trans (actual_indicator_le_one N z (n:ℤ))
    simpa only [Int.natAbs_natCast] using h)
  have hidentity : ((chenPrimePrefix N).card:ℝ) * physicalDensitySum S rho +
      P5OriginalSharpPrime.totalPiError N S rho -
        (∑ q ∈ S, rho q * chenCentrePrimeAPCount N N q) =
      ∑ q ∈ S, rho q * (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q) := by
    simp only [physicalDensitySum, P5OriginalSharpPrime.totalPiError,
      Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  linarith only [hfinite, hcentre, hidentity]

/-- Concrete even-exit source: its proved physical minorant supplies the
input above, with no analytic or pointwise licence requested from a caller. -/
theorem actual_causal_total_pi_mean_lower (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (hL : 1<L) (hwL : w≤L) (hwz : w≤z)
    (hzcap : z≤(cap:ℝ)) :
    ((chenPrimePrefix N).card:ℝ) *
        physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) +
      P5OriginalSharpPrime.totalPiError N
        (actualLowerSmallRoughModuli retainEven N cap w z)
        (actualLowerSmallRoughRho retainEven N cap w z L) - chenPrimeDivisorCount N N ≤
      ((chenSiftedPrimeSource N z).card:ℝ) :=
  total_pi_mean_lower N cap z _ _ hzcap
    (actualLowerSmallRoughRho_minorant retainEven N cap w z L hL hwL hwz hzcap)

/-- The ACTUAL rounded output, not an invented replacement policy, has
the same prime-count entrance and one-sided centre payment. -/
theorem actual_compiled_total_pi_mean_lower (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z tau L : ℝ) (hL : 1<L) (hwL : w≤L) (hwz : w≤z)
    (hzcap : z≤(cap:ℝ)) :
    ((chenPrimePrefix N).card:ℝ) *
        physicalDensitySum (P2LowerFiniteCellBetaCompiler.support N cap w z)
          (P2LowerFiniteCellBetaCompiler.rho retainEven N cap w z tau L) +
      P5OriginalSharpPrime.totalPiError N
        (P2LowerFiniteCellBetaCompiler.support N cap w z)
        (P2LowerFiniteCellBetaCompiler.rho retainEven N cap w z tau L) -
      chenPrimeDivisorCount N N ≤ ((chenSiftedPrimeSource N z).card:ℝ) :=
  total_pi_mean_lower N cap z _ _ hzcap
    (P2LowerFiniteCellBetaCompiler.rho_minorant retainEven N cap w z tau L hL hwL hwz hzcap)

def compiledDensity (N cap : ℕ) (w z tau L : ℝ) (retainEven : List ℕ → Bool) : ℝ :=
  physicalDensitySum (P2LowerFiniteCellBetaCompiler.support N cap w z)
    (P2LowerFiniteCellBetaCompiler.rho retainEven N cap w z tau L)

def compiledSharpError (N cap : ℕ) (w z tau L : ℝ) (retainEven : List ℕ → Bool) : ℝ :=
  P5OriginalSharpPrime.totalPiError N (P2LowerFiniteCellBetaCompiler.support N cap w z)
    (P2LowerFiniteCellBetaCompiler.rho retainEven N cap w z tau L)

/-- The real original grouped source with common physical beta pair and
common mesh. It is not the eight-slot eventual consumer. -/
theorem actual_grouped_starts_total_pi_lower
    (N cap : ℕ) (w tau L : ℝ) (ra rh : List ℕ → Bool)
    (hEven : Even N) (hL : 1<L) (hwL : w≤L)
    (hwa : w≤(N:ℝ)^(417/5000:ℝ)) (hwh : w≤(N:ℝ)^(19/125:ℝ))
    (haCap : (N:ℝ)^(417/5000:ℝ)≤(cap:ℝ))
    (hhCap : (N:ℝ)^(19/125:ℝ)≤(cap:ℝ)) :
    ((chenPrimePrefix N).card:ℝ) *
        (3*compiledDensity N cap w ((N:ℝ)^(417/5000:ℝ)) tau L ra +
          compiledDensity N cap w ((N:ℝ)^(19/125:ℝ)) tau L rh) +
      3*compiledSharpError N cap w ((N:ℝ)^(417/5000:ℝ)) tau L ra +
        compiledSharpError N cap w ((N:ℝ)^(19/125:ℝ)) tau L rh -
      4*chenPrimeDivisorCount N N ≤ 3*currentChenUpsilon1 N + currentChenUpsilon2 N := by
  have ha := actual_compiled_total_pi_mean_lower ra N cap w
    ((N:ℝ)^(417/5000:ℝ)) tau L hL hwL hwa haCap
  have hh := actual_compiled_total_pi_mean_lower rh N cap w
    ((N:ℝ)^(19/125:ℝ)) tau L hL hwL hwh hhCap
  rw [currentChenUpsilon1_eq_actual_sifted_card N hEven,
    currentChenUpsilon2_eq_actual_sifted_card N hEven]
  change ((chenPrimePrefix N).card:ℝ)*compiledDensity N cap w
    ((N:ℝ)^(417/5000:ℝ)) tau L ra +
    compiledSharpError N cap w ((N:ℝ)^(417/5000:ℝ)) tau L ra -
    chenPrimeDivisorCount N N ≤ _ at ha
  change ((chenPrimePrefix N).card:ℝ)*compiledDensity N cap w
    ((N:ℝ)^(19/125:ℝ)) tau L rh +
    compiledSharpError N cap w ((N:ℝ)^(19/125:ℝ)) tau L rh -
    chenPrimeDivisorCount N N ≤ _ at hh
  nlinarith only [ha,hh]

/-- One threshold precedes BOTH policies and all compiler data. The full
3+1 centre loss is paid in H_N without an active-support power premise. -/
theorem eventually_actual_grouped_starts_total_pi_lower_paid
    (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (cap : ℕ) (w tau L : ℝ) (ra rh : List ℕ → Bool),
      Even N → 1<L → w≤L → w≤(N:ℝ)^(417/5000:ℝ) → w≤(N:ℝ)^(19/125:ℝ) →
      (N:ℝ)^(417/5000:ℝ)≤(cap:ℝ) → (N:ℝ)^(19/125:ℝ)≤(cap:ℝ) →
      ((chenPrimePrefix N).card:ℝ) *
          (3*compiledDensity N cap w ((N:ℝ)^(417/5000:ℝ)) tau L ra +
            compiledDensity N cap w ((N:ℝ)^(19/125:ℝ)) tau L rh) +
        3*compiledSharpError N cap w ((N:ℝ)^(417/5000:ℝ)) tau L ra +
          compiledSharpError N cap w ((N:ℝ)^(19/125:ℝ)) tau L rh -
        eta*singularNormalization N ≤ 3*currentChenUpsilon1 N + currentChenUpsilon2 N := by
  filter_upwards [eventually_currentChen_primeFactors_negligible (eta/4) (by positivity),
    eventually_ge_atTop (1:ℕ)] with N hpaid hN
  intro cap w tau L ra rh hEven hL hwL hwa hwh haCap hhCap
  have hcentre := (chenPrimeDivisorCount_le_primeFactors_card N
    (show 0<N by omega)).trans hpaid
  have hfinite := actual_grouped_starts_total_pi_lower N cap w tau L ra rh
    hEven hL hwL hwa hwh haCap hhCap
  nlinarith only [hcentre,hfinite]

end
end ImbalancedChen.P5OriginalStartsOneSidedCentre
