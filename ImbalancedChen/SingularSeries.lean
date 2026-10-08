import ImbalancedChen.NormalizationGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# The manuscript's singular series and normalization

The manuscript uses the product over primes greater than two, with no leading
factor of two. We prove convergence and strict positivity of that genuine
infinite product. The proof restricts the convergent inverse-square series
along the injective map `p ↦ p - 1`, sums the logarithms of the factors, and
identifies the product with the exponential of that sum.

Every factor in the finite correction for odd prime divisors of `N` is at
least one. Thus the manuscript's singular series is bounded below by a fixed
strictly positive constant. Its normalization consequently tends to infinity
and absorbs the receiver-one correction, without any prime-count estimate.

The prime-divisor formula agrees with the manuscript for `N ≠ 0`. At zero we
use the usual empty `Nat.primeFactors` convention to give a total definition.
-/

namespace ImbalancedChen

open Filter

/-- The primes in the manuscript's infinite product. -/
def OddPrime := {p : ℕ // Nat.Prime p ∧ 2 < p}

/-- The factor contributed by an odd prime. -/
noncomputable def oddPrimeFactor (p : OddPrime) : ℝ :=
  1 - 1 / ((p.val : ℝ) - 1) ^ 2

theorem oddPrimeFactor_pos (p : OddPrime) : 0 < oddPrimeFactor p := by
  have hp : (2 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.property.2
  have hsq : (1 : ℝ) < ((p.val : ℝ) - 1) ^ 2 := by
    nlinarith [sq_nonneg ((p.val : ℝ) - 2)]
  unfold oddPrimeFactor
  exact sub_pos.mpr ((div_lt_one (by linarith :
    (0 : ℝ) < ((p.val : ℝ) - 1) ^ 2)).mpr hsq)

/-- The inverse-square error terms are a subseries of the ordinary convergent
inverse-square series, reindexed injectively by `p - 1`. -/
theorem summable_oddPrime_reciprocal_sq :
    Summable (fun p : OddPrime => 1 / ((p.val : ℝ) - 1) ^ 2) := by
  have hInjective : Function.Injective (fun p : OddPrime => p.val - 1) := by
    intro p q hpq
    apply Subtype.ext
    have hp := p.property.2
    have hq := q.property.2
    omega
  have hSeries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hSubseries : Summable
      (fun p : OddPrime => 1 / ((p.val - 1 : ℕ) : ℝ) ^ 2) :=
    hSeries.comp_injective hInjective
  apply hSubseries.congr
  intro p
  have hp : 1 ≤ p.val := by have := p.property.2; omega
  rw [Nat.cast_sub hp, Nat.cast_one]

theorem summable_log_oddPrimeFactor :
    Summable (fun p : OddPrime => Real.log (oddPrimeFactor p)) := by
  simpa only [oddPrimeFactor, sub_eq_add_neg] using
    Real.summable_log_one_add_of_summable summable_oddPrime_reciprocal_sq.neg

/-- This proves convergence of the actual product; positivity is not obtained
by exploiting the default value assigned to a nonconvergent `tprod`. -/
theorem multipliable_oddPrimeFactor : Multipliable oddPrimeFactor :=
  Real.multipliable_of_summable_log oddPrimeFactor_pos summable_log_oddPrimeFactor

/-- The constant product in the manuscript, with no leading factor of two. -/
noncomputable def twinPrimeConstant : ℝ := ∏' p : OddPrime, oddPrimeFactor p

theorem hasProd_oddPrimeFactor : HasProd oddPrimeFactor twinPrimeConstant :=
  multipliable_oddPrimeFactor.hasProd

theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  unfold twinPrimeConstant
  rw [← Real.rexp_tsum_eq_tprod oddPrimeFactor_pos summable_log_oddPrimeFactor]
  exact Real.exp_pos _

/-- The finite set of odd prime divisors in the correction factor. -/
def oddPrimeDivisors (N : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun p => 2 < p)

theorem mem_oddPrimeDivisors {N p : ℕ} (hN : N ≠ 0) :
    p ∈ oddPrimeDivisors N ↔ Nat.Prime p ∧ 2 < p ∧ p ∣ N := by
  simp [oddPrimeDivisors, Nat.mem_primeFactors, hN, and_assoc, and_comm,
    and_left_comm]

/-- The manuscript's `C(N)`, namely the constant product multiplied by the
finite product `(p - 1) / (p - 2)` over its odd prime divisors. -/
noncomputable def singularSeries (N : ℕ) : ℝ :=
  twinPrimeConstant * ∏ p ∈ oddPrimeDivisors N, ((p : ℝ) - 1) / ((p : ℝ) - 2)

theorem one_le_oddPrimeDivisor_product (N : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ oddPrimeDivisors N, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  apply Finset.one_le_prod
  intro p hp
  have hpNat : 2 < p := (Finset.mem_filter.mp hp).2
  have hpReal : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hpNat
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 2)).mpr
  linarith

/-- A uniform lower bound by a fixed strictly positive constant. -/
theorem twinPrimeConstant_le_singularSeries (N : ℕ) :
    twinPrimeConstant ≤ singularSeries N := by
  unfold singularSeries
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (one_le_oddPrimeDivisor_product N)
      twinPrimeConstant_pos.le

theorem singularSeries_pos (N : ℕ) : 0 < singularSeries N :=
  twinPrimeConstant_pos.trans_le (twinPrimeConstant_le_singularSeries N)

/-- The manuscript's actual `H(N) = C(N) N / (log N)^2`. -/
noncomputable def singularNormalization (N : ℕ) : ℝ :=
  singularSeries N * (N : ℝ) / (Real.log (N : ℝ)) ^ 2

theorem singularNormalization_lower (N : ℕ) :
    twinPrimeConstant * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      singularNormalization N := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (twinPrimeConstant_le_singularSeries N)
      (Nat.cast_nonneg N)) (sq_nonneg _)

theorem tendsto_singularNormalization_atTop :
    Tendsto singularNormalization atTop atTop := by
  exact tendsto_atTop_mono singularNormalization_lower
    (tendsto_pos_mul_nat_div_log_sq_atTop twinPrimeConstant_pos)

/-- The concrete manuscript normalization absorbs the unit correction on all
sufficiently large integers. No counting or sieve premise is used. -/
theorem eventually_singularNormalization_unit_absorption :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in atTop, 1 ≤ epsilon * singularNormalization N :=
  eventually_unit_absorption_of_tendsto tendsto_singularNormalization_atTop

/-- The exact even-integer absorption premise of the omega-count transfer. -/
theorem eventuallyEven_singularNormalization_unit_absorption :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in atTop, Even N → 1 ≤ epsilon * singularNormalization N :=
  eventuallyEven_unit_absorption_of_tendsto tendsto_singularNormalization_atTop

theorem eventually_singularNormalization_pos :
    ∀ᶠ N in atTop, 0 < singularNormalization N :=
  tendsto_singularNormalization_atTop.eventually (eventually_gt_atTop 0)

end ImbalancedChen
