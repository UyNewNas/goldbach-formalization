import ImbalancedChen.SingularSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Genuine singular-product identities on natural-number indices

The owned twin-prime constant is indexed by the subtype of odd primes.
Here it is reindexed over all natural numbers, with factor one outside the
odd primes. Its `HasProd` proof is transported, so these identities do not
use the default value of a nonconvergent infinite product.

The raw natural-index formula for `singularSeries` has its finite correction
on the left and has no leading factor two. It is suitable for comparing with
another definition using the same literal Euler factors, without importing
that definition or assuming an equality of infinite products.

For nonzero centres we also combine the finite correction and universal
product into the actual centre-dependent local factors. Adding the factor
at the prime two gives exactly twice `singularSeries` for even centres.
The nonzero condition is needed only for the local divisibility formula:
`Nat.primeFactors 0` is empty although every prime divides zero.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The odd-prime universal factor, extended by one to all naturals. The
`1 + deviation` form fixes the exact convention for natural-index products. -/
def oddPrimeBaseNat (p : ℕ) : ℝ :=
  1 + if p.Prime ∧ 2 < p then -1 / ((p : ℝ) - 1) ^ 2 else 0

@[simp] theorem oddPrimeBaseNat_coe (p : OddPrime) :
    oddPrimeBaseNat p.val = oddPrimeFactor p := by
  simp [oddPrimeBaseNat, oddPrimeFactor, p.property, neg_div, sub_eq_add_neg]

/-- Genuine convergence, transported along the injective subtype inclusion. -/
theorem hasProd_oddPrimeBaseNat :
    HasProd oddPrimeBaseNat twinPrimeConstant := by
  have hoff : ∀ p, p ∉ Set.range (fun q : OddPrime => q.val) →
      oddPrimeBaseNat p = 1 := by
    intro p hp
    have hnot : ¬ (p.Prime ∧ 2 < p) := by
      intro h
      exact hp ⟨⟨p, h⟩, rfl⟩
    simp [oddPrimeBaseNat, hnot]
  apply (Subtype.val_injective.hasProd_iff hoff).mp
  exact hasProd_oddPrimeFactor.congr_fun fun p => by
    simpa only [Function.comp_apply] using oddPrimeBaseNat_coe p

theorem multipliable_oddPrimeBaseNat : Multipliable oddPrimeBaseNat :=
  hasProd_oddPrimeBaseNat.multipliable

/-- Equality of the genuinely convergent natural-index universal product
and the already proved positive owned constant. -/
theorem tprod_oddPrimeBaseNat :
    (∏' p : ℕ, oddPrimeBaseNat p) = twinPrimeConstant :=
  hasProd_oddPrimeBaseNat.tprod_eq

/-- The exact raw universal-product formula, without a leading factor two. -/
theorem twinPrimeConstant_eq_natProduct :
    twinPrimeConstant =
      ∏' p : ℕ, (1 + if p.Prime ∧ 2 < p then
        -1 / ((p : ℝ) - 1) ^ 2 else 0) :=
  tprod_oddPrimeBaseNat.symm

/-- The literal natural-index singular-series formula. This includes zero,
using the same empty-prime-factor convention as the owned definition. -/
theorem singularSeries_eq_natProduct (N : ℕ) :
    singularSeries N =
      (∏ p ∈ N.primeFactors.filter (fun p => 2 < p),
        ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
      ∏' p : ℕ, (1 + if p.Prime ∧ 2 < p then
        -1 / ((p : ℝ) - 1) ^ 2 else 0) := by
  rw [← twinPrimeConstant_eq_natProduct]
  exact mul_comm _ _

/-- The finite correction extended by one to every natural-number index. -/
def oddPrimeCorrectionNat (N p : ℕ) : ℝ :=
  if p ∈ oddPrimeDivisors N then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

/-- The correction has an actual finite-support product, also at zero. -/
theorem hasProd_oddPrimeCorrectionNat (N : ℕ) :
    HasProd (oddPrimeCorrectionNat N)
      (∏ p ∈ oddPrimeDivisors N, ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  have h : HasProd (oddPrimeCorrectionNat N)
      (∏ p ∈ oddPrimeDivisors N, oddPrimeCorrectionNat N p) :=
    hasProd_prod_of_ne_finset_one
      (fun p hp => by simp [oddPrimeCorrectionNat, hp])
  have heq : (∏ p ∈ oddPrimeDivisors N, oddPrimeCorrectionNat N p) =
      ∏ p ∈ oddPrimeDivisors N, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    apply Finset.prod_congr rfl
    intro p hp
    simp only [oddPrimeCorrectionNat, if_pos hp]
  rwa [heq] at h

/-- Multiplying the true universal `HasProd` by the finite correction gives
the owned singular series, without any assumed normalizer identity. -/
theorem hasProd_correctedOddPrimeBaseNat (N : ℕ) :
    HasProd (fun p => oddPrimeBaseNat p * oddPrimeCorrectionNat N p)
      (singularSeries N) :=
  hasProd_oddPrimeBaseNat.mul (hasProd_oddPrimeCorrectionNat N)

/-- Literal odd-prime local factor for a centre `N`; other indices are one. -/
def oddCenterFactorNat (N p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p then
    if p ∣ N then (p : ℝ) / ((p : ℝ) - 1)
    else (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2
  else 1

/-- The local algebra matches the universal factor times the finite divisor
correction. Real, rather than truncated natural, subtraction is used. -/
theorem oddCenterFactorNat_eq_corrected {N : ℕ} (hN : N ≠ 0) (p : ℕ) :
    oddCenterFactorNat N p =
      oddPrimeBaseNat p * oddPrimeCorrectionNat N p := by
  by_cases hp : p.Prime ∧ 2 < p
  · have hpReal : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
    by_cases hd : p ∣ N
    · have hmem : p ∈ oddPrimeDivisors N :=
        (mem_oddPrimeDivisors hN).mpr ⟨hp.1, hp.2, hd⟩
      simp only [oddCenterFactorNat, oddPrimeBaseNat, oddPrimeCorrectionNat,
        if_pos hp, if_pos hd, if_pos hmem]
      field_simp [hp1, hp2]
      <;> ring
    · have hmem : p ∉ oddPrimeDivisors N := by
        intro h
        exact hd ((mem_oddPrimeDivisors hN).mp h).2.2
      simp only [oddCenterFactorNat, oddPrimeBaseNat, oddPrimeCorrectionNat,
        if_pos hp, if_neg hd, if_neg hmem, mul_one]
      field_simp [hp1, hp2]
      <;> ring
  · have hmem : p ∉ oddPrimeDivisors N := by
      intro h
      have h' := (mem_oddPrimeDivisors hN).mp h
      exact hp ⟨h'.1, h'.2.1⟩
    simp [oddCenterFactorNat, oddPrimeBaseNat, oddPrimeCorrectionNat, hp, hmem]

/-- The actual odd-prime local-factor product converges to `C(N)` for every
nonzero centre. No evenness or analytic estimate is required. -/
theorem hasProd_oddCenterFactorNat {N : ℕ} (hN : N ≠ 0) :
    HasProd (oddCenterFactorNat N) (singularSeries N) :=
  (hasProd_correctedOddPrimeBaseNat N).congr_fun
    (oddCenterFactorNat_eq_corrected hN)

theorem multipliable_oddCenterFactorNat {N : ℕ} (hN : N ≠ 0) :
    Multipliable (oddCenterFactorNat N) :=
  (hasProd_oddCenterFactorNat hN).multipliable

theorem tprod_oddCenterFactorNat {N : ℕ} (hN : N ≠ 0) :
    (∏' p : ℕ, oddCenterFactorNat N p) = singularSeries N :=
  (hasProd_oddCenterFactorNat hN).tprod_eq

/-- Including the prime-two factor uses the sieve-normalized convention.
For odd centres the prime-two factor is one, as in the legacy local formula. -/
def primeCenterFactorNat (N p : ℕ) : ℝ :=
  if p = 2 then (if 2 ∣ N then 2 else 1) else oddCenterFactorNat N p

/-- The factor of two is an actual singleton product, not a normalization
assumption. -/
theorem hasProd_primeCenterFactorNat {N : ℕ} (hN : N ≠ 0) (heven : Even N) :
    HasProd (primeCenterFactorNat N) (2 * singularSeries N) := by
  have htwo : 2 ∣ N := even_iff_two_dvd.mp heven
  have hsingle : HasProd (fun p : ℕ => if p = 2 then (2 : ℝ) else 1) 2 :=
    hasProd_ite_eq 2 2
  apply (hsingle.mul (hasProd_oddCenterFactorNat hN)).congr_fun
  intro p
  by_cases hp : p = 2
  · subst p
    simp [primeCenterFactorNat, oddCenterFactorNat, htwo]
  · simp [primeCenterFactorNat, hp]

/-- The all-prime product is exactly twice the manuscript normalization. -/
theorem tprod_primeCenterFactorNat {N : ℕ} (hN : N ≠ 0) (heven : Even N) :
    (∏' p : ℕ, primeCenterFactorNat N p) = 2 * singularSeries N :=
  (hasProd_primeCenterFactorNat hN heven).tprod_eq

end

end ImbalancedChen
