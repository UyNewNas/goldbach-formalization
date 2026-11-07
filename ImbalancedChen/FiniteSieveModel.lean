import ImbalancedChen.SieveSourceCoprimality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# A genuine mathlib sieve on the shifted half-product source

This file instantiates `BoundingSieve` from mathlib with the image of the
actual finite source under `m ↦ N - m`, unit weights, the literal source
cardinality, the actual allowed-prime product, and density `1 / φ(d)`.
The density is an arithmetic function, including its required zero value
at zero and its multiplicative normalization at one.

The inclusive endpoint `m = N` is preserved: its image is zero, which
mathlib's support permits. The complement map is injective because every
source member satisfies `m ≤ N`. No endpoint or prime square is discarded.
Evenness of `N` excludes the prime two and makes the density strictly less
than one at every prime dividing the sieve product.

The finite upper bound below applies mathlib's upper-Moebius theorem to
this model. Its remainder is identified exactly with the actual residue
count minus `card / φ(d)`. Replacing that literal card by the coprime-source
count is justified separately, and only under the proved roughness gate.
No distribution estimate, optimized sieve coefficient, or asymptotic
prime-counting assertion is assumed or proved here.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Distinct primes occur once in the actual finite sieving product. -/
theorem sieveProduct_squarefree (N z : ℕ) : Squarefree (sieveProduct N z) := by
  classical
  have hprod : ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) →
      Squarefree (∏ p ∈ s, p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simpa using (squarefree_one : Squarefree (1 : ℕ))
    | @insert p s hp ih =>
        intro h
        have hprime : Nat.Prime p := h p (Finset.mem_insert_self p s)
        have hs : ∀ q ∈ s, Nat.Prime q :=
          fun q hq => h q (Finset.mem_insert_of_mem hq)
        rw [Finset.prod_insert hp, Nat.squarefree_mul_iff]
        refine ⟨?_, hprime.squarefree, ih hs⟩
        apply Nat.coprime_prod_right_iff.mpr
        intro q hq
        apply (Nat.coprime_primes hprime (hs q hq)).mpr
        intro heq
        apply hp
        simpa only [heq] using hq
  exact hprod (sievePrimes N z) fun p hp => (mem_sievePrimes.mp hp).2.1

/-- A prime divisor of the actual product is an actual allowed sieve prime. -/
theorem prime_mem_sievePrimes_of_dvd {N z p : ℕ}
    (hp : Nat.Prime p) (hd : p ∣ sieveProduct N z) : p ∈ sievePrimes N z := by
  have hmem : p ∈ (sieveProduct N z).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hd, (sieveProduct_squarefree N z).ne_zero⟩
  have hprod : (sieveProduct N z).primeFactors = sievePrimes N z := by
    unfold sieveProduct
    exact Nat.primeFactors_prod fun q hq => (mem_sievePrimes.mp hq).2.1
  rwa [hprod] at hmem

/-- For even `N`, all allowed prime divisors are strictly larger than two. -/
theorem two_lt_prime_of_dvd_sieveProduct {N z p : ℕ}
    (hN : Even N) (hp : Nat.Prime p) (hd : p ∣ sieveProduct N z) : 2 < p := by
  have hnot : ¬p ∣ N :=
    (mem_sievePrimes.mp (prime_mem_sievePrimes_of_dvd hp hd)).2.2
  have hpne : p ≠ 2 := by
    intro heq
    apply hnot
    simpa only [heq] using hN.two_dvd
  have hp2 := hp.two_le
  omega

/-- The literal density, as a multiplicative arithmetic function.
Real inversion at zero gives the required value zero. -/
def halfProductDensity : ArithmeticFunction ℝ where
  toFun d := 1 / (Nat.totient d : ℝ)
  map_zero' := by simp

@[simp] theorem halfProductDensity_apply (d : ℕ) :
    halfProductDensity d = 1 / (Nat.totient d : ℝ) := rfl

@[simp] theorem halfProductDensity_one : halfProductDensity 1 = 1 := by
  simp

/-- This is mathlib's multiplicativity property, not a substitute predicate. -/
theorem halfProductDensity_isMultiplicative : halfProductDensity.IsMultiplicative := by
  refine ⟨halfProductDensity_one, ?_⟩
  intro m n hmn
  simp only [halfProductDensity_apply, Nat.totient_mul hmn, Nat.cast_mul,
    one_div, mul_inv_rev, mul_comm]

theorem halfProductDensity_pos_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 < halfProductDensity p := by
  rw [halfProductDensity_apply]
  exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.totient_pos.mpr hp.pos))

theorem halfProductDensity_lt_one_of_prime {p : ℕ}
    (hp : Nat.Prime p) (hp2 : 2 < p) : halfProductDensity p < 1 := by
  have hphi : (1 : ℝ) < (Nat.totient p : ℝ) := by
    exact_mod_cast (show 1 < Nat.totient p by rw [Nat.totient_prime hp]; omega)
  rw [halfProductDensity_apply]
  exact (div_lt_one (lt_trans zero_lt_one hphi)).mpr hphi

/-- The actual shifted source. In particular, zero is retained when `N`
itself belongs to the inclusive half-product source. -/
def shiftedHalfProductSource (num den N : ℕ) (T : ℝ) : Finset ℕ :=
  (halfProductSource num den N T).image (fun m : ℕ => N - m)

/-- Complementation is injective on the full inclusive source. -/
theorem halfProductSource_shift_injective {num den N : ℕ} {T : ℝ}
    {m n : ℕ} (hm : m ∈ halfProductSource num den N T)
    (hn : n ∈ halfProductSource num den N T) (hmn : N - m = N - n) : m = n := by
  have hmN := (mem_halfProductSource.mp hm).1
  have hnN := (mem_halfProductSource.mp hn).1
  omega

theorem shiftedHalfProductSource_card (num den N : ℕ) (T : ℝ) :
    (shiftedHalfProductSource num den N T).card =
      (halfProductSource num den N T).card := by
  classical
  apply Finset.card_image_of_injOn
  intro m hm n hn hmn
  exact halfProductSource_shift_injective hm hn hmn

/-- Reindex a sum by the genuine injective complement map. -/
theorem sum_shiftedHalfProductSource (num den N : ℕ) (T : ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ shiftedHalfProductSource num den N T, f n) =
      ∑ m ∈ halfProductSource num den N T, f (N - m) := by
  classical
  unfold shiftedHalfProductSource
  apply Finset.sum_image
  intro m hm n hn hmn
  exact halfProductSource_shift_injective hm hn hmn

/-- The endpoint has shifted value zero, without a hidden strict cutoff. -/
@[simp] theorem zero_mem_shiftedHalfProductSource (num den N : ℕ) (T : ℝ) :
    0 ∈ shiftedHalfProductSource num den N T ↔ N ∈ halfProductSource num den N T := by
  classical
  constructor
  · intro h
    obtain ⟨m, hm, hzero⟩ := Finset.mem_image.mp h
    change N - m = 0 at hzero
    have hmN := (mem_halfProductSource.mp hm).1
    have hmEq : m = N := by omega
    simpa only [hmEq] using hm
  · intro h
    exact Finset.mem_image.mpr ⟨N, h, Nat.sub_self N⟩

/-- The actual manuscript source instantiated in mathlib's sieve structure. -/
def halfProductBoundingSieve (num den N : ℕ) (T : ℝ) (z : ℕ)
    (hN : Even N) : BoundingSieve where
  support := shiftedHalfProductSource num den N T
  prodPrimes := sieveProduct N z
  prodPrimes_squarefree := sieveProduct_squarefree N z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := ((halfProductSource num den N T).card : ℝ)
  nu := halfProductDensity
  nu_mult := halfProductDensity_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => halfProductDensity_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd =>
    halfProductDensity_lt_one_of_prime hp (two_lt_prime_of_dvd_sieveProduct hN hp hd)

@[simp] theorem halfProductBoundingSieve_totalMass
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) :
    (halfProductBoundingSieve num den N T z hN).totalMass =
      ((halfProductSource num den N T).card : ℝ) := rfl

/-- The chosen mass is exactly the sum of the unit support weights. -/
theorem halfProductBoundingSieve_totalMass_eq_sum
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) :
    (halfProductBoundingSieve num den N T z hN).totalMass =
      ∑ n ∈ (halfProductBoundingSieve num den N T z hN).support,
        (halfProductBoundingSieve num den N T z hN).weights n := by
  simp [halfProductBoundingSieve, shiftedHalfProductSource_card]

/-- Mathlib's sifted sum is the cardinality of the existing actual sifted set. -/
theorem halfProductBoundingSieve_siftedSum
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) :
    (halfProductBoundingSieve num den N T z hN).siftedSum =
      ((siftedHalfProductSource num den N T z).card : ℝ) := by
  classical
  change (∑ n ∈ shiftedHalfProductSource num den N T,
      if Nat.Coprime (sieveProduct N z) n then (1 : ℝ) else 0) = _
  rw [sum_shiftedHalfProductSource]
  simp_rw [@Nat.coprime_comm (sieveProduct N z)]
  rw [← Finset.sum_filter]
  simp [siftedHalfProductSource]

/-- The literal source count in the residue class of `N`, as a real mass. -/
def halfProductCongruenceMass (num den N : ℕ) (T : ℝ) (d : ℕ) : ℝ :=
  (((halfProductSource num den N T).filter
    (fun m : ℕ => Nat.ModEq d m N)).card : ℝ)

/-- Divisibility of shifted support is exactly the actual residue-class count. -/
theorem halfProductBoundingSieve_multSum
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) (d : ℕ) :
    (halfProductBoundingSieve num den N T z hN).multSum d =
      halfProductCongruenceMass num den N T d := by
  classical
  change (∑ n ∈ shiftedHalfProductSource num den N T,
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [sum_shiftedHalfProductSource, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [halfProductSource_filter_dvd_eq_filter_modEq]
  rfl

/-- The exact mathlib remainder, with no distribution assumption.
This identity actually holds for every modulus, including the allowed divisors. -/
theorem halfProductBoundingSieve_rem
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) (d : ℕ) :
    (halfProductBoundingSieve num den N T z hN).rem d =
      halfProductCongruenceMass num den N T d -
        ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ) := by
  rw [BoundingSieve.rem, halfProductBoundingSieve_multSum,
    halfProductBoundingSieve_totalMass]
  change _ - (1 / (Nat.totient d : ℝ)) * _ = _
  ring

/-- The main sum uses the actual reciprocal-totient density. -/
theorem halfProductBoundingSieve_mainSum
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) (muPlus : ℕ → ℝ) :
    (halfProductBoundingSieve num den N T z hN).mainSum muPlus =
      ∑ d ∈ (sieveProduct N z).divisors, muPlus d / (Nat.totient d : ℝ) := by
  simp only [BoundingSieve.mainSum, halfProductBoundingSieve, halfProductDensity_apply,
    div_eq_mul_inv, one_mul]

/-- The error sum is the weighted absolute discrepancy of actual residue counts. -/
theorem halfProductBoundingSieve_errSum
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) (muPlus : ℕ → ℝ) :
    (halfProductBoundingSieve num den N T z hN).errSum muPlus =
      ∑ d ∈ (sieveProduct N z).divisors, |muPlus d| *
        |halfProductCongruenceMass num den N T d -
          ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)| := by
  unfold BoundingSieve.errSum
  simp only [halfProductBoundingSieve_rem]
  rfl

/-- Mathlib's actual finite upper-bound sieve, specialized to the actual source.
The only coefficient premise is the standard upper-Moebius property; no
bound on the desired source count is inserted as a hypothesis. -/
theorem siftedHalfProductSource_card_le_upperMoebius
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (muPlus : ℕ → ℝ) (hmu : BoundingSieve.IsUpperMoebius muPlus) :
    ((siftedHalfProductSource num den N T z).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) *
        (∑ d ∈ (sieveProduct N z).divisors, muPlus d / (Nat.totient d : ℝ)) +
      ∑ d ∈ (sieveProduct N z).divisors, |muPlus d| *
        |halfProductCongruenceMass num den N T d -
          ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)| := by
  simpa only [halfProductBoundingSieve_siftedSum, halfProductBoundingSieve_totalMass,
    halfProductBoundingSieve_mainSum, halfProductBoundingSieve_errSum] using
    (BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
      (s := halfProductBoundingSieve num den N T z hN) muPlus hmu)

/-- Lambda-square weights with `w(1) = 1` supply genuine upper-Moebius
coefficients by mathlib's proved theorem. No sieve bound is assumed. -/
theorem siftedHalfProductSource_card_le_lambdaSquared
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((siftedHalfProductSource num den N T z).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) *
        (∑ d ∈ (sieveProduct N z).divisors,
          BoundingSieve.lambdaSquared w d / (Nat.totient d : ℝ)) +
      ∑ d ∈ (sieveProduct N z).divisors, |BoundingSieve.lambdaSquared w d| *
        |halfProductCongruenceMass num den N T d -
          ((halfProductSource num den N T).card : ℝ) / (Nat.totient d : ℝ)| :=
  siftedHalfProductSource_card_le_upperMoebius num den N T z hN
    (BoundingSieve.lambdaSquared w) (BoundingSieve.upperMoebius_lambdaSquared w hw)

/-- The source mass restricted to integers coprime to a modulus. -/
def halfProductCoprimeMass (num den N : ℕ) (T : ℝ) (d : ℕ) : ℝ :=
  (((halfProductSource num den N T).filter (fun m : ℕ => Nat.Coprime m d)).card : ℝ)

/-- Only this replacement of the coprime-source mass by the total source
mass needs roughness of the factors and the restriction to allowed moduli. -/
theorem halfProductCoprimeMass_eq_card_of_gate
    {num den N z d : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ)))) (hd : d ∣ sieveProduct N z) :
    halfProductCoprimeMass num den N T d =
      ((halfProductSource num den N T).card : ℝ) := by
  classical
  have hfilter : (halfProductSource num den N T).filter
      (fun m : ℕ => Nat.Coprime m d) = halfProductSource num den N T := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact halfProductSource_coprime_of_dvd_sieveProduct hnum hden hT hcap hm hd
  rw [halfProductCoprimeMass, hfilter]

/-- Under the geometric gate, the exact model remainder is the discrepancy
from the coprime-source mass divided by the totient. -/
theorem halfProductBoundingSieve_rem_eq_primitive_discrepancy
    {num den N z d : ℕ} {T : ℝ} (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ)))) (hd : d ∣ sieveProduct N z) :
    (halfProductBoundingSieve num den N T z hN).rem d =
      halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ) := by
  rw [halfProductCoprimeMass_eq_card_of_gate hnum hden hT hcap hd]
  exact halfProductBoundingSieve_rem num den N T z hN d

end

end ImbalancedChen
