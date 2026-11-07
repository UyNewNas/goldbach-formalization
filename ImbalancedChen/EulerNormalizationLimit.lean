import ImbalancedChen.CenterPrimeTail
import ImbalancedChen.PowerErrorBudget
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Convergence of the actual finite Euler normalization

The strict-cap odd Euler products converge to the already constructed,
strictly positive twin-prime constant. This follows from an explicit
exhaustion of the subtype of odd primes by preimages of `Finset.range`.
Thus it uses the actual `HasProd`, not the default value of a `tprod`.

At the exact natural cap `ceil(N^(1/5))`, the center-prime tail correction
tends to one, by the proved uniform bound from `CenterPrimeTail`. Combining
these two limits with the exact finite Euler factorization gives

`V_N(z) / (2 * (product of (1 - 1/p), p < z) * singularSeries N) -> 1`

along positive even centers with this cap. The ordinary prime Euler product
remains explicit: there is no Mertens estimate, prime-counting hypothesis,
or sieve/distribution estimate in this statement.

All definitions are total, including at zero. Identities which identify the
full prime-divisor correction require `N != 0`; the finite sieve Euler
identity itself is the previously proved one. Strict cap endpoints are
unchanged, and every normalization denominator is proved positive.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators

/-- The ordinary prime Euler product, with the same strict cap as the sieve. -/
def primeEulerProduct (z : ℕ) : ℝ :=
  ∏ p ∈ primesBelowCap z, (1 - 1 / (p : ℝ))

/-- The finite odd-prime constant, with the same strict cap as the sieve. -/
def oddEulerProduct (z : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesBelowCap z, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- The full finite prime-divisor correction; it is one at zero. -/
def centerPrimeCorrection (N : ℕ) : ℝ :=
  ∏ p ∈ oddPrimeDivisors N, ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- The strict-cap part of the finite correction. At zero it retains the
literal below-cap divisibility convention from `FiniteSieveEuler`. -/
def centerPrimeCorrectionBelowCap (N z : ℕ) : ℝ :=
  ∏ p ∈ oddPrimeDivisorsBelowCap N z, ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- The exact natural cap corresponding to the manuscript's real fifth root. -/
def fifthRootSieveCap (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))

/-- The actual finite sieve density normalized by the actual singular
series, with the ordinary prime Euler product deliberately left explicit. -/
def normalizedFiniteSieveDensity (N z : ℕ) : ℝ :=
  finiteSieveDensity N z / (2 * primeEulerProduct z * singularSeries N)

/-- Odd primes below the strict cap, represented in the index type of the
genuine infinite product. -/
def oddPrimeIndicesBelowCap (z : ℕ) : Finset OddPrime :=
  (Finset.range z).preimage (Subtype.val : OddPrime → ℕ)
    Subtype.val_injective.injOn

@[simp] theorem mem_oddPrimeIndicesBelowCap {z : ℕ} {p : OddPrime} :
    p ∈ oddPrimeIndicesBelowCap z ↔ p.val < z := by
  change p ∈ (Finset.range z).preimage (Subtype.val : OddPrime → ℕ)
    Subtype.val_injective.injOn ↔ p.val < z
  exact (Finset.mem_preimage (f := (Subtype.val : OddPrime → ℕ))
    (s := Finset.range z) (hf := Subtype.val_injective.injOn) (x := p)).trans
      Finset.mem_range

/-- The finite product over natural primes is exactly the corresponding
finite product in the index type of `hasProd_oddPrimeFactor`. -/
theorem oddEulerProduct_eq_index_product (z : ℕ) :
    oddEulerProduct z = ∏ p ∈ oddPrimeIndicesBelowCap z, oddPrimeFactor p := by
  classical
  symm
  unfold oddEulerProduct
  apply Finset.prod_bij (fun p _ => p.val)
  · intro p hp
    exact mem_oddPrimesBelowCap.mpr
      ⟨mem_oddPrimeIndicesBelowCap.mp hp, p.property.1, p.property.2⟩
  · intro p hp q hq hpq
    exact Subtype.ext hpq
  · intro p hp
    obtain ⟨hpz, hpprime, hpodd⟩ := mem_oddPrimesBelowCap.mp hp
    exact ⟨⟨p, hpprime, hpodd⟩, mem_oddPrimeIndicesBelowCap.mpr hpz, rfl⟩
  · intro p hp
    rfl

/-- A genuine finite-set exhaustion of all odd primes. -/
theorem tendsto_oddPrimeIndicesBelowCap_atTop :
    Tendsto oddPrimeIndicesBelowCap atTop atTop := by
  exact (tendsto_finset_preimage_atTop_atTop
    (f := (Subtype.val : OddPrime → ℕ)) Subtype.val_injective).comp
      tendsto_finset_range

/-- Strict-cap partial products converge to the actual positive constant. -/
theorem tendsto_oddEulerProduct :
    Tendsto oddEulerProduct atTop (𝓝 twinPrimeConstant) := by
  have hprod : Tendsto (fun s : Finset OddPrime => ∏ p ∈ s, oddPrimeFactor p)
      atTop (𝓝 twinPrimeConstant) := hasProd_oddPrimeFactor
  have h := hprod.comp tendsto_oddPrimeIndicesBelowCap_atTop
  apply h.congr'
  exact Filter.Eventually.of_forall fun z => (oddEulerProduct_eq_index_product z).symm

theorem primeEulerProduct_pos (z : ℕ) : 0 < primeEulerProduct z := by
  apply Finset.prod_pos
  intro p hp
  have hpprime := (mem_primesBelowCap.mp hp).2
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
  apply sub_pos.mpr
  apply (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ))).mpr
  linarith

theorem oddEulerProduct_pos (z : ℕ) : 0 < oddEulerProduct z := by
  rw [oddEulerProduct_eq_index_product]
  exact Finset.prod_pos (fun p _ => oddPrimeFactor_pos p)

theorem one_le_centerPrimeCorrection (N : ℕ) : 1 ≤ centerPrimeCorrection N :=
  one_le_oddPrimeDivisor_product N

theorem centerPrimeCorrection_pos (N : ℕ) : 0 < centerPrimeCorrection N :=
  lt_of_lt_of_le zero_lt_one (one_le_centerPrimeCorrection N)

theorem one_le_centerPrimeCorrectionBelowCap (N z : ℕ) :
    1 ≤ centerPrimeCorrectionBelowCap N z := by
  apply Finset.one_le_prod
  intro p hp
  exact one_le_centerPrimeFactor (mem_oddPrimeDivisorsBelowCap.mp hp).2.2.1

theorem centerPrimeCorrectionBelowCap_pos (N z : ℕ) :
    0 < centerPrimeCorrectionBelowCap N z :=
  lt_of_lt_of_le zero_lt_one (one_le_centerPrimeCorrectionBelowCap N z)

theorem centerPrimeTailCorrection_pos (N z : ℕ) :
    0 < centerPrimeTailCorrection N z :=
  lt_of_lt_of_le zero_lt_one (one_le_centerPrimeTailCorrection N z)

/-- Every normalization denominator is positive, even at the totalized
small arguments. This is independent of evenness. -/
theorem finiteSieveNormalization_denominator_pos (N z : ℕ) :
    0 < 2 * primeEulerProduct z * singularSeries N :=
  mul_pos (mul_pos (by norm_num) (primeEulerProduct_pos z)) (singularSeries_pos N)

theorem centerPrimeCorrection_eq_below_mul_tail {N z : ℕ} (hN : N ≠ 0) :
    centerPrimeCorrection N =
      centerPrimeCorrectionBelowCap N z * centerPrimeTailCorrection N z :=
  oddPrimeDivisor_product_eq_below_mul_tail hN

/-- The full-to-truncated correction ratio is the actual omitted tail. -/
theorem centerPrimeCorrection_div_below_eq_tail {N z : ℕ} (hN : N ≠ 0) :
    centerPrimeCorrection N / centerPrimeCorrectionBelowCap N z =
      centerPrimeTailCorrection N z := by
  rw [centerPrimeCorrection_eq_below_mul_tail (z := z) hN]
  field_simp [(centerPrimeCorrectionBelowCap_pos N z).ne'] <;> ring

/-- The reverse correction ratio is the inverse of the actual tail. -/
theorem centerPrimeCorrectionBelowCap_div_full_eq_inv_tail
    {N z : ℕ} (hN : N ≠ 0) :
    centerPrimeCorrectionBelowCap N z / centerPrimeCorrection N =
      (centerPrimeTailCorrection N z)⁻¹ := by
  rw [centerPrimeCorrection_eq_below_mul_tail (z := z) hN]
  field_simp [(centerPrimeCorrectionBelowCap_pos N z).ne',
    (centerPrimeTailCorrection_pos N z).ne'] <;> ring

/-- The exact normalized finite identity; zero is explicitly excluded
because the full prime-factor convention at zero is empty. -/
theorem normalizedFiniteSieveDensity_eq_odd_div_tail
    {N z : ℕ} (hN : N ≠ 0) (hEven : Even N) (hz : 2 < z) :
    normalizedFiniteSieveDensity N z =
      oddEulerProduct z / (twinPrimeConstant * centerPrimeTailCorrection N z) := by
  unfold normalizedFiniteSieveDensity
  rw [finiteSieveDensity_euler_identity hEven hz, singularSeries,
    oddPrimeDivisor_product_eq_below_mul_tail (z := z) hN]
  change
    (2 * primeEulerProduct z * oddEulerProduct z * centerPrimeCorrectionBelowCap N z) /
        (2 * primeEulerProduct z *
          (twinPrimeConstant *
            (centerPrimeCorrectionBelowCap N z * centerPrimeTailCorrection N z))) = _
  field_simp [(primeEulerProduct_pos z).ne', twinPrimeConstant_pos.ne',
    (centerPrimeCorrectionBelowCap_pos N z).ne',
    (centerPrimeTailCorrection_pos N z).ne'] <;> ring

/-- The exact ceiling cap tends to infinity. This elementary proof uses
the already proved fifth-power bound, so it loses no endpoint information. -/
theorem tendsto_fifthRootSieveCap_atTop :
    Tendsto fifthRootSieveCap atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b ^ 5 + 1, ?_⟩
  intro N hN
  by_contra h
  have hz : fifthRootSieveCap N ≤ b := by omega
  have hpow := pow_le_pow_left' hz 5
  have hle : N ≤ (fifthRootSieveCap N) ^ 5 := le_ceil_fifthRoot_pow_five N
  omega

/-- The genuine constant-product limit along the actual manuscript cap. -/
theorem tendsto_oddEulerProduct_actual_cap :
    Tendsto (fun N : ℕ => oddEulerProduct (fifthRootSieveCap N))
      atTop (𝓝 twinPrimeConstant) :=
  tendsto_oddEulerProduct.comp tendsto_fifthRootSieveCap_atTop

/-- The actual omitted correction tends to one on all natural centers.
The estimate is uniform and was proved from distinct prime divisors. -/
theorem tendsto_centerPrimeTailCorrection_actual_cap :
    Tendsto (fun N : ℕ => centerPrimeTailCorrection N (fifthRootSieveCap N))
      atTop (𝓝 1) := by
  have hrecip : Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ (1 / 5 : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_zero] using
      tendsto_nat_log_pow_div_rpow 0 (by norm_num : (0 : ℝ) < 1 / 5)
  have hdecay : Tendsto (fun N : ℕ => 62 / (N : ℝ) ^ (1 / 5 : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using hrecip.const_mul 62
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [hdecay.eventually (gt_mem_nhds hepsilon),
    eventually_ge_atTop (1024 : ℕ)] with N hsmall hN
  rw [Real.dist_eq]
  exact (centerPrimeTailCorrection_actual_cap_abs_sub_one_le hN).trans_lt hsmall

/-- The full-to-capped correction ratio tends to one, with no arithmetic
restriction on the positive centers. -/
theorem tendsto_centerPrimeCorrection_div_below_actual_cap :
    Tendsto (fun N : ℕ =>
      centerPrimeCorrection N / centerPrimeCorrectionBelowCap N (fifthRootSieveCap N))
      atTop (𝓝 1) := by
  apply tendsto_centerPrimeTailCorrection_actual_cap.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (centerPrimeCorrection_div_below_eq_tail (by omega : N ≠ 0)).symm

/-- The truncated-to-full correction ratio also tends to one. -/
theorem tendsto_centerPrimeCorrectionBelowCap_div_full_actual_cap :
    Tendsto (fun N : ℕ =>
      centerPrimeCorrectionBelowCap N (fifthRootSieveCap N) / centerPrimeCorrection N)
      atTop (𝓝 1) := by
  have hinv : Tendsto (fun N : ℕ =>
      (centerPrimeTailCorrection N (fifthRootSieveCap N))⁻¹)
      atTop (𝓝 1) := by
    simpa only [inv_one] using
      tendsto_centerPrimeTailCorrection_actual_cap.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (centerPrimeCorrectionBelowCap_div_full_eq_inv_tail (by omega : N ≠ 0)).symm

/-- The ratio appearing in the exact normalized identity tends to one on
all centers, before specializing that identity to positive even centers. -/
theorem tendsto_oddEulerProduct_div_constant_tail_actual_cap :
    Tendsto (fun N : ℕ => oddEulerProduct (fifthRootSieveCap N) /
      (twinPrimeConstant * centerPrimeTailCorrection N (fifthRootSieveCap N)))
      atTop (𝓝 1) := by
  have hden : Tendsto (fun N : ℕ =>
      twinPrimeConstant * centerPrimeTailCorrection N (fifthRootSieveCap N))
      atTop (𝓝 twinPrimeConstant) := by
    simpa only [mul_one] using
      tendsto_centerPrimeTailCorrection_actual_cap.const_mul twinPrimeConstant
  have h :=
    tendsto_oddEulerProduct_actual_cap.div hden twinPrimeConstant_pos.ne'
  change Tendsto (fun N : ℕ => oddEulerProduct (fifthRootSieveCap N) /
    (twinPrimeConstant * centerPrimeTailCorrection N (fifthRootSieveCap N)))
    atTop (𝓝 (twinPrimeConstant / twinPrimeConstant)) at h
  rw [div_self twinPrimeConstant_pos.ne'] at h
  exact h

/-- The epsilon statement of the normalized finite sieve limit, with
evenness as an implication and positivity of centers made eventual. -/
theorem eventuallyEven_normalizedFiniteSieveDensity_actual_cap_sub_one
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |normalizedFiniteSieveDensity N (fifthRootSieveCap N) - 1| < epsilon := by
  have hclose := Metric.tendsto_nhds.mp
    tendsto_oddEulerProduct_div_constant_tail_actual_cap epsilon hepsilon
  have hcap : ∀ᶠ N : ℕ in atTop, 2 < fifthRootSieveCap N :=
    tendsto_fifthRootSieveCap_atTop.eventually (eventually_gt_atTop 2)
  filter_upwards [hclose, hcap, eventually_ge_atTop (1 : ℕ)] with N hcloseN hcapN hN
  intro hEven
  rw [normalizedFiniteSieveDensity_eq_odd_div_tail (by omega : N ≠ 0) hEven hcapN]
  simpa only [Real.dist_eq] using hcloseN

/-- The normalized limit along positive even integers. The prime Euler
product remains explicit and no asymptotic for it is assumed. -/
theorem tendsto_normalizedFiniteSieveDensity_actual_cap_positive_even :
    Tendsto (fun N : ℕ => normalizedFiniteSieveDensity N (fifthRootSieveCap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  rw [Filter.eventually_inf_principal]
  filter_upwards [eventuallyEven_normalizedFiniteSieveDensity_actual_cap_sub_one
    epsilon hepsilon] with N hN
  intro hEven
  simpa only [Real.dist_eq] using hN hEven.2

end

end ImbalancedChen
