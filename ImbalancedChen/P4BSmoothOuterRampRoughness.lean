import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp
import ImbalancedChen.P4BOuterRampRoughness
import ImbalancedChen.P4BLabelledOuterPushforward
import ImbalancedChen.P4BOuterCoprimeElimination

/-!
# P4B: actual smooth outer support is rough and has zero coprime correction

YELLOW / SOURCE-ONLY / UNCOMPILED. Sibling imports are future normal module
names. The weight is the actual smoothPhysicalPairOuterRamp, whose factors
are Real.smoothTransition applied to 1 plus the true physical margin divided
by width. It is not identified with the earlier piecewise-linear ramp.

The smooth weight's own proved nonzero-support theorem supplies the first
three relaxed normalized margins. Only the elementary three-margin algebra,
the exact manuscript lower-cutoff logarithm, and the strict-real-cutoff
coprimality lemma are reused from P4BOuterRampRoughness. No assertion about
the linear weight is used as a premise about the smooth weight.

Every actual smooth tuple factor and every prime divisor of its product
is rough under the explicit exponent gap. The exact product-fibre witness
transports that proved statement to the actual smooth productWeight. The
final same-rho outer coprime correction is exactly zero, with no hrough,
weight-equality, density, boundary-mass or distribution premise.
-/

namespace ImbalancedChen.P4BSmoothOuterRampRoughness

noncomputable section

open scoped BigOperators
open Classical
open ImbalancedChen.Part3
open ImbalancedChen.P4B
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry
open ImbalancedChen.P4BLabelledOuterPushforward
open ImbalancedChen.P4BOuterCoprimeElimination
open ImbalancedChen.P4BOuterRampRoughness

/-- Nonzero actual smooth weight supplies its own three softened margins.
Their combination loses at most two widths from the baseline exponent. -/
theorem smooth_physical_ramp_nonzero_log_coordinates_above_theta
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta)
    {t : Fin 2 → Fin (N + 1)}
    (hnonzero : smoothPhysicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) width t ≠ 0) :
    theta < logPoint N t 0 ∧ theta < logPoint N t 1 := by
  have horder := smoothPhysicalPairOuterRamp_nonzero_original_margin_support
    hwidth hnonzero (i := (0 : Fin 4)) (by decide)
  have hbalance := smoothPhysicalPairOuterRamp_nonzero_original_margin_support
    hwidth hnonzero (i := (1 : Fin 4)) (by decide)
  have hlower := smoothPhysicalPairOuterRamp_nonzero_original_margin_support
    hwidth hnonzero (i := (2 : Fin 4)) (by decide)
  change -width < logPoint N t 1 - logPoint N t 0 at horder
  change -width < logPoint N t 0 - b * logPoint N t 1 at hbalance
  change -width < logPoint N t 0 + logPoint N t 1 -
    Real.log (manuscriptHalfProductCutoff kappa N) / Real.log (N : ℝ) at hlower
  have hcutoff := manuscript_log_cutoff_ratio_ge (kappa := kappa) hN
  exact relaxed_three_margins_above_theta hb hwidth.le horder hbalance
    (by linarith only [hlower, hcutoff]) hgap

/-- Each factor is a genuine prime from the existing labelled carrier.
The lower bounds are for the actual real powers, including prime squares. -/
theorem smooth_physical_ramp_nonzero_prime_factors_rough
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hnonzero : smoothPhysicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) width t ≠ 0) :
    (N : ℝ) ^ theta < ((tuplePair t).1 : ℝ) ∧
      (N : ℝ) ^ theta < ((tuplePair t).2 : ℝ) := by
  obtain ⟨hx, hy⟩ := smooth_physical_ramp_nonzero_log_coordinates_above_theta
    hb hN hwidth hgap hnonzero
  obtain ⟨hr, hq⟩ := labelled_prime_pair_pos ht
  exact ⟨real_rpow_lt_of_log_coordinate hN hr hx,
    real_rpow_lt_of_log_coordinate hN hq hy⟩

/-- Every prime divisor of the nonzero smooth tuple's literal product
equals one of those same two actual prime factors. -/
theorem smooth_physical_ramp_nonzero_prime_divisor_rough
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hnonzero : smoothPhysicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) width t ≠ 0)
    {ell : ℕ} (hell : Nat.Prime ell) (hdvd : ell ∣ labelledProduct t) :
    (N : ℝ) ^ theta < (ell : ℝ) := by
  have hprime : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  obtain ⟨hr, hq⟩ := smooth_physical_ramp_nonzero_prime_factors_rough
    hb hN hwidth hgap ht hnonzero
  rw [labelledProduct_eq_pairProduct] at hdvd
  rcases (prime_dvd_halfProduct_iff hell (hprime 0) (hprime 1)).mp hdvd with h | h
  · simpa only [h] using hr
  · simpa only [h] using hq

/-- Exact nonzero-fibre extraction applies to any tuple weight and hence
to this actual smooth weight, without a no-cancellation hypothesis. -/
theorem smooth_physical_ramp_productWeight_nonzero_prime_divisor_rough
    {b kappa width theta : ℝ} {N m : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta)
    (hweight : productWeight N (smoothPhysicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) width) m ≠ 0)
    {ell : ℕ} (hell : Nat.Prime ell) (hdvd : ell ∣ m) :
    (N : ℝ) ^ theta < (ell : ℝ) := by
  obtain ⟨t, ht, hproduct, hnonzero⟩ := exists_nonzero_fibre_of_productWeight_ne_zero hweight
  apply smooth_physical_ramp_nonzero_prime_divisor_rough
    hb hN hwidth hgap ht hnonzero hell
  simpa only [hproduct] using hdvd

/-- The real cutoff in the proved factor bound is exactly the cutoff
whose ceiling defines the attached physical modulus support. -/
theorem smooth_physical_ramp_productWeight_coprime_attachedModulus
    {b kappa nu r epsilon width : ℝ} {N m d : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hN : 2 ≤ N)
    (hepsilonR : epsilon ^ 2 ≤ r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (hweight : productWeight N (smoothPhysicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) width) m ≠ 0)
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    Nat.Coprime m d := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hdvd : d ∣ sieveProduct N (Nat.ceil ((N : ℝ) ^ (nu * r))) :=
    actualSmallRoughModuli_dvd_sieveProduct_ceil (retain N) N (cap N) _ _
      (Real.rpow_le_rpow_of_exponent_le hNreal
        (mul_le_mul_of_nonneg_left hepsilonR hnu.le)) hd
  apply (coprime_sieveProduct_ceil_of_prime_divisor_rough N m
    ((N : ℝ) ^ (nu * r)) ?_).of_dvd_right hdvd
  intro ell hell hellm
  exact smooth_physical_ramp_productWeight_nonzero_prime_divisor_rough
    hb hN hwidth hgap hweight hell hellm

/-- The smooth pushed-forward weight has its full source mass in every
literal attached coprime restriction, including exterior zero values. -/
theorem smooth_physical_ramp_productWeight_coprimeMass_eq_sourceMass
    {b kappa nu r epsilon width : ℝ} {N d : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hN : 2 ≤ N)
    (hepsilonR : epsilon ^ 2 ≤ r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    finiteCoprimeMass (productCarrier N)
      (productWeight N (smoothPhysicalPairOuterRamp b N
        (manuscriptHalfProductCutoff kappa N) width)) d =
      finiteSourceMass (productCarrier N)
        (productWeight N (smoothPhysicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) width)) := by
  apply finiteCoprimeMass_eq_sourceMass_of_weight_support
  intro m hm hweight
  exact smooth_physical_ramp_productWeight_coprime_attachedModulus
    hb hnu hN hepsilonR hwidth hgap retain cap hweight hd

/-- Final actual smooth same-rho supplier: the signed outer coprime
correction vanishes exactly, with the original coefficient unchanged. -/
theorem smooth_physical_ramp_outer_signed_coprime_sum_eq_zero
    {b kappa nu r epsilon width : ℝ} {N : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hN : 2 ≤ N)
    (hepsilonR : epsilon ^ 2 ≤ r) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - nu * r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        ((finiteCoprimeMass (productCarrier N)
            (productWeight N (smoothPhysicalPairOuterRamp b N
              (manuscriptHalfProductCutoff kappa N) width)) d -
          finiteSourceMass (productCarrier N)
            (productWeight N (smoothPhysicalPairOuterRamp b N
              (manuscriptHalfProductCutoff kappa N) width))) /
          (Nat.totient d : ℝ))) = 0 := by
  apply signed_coprime_sum_eq_zero_of_active_weight_support
  intro d hd hactive m hm hweight
  exact smooth_physical_ramp_productWeight_coprime_attachedModulus
    hb hnu hN hepsilonR hwidth hgap retain cap hweight hd

end

end ImbalancedChen.P4BSmoothOuterRampRoughness
