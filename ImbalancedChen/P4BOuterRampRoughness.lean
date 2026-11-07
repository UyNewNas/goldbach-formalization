import ImbalancedChen.P4BPhysicalProductOuterRamp
import ImbalancedChen.P4BLabelledOuterPushforward
import ImbalancedChen.P4BOuterCoprimeElimination

/-!
# P4B: genuine roughness and exact coprime elimination for the physical ramp

YELLOW / SOURCE-ONLY / UNCOMPILED. Imports above are future normal module
names of sibling source-only drafts. All proofs below use the actual four
ramp weight and its unchanged labelled prime carrier.

The first three margins are normalized; only the last product wall has a
physical log-gap scale. Nonzero outer weight therefore weakens the order,
imbalance and lower-product margins by delta. Their elementary combination
loses at most two delta from the baseline roughness exponent. No roughness
of an arbitrary outer envelope or pushed-forward product is assumed.

The final theorem eliminates the actual attached coefficient's outer
coprime correction exactly. The strict real prime cutoff is matched to
the natural ceiling by Nat.lt_ceil, with no rounding buffer requirement.
No density, Part 3 distribution, derivative or boundary-count estimate is
claimed here.
-/

namespace ImbalancedChen.P4BOuterRampRoughness

noncomputable section

open scoped BigOperators
open Classical
open ImbalancedChen.Part3
open ImbalancedChen.P4B
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry
open ImbalancedChen.P4BLabelledOuterPushforward
open ImbalancedChen.P4BOuterCoprimeElimination

/-- The genuine baseline exponent before expanding the first three walls. -/
def baseline (b kappa : ℝ) : ℝ := (1 - kappa) * b / (1 + b)

/-- The three relaxed affine inequalities imply separate lower bounds for
both coordinates. No upper-product-wall estimate is needed for this step. -/
theorem relaxed_three_margins_coordinate_bounds
    {b kappa delta x y : ℝ} (hb : 0 < b)
    (horder : -delta < y - x) (hbalance : -delta < x - b * y)
    (hlower : 1 - kappa - delta < x + y) :
    baseline b kappa - delta < x ∧ baseline b kappa - 2 * delta < y := by
  have hden : 0 < 1 + b := by linarith only [hb]
  have hbaseline : baseline b kappa * (1 + b) = (1 - kappa) * b := by
    unfold baseline
    field_simp [ne_of_gt hden]
    <;> ring
  have hscaled : b * (1 - kappa - delta) < b * (x + y) :=
    mul_lt_mul_of_pos_left hlower hb
  have hxmul : (baseline b kappa - delta) * (1 + b) < x * (1 + b) := by
    nlinarith only [hscaled, hbalance, hbaseline]
  have hx : baseline b kappa - delta < x := (mul_lt_mul_right hden).mp hxmul
  exact ⟨hx, by linarith only [hx, horder]⟩

theorem relaxed_three_margins_above_theta
    {b kappa delta theta x y : ℝ} (hb : 0 < b) (hdelta : 0 ≤ delta)
    (horder : -delta < y - x) (hbalance : -delta < x - b * y)
    (hlower : 1 - kappa - delta < x + y)
    (hgap : 2 * delta ≤ baseline b kappa - theta) :
    theta < x ∧ theta < y := by
  obtain ⟨hx, hy⟩ := relaxed_three_margins_coordinate_bounds hb horder hbalance hlower
  constructor <;> linarith only [hx, hy, hgap, hdelta]

/-- The manuscript lower cutoff has normalized logarithm at least
1-kappa, retaining its literal factor two. -/
theorem manuscript_log_cutoff_ratio_ge
    {kappa : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    1 - kappa ≤ Real.log (manuscriptHalfProductCutoff kappa N) / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
  have hpower : 0 < (N : ℝ) ^ (1 - kappa) := Real.rpow_pos_of_pos hNpos _
  apply (le_div_iff₀ (Real.log_pos hN1)).mpr
  calc
    (1 - kappa) * Real.log (N : ℝ) = Real.log ((N : ℝ) ^ (1 - kappa)) :=
      (Real.log_rpow hNpos _).symm
    _ ≤ Real.log (manuscriptHalfProductCutoff kappa N) := by
      apply Real.log_le_log hpower
      change (N : ℝ) ^ (1 - kappa) ≤ 2 * (N : ℝ) ^ (1 - kappa)
      linarith only [hpower]

/-- Actual nonzero physical ramp support supplies the three inequalities;
none of them is accepted as an external analytic or roughness hypothesis. -/
theorem physical_ramp_nonzero_log_coordinates_above_theta
    {b kappa delta theta : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hdelta : 0 < delta) (hgap : 2 * delta ≤ baseline b kappa - theta)
    {t : Fin 2 → Fin (N + 1)}
    (hnonzero : physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N)
      delta t ≠ 0) :
    theta < logPoint N t 0 ∧ theta < logPoint N t 1 := by
  have horder := physicalPairOuterRamp_nonzero_original_margin_support
    hdelta hnonzero (i := (0 : Fin 4)) (by decide)
  have hbalance := physicalPairOuterRamp_nonzero_original_margin_support
    hdelta hnonzero (i := (1 : Fin 4)) (by decide)
  have hlower := physicalPairOuterRamp_nonzero_original_margin_support
    hdelta hnonzero (i := (2 : Fin 4)) (by decide)
  change -delta < logPoint N t 1 - logPoint N t 0 at horder
  change -delta < logPoint N t 0 - b * logPoint N t 1 at hbalance
  change -delta < logPoint N t 0 + logPoint N t 1 -
    Real.log (manuscriptHalfProductCutoff kappa N) / Real.log (N : ℝ) at hlower
  have hcutoff := manuscript_log_cutoff_ratio_ge (kappa := kappa) hN
  apply relaxed_three_margins_above_theta hb hdelta.le horder hbalance
    (by linarith only [hlower, hcutoff]) hgap

/-- A strict normalized prime-log lower bound is the literal real-power
roughness bound. The prime positivity is supplied by the actual carrier. -/
theorem real_rpow_lt_of_log_coordinate
    {N p : ℕ} {theta : ℝ} (hN : 2 ≤ N) (hp : 0 < (p : ℝ))
    (hlog : theta < Real.log (p : ℝ) / Real.log (N : ℝ)) :
    (N : ℝ) ^ theta < (p : ℝ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hNpos theta) hp).mp
  rw [Real.log_rpow hNpos]
  exact (lt_div_iff₀ (Real.log_pos hN1)).mp hlog

/-- Both actual labelled prime factors of a nonzero physical outer tuple
exceed N^theta, including when the two prime factors coincide. -/
theorem physical_ramp_nonzero_prime_factors_rough
    {b kappa delta theta : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hdelta : 0 < delta) (hgap : 2 * delta ≤ baseline b kappa - theta)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hnonzero : physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N)
      delta t ≠ 0) :
    (N : ℝ) ^ theta < ((tuplePair t).1 : ℝ) ∧
      (N : ℝ) ^ theta < ((tuplePair t).2 : ℝ) := by
  obtain ⟨hx, hy⟩ := physical_ramp_nonzero_log_coordinates_above_theta
    hb hN hdelta hgap hnonzero
  obtain ⟨hr, hq⟩ := labelled_prime_pair_pos ht
  exact ⟨real_rpow_lt_of_log_coordinate hN hr hx,
    real_rpow_lt_of_log_coordinate hN hq hy⟩

/-- Every prime divisor of the genuine labelled product is one of its two
actual prime factors. Repetition and square products require no exception. -/
theorem physical_ramp_nonzero_prime_divisor_rough
    {b kappa delta theta : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hdelta : 0 < delta) (hgap : 2 * delta ≤ baseline b kappa - theta)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hnonzero : physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N)
      delta t ≠ 0) {ell : ℕ} (hell : Nat.Prime ell) (hdvd : ell ∣ labelledProduct t) :
    (N : ℝ) ^ theta < (ell : ℝ) := by
  have hprime : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  obtain ⟨hr, hq⟩ := physical_ramp_nonzero_prime_factors_rough hb hN hdelta hgap ht hnonzero
  rw [labelledProduct_eq_pairProduct] at hdvd
  rcases (prime_dvd_halfProduct_iff hell (hprime 0) (hprime 1)).mp hdvd with h | h
  · simpa only [h] using hr
  · simpa only [h] using hq

/-- Nonzero actual pushed-forward weight has a nonzero tuple in its exact
fibre. This uses the proved fibre API; no sign or no-cancellation assumption
is imposed on the pushforward. -/
theorem physical_ramp_productWeight_nonzero_prime_divisor_rough
    {b kappa delta theta : ℝ} {N m : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hdelta : 0 < delta) (hgap : 2 * delta ≤ baseline b kappa - theta)
    (hweight : productWeight N
      (physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) delta) m ≠ 0)
    {ell : ℕ} (hell : Nat.Prime ell) (hdvd : ell ∣ m) :
    (N : ℝ) ^ theta < (ell : ℝ) := by
  obtain ⟨t, ht, hproduct, hnonzero⟩ := exists_nonzero_fibre_of_productWeight_ne_zero hweight
  apply physical_ramp_nonzero_prime_divisor_rough hb hN hdelta hgap ht hnonzero hell
  simpa only [hproduct] using hdvd

/-- Exact strict-real-cutoff version of the sieve-product coprimality
lemma. A prime in the natural carrier is < realCutoff, not merely < ceil. -/
theorem coprime_sieveProduct_ceil_of_prime_divisor_rough
    (N m : ℕ) (realCutoff : ℝ)
    (hrough : ∀ ell : ℕ, Nat.Prime ell → ell ∣ m → realCutoff < (ell : ℝ)) :
    Nat.Coprime m (sieveProduct N (Nat.ceil realCutoff)) := by
  unfold sieveProduct
  apply Nat.coprime_prod_right_iff.mpr
  intro ell hell
  obtain ⟨hellceil, hprime, hnotN⟩ := mem_sievePrimes.mp hell
  apply (hprime.coprime_iff_not_dvd.mpr ?_).symm
  intro hdvd
  have hellReal : (ell : ℝ) < realCutoff := Nat.lt_ceil.mp hellceil
  exact (not_lt_of_ge hellReal.le) (hrough ell hprime hdvd)

/-- The real cutoff N^(nu*r) is the identical cutoff in the physical
coefficient's proved support theorem. No ceiling-loss premise is needed. -/
theorem physical_ramp_productWeight_coprime_attachedModulus
    {b kappa nu r epsilon delta : ℝ} {N m d : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hN : 2 ≤ N)
    (hepsilonR : epsilon ^ 2 ≤ r) (hdelta : 0 < delta)
    (hgap : 2 * delta ≤ baseline b kappa - nu * r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (hweight : productWeight N
      (physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) delta) m ≠ 0)
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
  exact physical_ramp_productWeight_nonzero_prime_divisor_rough
    hb hN hdelta hgap hweight hell hellm

/-- The full actual pushed-forward source has the literal total mass in
every displayed attached modulus, including zero-weight exterior points. -/
theorem physical_ramp_productWeight_coprimeMass_eq_sourceMass
    {b kappa nu r epsilon delta : ℝ} {N d : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hN : 2 ≤ N)
    (hepsilonR : epsilon ^ 2 ≤ r) (hdelta : 0 < delta)
    (hgap : 2 * delta ≤ baseline b kappa - nu * r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    finiteCoprimeMass (productCarrier N)
      (productWeight N (physicalPairOuterRamp b N
        (manuscriptHalfProductCutoff kappa N) delta)) d =
      finiteSourceMass (productCarrier N)
        (productWeight N (physicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) delta)) := by
  apply finiteCoprimeMass_eq_sourceMass_of_weight_support
  intro m hm hweight
  exact physical_ramp_productWeight_coprime_attachedModulus
    hb hnu hN hepsilonR hdelta hgap retain cap hweight hd

/-- Exact payment of the actual outer coprime-correction slot. Unlike the
generic interface, the true ramp's outer-support roughness is proved here. -/
theorem physical_ramp_outer_signed_coprime_sum_eq_zero
    {b kappa nu r epsilon delta : ℝ} {N : ℕ}
    (hb : 0 < b) (hnu : 0 < nu) (hN : 2 ≤ N)
    (hepsilonR : epsilon ^ 2 ≤ r) (hdelta : 0 < delta)
    (hgap : 2 * delta ≤ baseline b kappa - nu * r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        ((finiteCoprimeMass (productCarrier N)
            (productWeight N (physicalPairOuterRamp b N
              (manuscriptHalfProductCutoff kappa N) delta)) d -
          finiteSourceMass (productCarrier N)
            (productWeight N (physicalPairOuterRamp b N
              (manuscriptHalfProductCutoff kappa N) delta))) /
          (Nat.totient d : ℝ))) = 0 := by
  apply signed_coprime_sum_eq_zero_of_active_weight_support
  intro d hd hactive m hm hweight
  exact physical_ramp_productWeight_coprime_attachedModulus
    hb hnu hN hepsilonR hdelta hgap retain cap hweight hd

/-- A strict exponent gap always permits a fixed positive physical ramp
width. This selection is purely scalar and precedes every target N. -/
theorem exists_positive_ramp_width_of_exponent_gap
    {b kappa theta : ℝ} (hgap : theta < baseline b kappa) :
    ∃ delta : ℝ, 0 < delta ∧ 2 * delta ≤ baseline b kappa - theta := by
  refine ⟨(baseline b kappa - theta) / 4, ?_, ?_⟩ <;> linarith only [hgap]

end

end ImbalancedChen.P4BOuterRampRoughness
