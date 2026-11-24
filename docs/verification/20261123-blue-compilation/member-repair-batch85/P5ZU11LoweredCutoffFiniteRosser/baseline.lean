import ImbalancedChen.P5ZU11SelectedLargestOrdinary
import ImbalancedChen.CurrentChenUpsilon1011JointOverlapFiniteMean
import ImbalancedChen.CurrentChenQuotientUpperRosser

/-!
Actual original U11 arithmetic at the ordinary reduced cutoff.

At the original p2 cutoff the selected multiplier overlaps the sieve
product (its gcd is p1). This file does not assign that count a coprime
density. It first lowers the roughness cutoff to Z <= p1, proves literal
count inclusion, and only then uses the actual upper Rosser coefficient
and the ordinary reciprocal-totient main term. The exact signed AP error
and centre-prime subtraction retain the same coefficient and modulus b*d.

The source cutoff is N^min(lower_w-xi,(nu-Tplus-20delta)/(2+rho)), as in
four-prefix-safe-minimum.tex:101--105. The physical row level is
N^(nu-Tplus-20delta). Both finite Rosser legality conditions are proved.
No H248 averaged semantics, distribution bound, endpoint limit or original
mean is supplied. Status: source_written / uncompiled; older files frozen.
-/

namespace ImbalancedChen.P5Z.U11LoweredRosser

open Set MeasureTheory
open U11Adaptive
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

noncomputable section

def multiplier (t : Four) : ℕ := t.1.1 * t.1.2 * t.2.1 * t.2.2

/-- Lowering the physical cutoff enlarges the literal quotient source,
with units and squareful receivers retained. -/
theorem siftedSource_subset_lowered (N b : ℕ) (low high : ℝ) (h : low ≤ high) :
    chenSiftedQuotientPrimeSource N b high ⊆ chenSiftedQuotientPrimeSource N b low := by
  intro q hq
  obtain ⟨hqc, hr⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hqc, fun p hp hpd => h.trans (hr p hp hpd)⟩

theorem original_carrier_order {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (hN : 1 ≤ (N : ℝ)) (ht : t ∈ source N E) :
    t.1.1 ∈ chenAdditivePrimeCarrier N ∧ t.1.2 ∈ chenAdditivePrimeCarrier N ∧
      t.2.1 ∈ chenAdditivePrimeCarrier N ∧ t.2.2 ∈ chenAdditivePrimeCarrier N ∧
      t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 :=
  P5U1011JointOverlap.joint_carrier_order
    (P5U1011JointOverlap.originalU11_mem_joint hN ht)

/-- The ordinary coprimality is established at the lowered cutoff only. -/
theorem multiplier_coprime_lowered {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (hN : 1 ≤ (N : ℝ)) (ht : t ∈ source N E) (Z : ℝ)
    (hZ : Z ≤ (t.1.1 : ℝ)) :
    Nat.Coprime (multiplier t) (sieveProduct N (Nat.ceil Z)) := by
  obtain ⟨h1, h2, h3, h4, h12, h23, h34⟩ := original_carrier_order hN ht
  have hZ2 : Z ≤ (t.1.2 : ℝ) := hZ.trans (by exact_mod_cast h12.le)
  have hZ3 : Z ≤ (t.2.1 : ℝ) := hZ2.trans (by exact_mod_cast h23.le)
  have hZ4 : Z ≤ (t.2.2 : ℝ) := hZ3.trans (by exact_mod_cast h34.le)
  have hc1 := chen_prime_coprime_sieveProduct_of_real_lower (N := N)
    (mem_chenAdditivePrimeCarrier.mp h1).2.1 hZ
  have hc2 := chen_prime_coprime_sieveProduct_of_real_lower (N := N)
    (mem_chenAdditivePrimeCarrier.mp h2).2.1 hZ2
  have hc3 := chen_prime_coprime_sieveProduct_of_real_lower (N := N)
    (mem_chenAdditivePrimeCarrier.mp h3).2.1 hZ3
  have hc4 := chen_prime_coprime_sieveProduct_of_real_lower (N := N)
    (mem_chenAdditivePrimeCarrier.mp h4).2.1 hZ4
  exact ((hc1.mul_left hc2).mul_left hc3).mul_left hc4

theorem rosser_support_dvd_lowered {N d : ℕ} {Z : ℝ}
    (hd : d ∈ actualSmallRosserSupport N (Nat.ceil Z) Z) :
    d ∣ sieveProduct N (Nat.ceil Z) := by
  have hh : d ∣ actualSmallPrimeProduct N (Nat.ceil Z) Z := (Nat.mem_divisors.mp hd).1
  rwa [currentChen_actualSmallPrimeProduct_eq_sieveProduct N (Nat.ceil Z) Z (Nat.le_ceil Z)] at hh

/-- The standard totient dictionary is valid on every actual lowered
Rosser divisor, not on the original overlapping p2-sieve support. -/
theorem totient_mul_on_lowered_support {N d : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (hN : 1 ≤ (N : ℝ)) (ht : t ∈ source N E) (Z : ℝ)
    (hZ : Z ≤ (t.1.1 : ℝ)) (hd : d ∈ actualSmallRosserSupport N (Nat.ceil Z) Z) :
    Nat.totient (multiplier t * d) = Nat.totient (multiplier t) * Nat.totient d :=
  Nat.totient_mul (chenQuotient_allowed_coprime
    (multiplier_coprime_lowered hN ht Z hZ) (rosser_support_dvd_lowered hd))

def mainTerm (N : ℕ) (t : Four) (Z R : ℝ) : ℝ :=
  trueLogarithmicIntegral N / (Nat.totient (multiplier t) : ℝ) *
    actualSmallRosserPlusDensity N (Nat.ceil Z) Z R

def signedAP (N : ℕ) (t : Four) (Z R : ℝ) : ℝ :=
  ∑ d ∈ actualSmallRosserSupport N (Nat.ceil Z) Z,
    actualSmallRosserPlus N (Nat.ceil Z) Z R d *
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (multiplier t * d)

def signedCentre (N : ℕ) (t : Four) (Z R : ℝ) : ℝ :=
  ∑ d ∈ actualSmallRosserSupport N (Nat.ceil Z) Z,
    actualSmallRosserPlus N (Nat.ceil Z) Z R d *
      chenCentrePrimeAPCount N N (multiplier t * d)

theorem row_upper {N : ℕ} {E : ℕ × ℕ → Prop} {t : Four}
    (hN : 1 ≤ (N : ℝ)) (ht : t ∈ source N E) (Z R : ℝ)
    (hZ : Z ≤ (t.1.1 : ℝ)) (hR : 1 < R) (hZR : Z ≤ R) :
    weight N t ≤ mainTerm N t Z R + signedAP N t Z R - signedCentre N t Z R := by
  have h12 := (original_carrier_order hN ht).2.2.2.2.1
  have hZ2 : Z ≤ (t.1.2 : ℝ) := hZ.trans (by exact_mod_cast h12.le)
  have hcount : ((chenSiftedQuotientPrimeSource N (multiplier t) (t.1.2 : ℝ)).card : ℝ) ≤
      ((chenSiftedQuotientPrimeSource N (multiplier t) Z).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (siftedSource_subset_lowered N (multiplier t) Z _ hZ2)
  exact hcount.trans (currentChen_quotient_actualRosser_density_upper N (multiplier t)
    (Nat.ceil Z) Z R (Nat.le_ceil Z) (multiplier_coprime_lowered hN ht Z hZ) hR hZR)

/-- Arbitrary literal subselectors, including winner cells, keep the same
signed coefficient in all three finite sums. No analytic error is hidden. -/
theorem subselector_upper (N : ℕ) (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ))
    (T : Finset Four) (hT : T ⊆ source N E) (Z R : Four → ℝ)
    (hZ : ∀ t ∈ T, Z t ≤ (t.1.1 : ℝ))
    (hR : ∀ t ∈ T, 1 < R t) (hZR : ∀ t ∈ T, Z t ≤ R t) :
    (∑ t ∈ T, weight N t) ≤ (∑ t ∈ T, mainTerm N t (Z t) (R t)) +
      (∑ t ∈ T, signedAP N t (Z t) (R t)) - ∑ t ∈ T, signedCentre N t (Z t) (R t) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  exact row_upper hN (hT ht) (Z t) (R t) (hZ t ht) (hR t ht) (hZR t ht)

theorem winner_upper (N : ℕ) (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ))
    (bank : Finset ℕ) (eligible : ℕ → Four → Prop)
    (switched : Four → ℝ) (ordinary : ℕ → Four → ℝ) (c : ℕ) (Z R : Four → ℝ)
    (hZ : ∀ t ∈ cell (source N E) bank eligible switched ordinary c, Z t ≤ (t.1.1 : ℝ))
    (hR : ∀ t ∈ cell (source N E) bank eligible switched ordinary c, 1 < R t)
    (hZR : ∀ t ∈ cell (source N E) bank eligible switched ordinary c, Z t ≤ R t) :
    (∑ t ∈ cell (source N E) bank eligible switched ordinary c, weight N t) ≤
      (∑ t ∈ cell (source N E) bank eligible switched ordinary c, mainTerm N t (Z t) (R t)) +
      (∑ t ∈ cell (source N E) bank eligible switched ordinary c, signedAP N t (Z t) (R t)) -
      ∑ t ∈ cell (source N E) bank eligible switched ordinary c, signedCentre N t (Z t) (R t) := by
  exact subselector_upper N E hN _ (fun t ht => (Finset.mem_filter.mp ht).1) Z R hZ hR hZR

/-- Physical cutoff from the exact ordinary margin formula. A lower
prefix-box wall is sufficient; original p2 is never substituted for Z. -/
theorem reduced_physical_cutoff_le_first (N : ℕ) (hN : 1 ≤ (N : ℝ))
    (lower upper : U11Integral.LogFour) (nu delta xi rho : ℝ) (hxi : 0 ≤ xi)
    (t : Four) (hfirst : (N : ℝ) ^ lower 3 ≤ (t.1.1 : ℝ)) :
    (N : ℝ) ^ (U11SelectedLargest.reducedCutoff lower upper nu delta xi rho) ≤ (t.1.1 : ℝ) := by
  have he : U11SelectedLargest.reducedCutoff lower upper nu delta xi rho ≤ lower 3 :=
    (min_le_left _ _).trans (by linarith)
  exact (Real.rpow_le_rpow_of_exponent_le hN he).trans hfirst

/-- The actual reduced cutoff and actual residual Rosser level satisfy
both finite upper-sieve legality conditions from their positive margins. -/
theorem reduced_physical_level_legal (N : ℕ) (hN : 1 < (N : ℝ))
    (lower upper : U11Integral.LogFour) (nu delta xi rho : ℝ)
    (hsmall : 0 < lower 3 - xi)
    (hmargin : 20 * delta < nu - U11SelectedLargest.prefixSum upper) (hrho : 0 < rho) :
    1 < (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta) ∧
      (N : ℝ) ^ (U11SelectedLargest.reducedCutoff lower upper nu delta xi rho) ≤
        (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta) := by
  have hn : 0 < nu - U11SelectedLargest.prefixSum upper - 20 * delta := by linarith
  refine ⟨Real.one_lt_rpow hN hn, ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  have hd : 0 < 2 + rho := by linarith
  have hquot : (nu - U11SelectedLargest.prefixSum upper - 20 * delta) / (2 + rho) ≤
      nu - U11SelectedLargest.prefixSum upper - 20 * delta := by
    apply (div_le_iff₀ hd).2
    nlinarith
  exact (min_le_right _ _).trans hquot

/-- Concrete ordinary reduced-cutoff row: the reciprocal-totient main
term is reached from the original p2-sifted count by proved inclusion.
All Rosser legality/coprimality suppliers are discharged by the actual
prefix lower wall and the source's explicit positive-margin conditions. -/
theorem reduced_row_upper (N : ℕ) (E : ℕ × ℕ → Prop) (hN : 1 < (N : ℝ))
    (t : Four) (ht : t ∈ source N E) (lower upper : U11Integral.LogFour)
    (nu delta xi rho : ℝ) (hxi : 0 ≤ xi) (hsmall : 0 < lower 3 - xi)
    (hmargin : 20 * delta < nu - U11SelectedLargest.prefixSum upper) (hrho : 0 < rho)
    (hfirst : (N : ℝ) ^ lower 3 ≤ (t.1.1 : ℝ)) :
    let Z := (N : ℝ) ^ U11SelectedLargest.reducedCutoff lower upper nu delta xi rho
    let R := (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta)
    weight N t ≤ mainTerm N t Z R + signedAP N t Z R - signedCentre N t Z R := by
  have hleg := reduced_physical_level_legal N hN lower upper nu delta xi rho hsmall hmargin hrho
  exact row_upper hN.le ht _ _
    (reduced_physical_cutoff_le_first N hN.le lower upper nu delta xi rho hxi t hfirst)
    hleg.1 hleg.2

/-- The fixed-parent arithmetic transfer is uniform over its labelled
positive family. All rows share the same actual residual sieve weight;
equal products from distinct four-label tuples are still counted twice. -/
theorem reduced_parent_family_upper (N : ℕ) (E : ℕ × ℕ → Prop) (hN : 1 < (N : ℝ))
    (T : Finset Four) (hT : T ⊆ source N E) (lower upper : U11Integral.LogFour)
    (nu delta xi rho : ℝ) (hxi : 0 ≤ xi) (hsmall : 0 < lower 3 - xi)
    (hmargin : 20 * delta < nu - U11SelectedLargest.prefixSum upper) (hrho : 0 < rho)
    (hfirst : ∀ t ∈ T, (N : ℝ) ^ lower 3 ≤ (t.1.1 : ℝ)) :
    let Z := (N : ℝ) ^ U11SelectedLargest.reducedCutoff lower upper nu delta xi rho
    let R := (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta)
    (∑ t ∈ T, weight N t) ≤ (∑ t ∈ T, mainTerm N t Z R) +
      (∑ t ∈ T, signedAP N t Z R) - ∑ t ∈ T, signedCentre N t Z R := by
  have hleg := reduced_physical_level_legal N hN lower upper nu delta xi rho hsmall hmargin hrho
  apply subselector_upper N E hN.le T hT
  · intro t ht
    exact reduced_physical_cutoff_le_first N hN.le lower upper nu delta xi rho hxi t (hfirst t ht)
  · exact fun _ _ => hleg.1
  · exact fun _ _ => hleg.2

end

end ImbalancedChen.P5Z.U11LoweredRosser
