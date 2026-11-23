import ImbalancedChen.CurrentChenP5SelectedMaskTransport
import ImbalancedChen.CurrentChenPairRosser
import ImbalancedChen.ActualLowerFirstExitDensityProjection

/-!
# Genuine even-exit lower rho on the original sixth quotient receivers

The coefficient is actualLowerSmallRoughRho, with its even-exit policy,
not the ordinary lower Rosser coefficient. Policies, small thresholds and
physical small-weight levels can vary with the labelled U6 pair. The
quotient is literally (N-P)/(p1*p2), and its real cutoff is N^(417/5000).

The finite lower inequality, signed AP decomposition, modulus-prime and
centre-prime corrections, and same-mask restriction are proved here.
No total support envelope, distribution estimate above sqrt(N), or
identification with the manuscript h248/nu kernel is asserted.

SOURCE ONLY: uncompiled; the companion transport import is also a draft.
-/

namespace ImbalancedChen.P5CausalRhoQuotientBridge

open scoped BigOperators
open Classical
open P5SelectedMaskTransport

noncomputable section

theorem quotient_sum_physicalDivisorSum (N b : ℕ) (S : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ q ∈ chenQuotientPrimeSource N b, physicalDivisorSum S rho q) =
      ∑ d ∈ S, rho d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d)) := by
  simpa only [physicalDivisorSum, supportedDivisorSum, Finset.sum_filter] using
    currentChen_quotient_sum_supportedDivisorSum N b S rho

/-- The same causal coefficient minorizes actual roughness on every
literal quotient-source point, including the quotient one. -/
theorem quotientSource_pointwise_minorant
    (retainEven : List ℕ → Bool) (N b cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ))
    {q : ℕ} (hq : q ∈ chenQuotientPrimeSource N b) :
    physicalDivisorSum (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualLowerSmallRoughRho retainEven N cap w z L) q ≤
        if ChenPrimeRough z q then (1 : ℝ) else 0 := by
  have h := actualLowerSmallRoughRho_minorant retainEven N cap w z L
    hL hwL hwz hzcap (q : ℤ)
  have hind : actualSmallRoughIndicator N z (q : ℤ) =
      if Nat.Coprime q (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
    unfold actualSmallRoughIndicator
    rw [← actualSmallPrimeProduct_coprime_natAbs_iff N cap z hzcap (q : ℤ)]
    simp only [Int.natAbs_natCast,
      currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap,
      Nat.coprime_comm]
  have hrough := chenPrimeRough_iff_coprime_sieveProduct z
    (chenQuotientPrimeSource_data hq).2.2
  simpa only [Int.natAbs_natCast, hind, ← hrough] using h

/-- Original additive-prime labels give the requested ChenQuotient
indicator, rather than a surrogate nonnegative lower polynomial. -/
theorem receiver_quotient_indicator_minorant
    (retainEven : List ℕ → Bool) (N b cap P : ℕ) (w z L : ℝ)
    (hP : P ∈ chenAdditivePrimeCarrier N)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (if b ∣ N - P then
      physicalDivisorSum (actualLowerSmallRoughModuli retainEven N cap w z)
        (actualLowerSmallRoughRho retainEven N cap w z L) ((N - P) / b) else 0) ≤
      if ChenQuotient b z (N - P) then (1 : ℝ) else 0 := by
  by_cases hd : b ∣ N - P
  · have hq : (N - P) / b ∈ chenQuotientPrimeSource N b :=
      Finset.mem_image.mpr ⟨P, mem_chenQuotientPrimeCarrier.mpr ⟨hP, hd⟩, rfl⟩
    simpa only [if_pos hd, ChenQuotient, hd, true_and] using
      quotientSource_pointwise_minorant retainEven N b cap w z L hL hwL hwz hzcap hq
  · have hnot : ¬ ChenQuotient b z (N - P) := fun h => hd h.1
    simp only [if_neg hd, if_neg hnot, le_refl]

theorem quotient_signed_sum_le_sifted
    (retainEven : List ℕ → Bool) (N b cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      actualLowerSmallRoughRho retainEven N cap w z L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) ≤
      ((chenSiftedQuotientPrimeSource N b z).card : ℝ) := by
  rw [← quotient_sum_physicalDivisorSum]
  calc
    _ ≤ ∑ q ∈ chenQuotientPrimeSource N b,
        if ChenPrimeRough z q then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      exact quotientSource_pointwise_minorant retainEven N b cap w z L
        hL hwL hwz hzcap hq
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedQuotientPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

private theorem rough_coprime_squarefree_small {b d : ℕ} {z : ℝ}
    (hb : ChenPrimeRough z b) (hd : Squarefree d)
    (hsmall : ∀ p ∈ d.primeFactors, (p : ℝ) < z) : Nat.Coprime b d := by
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  have hpprime := (Nat.mem_primeFactors.mp hp).1
  exact (hpprime.coprime_iff_not_dvd.mpr
    (fun hpb => (not_lt_of_ge (hb p hpprime hpb)) (hsmall p hp))).symm

/-- The actual small/rough support, including all retained rough
prefixes, is coprime to the genuine U6 multiplier. -/
theorem moduli_coprime_multiplier
    (retainEven : List ℕ → Bool) (N cap b : ℕ) (w z : ℝ)
    (hwz : w ≤ z) (hb : ChenPrimeRough z b) {d : ℕ}
    (hd : d ∈ actualLowerSmallRoughModuli retainEven N cap w z) : Nat.Coprime b d := by
  rcases Finset.mem_image.mp hd with ⟨⟨a, c⟩, hac, rfl⟩
  obtain ⟨ha, hc⟩ := Finset.mem_product.mp hac
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · apply rough_coprime_squarefree_small hb (actualSmallRosserSupport_squarefree N cap w ha)
    intro p hp
    exact ((actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha).2 p hp).trans_le hwz
  · apply rough_coprime_squarefree_small hb
      (fixedEvenRoughSupport_squarefree retainEven N cap w z hc)
    intro p hp
    exact mem_roughPrimeUniverse_upper
      (fixedEvenRoughSupport_primeFactors_mem retainEven N cap w z hc hp)

/-- Exact true-prime-AP main and signed errors at the full product b*d.
The lower causal rho is unchanged in all three terms. -/
theorem quotient_main_and_AP_errors
    (retainEven : List ℕ → Bool) (N cap b : ℕ) (w z L M : ℝ)
    (hwz : w ≤ z) (hb : ChenPrimeRough z b) :
    (∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      actualLowerSmallRoughRho retainEven N cap w z L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) =
      M / (Nat.totient b : ℝ) *
        physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) +
      (∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
        actualLowerSmallRoughRho retainEven N cap w z L d *
          chenQuotientPrimeAPError N M (b * d)) -
      ∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
        actualLowerSmallRoughRho retainEven N cap w z L d *
          chenCentrePrimeAPCount N N (b * d) := by
  simp only [physicalDensitySum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold chenQuotientPrimeAPError
  rw [Nat.totient_mul (moduli_coprime_multiplier retainEven N cap b w z hwz hb hd),
    Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Recentring at the full prime prefix retains the negative
modulus-prime atom and the actual centre-prime subtraction separately. -/
theorem quotient_main_primitive_and_prime_corrections
    (retainEven : List ℕ → Bool) (N cap b : ℕ) (w z L : ℝ)
    (hwz : w ≤ z) (hb : ChenPrimeRough z b) :
    (∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      actualLowerSmallRoughRho retainEven N cap w z L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) =
      ((chenPrimePrefix N).card : ℝ) / (Nat.totient b : ℝ) *
        physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) +
      (∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
        actualLowerSmallRoughRho retainEven N cap w z L d *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (b * d)) -
      (∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
        actualLowerSmallRoughRho retainEven N cap w z L d *
          (chenPrimeDivisorCount N (b * d) / (Nat.totient (b * d) : ℝ))) -
      ∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
        actualLowerSmallRoughRho retainEven N cap w z L d *
          chenCentrePrimeAPCount N N (b * d) := by
  have heq (k : ℕ) : chenQuotientPrimeAPError N ((chenPrimePrefix N).card : ℝ) k =
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N k -
        chenPrimeDivisorCount N k / (Nat.totient k : ℝ) := by
    have hAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N k =
        chenPrimeAPCount N N k := by simp [finiteCongruenceMass, chenPrimeAPCount]
    rw [finitePrimitiveDiscrepancy, hAP, chenPrimePrefix_coprime_mass]
    unfold chenQuotientPrimeAPError
    ring
  rw [quotient_main_and_AP_errors retainEven N cap b w z L
    ((chenPrimePrefix N).card : ℝ) hwz hb]
  simp_rw [heq, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

def active (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : Finset ℕ :=
  (actualLowerSmallRoughModuli retainEven N cap w z).filter
    (fun d => actualLowerSmallRoughRho retainEven N cap w z L d ≠ 0)

theorem sum_eq_active (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (f : ℕ → ℝ) :
    (∑ d ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      actualLowerSmallRoughRho retainEven N cap w z L d * f d) =
      ∑ d ∈ active retainEven N cap w z L,
        actualLowerSmallRoughRho retainEven N cap w z L d * f d := by
  simp only [active, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : actualLowerSmallRoughRho retainEven N cap w z L d = 0 <;> simp [h]

/-- Only the small factor is licensed below L by the actual producer.
The full modulus b*d is deliberately not assigned a square-root cap. -/
theorem active_small_factor (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) {d : ℕ} (hd : d ∈ active retainEven N cap w z L) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ c ∈ fixedEvenRoughSupport retainEven N cap w z,
        d = a * c ∧ (a : ℝ) < L ∧ fixedEvenRoughCoefficient retainEven N cap w z c ≠ 0 := by
  exact actualLowerSmallRoughRho_ne_zero_factors retainEven N cap w z L
    (Finset.mem_filter.mp hd).2

abbrev cutoff (N : ℕ) : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)

def rowEstimator (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : ℝ :=
  ∑ d ∈ actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N),
    actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t) d *
      (chenPrimeAPCount N N ((t.1 * t.2) * d) -
        chenCentrePrimeAPCount N N ((t.1 * t.2) * d))

theorem rowEstimator_le_actual (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ)
    (hgates : 1 < L t ∧ w t ≤ L t ∧ w t ≤ cutoff N) :
    rowEstimator N policy w L t ≤ sixthWeight N t := by
  exact quotient_signed_sum_le_sifted (policy t) N (t.1 * t.2) (Nat.ceil (cutoff N))
    (w t) (cutoff N) (L t) hgates.1 hgates.2.1 hgates.2.2 (Nat.le_ceil _)

/-- Literal sixth-selector membership supplies the rough multiplier
needed for the exact reciprocal-totient main-term dictionary. -/
theorem row_multiplier_rough {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ sixthSupport N) :
    ChenPrimeRough (cutoff N) (t.1 * t.2) := by
  have hd := chenY6PrimeSelector_sieve_data ht
  exact (chenPrimeRough_iff_coprime_sieveProduct (cutoff N) hd.2.1).mpr hd.2.2

/-- Literal b=p1*p2 specialization of the signed prime-AP identity.
The policy, w and enhanced physical small-weight level L remain per pair. -/
theorem rowEstimator_main_and_signed_AP (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ)
    (t : ℕ × ℕ) (ht : t ∈ sixthSupport N) (hwz : w t ≤ cutoff N) (M : ℝ) :
    rowEstimator N policy w L t =
      M / (Nat.totient (t.1 * t.2) : ℝ) *
        physicalDensitySum
          (actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N))
          (actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N))
            (w t) (cutoff N) (L t)) +
      (∑ d ∈ actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N),
        actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N))
          (w t) (cutoff N) (L t) d * chenQuotientPrimeAPError N M ((t.1 * t.2) * d)) -
      ∑ d ∈ actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N),
        actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N))
          (w t) (cutoff N) (L t) d * chenCentrePrimeAPCount N N ((t.1 * t.2) * d) := by
  exact quotient_main_and_AP_errors (policy t) N (Nat.ceil (cutoff N)) (t.1 * t.2)
    (w t) (cutoff N) (L t) M hwz (row_multiplier_rough ht)

theorem rowEstimator_primitive_and_prime_corrections (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ)
    (t : ℕ × ℕ) (ht : t ∈ sixthSupport N) (hwz : w t ≤ cutoff N) :
    rowEstimator N policy w L t =
      ((chenPrimePrefix N).card : ℝ) / (Nat.totient (t.1 * t.2) : ℝ) *
        physicalDensitySum
          (actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N))
          (actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N))
            (w t) (cutoff N) (L t)) +
      (∑ d ∈ actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N),
        actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N))
          (w t) (cutoff N) (L t) d *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((t.1 * t.2) * d)) -
      (∑ d ∈ actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N),
        actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N))
          (w t) (cutoff N) (L t) d *
          (chenPrimeDivisorCount N ((t.1 * t.2) * d) /
            (Nat.totient ((t.1 * t.2) * d) : ℝ))) -
      ∑ d ∈ actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N),
        actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N))
          (w t) (cutoff N) (L t) d * chenCentrePrimeAPCount N N ((t.1 * t.2) * d) := by
  exact quotient_main_primitive_and_prime_corrections (policy t) N (Nat.ceil (cutoff N))
    (t.1 * t.2) (w t) (cutoff N) (L t) hwz (row_multiplier_rough ht)

def estimatorSum (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ T, rowEstimator N policy w L t

theorem retainedSelector_eq_compl (N : ℕ) (eta : ℝ) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6RetainedSelector N E eta =
      (retainedSupport N eta).filter (fun t => ¬ E t) := by
  unfold currentChenUpsilon6RetainedSelector retainedSupport
  simp only [Finset.filter_filter, and_comm]

/-- Exact full-minus-selected estimator restriction with genuine causal
rho and arbitrary pair-dependent enhanced levels and policies. -/
theorem estimator_full_sub_selected_eq_retained (N : ℕ) (eta : ℝ)
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ)
    (E : ℕ × ℕ → Prop) :
    estimatorSum N policy w L (retainedSupport N eta) -
      estimatorSum N policy w L ((retainedSupport N eta).filter E) =
      estimatorSum N policy w L (currentChenUpsilon6RetainedSelector N E eta) := by
  have h := Finset.sum_filter_add_sum_filter_not (retainedSupport N eta) E
    (rowEstimator N policy w L)
  unfold estimatorSum
  rw [retainedSelector_eq_compl]
  linarith only [h]

theorem estimator_retained_le_actual (N : ℕ) (eta : ℝ)
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ)
    (E : ℕ × ℕ → Prop)
    (hgates : ∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
      1 < L t ∧ w t ≤ L t ∧ w t ≤ cutoff N) :
    estimatorSum N policy w L (retainedSupport N eta) -
      estimatorSum N policy w L ((retainedSupport N eta).filter E) ≤
      currentChenUpsilon6Retained N E eta := by
  rw [estimator_full_sub_selected_eq_retained]
  apply Finset.sum_le_sum
  intro t ht
  exact rowEstimator_le_actual N policy w L t (hgates t ht)

/-- The actual lower attachment projection scales by the quotient's
literal M/phi(b) main factor. No h248 or nu dictionary is assumed. -/
theorem exists_quotient_full_density_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 ≤ r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ retainEven : List ℕ → Bool, ∀ b : ℕ, ∀ M : ℝ, 0 ≤ M →
            M / (Nat.totient b : ℝ) *
              (reciprocalTotientDensity
                (fixedEvenRoughSupport retainEven N cap 0 ((N : ℝ) ^ (nu * r)))
                (fixedEvenRoughCoefficient retainEven N cap 0 ((N : ℝ) ^ (nu * r))) -
                eta * singularSeries N / Real.log (N : ℝ)) ≤
            M / (Nat.totient b : ℝ) * physicalDensitySum
              (actualLowerSmallRoughModuli retainEven N cap
                ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)))
              (actualLowerSmallRoughRho retainEven N cap
                ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
                ((N : ℝ) ^ (nu * epsilon))) := by
  obtain ⟨epsilon, heps, heps8, hepsMax, hepsr, N₀, hN₀, hproj⟩ :=
    exists_actualLowerSmallRoughRho_density_ge_full_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, heps, heps8, hepsMax, hepsr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap retainEven b M hM
  exact mul_le_mul_of_nonneg_left (hproj N hN hEven cap hcap retainEven)
    (div_nonneg hM (Nat.cast_nonneg _))

end

end ImbalancedChen.P5CausalRhoQuotientBridge
