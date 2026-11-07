import ImbalancedChen.CurrentChenP5OriginalU5CausalFinite
import ImbalancedChen.P2SameQSeedCoprimeMean

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original U5 prime source excludes every prime dividing N.  The
immutable receiver below keeps precisely this exclusion in the actual
same-Q count state.  Removing the selected prefix from the sifted integer
requires a proved rough-prefix gate; this gate is supplied at the original
U5 cutoff.  No analogous gate is asserted for arbitrary later queries.

The AP dictionary retains the same signed Rosser coefficient and the true
finite coprime population.  In particular no enhanced distribution bound,
positive seed, H248 soundness, or physical W adoption is an input.
-/
namespace ImbalancedChen.P5OriginalU5FrozenSource

noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions P2SameQSeedCoprimeMean
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical BigOperators

/-- One fixed predicate of the original prime, unchanged by all descendants. -/
def receiver (N ell : ℕ) : Prop := ell.Coprime N

theorem receiverPrimes_eq_actualSource (N : ℕ) :
    receiverPrimes N (receiver N) = chenAdditivePrimeCarrier N := by
  ext ell
  simp only [receiverPrimes, receiver, mem_filter, mem_range, Nat.lt_succ_iff,
    mem_chenAdditivePrimeCarrier_iff_le]
  tauto

/-- Exact original prime labels, including their centre-divisor deletion. -/
theorem divisible_receiver_eq_actualSource (N d : ℕ) :
    (goldbachDivisible N d).filter (receiver N) =
      (chenAdditivePrimeCarrier N).filter (fun ell => d ∣ N - ell) := by
  ext ell
  simp only [goldbachDivisible, receiver, mem_filter, mem_range,
    Nat.lt_succ_iff, mem_chenAdditivePrimeCarrier_iff_le]
  tauto

/-- The d*N mask can be removed from the residual source only because the
old prefix has no prime below z and the quotient is coprime to N. -/
theorem sifted_iff_rough {N d n : ℕ} {z : ℝ}
    (hd : ChenPrimeRough z d) (hn : n.Coprime N) :
    Sifted (d * N) n z ↔ ChenPrimeRough z n := by
  constructor
  · intro hs q hq hqn
    by_contra hlow
    have hqz : (q : ℝ) < z := lt_of_not_ge hlow
    have hqd : q.Coprime d := hq.coprime_iff_not_dvd.mpr
      (fun hdiv => (not_lt_of_ge (hd q hq hdiv)) hqz)
    have hqN : q.Coprime N := hn.of_dvd_left hqn
    exact hs q hq (Nat.coprime_mul_iff_right.mpr ⟨hqd, hqN⟩) hqz hqn
  · intro hr q hq _ hqz hqn
    exact (not_lt_of_ge (hr q hq hqn)) hqz

theorem receiver_quotient_coprime {N d ell : ℕ}
    (hell : ell ∈ chenAdditivePrimeCarrier N) (hd : d ∣ N - ell) :
    ((N - ell) / d).Coprime N := by
  have hq : (N - ell) / d ∈ chenQuotientPrimeSource N d :=
    mem_image.mpr ⟨ell, mem_chenQuotientPrimeCarrier.mpr ⟨hell, hd⟩, rfl⟩
  exact (chenQuotientPrimeSource_data hq).2.2

/-- The independently defined frozen carrier equals the true quotient
source in original prime labels.  Neither injectivity nor a desired count
identity is assumed.  Strict sifting keeps equality at z. -/
theorem frozenCarrier_eq_original_labels (N d : ℕ) (z : ℝ)
    (hdrough : ChenPrimeRough z d) :
    frozenCarrier N d (receiver N) z =
      (chenAdditivePrimeCarrier N).filter
        (fun ell => d ∣ N - ell ∧ ChenPrimeRough z ((N - ell) / d)) := by
  unfold frozenCarrier
  rw [(source_double_sieve_carriers N d z).1]
  ext ell
  simp only [sieveCarrier, receiver, mem_filter, mem_range,
    Nat.lt_succ_iff, mem_chenAdditivePrimeCarrier_iff_le]
  constructor
  · rintro ⟨⟨hle, hp, hd, hs⟩, hcop⟩
    have hell : ell ∈ chenAdditivePrimeCarrier N :=
      mem_chenAdditivePrimeCarrier_iff_le.mpr ⟨hle, hp, hcop⟩
    exact ⟨⟨hle, hp, hcop⟩, hd,
      (sifted_iff_rough hdrough (receiver_quotient_coprime hell hd)).mp hs⟩
  · rintro ⟨⟨hle, hp, hcop⟩, hd, hr⟩
    have hell : ell ∈ chenAdditivePrimeCarrier N :=
      mem_chenAdditivePrimeCarrier_iff_le.mpr ⟨hle, hp, hcop⟩
    exact ⟨⟨hle, hp, hd,
      (sifted_iff_rough hdrough (receiver_quotient_coprime hell hd)).mpr hr⟩, hcop⟩

/-- Cardinality uses the established injective original-prime/quotient map.
Unit quotients and repeated residual prime factors remain present. -/
theorem frozenCount_eq_original_count (N d : ℕ) (z : ℝ)
    (hdrough : ChenPrimeRough z d) :
    (frozenCount N d (receiver N) z : ℝ) =
      ((chenSiftedQuotientPrimeSource N d z).card : ℝ) := by
  have hc : (chenSiftedQuotientPrimeSource N d z).card =
      (frozenCarrier N d (receiver N) z).card := by
    rw [frozenCarrier_eq_original_labels N d z hdrough]
    exact chenQuotientPrimeSource_filter_card N d (ChenPrimeRough z)
  simp only [frozenCount, Int.cast_natCast, hc]

/-- Exact U5 occurrence, before any analytic limit or table interpretation. -/
theorem originalU5_eq_frozen_count_sum (N : ℕ) :
    currentChenUpsilon5 N =
      ∑ t ∈ P5OriginalU5CausalFinite.pairSupport N,
        (frozenCount N (t.1 * t.2) (receiver N)
          (P5OriginalU5CausalFinite.cutoff N) : ℝ) := by
  rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
  apply sum_congr rfl
  intro t ht
  exact (frozenCount_eq_original_count N (t.1 * t.2) _
    (P5OriginalU5CausalFinite.row_multiplier_rough ht)).symm

theorem coprimePopulation_eq_actualSource_mass (N m : ℕ) :
    (coprimePopulation N (receiver N) m : ℝ) =
      finiteCoprimeMass (chenAdditivePrimeCarrier N) (fun _ => 1) m := by
  rw [coprimePopulation, receiverPrimes_eq_actualSource]
  simp only [finiteCoprimeMass, sum_const, nsmul_eq_mul, mul_one]

/-- The error is the primitive discrepancy of the actual original prime
source, not that of a freely chosen frozen population. -/
theorem finiteAPDiscrepancy_eq_actualSource (N m : ℕ) :
    finiteAPDiscrepancy N (receiver N) m =
      finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N m := by
  unfold finiteAPDiscrepancy
  rw [divisible_receiver_eq_actualSource,
    chenAdditivePrimeCarrier_filter_dvd_eq_AP, coprimePopulation_eq_actualSource_mass]
  simp only [finitePrimitiveDiscrepancy, finiteCongruenceMass,
    sum_const, nsmul_eq_mul, mul_one]

/-- The remaining true-li shift contains the actual modulus-prime loss.
The receiver deletion is already in the total original-source cardinality. -/
theorem finiteMeanShift_eq_actualSource {N m : ℕ} (hm : m.Coprime N) :
    finiteMeanShift N (receiver N) m =
      (((chenAdditivePrimeCarrier N).card : ℝ) - logarithmicIntegral N -
        chenPrimeDivisorCount N m) / (Nat.totient m : ℝ) := by
  unfold finiteMeanShift
  rw [coprimePopulation_eq_actualSource_mass,
    chenAdditivePrimeCarrier_coprime_mass hm]
  ring

/-- Exact bridge to the complete-prime-prefix discrepancy used by the
sharp original-prime supplier.  The centre deletion is an AP correction,
not merely the deletion of the zero-difference endpoint. -/
theorem receiver_error_eq_sharp_prime_error (N m : ℕ) :
    finiteAPDiscrepancy N (receiver N) m + finiteMeanShift N (receiver N) m =
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N m +
        (((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N -
          chenPrimeDivisorCount N m) / (Nat.totient m : ℝ) -
        chenCentrePrimeAPCount N N m := by
  have hAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N m =
      chenPrimeAPCount N N m := by
    simp only [finiteCongruenceMass, chenPrimeAPCount, sum_const, nsmul_eq_mul, mul_one]
  unfold finiteAPDiscrepancy finiteMeanShift
  rw [divisible_receiver_eq_actualSource,
    chenAdditivePrimeCarrier_filter_dvd_eq_AP, chenAdditivePrimeCarrier_AP_count,
    finitePrimitiveDiscrepancy, hAP, chenPrimePrefix_coprime_mass]
  ring

/-- Every signed ordinary seed coefficient carries exactly this original
AP discrepancy and this finite-mean shift.  The full modulus is d*r. -/
theorem frozenRemainder_eq_actual_signed_AP (side : Bool) (N d D : ℕ)
    (z : ℝ) (hdN : d.Coprime N) :
    frozenRemainder side N d D (receiver N) z =
      ∑ r ∈ (ordinarySievePrimeProduct (d * N) z).divisors,
        ordinaryRosserWeight side N d D z r *
          (finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N (d*r) +
            (((chenAdditivePrimeCarrier N).card : ℝ) - logarithmicIntegral N -
              chenPrimeDivisorCount N (d*r)) / (Nat.totient (d*r) : ℝ)) := by
  rw [frozenRemainder_eq_coprime_split]
  unfold signedAPDiscrepancy signedMeanShift
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  rw [finiteAPDiscrepancy_eq_actualSource,
    finiteMeanShift_eq_actualSource (complete_modulus_coprime hdN hr)]
  ring

/-- Same-coefficient sharp-prefix form.  No absolute value or rowwise
distribution estimate is substituted for the signed AP sum. -/
theorem frozenRemainder_eq_sharp_prime_error (side : Bool) (N d D : ℕ) (z : ℝ) :
    frozenRemainder side N d D (receiver N) z =
      ∑ r ∈ (ordinarySievePrimeProduct (d * N) z).divisors,
        ordinaryRosserWeight side N d D z r *
          (finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (d*r) +
            (((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N -
              chenPrimeDivisorCount N (d*r)) / (Nat.totient (d*r) : ℝ) -
            chenCentrePrimeAPCount N N (d*r)) := by
  rw [frozenRemainder_eq_coprime_split]
  unfold signedAPDiscrepancy signedMeanShift
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  rw [← mul_add, receiver_error_eq_sharp_prime_error]

end
end ImbalancedChen.P5OriginalU5FrozenSource
