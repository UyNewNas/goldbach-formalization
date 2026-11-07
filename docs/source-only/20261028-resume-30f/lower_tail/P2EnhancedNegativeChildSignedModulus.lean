import ImbalancedChen.P2EnhancedNegativeChildPhysicalSupport
import ImbalancedChen.P2EnhancedTwentyOneChildCorrection
import ImbalancedChen.ChenQuotientSieveRemainders

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The original three negative windows are marked before multiplying their
actual lower Rosser coefficient. Signed pushforward retains all coincident
physical moduli, not a unit coefficient. Count, exact coprime population
mean and signed discrepancy use exactly that same physical coefficient.
Nonprimitive classes remain an explicit original-count fallback. -/

namespace ImbalancedChen.P2EnhancedNegativeChildSignedModulus

noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve P2EnhancedTwentyOneSameQWeighted
open P2EnhancedNegativeChildRosser
open P2OriginalNegativeSingleSameQSupport (negativeWindow negativeParameter lowerCutoff)

abbrev Label := Σ _d : ℕ, Σ _j : Fin 3, ℕ
abbrev Mark := Σ _t : Label, ℕ

def labels (N : ℕ) (Q : ℝ) (D : Finset ℕ) : Finset Label :=
  D.sigma (fun d => Finset.univ.sigma (fun j => negativeWindow N Q d j))

def activeRows (N : ℕ) (Q : ℝ) (t : Label) : Finset ℕ :=
  (childSupport N Q t.1).filter (fun k => childCoefficient N Q t.1 t.2.2 k ≠ 0)

def marks (N : ℕ) (Q : ℝ) (D : Finset ℕ) : Finset Mark :=
  (labels N Q D).sigma (activeRows N Q)

def physicalModulus (m : Mark) : ℕ := m.1.1 * m.1.2.2 * m.2

def markWeight (N : ℕ) (Q : ℝ) (sigma : ℕ → ℝ) (m : Mark) : ℝ :=
  sigma m.1.1 * childCoefficient N Q m.1.1 m.1.2.2 m.2

def modulusSupport (N : ℕ) (Q : ℝ) (D : Finset ℕ) : Finset ℕ :=
  (marks N Q D).image physicalModulus

def modulusFibre (N : ℕ) (Q : ℝ) (D : Finset ℕ) (q : ℕ) : Finset Mark :=
  (marks N Q D).filter (fun m => physicalModulus m = q)

def physicalCoefficient (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ m ∈ modulusFibre N Q D q, markWeight N Q sigma m

def markedMultiplicityMass (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ m ∈ modulusFibre N Q D q, sigma m.1.1

def sourceTestSum (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (F : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * ∑ j : Fin 3, ∑ p ∈ negativeWindow N Q d j,
    ∑ k ∈ childSupport N Q d, childCoefficient N Q d p k * F (d * p * k)

/-- This is the actual three-window coefficient, before any absolute
values, with the original occurrence multiplicity j intact. -/
theorem sourceTestSum_eq_marks (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (F : ℕ → ℝ) :
    sourceTestSum N Q D sigma F =
      ∑ m ∈ marks N Q D, markWeight N Q sigma m * F (physicalModulus m) := by
  unfold sourceTestSum marks labels
  simp only [Finset.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  unfold activeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hz : childCoefficient N Q d p k = 0 <;>
    simp [markWeight, physicalModulus, hz, mul_assoc]

/-- Equal physical products are summed with their signs. No injectivity
or boundedness of the resulting physical coefficient is presumed. -/
theorem actual_signed_pushforward (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (F : ℕ → ℝ) :
    sourceTestSum N Q D sigma F = ∑ q ∈ modulusSupport N Q D,
      physicalCoefficient N Q D sigma q * F q := by
  rw [sourceTestSum_eq_marks]
  have hf := Finset.sum_fiberwise_of_maps_to (s := marks N Q D)
    (t := modulusSupport N Q D) (g := physicalModulus)
    (fun m hm => Finset.mem_image_of_mem physicalModulus hm)
    (fun m => markWeight N Q sigma m * F (physicalModulus m))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q hq
  unfold physicalCoefficient modulusFibre
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

theorem mark_original_data {N : ℕ} {Q : ℝ} {D : Finset ℕ} {m : Mark}
    (hm : m ∈ marks N Q D) :
    m.1.1 ∈ D ∧ m.1.2.2 ∈ negativeWindow N Q m.1.1 m.1.2.1 ∧
      childCoefficient N Q m.1.1 m.1.2.2 m.2 ≠ 0 := by
  obtain ⟨hl, hk⟩ := Finset.mem_sigma.mp hm
  obtain ⟨hd, hjp⟩ := Finset.mem_sigma.mp hl
  obtain ⟨hj, hp⟩ := Finset.mem_sigma.mp hjp
  exact ⟨hd, hp, (Finset.mem_filter.mp hk).2⟩

/-- A genuine coefficient norm bound retains the complete weighted
occurrence multiplicity. It does not replace rho by a unit coefficient. -/
theorem physicalCoefficient_abs_le_marked_mass (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (q : ℕ) :
    |physicalCoefficient N Q D sigma q| ≤ markedMultiplicityMass N Q D sigma q := by
  unfold physicalCoefficient markedMultiplicityMass
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  have hdata := mark_original_data (Finset.mem_filter.mp hm).1
  have hs := hsigma _ hdata.1
  have hb : |childCoefficient N Q m.1.1 m.1.2.2 m.2| ≤ 1 :=
    actualSmallRosserMinus_abs_le_one _ _ _ _ _
  unfold markWeight
  rw [abs_mul, abs_of_nonneg hs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hs

/-- The full arithmetic modulus bound is derived from each actual active
coefficient at its literal original child level. -/
theorem physical_support {N : ℕ} {Q : ℝ} {D : Finset ℕ}
    (hd : ∀ d ∈ D, 0 < d) {q : ℕ} (hq : q ∈ modulusSupport N Q D) :
    0 < q ∧ (q : ℝ) < Q := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hdm, hp, hk⟩ := mark_original_data hm
  have hpData := mem_primeWindow.mp hp
  have hact := childCoefficient_active_fullQ (hd _ hdm) hpData.1 hpData.2.2.1 hk
  have hkact := actualSmallRosserMinus_active hk
  have hkpos : 0 < m.2 := Nat.pos_of_ne_zero hkact.2.2.1
  exact ⟨Nat.mul_pos (Nat.mul_pos (hd _ hdm) hpData.1.pos) hkpos, hact.1⟩

theorem physical_coprime_of_old_coprime {N : ℕ} {Q : ℝ} {D : Finset ℕ}
    (hdN : ∀ d ∈ D, d.Coprime N) {q : ℕ} (hq : q ∈ modulusSupport N Q D) : q.Coprime N := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hdm, hp, hk⟩ := mark_original_data hm
  have hpData := mem_primeWindow.mp hp
  have hkact := actualSmallRosserMinus_active hk
  have hkcop := (childSupport_coprime_prefix hpData.1 hpData.2.2.1 hkact.1).2
  exact ((hdN _ hdm).mul_left hpData.2.1).mul_left hkcop

theorem model_mean_pushforward (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeMean N Q D sigma =
      ∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q * childAPMean N q := by
  rw [← actual_signed_pushforward]
  simp [sourceTestSum, P2EnhancedTwentyOneChildCorrection.negativeMean,
    P2EnhancedTwentyOneChildCorrection.localNegativeMean, windowMean, childMean,
    negativeWindow, lowerCutoff, negativeParameter, Fin.sum_univ_three]

theorem model_error_pushforward (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeSignedRemainder N Q D sigma =
      ∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q *
        (rawPrimeAPCount N q - childAPMean N q) := by
  rw [← actual_signed_pushforward]
  simp [sourceTestSum, P2EnhancedTwentyOneChildCorrection.negativeSignedRemainder,
    P2EnhancedTwentyOneChildCorrection.localNegativeRemainder, windowSignedRemainder,
    childSignedRemainder, negativeWindow, lowerCutoff, negativeParameter, Fin.sum_univ_three]

theorem finite_mean_pushforward (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeFiniteCoprimeMean N Q D sigma =
      ∑ q ∈ modulusSupport N Q D,
        physicalCoefficient N Q D sigma q * finiteCoprimeAPMean N q := by
  rw [← actual_signed_pushforward]
  simp [sourceTestSum, P2EnhancedTwentyOneChildCorrection.negativeFiniteCoprimeMean,
    windowFiniteCoprimeMean, childFiniteCoprimeMean, negativeWindow,
    lowerCutoff, negativeParameter, Fin.sum_univ_three]

theorem finite_error_pushforward (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeFiniteSignedRemainder N Q D sigma =
      ∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q *
        (rawPrimeAPCount N q - finiteCoprimeAPMean N q) := by
  rw [← actual_signed_pushforward]
  simp [sourceTestSum, P2EnhancedTwentyOneChildCorrection.negativeFiniteSignedRemainder,
    windowFiniteSignedRemainder, childFiniteSignedRemainder, negativeWindow,
    lowerCutoff, negativeParameter, Fin.sum_univ_three]

/-- Source AP counts are the existing inclusive classical prime AP counts,
not a source redefined to fit a proposed discrepancy formula. -/
theorem rawPrimeAPCount_eq_existing (N q : ℕ) : rawPrimeAPCount N q = chenPrimeAPCount N N q := by
  have hc : rawPrimeAPCarrier N q =
      (chenPrimePrefix N).filter (fun ell => Nat.ModEq q ell N) := by
    ext ell
    simp only [rawPrimeAPCarrier, chenPrimePrefix, Finset.mem_filter]
    constructor
    · rintro ⟨hr, hp, hd⟩
      exact ⟨⟨hr, hp⟩, (dvd_sub_iff_modEq_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))).mp hd⟩
    · rintro ⟨⟨hr, hp⟩, hd⟩
      exact ⟨hr, hp, (dvd_sub_iff_modEq_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))).mpr hd⟩
  exact congrArg (fun S : Finset ℕ => (S.card : ℝ)) hc

theorem population_eq_existing (N q : ℕ) :
    coprimePrimePopulation N q = finiteCoprimeMass (chenPrimePrefix N) (fun _ => 1) q := by
  have hprefix : rawPrimeAPCarrier N 1 = chenPrimePrefix N := by
    ext ell
    simp [rawPrimeAPCarrier, chenPrimePrefix]
  simp only [coprimePrimePopulation, hprefix, finiteCoprimeMass,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A primitive physical class gives the EXACT existing coprime-normalized
prime discrepancy. Nonprimitive classes retain their actual raw count. -/
theorem finite_error_eq_classical_or_fallback (N q : ℕ) :
    rawPrimeAPCount N q - finiteCoprimeAPMean N q =
      if q.Coprime N then finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q
      else rawPrimeAPCount N q := by
  by_cases hcop : q.Coprime N
  · rw [finiteCoprimeAPMean, if_pos hcop, if_pos hcop,
      rawPrimeAPCount_eq_existing, population_eq_existing]
    simp [finitePrimitiveDiscrepancy, finiteCongruenceMass, chenPrimeAPCount]
  · simp only [finiteCoprimeAPMean, if_neg hcop, sub_zero]

/-- The signed total is now an actual original prime discrepancy packet,
plus its exact nonprimitive fallback, on the SAME physical rho. -/
theorem finite_error_exact_packet (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeFiniteSignedRemainder N Q D sigma =
      (∑ q ∈ (modulusSupport N Q D).filter (fun q => q.Coprime N),
        physicalCoefficient N Q D sigma q *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) +
      ∑ q ∈ (modulusSupport N Q D).filter (fun q => ¬ q.Coprime N),
        physicalCoefficient N Q D sigma q * rawPrimeAPCount N q := by
  rw [finite_error_pushforward]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [finite_error_eq_classical_or_fallback]
  by_cases hcop : q.Coprime N <;> simp [hcop]

theorem finite_error_packet_of_old_coprime (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hdN : ∀ d ∈ D, d.Coprime N) :
    P2EnhancedTwentyOneChildCorrection.negativeFiniteSignedRemainder N Q D sigma =
      ∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q *
        finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q := by
  rw [finite_error_pushforward]
  apply Finset.sum_congr rfl
  intro q hq
  rw [finite_error_eq_classical_or_fallback, if_pos (physical_coprime_of_old_coprime hdN hq)]

theorem model_error_eq_classical_or_fallback (N q : ℕ) :
    rawPrimeAPCount N q - childAPMean N q =
      if q.Coprime N then
        chenQuotientPrimeAPError N
          (AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) q
      else rawPrimeAPCount N q := by
  by_cases hcop : q.Coprime N
  · rw [childAPMean, if_pos hcop, if_pos hcop, rawPrimeAPCount_eq_existing]
    rfl
  · simp only [childAPMean, if_neg hcop, sub_zero]

theorem model_error_exact_packet (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeSignedRemainder N Q D sigma =
      (∑ q ∈ (modulusSupport N Q D).filter (fun q => q.Coprime N),
        physicalCoefficient N Q D sigma q * chenQuotientPrimeAPError N
          (AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) q) +
      ∑ q ∈ (modulusSupport N Q D).filter (fun q => ¬ q.Coprime N),
        physicalCoefficient N Q D sigma q * rawPrimeAPCount N q := by
  rw [model_error_pushforward]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [model_error_eq_classical_or_fallback]
  by_cases hcop : q.Coprime N <;> simp [hcop]

/-- Reuse the existing true prime-prefix coprime-mass identity. The
finite-to-li shift retains the whole modulus-prime divisor correction. -/
theorem population_eq_pi_sub_prime_divisors (N q : ℕ) :
    coprimePrimePopulation N q =
      ((chenPrimePrefix N).card : ℝ) - chenPrimeDivisorCount N q := by
  rw [population_eq_existing, chenPrimePrefix_coprime_mass]

theorem finite_mean_shift_exact (N q : ℕ) :
    finiteCoprimeAPMean N q - childAPMean N q =
      if q.Coprime N then
        (((chenPrimePrefix N).card : ℝ) -
          AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) /
            (Nat.totient q : ℝ) - chenPrimeDivisorCount N q / (Nat.totient q : ℝ)
      else 0 := by
  by_cases hcop : q.Coprime N
  · rw [finiteCoprimeAPMean, childAPMean, if_pos hcop, if_pos hcop,
      if_pos hcop, population_eq_pi_sub_prime_divisors]
    ring
  · simp only [finiteCoprimeAPMean, childAPMean, if_neg hcop, sub_self]

/-- Exact physical signed finite-to-li correction. PNT and modulus-prime
payment are not invoked until AFTER the same-rho identity is established. -/
theorem finite_mean_minus_model_exact (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeFiniteCoprimeMean N Q D sigma -
        P2EnhancedTwentyOneChildCorrection.negativeMean N Q D sigma =
      ∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q *
        (if q.Coprime N then
          (((chenPrimePrefix N).card : ℝ) -
            AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) /
              (Nat.totient q : ℝ) - chenPrimeDivisorCount N q / (Nat.totient q : ℝ)
        else 0) := by
  rw [finite_mean_pushforward, model_mean_pushforward, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_sub, finite_mean_shift_exact]

/-- Absolute values are taken only after signed physical regrouping.
This is the actual analytic error awaiting original PP/distribution,
not an assumed small-error conclusion. -/
theorem abs_model_error_le_physical_packet (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    |P2EnhancedTwentyOneChildCorrection.negativeSignedRemainder N Q D sigma| ≤
      ∑ q ∈ modulusSupport N Q D, |physicalCoefficient N Q D sigma q| *
        |rawPrimeAPCount N q - childAPMean N q| := by
  rw [model_error_pushforward]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun q => physicalCoefficient N Q D sigma q * (rawPrimeAPCount N q - childAPMean N q))
    (modulusSupport N Q D)

end
end ImbalancedChen.P2EnhancedNegativeChildSignedModulus
