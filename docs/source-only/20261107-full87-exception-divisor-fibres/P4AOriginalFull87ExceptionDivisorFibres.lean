import ImbalancedChen.P4AOriginalFull87TerminalPrimeExceptionBudget
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: both actual prime-exception absolute invoices can be reindexed by
arithmetic divisibility on the SAME signed full-beta physical modulus
population. The centre invoice is carried only by true d | (N-p) fibres
with p prime and p | N; the modulus invoice only by true p | d fibres
with p in the original inclusive prime prefix. In particular d=0 is
handled by totalized division, not an undeclared positivity premise.

This supplies the precise finite divisor-fibre expressions needed before
any endpoint or same-rho H_N estimate. It does not assert any such estimate
or pay a compiler/density reserve.
-/

namespace ImbalancedChen.P4AOriginalFull87ExceptionDivisorFibres
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87EighthPrimeMeanLedger
open P4AOriginalFull87TerminalPrimeExceptionBudget
open P4AOriginalFull87LicensedSixthPolicy

/-- The original centre-excluded primes; no substitution of a different
source or enlargement to every prime below N. -/
def centrePrimeFactors (N : ℕ) : Finset ℕ :=
  (chenPrimePrefix N).filter (fun p => p ∣ N)

private theorem centre_AP_filter_eq_divisor_filter (N d : ℕ) :
    (chenPrimePrefix N).filter (fun p => Nat.ModEq d p N ∧ p ∣ N) =
      (centrePrimeFactors N).filter (fun p => d ∣ N - p) := by
  classical
  ext p
  simp only [Finset.mem_filter, centrePrimeFactors]
  constructor
  · rintro ⟨hp, ⟨hcong, hdiv⟩⟩
    have hpN : p ≤ N := (mem_chenPrimePrefix.mp hp).1
    exact ⟨⟨hp, hdiv⟩, (dvd_sub_iff_modEq_of_le hpN).mpr hcong⟩
  · rintro ⟨⟨hp, hdiv⟩, hsub⟩
    have hpN : p ≤ N := (mem_chenPrimePrefix.mp hp).1
    exact ⟨hp, ⟨(dvd_sub_iff_modEq_of_le hpN).mp hsub, hdiv⟩⟩

/-- Exact centre correction: a genuine divisor incidence on N-p. The
original prime-prefix endpoint p <= N is essential to the subtraction. -/
theorem centrePrimeAPCount_eq_divisor_fibres (N d : ℕ) :
    chenCentrePrimeAPCount N N d =
      ∑ p ∈ centrePrimeFactors N, if d ∣ N - p then (1 : ℝ) else 0 := by
  classical
  unfold chenCentrePrimeAPCount
  rw [centre_AP_filter_eq_divisor_filter]
  calc
    (((centrePrimeFactors N).filter (fun p => d ∣ N - p)).card : ℝ) =
      ∑ p ∈ (centrePrimeFactors N).filter (fun p => d ∣ N - p), (1 : ℝ) := by
        simp
    _ = ∑ p ∈ centrePrimeFactors N, if d ∣ N - p then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]

/-- The primitive mean's modulus-prime correction is also a finite
incidence sum, now in the complementary direction p | d. -/
theorem modulusPrimeTerm_eq_divisor_fibres (N d : ℕ) :
    modulusPrimeTerm N d =
      ∑ p ∈ chenPrimePrefix N,
        if p ∣ d then (1 : ℝ) / (Nat.totient d : ℝ) else 0 := by
  classical
  have hcard :
      ((((chenPrimePrefix N).filter (fun p => p ∣ d)).card : ℝ)) =
        ∑ p ∈ chenPrimePrefix N, if p ∣ d then (1 : ℝ) else 0 := by
    calc
      _ = ∑ p ∈ (chenPrimePrefix N).filter (fun p => p ∣ d), (1 : ℝ) := by
        simp
      _ = _ := by rw [Finset.sum_filter]
  unfold modulusPrimeTerm chenPrimeDivisorCount
  rw [hcard, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∣ d <;> simp [hp]

/-- Actual centre divisor-fibre invoice, with the physical full modulus
and sign-attached rho exactly as stored in the original two policies. -/
def centreDivisorInvoice (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ p ∈ centrePrimeFactors N,
    ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun d => d ∣ N - p),
      |actualSmallRoughRho (P false) N cap w z L d|

/-- Actual modulus-prime divisor-fibre invoice, retaining the precise
prime prefix rather than a centre-independent omega(d) upper cover. -/
def modulusDivisorInvoice (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ p ∈ chenPrimePrefix N,
    ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
        (fun d => p ∣ d),
      |actualSmallRoughRho (P false) N cap w z L d| /
        (Nat.totient d : ℝ)

/-- No generic weight assumption: the original centre absolute sum is
EXACTLY the actual divisor-fibre invoice. All physical multiplicities
already aggregated in the original rho are retained. -/
theorem absolutePhysical_centre_eq_divisor_invoice
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    absolutePhysical P N cap w z L (chenCentrePrimeAPCount N N) =
      centreDivisorInvoice P N cap w z L := by
  classical
  have hterm (d : ℕ) : |chenCentrePrimeAPCount N N d| =
      ∑ p ∈ centrePrimeFactors N,
        if d ∣ N - p then (1 : ℝ) else 0 := by
    rw [abs_of_nonneg (centrePrimeTerm_nonneg N d)]
    exact centrePrimeAPCount_eq_divisor_fibres N d
  unfold absolutePhysical centreDivisorInvoice
  simp_rw [hterm]
  calc
    (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        |actualSmallRoughRho (P false) N cap w z L d| *
          (∑ p ∈ centrePrimeFactors N,
            if d ∣ N - p then (1 : ℝ) else 0)) =
      ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        ∑ p ∈ centrePrimeFactors N,
          if d ∣ N - p then |actualSmallRoughRho (P false) N cap w z L d|
            else 0 := by
              apply Finset.sum_congr rfl
              intro d _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _
              by_cases hp : d ∣ N - p <;> simp [hp]
    _ = ∑ p ∈ centrePrimeFactors N,
        ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
          if d ∣ N - p then |actualSmallRoughRho (P false) N cap w z L d|
            else 0 := by rw [Finset.sum_comm]
    _ = ∑ p ∈ centrePrimeFactors N,
        ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
          (fun d => d ∣ N - p),
          |actualSmallRoughRho (P false) N cap w z L d| := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.sum_filter]

/-- Same full physical-modulus coefficient in the complementary
modulus-prime incidence. Valid even at modulus zero by totalized phi. -/
theorem absolutePhysical_modulus_eq_divisor_invoice
    (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    absolutePhysical P N cap w z L (modulusPrimeTerm N) =
      modulusDivisorInvoice P N cap w z L := by
  classical
  have hterm (d : ℕ) : |modulusPrimeTerm N d| =
      ∑ p ∈ chenPrimePrefix N,
        if p ∣ d then (1 : ℝ) / (Nat.totient d : ℝ) else 0 := by
    rw [abs_of_nonneg (modulusPrimeTerm_nonneg N d)]
    exact modulusPrimeTerm_eq_divisor_fibres N d
  unfold absolutePhysical modulusDivisorInvoice
  simp_rw [hterm]
  calc
    (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        |actualSmallRoughRho (P false) N cap w z L d| *
          (∑ p ∈ chenPrimePrefix N,
            if p ∣ d then (1 : ℝ) / (Nat.totient d : ℝ) else 0)) =
      ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        ∑ p ∈ chenPrimePrefix N,
          if p ∣ d then
            |actualSmallRoughRho (P false) N cap w z L d| /
              (Nat.totient d : ℝ)
          else 0 := by
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            by_cases hp : p ∣ d <;> simp [hp, div_eq_mul_inv]
    _ = ∑ p ∈ chenPrimePrefix N,
        ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
          if p ∣ d then
            |actualSmallRoughRho (P false) N cap w z L d| /
              (Nat.totient d : ℝ)
          else 0 := by rw [Finset.sum_comm]
    _ = ∑ p ∈ chenPrimePrefix N,
        ∑ d ∈ (actualSmallRoughModuli (P false) N cap w z).filter
          (fun d => p ∣ d),
          |actualSmallRoughRho (P false) N cap w z L d| /
            (Nat.totient d : ℝ) := by
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.sum_filter]

/-- On the ORIGINAL sixth-to-eighth gain, each exceptional absolute
budget is the sum of the two genuine, differently signed policies'
physical divisor-fibre invoices. No third coefficient family. -/
theorem absoluteGainBudget_exception_eq_fibres
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    absoluteGainBudget delta n e q om N cap w z L (modulusPrimeTerm N) +
      absoluteGainBudget delta n e q om N cap w z L
        (chenCentrePrimeAPCount N N) =
      modulusDivisorInvoice (sixthPolicy n e q om (N : ℝ)) N cap w z L +
      modulusDivisorInvoice (policy delta n e q om (N : ℝ)) N cap w z L +
      centreDivisorInvoice (sixthPolicy n e q om (N : ℝ)) N cap w z L +
      centreDivisorInvoice (policy delta n e q om (N : ℝ)) N cap w z L := by
  unfold absoluteGainBudget
  rw [absolutePhysical_modulus_eq_divisor_invoice,
      absolutePhysical_modulus_eq_divisor_invoice,
      absolutePhysical_centre_eq_divisor_invoice,
      absolutePhysical_centre_eq_divisor_invoice]
  ring

/-- The exact original receiver-minus-density error now has explicit
prime-incidence invoices on the same full-beta rho, with primitive AP
error separate. No asymptotic smallness follows from this identity. -/
theorem receiver_density_error_divisor_fibre_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
        primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      absoluteGainBudget delta n e q om N cap w z L (primitiveError N) +
      modulusDivisorInvoice (sixthPolicy n e q om (N : ℝ)) N cap w z L +
      modulusDivisorInvoice (policy delta n e q om (N : ℝ)) N cap w z L +
      centreDivisorInvoice (sixthPolicy n e q om (N : ℝ)) N cap w z L +
      centreDivisorInvoice (policy delta n e q om (N : ℝ)) N cap w z L := by
  have h := receiver_density_error_bound delta n e q om N cap w z L
  have hsum := absoluteGainBudget_exception_eq_fibres
    delta n e q om N cap w z L
  linarith

/-- For a nonprime centre the p=N zero-gap endpoint is absent. For the
pinned manuscript's even N>2 this is the relevant case; no geometric
zero-measure argument is substituted for this arithmetic fact. -/
theorem centre_factor_gap_pos (N p : ℕ)
    (hN : ¬ Nat.Prime N) (hp : p ∈ centrePrimeFactors N) :
    0 < N - p := by
  obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨hle, hprime⟩ := mem_chenPrimePrefix.mp hmem
  have hneq : p ≠ N := by
    intro h
    exact hN (by simpa [h] using hprime)
  omega

theorem centre_prime_zero_modulus_of_nonprime (N : ℕ)
    (hN : ¬ Nat.Prime N) :
    chenCentrePrimeAPCount N N 0 = 0 := by
  rw [centrePrimeAPCount_eq_divisor_fibres]
  apply Finset.sum_eq_zero
  intro p hp
  have hgap := centre_factor_gap_pos N p hN hp
  simp [Nat.ne_of_gt hgap]

end
end ImbalancedChen.P4AOriginalFull87ExceptionDivisorFibres
