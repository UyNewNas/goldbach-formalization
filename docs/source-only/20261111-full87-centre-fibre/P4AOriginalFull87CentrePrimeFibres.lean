import ImbalancedChen.P4AOriginalFull87SignedSharpReceiver
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An exact finite centre-prime correction on the SAME original full87 actual
signed sixth/eighth physical coefficient. The sharp-prime recentering removes
the modulus-prime bill algebraically, but does NOT remove prime divisors of N.
This packet exchanges the actual full-modulus sum with that finite prime-divisor
fibre, localizes its absolute cost to genuine congruence incidences, and ties
it back to the original owned occurrence sum. No PP, little-o, numerical gain,
or reserve payment is asserted. No new signed sieve coefficient is licensed.
-/

namespace ImbalancedChen.P4AOriginalFull87CentrePrimeFibres
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87OwnedEighthSource (ownedSource)
open P4AOriginalFull87EighthPrimeMeanLedger
  (gain gain_eq_owned_sources primeMass densityTest receiverTest)
open P4AOriginalFull87SignedSharpReceiver
  (sharpPrimeError full87PhysicalSupport full87PhysicalRhoChange
   full87_physical_signed_normal_form full87_receiver_sharp_centre_exact)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalLicensedSixthSignedLedger (physical)

/-- The literal prime divisors of the original target N in the inclusive
prime prefix, rather than an invented zero centre correction. -/
def centreDivisorPrimes (N : ℕ) : Finset ℕ :=
  (chenPrimePrefix N).filter (fun P => P ∣ N)

/-- The original centre-prime AP correction is a finite congruence fibre.
This remains exact at d=0 and d=1. -/
theorem centre_count_eq_divisor_fibre (N d : ℕ) :
    chenCentrePrimeAPCount N N d =
      (((centreDivisorPrimes N).filter (fun P => Nat.ModEq d P N)).card : ℝ) := by
  unfold chenCentrePrimeAPCount centreDivisorPrimes
  congr 1
  ext P
  simp only [Finset.mem_filter]
  tauto

/-- An exact indicator expansion, allowing the original moduli to remain
inside their physical finite support. -/
theorem centre_count_eq_indicator_sum (N d : ℕ) :
    chenCentrePrimeAPCount N N d =
      ∑ P ∈ centreDivisorPrimes N,
        if Nat.ModEq d P N then (1 : ℝ) else 0 := by
  classical
  rw [centre_count_eq_divisor_fibre, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A centre prime is strictly before the endpoint whenever the centre is
not prime. This is the exact finite nonzero-difference obligation behind
exclusion of the p=N endpoint; no estimate for a divisor function at zero. -/
theorem centre_divisor_lt_of_not_prime {N P : ℕ}
    (hN : ¬Nat.Prime N) (hP : P ∈ centreDivisorPrimes N) : P < N := by
  have hm := Finset.mem_filter.mp hP
  have hp := mem_chenPrimePrefix.mp hm.1
  have hne : P ≠ N := by
    intro h
    apply hN
    simpa [h] using hp.2
  omega

/-- For each actual centre-prime congruence incidence, the COMPLETE modulus
d divides the genuine nonzero integer difference N-P (under nonprime N). -/
theorem centre_fibre_dvd_nonzero {N P d : ℕ}
    (hN : ¬Nat.Prime N) (hP : P ∈ centreDivisorPrimes N)
    (hmod : Nat.ModEq d P N) : d ∣ N - P ∧ 0 < N - P := by
  have hlt := centre_divisor_lt_of_not_prime hN hP
  exact ⟨(dvd_sub_iff_modEq_of_le hlt.le).mpr hmod, by omega⟩

/-- Finite Fubini identity; no cancellation or occurrence is dropped. -/
private theorem weighted_centre_fibre_sum
    (N : ℕ) (S : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ S, rho d * chenCentrePrimeAPCount N N d) =
      ∑ P ∈ centreDivisorPrimes N,
        ∑ d ∈ S, if Nat.ModEq d P N then rho d else 0 := by
  classical
  simp_rw [centre_count_eq_indicator_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hmod : Nat.ModEq d P N <;> simp [hmod]

/-- The exact centre correction is evaluated on the original signed
sixth-minus-eighth rho at the COMPLETE modulus, not a new PP family. -/
theorem full87_centre_fibre_exact
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    gain (width r) n e q om N cap w z L (chenCentrePrimeAPCount N N) =
      ∑ P ∈ centreDivisorPrimes N,
        ∑ d ∈ full87PhysicalSupport r n e q om N cap w z,
          if Nat.ModEq d P N then
            full87PhysicalRhoChange r n e q om N cap w z L d else 0 := by
  rw [full87_physical_signed_normal_form]
  exact weighted_centre_fibre_sum N
    (full87PhysicalSupport r n e q om N cap w z)
    (full87PhysicalRhoChange r n e q om N cap w z L)

/-- The same exchange, now at the original87 owned strict-trim List call
site, by the pre-existing exact gain_eq_owned_sources. -/
theorem full87_owned_centre_fibre_exact
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    (∑ c : Cell, ownedSource (width r) n e q om N cap w z L
      (chenCentrePrimeAPCount N N) c) =
      ∑ P ∈ centreDivisorPrimes N,
        ∑ d ∈ full87PhysicalSupport r n e q om N cap w z,
          if Nat.ModEq d P N then
            full87PhysicalRhoChange r n e q om N cap w z L d else 0 := by
  calc
    _ = gain (width r) n e q om N cap w z L (chenCentrePrimeAPCount N N) :=
      (gain_eq_owned_sources (width r) n e q om N cap w z L
        (chenCentrePrimeAPCount N N)).symm
    _ = _ := full87_centre_fibre_exact r n e q om N cap w z L

/-- A NON-asymptotic, true-incidence-only absolute centre-prime invoice.
Unlike the global old+new absolute budget it charges only actual (P,d)
congruence fibres, and it does not assert a signed PP bound. -/
def centreFibreAbsBudget
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ P ∈ centreDivisorPrimes N,
    ∑ d ∈ full87PhysicalSupport r n e q om N cap w z,
      if Nat.ModEq d P N then
        |full87PhysicalRhoChange r n e q om N cap w z L d| else 0

private theorem abs_weighted_centre_fibre_sum_le
    (N : ℕ) (S : Finset ℕ) (rho : ℕ → ℝ) :
    |∑ P ∈ centreDivisorPrimes N,
      ∑ d ∈ S, if Nat.ModEq d P N then rho d else 0| ≤
      ∑ P ∈ centreDivisorPrimes N,
        ∑ d ∈ S, if Nat.ModEq d P N then |rho d| else 0 := by
  classical
  calc
    _ ≤ ∑ P ∈ centreDivisorPrimes N,
        |∑ d ∈ S, if Nat.ModEq d P N then rho d else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro P hP
      calc
        _ ≤ ∑ d ∈ S, |if Nat.ModEq d P N then rho d else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hmod : Nat.ModEq d P N <;> simp [hmod]

/-- This finite centre-prime bound has the original signed physical rho,
and does not add the already-cancelled modulus-prime term. -/
theorem full87_centre_fibre_abs_bound
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain (width r) n e q om N cap w z L (chenCentrePrimeAPCount N N)| ≤
      centreFibreAbsBudget r n e q om N cap w z L := by
  rw [full87_centre_fibre_exact]
  exact abs_weighted_centre_fibre_sum_le N
    (full87PhysicalSupport r n e q om N cap w z)
    (full87PhysicalRhoChange r n e q om N cap w z L)

/-- A tighter INTERNAL conditional interface: the two real policy-specific
sharp PP estimates remain separate unproved hypotheses; the centre bill is
paid only at actual congruence incidences. This does not prove o(H_N). -/
theorem full87_receiver_if_sharp_PP_pair_centre_fibres
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (boundSixth boundEighth : ℝ)
    (hSixth :
      |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤ boundSixth)
    (hEighth :
      |physical (policy (width r) n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤ boundEighth) :
    |gain (width r) n e q om N cap w z L (receiverTest N) -
      primeMass N * gain (width r) n e q om N cap w z L densityTest| ≤
      boundSixth + boundEighth +
        centreFibreAbsBudget r n e q om N cap w z L := by
  rw [full87_receiver_sharp_centre_exact]
  have hPP :
      |gain (width r) n e q om N cap w z L (sharpPrimeError N)| ≤
        boundSixth + boundEighth := by
    change |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N) -
        physical (policy (width r) n e q om (N : ℝ)) N cap w z L
          (sharpPrimeError N)| ≤ _
    calc
      _ ≤ |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
          (sharpPrimeError N)| +
          |physical (policy (width r) n e q om (N : ℝ)) N cap w z L
            (sharpPrimeError N)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add
            (physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
              (sharpPrimeError N))
            (-physical (policy (width r) n e q om (N : ℝ)) N cap w z L
              (sharpPrimeError N))
      _ ≤ _ := add_le_add hSixth hEighth
  calc
    |gain (width r) n e q om N cap w z L (sharpPrimeError N) -
      gain (width r) n e q om N cap w z L
        (chenCentrePrimeAPCount N N)| ≤
      |gain (width r) n e q om N cap w z L (sharpPrimeError N)| +
        |gain (width r) n e q om N cap w z L
          (chenCentrePrimeAPCount N N)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add
          (gain (width r) n e q om N cap w z L (sharpPrimeError N))
          (-gain (width r) n e q om N cap w z L
            (chenCentrePrimeAPCount N N))
    _ ≤ _ := add_le_add hPP
      (full87_centre_fibre_abs_bound r n e q om N cap w z L)

end
end ImbalancedChen.P4AOriginalFull87CentrePrimeFibres
