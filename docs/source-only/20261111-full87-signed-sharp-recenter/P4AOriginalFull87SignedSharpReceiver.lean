import ImbalancedChen.P4AOriginalFull87OwnedPrimitiveLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Exact signed endpoint recentering of the ORIGINAL full87 physical coefficient.
The exact-coprime primitive discrepancy and the sharp pi(N)/phi(q)
discrepancy differ by the literal modulus-prime term. Consequently that
term cancels, with its correct sign, from the receiver-density identity
WHEN the error is expressed using the sharp original-prime endpoint.
The centre-prime deletion remains. No PP input is proved or called.

The second part displays the same physical coefficient as a signed function
on the union of the genuine sixth and eighth full-modulus supports. This
is NOT the termwise absolute primitive invoice and does not identify that
invoice with an admissible PP coefficient. Its signed old/new components
must be licensed and bounded separately to apply the manuscript's sharp
endpoint PP lemma; the conditional bound below does not supply them.
-/

namespace ImbalancedChen.P4AOriginalFull87SignedSharpReceiver
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87OwnedEighthSource (ownedSource)
open P4AOriginalFull87EighthPrimeMeanLedger
  (gain gain_add gain_eq_owned_sources primeMass densityTest primitiveError
   modulusPrimeTerm receiverTest exactCoprimeMean_eq_density_sub_modulus
   receiver_gain_decomposition abs_gain_le absoluteGainBudget)

/-- The sharp inclusive prime-prefix discrepancy of the FROZEN manuscript,
with the SAME complete physical modulus, rather than a coprime recentering. -/
def sharpPrimeError (N d : ℕ) : ℝ :=
  chenPrimeAPCount N N d - primeMass N * densityTest d

/-- Exact conversion between the two legitimate prime means. No error is
thrown away: the modulus-prime divisor term has a PLUS sign here. -/
theorem primitive_eq_sharp_add_modulus (N d : ℕ) :
    primitiveError N d = sharpPrimeError N d + modulusPrimeTerm N d := by
  unfold primitiveError sharpPrimeError
  rw [exactCoprimeMean_eq_density_sub_modulus]
  ring

/-- The ORIGINAL receiver with centre-prime deletion, at one full modulus.
Only after recentering from exact coprime mass to pi(N)/phi(q) does the
modulus-prime correction cancel exactly. -/
theorem receiver_eq_sharp_density_minus_centre (N d : ℕ) :
    receiverTest N d = primeMass N * densityTest d + sharpPrimeError N d -
      chenCentrePrimeAPCount N N d := by
  rw [P4AOriginalFull87EighthPrimeMeanLedger.receiverTest_eq]
  unfold sharpPrimeError
  ring

/-- Actual sixth-minus-eighth physical saving, not a second sieve bound.
The modulus term is cancelled algebraically, not assumed negligible. -/
theorem full87_receiver_sharp_centre_exact
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    gain (width r) n e q om N cap w z L (receiverTest N) -
      primeMass N * gain (width r) n e q om N cap w z L densityTest =
    gain (width r) n e q om N cap w z L (sharpPrimeError N) -
      gain (width r) n e q om N cap w z L (chenCentrePrimeAPCount N N) := by
  have htest : primitiveError N =
      (fun d => sharpPrimeError N d + modulusPrimeTerm N d) := by
    funext d
    exact primitive_eq_sharp_add_modulus N d
  rw [receiver_gain_decomposition, htest,
      gain_add (width r) n e q om N cap w z L]
  ring

/-- The exact FULL physical modulus union. Both supported rho values are
those of the unchanged real sixth and eighth policies. -/
def full87PhysicalSupport
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli ((sixthPolicy n e q om (N : ℝ)) false) N cap w z ∪
  actualSmallRoughModuli ((policy (width r) n e q om (N : ℝ)) false) N cap w z

/-- Signed old-minus-new coefficient, with zero extension outside each
policy's own actual support. The complete small/rough modulus is retained. -/
def full87PhysicalRhoChange
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) : ℝ :=
  (if d ∈ actualSmallRoughModuli ((sixthPolicy n e q om (N : ℝ)) false) N cap w z
   then actualSmallRoughRho ((sixthPolicy n e q om (N : ℝ)) false) N cap w z L d
   else 0) -
  (if d ∈ actualSmallRoughModuli ((policy (width r) n e q om (N : ℝ)) false) N cap w z
   then actualSmallRoughRho ((policy (width r) n e q om (N : ℝ)) false) N cap w z L d
   else 0)

private theorem sum_union_mask (A B : Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ A ∪ B, if d ∈ A then f d else 0) = ∑ d ∈ A, f d := by
  classical
  calc
    (∑ d ∈ A ∪ B, if d ∈ A then f d else 0) =
        ∑ d ∈ A, if d ∈ A then f d else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_union_left)
      intro d hd hdA
      simp [hdA]
    _ = ∑ d ∈ A, f d := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [hd]

private theorem finite_signed_union (A B : Finset ℕ)
    (a b G : ℕ → ℝ) :
    (∑ d ∈ A, a d * G d) - (∑ d ∈ B, b d * G d) =
      ∑ d ∈ A ∪ B,
        ((if d ∈ A then a d else 0) -
         (if d ∈ B then b d else 0)) * G d := by
  classical
  have hA := sum_union_mask A B (fun d => a d * G d)
  have hB := sum_union_mask B A (fun d => b d * G d)
  rw [Finset.union_comm B A] at hB
  calc
    (∑ d ∈ A, a d * G d) - (∑ d ∈ B, b d * G d) =
      (∑ d ∈ A ∪ B, if d ∈ A then a d * G d else 0) -
      (∑ d ∈ A ∪ B, if d ∈ B then b d * G d else 0) := by
        rw [hA, hB]
    _ = ∑ d ∈ A ∪ B,
          ((if d ∈ A then a d else 0) -
           (if d ∈ B then b d else 0)) * G d := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hA : d ∈ A <;> by_cases hB : d ∈ B <;>
        simp [hA, hB] <;> ring

/-- The genuine sixth-minus-eighth physical gain has ONE exact signed
full-modulus normal form. It is a rewriting of the old policies, not a new
PP coefficient class or a bound on the absolute leaf invoice. -/
theorem full87_physical_signed_normal_form
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    gain (width r) n e q om N cap w z L G =
      ∑ d ∈ full87PhysicalSupport r n e q om N cap w z,
        full87PhysicalRhoChange r n e q om N cap w z L d * G d := by
  simpa only [gain, physical, full87PhysicalSupport, full87PhysicalRhoChange] using
    finite_signed_union
      (actualSmallRoughModuli ((sixthPolicy n e q om (N : ℝ)) false) N cap w z)
      (actualSmallRoughModuli ((policy (width r) n e q om (N : ℝ)) false) N cap w z)
      (actualSmallRoughRho ((sixthPolicy n e q om (N : ℝ)) false) N cap w z L)
      (actualSmallRoughRho ((policy (width r) n e q om (N : ℝ)) false) N cap w z L)
      G

/-- Tie this signed full-q coefficient back to ALL original87 changed
owner/trim occurrence lists, whose multiplicities were never discarded. -/
theorem full87_owned_signed_sharp_callsite
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    (∑ c : Cell, ownedSource (width r) n e q om N cap w z L
      (sharpPrimeError N) c) =
    ∑ d ∈ full87PhysicalSupport r n e q om N cap w z,
      full87PhysicalRhoChange r n e q om N cap w z L d * sharpPrimeError N d := by
  calc
    _ = gain (width r) n e q om N cap w z L (sharpPrimeError N) :=
      (gain_eq_owned_sources (width r) n e q om N cap w z L (sharpPrimeError N)).symm
    _ = _ := full87_physical_signed_normal_form r n e q om N cap w z L (sharpPrimeError N)

/-- Conditional INTERNAL payment step, not an external theorem or proof of
its hypotheses. PP must be separately justified for EACH ORIGINAL signed
sixth/eighth rho at the sharp endpoint, with the manuscript's fixed-parameter
and smoothness/squarefree-support requirements. No absolute-per-leaf PP bound
is inferred. Only the real centre-prime bill survives exact recentering. -/
theorem full87_receiver_if_sharp_PP_pair
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
      absoluteGainBudget (width r) n e q om N cap w z L
        (chenCentrePrimeAPCount N N) := by
  rw [full87_receiver_sharp_centre_exact]
  have hPP :
      |gain (width r) n e q om N cap w z L (sharpPrimeError N)| ≤
        boundSixth + boundEighth := by
    change |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N) -
        physical (policy (width r) n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤ _
    have htriangle :
        |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L (sharpPrimeError N) -
          physical (policy (width r) n e q om (N : ℝ)) N cap w z L
            (sharpPrimeError N)| ≤
        |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L (sharpPrimeError N)| +
        |physical (policy (width r) n e q om (N : ℝ)) N cap w z L
          (sharpPrimeError N)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add (physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
          (sharpPrimeError N))
          (-physical (policy (width r) n e q om (N : ℝ)) N cap w z L
            (sharpPrimeError N))
    exact htriangle.trans (add_le_add hSixth hEighth)
  have hCentre := abs_gain_le (width r) n e q om N cap w z L
    (chenCentrePrimeAPCount N N)
  calc
    |gain (width r) n e q om N cap w z L (sharpPrimeError N) -
       gain (width r) n e q om N cap w z L
         (chenCentrePrimeAPCount N N)| ≤
      |gain (width r) n e q om N cap w z L (sharpPrimeError N)| +
      |gain (width r) n e q om N cap w z L
         (chenCentrePrimeAPCount N N)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add
        (gain (width r) n e q om N cap w z L (sharpPrimeError N))
        (-gain (width r) n e q om N cap w z L
          (chenCentrePrimeAPCount N N))
    _ ≤ _ := by exact add_le_add hPP hCentre

end
end ImbalancedChen.P4AOriginalFull87SignedSharpReceiver
