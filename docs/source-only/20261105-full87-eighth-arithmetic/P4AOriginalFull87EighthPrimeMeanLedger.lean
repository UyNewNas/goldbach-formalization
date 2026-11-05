import ImbalancedChen.P4AOriginalFull87OwnedEighthSource

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Exact arithmetic normalization of the SAME new eighth saving. The exact
coprime mean has a genuine modulus-prime correction; the additive receiver
source has a centre-prime correction. Both survive signed beta attachment.

No PNT, distribution, exit-series mean, numerical saving, little-o estimate
or reserve payment is assumed/proved in this finite identity. The remaining
analytic bridge must bound these actual errors and identify this density
with the residual integrals already controlled in the preceding packet.
-/
namespace ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87OwnedEighthSource

/-- The inclusive prime prefix, not a prematurely substituted li(N). -/
def primeMass (N : ℕ) : ℝ := ((chenPrimePrefix N).card : ℝ)
def densityTest (d : ℕ) : ℝ := 1 / (Nat.totient d : ℝ)
def modulusPrimeTerm (N d : ℕ) : ℝ :=
  chenPrimeDivisorCount N d / (Nat.totient d : ℝ)

def primitiveError (N d : ℕ) : ℝ :=
  chenPrimeAPCount N N d - exactCoprimeMean N d

/-- A direct divisibility count on the ACTUAL target-deleted receiver set. -/
def receiverTest (N d : ℕ) : ℝ :=
  (((chenPrimeReceiverSource N).filter (fun x => d ∣ x)).card : ℝ)

theorem receiverTest_eq (N d : ℕ) :
    receiverTest N d = chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d := by
  unfold receiverTest
  rw [chenPrimeReceiverSource_divisibility_fibre_card]
  exact chenAdditivePrimeCarrier_AP_count N N d

/-- The correction is exact for the FULL modulus, not just its rough part.
The formula is also a total identity at d=0, using Lean's total division. -/
theorem exactCoprimeMean_eq_density_sub_modulus (N d : ℕ) :
    exactCoprimeMean N d = primeMass N * densityTest d - modulusPrimeTerm N d := by
  have hm : (((chenPrimePrefix N).filter (fun p => p.Coprime d)).card : ℝ) =
      primeMass N - chenPrimeDivisorCount N d := by
    simpa [finiteCoprimeMass, primeMass] using chenPrimePrefix_coprime_mass N d
  rw [exactCoprimeMean, hm]
  unfold densityTest modulusPrimeTerm
  ring

theorem modulusPrimeTerm_nonneg (N d : ℕ) : 0 ≤ modulusPrimeTerm N d := by
  unfold modulusPrimeTerm chenPrimeDivisorCount
  positivity

theorem centrePrimeTerm_nonneg (N d : ℕ) : 0 ≤ chenCentrePrimeAPCount N N d := by
  unfold chenCentrePrimeAPCount
  positivity

/-- Modulus one is a genuine zero-correction boundary, not an omitted
case of an asymptotic argument. -/
theorem modulusPrimeTerm_one (N : ℕ) : modulusPrimeTerm N 1 = 0 := by
  have hf : (chenPrimePrefix N).filter (fun p => p ∣ 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hp
    obtain ⟨hmem, hd⟩ := Finset.mem_filter.mp hp
    have htwo := (mem_chenPrimePrefix.mp hmem).2.two_le
    have hone := Nat.dvd_one.mp hd
    omega
  simp only [modulusPrimeTerm, chenPrimeDivisorCount, hf, Finset.card_empty,
    Nat.cast_zero, zero_div]

theorem physical_linear (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G H : ℕ → ℝ) (a b : ℝ) :
    physical P N cap w z L (fun d => a * G d + b * H d) =
      a * physical P N cap w z L G + b * physical P N cap w z L H := by
  unfold physical
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Savings are predecessor minus updated policy, on identical tests. -/
def gain (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  physical (sixthPolicy n e q om (N : ℝ)) N cap w z L G -
    physical (policy delta n e q om (N : ℝ)) N cap w z L G

section FixedRealization
variable (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
  (N cap : ℕ) (w z L : ℝ)

theorem gain_linear (G H : ℕ → ℝ) (a b : ℝ) :
    gain delta n e q om N cap w z L (fun d => a * G d + b * H d) =
      a * gain delta n e q om N cap w z L G +
        b * gain delta n e q om N cap w z L H := by
  unfold gain
  rw [physical_linear, physical_linear]
  ring

theorem gain_add (G H : ℕ → ℝ) :
    gain delta n e q om N cap w z L (fun d => G d + H d) =
      gain delta n e q om N cap w z L G + gain delta n e q om N cap w z L H := by
  simpa only [one_mul] using gain_linear delta n e q om N cap w z L G H 1 1

theorem gain_sub (G H : ℕ → ℝ) :
    gain delta n e q om N cap w z L (fun d => G d - H d) =
      gain delta n e q om N cap w z L G - gain delta n e q om N cap w z L H := by
  simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
    gain_linear delta n e q om N cap w z L G H 1 (-1)

theorem gain_eq_owned_sources (G : ℕ → ℝ) :
    gain delta n e q om N cap w z L G =
      ∑ c : Cell, ownedSource delta n e q om N cap w z L G c :=
  physical_saving_eq_owned_sources delta n e q om N cap w z L G

/-- The density is the actual signed finite physical-rho density of this
one realization, not a linear-sieve bound imported from another policy. -/
theorem exact_mean_gain :
    gain delta n e q om N cap w z L (exactCoprimeMean N) =
      primeMass N * gain delta n e q om N cap w z L densityTest -
        gain delta n e q om N cap w z L (modulusPrimeTerm N) := by
  have heq : exactCoprimeMean N =
      fun d => primeMass N * densityTest d + (-1) * modulusPrimeTerm N d := by
    funext d
    rw [exactCoprimeMean_eq_density_sub_modulus]
    ring
  rw [heq, gain_linear]
  ring

/-- Exact source arithmetic: prime AP error, modulus-prime defect and
centre-prime defect are all retained, with their correct saving signs. -/
theorem receiver_gain_decomposition :
    gain delta n e q om N cap w z L (receiverTest N) =
      primeMass N * gain delta n e q om N cap w z L densityTest +
        gain delta n e q om N cap w z L (primitiveError N) -
        gain delta n e q om N cap w z L (modulusPrimeTerm N) -
        gain delta n e q om N cap w z L (chenCentrePrimeAPCount N N) := by
  have heq : receiverTest N = fun d =>
      (exactCoprimeMean N d + primitiveError N d) - chenCentrePrimeAPCount N N d := by
    funext d
    rw [receiverTest_eq]
    unfold primitiveError
    ring
  rw [heq, gain_sub, gain_add, exact_mean_gain]
  ring

/-- Same formula on the complete original87 occurrence sources. This is
an equality of full finite sums, not an existence-only tuple interface. -/
theorem owned_receiver_decomposition :
    (∑ c : Cell, ownedSource delta n e q om N cap w z L (receiverTest N) c) =
      primeMass N * (∑ c : Cell, ownedSource delta n e q om N cap w z L densityTest c) +
        (∑ c : Cell, ownedSource delta n e q om N cap w z L (primitiveError N) c) -
        (∑ c : Cell, ownedSource delta n e q om N cap w z L (modulusPrimeTerm N) c) -
        (∑ c : Cell, ownedSource delta n e q om N cap w z L (chenCentrePrimeAPCount N N) c) := by
  simpa only [gain_eq_owned_sources] using
    receiver_gain_decomposition delta n e q om N cap w z L

end FixedRealization

/-- Absolute arithmetic ledger; no sign cancellation is assumed. -/
def absolutePhysical (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
    |actualSmallRoughRho (P false) N cap w z L d| * |G d|

theorem abs_physical_le (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    |physical P N cap w z L G| ≤ absolutePhysical P N cap w z L G := by
  unfold physical absolutePhysical
  calc
    _ ≤ ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        |actualSmallRoughRho (P false) N cap w z L d * G d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul]

private theorem abs_sub_bound (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add a (-b)

def absoluteGainBudget (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  absolutePhysical (sixthPolicy n e q om (N : ℝ)) N cap w z L G +
    absolutePhysical (policy delta n e q om (N : ℝ)) N cap w z L G

theorem abs_gain_le (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    |gain delta n e q om N cap w z L G| ≤
      absoluteGainBudget delta n e q om N cap w z L G := by
  exact (abs_sub_bound _ _).trans
    (add_le_add (abs_physical_le _ N cap w z L G) (abs_physical_le _ N cap w z L G))

/-- A finite bound exposing precisely the THREE arithmetic payments still
needed. It is not an asymptotic estimate and does not spend either reserve. -/
theorem receiver_density_error_bound (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
        primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      absoluteGainBudget delta n e q om N cap w z L (primitiveError N) +
        absoluteGainBudget delta n e q om N cap w z L (modulusPrimeTerm N) +
        absoluteGainBudget delta n e q om N cap w z L (chenCentrePrimeAPCount N N) := by
  rw [receiver_gain_decomposition]
  have heq :
      (primeMass N * gain delta n e q om N cap w z L densityTest +
          gain delta n e q om N cap w z L (primitiveError N) -
          gain delta n e q om N cap w z L (modulusPrimeTerm N) -
          gain delta n e q om N cap w z L (chenCentrePrimeAPCount N N)) -
          primeMass N * gain delta n e q om N cap w z L densityTest =
      (gain delta n e q om N cap w z L (primitiveError N) -
          gain delta n e q om N cap w z L (modulusPrimeTerm N)) -
          gain delta n e q om N cap w z L (chenCentrePrimeAPCount N N) := by ring
  rw [heq]
  exact (abs_sub_bound _ _).trans (add_le_add
    ((abs_sub_bound _ _).trans (add_le_add
      (abs_gain_le _ _ _ _ _ _ _ _ _ _ _) (abs_gain_le _ _ _ _ _ _ _ _ _ _ _)))
    (abs_gain_le _ _ _ _ _ _ _ _ _ _ _))

end
end ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
