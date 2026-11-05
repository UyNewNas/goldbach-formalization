import ImbalancedChen.P4AOriginalFull87PopulationScaling
import Mathlib.Data.Nat.PrimeFin

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

Replace the previous \`pi_N / phi(d)\` bound on the SAME full physical
modulus-prime correction by a cap using the actual distinct prime factors
of d. At d=0 the full-prefix population is retained explicitly; at d>0
the cap is min(pi_N, omega(d)). This does not assume a positive modulus
on the physical coefficient's entire support.

The exact factor-to-prime-prefix identity and the monotone propagation
through both sign-dependent beta-weighted ordinary continuations are
manuscript-internal finite lemmas. No prime distribution input, sieve
asymptotic, signed-cap monotonicity, or reserve payment is assumed.
-/

namespace ImbalancedChen.P4AOriginalFull87FactorPopulation
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87EighthPrimeMeanLedger
open P4AOriginalFull87ChangedFrontierBudget
open P4AOriginalFull87PopulationVariation
open P4AOriginalFull87PopulationScaling

/-- For nonzero d, the original inclusive prefix's primes dividing d are
exactly its genuine prime factors not exceeding N. No multiplicity of a
prime power is counted, and neither the prefix nor d is replaced. -/
theorem prefix_divisors_eq_filtered_factors (N d : ℕ) (hd : d ≠ 0) :
    (chenPrimePrefix N).filter (fun p => p ∣ d) =
      d.primeFactors.filter (fun p => p ≤ N) := by
  ext p
  simp only [Finset.mem_filter, mem_chenPrimePrefix, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpd⟩
    exact ⟨⟨hp, hpd, hd⟩, hpN⟩
  · rintro ⟨⟨hp, hpd, _⟩, hpN⟩
    exact ⟨⟨hpN, hp⟩, hpd⟩

/-- The actual modulus-prime correction, not a replacement test, has an
exact prime-factor expression on every nonzero complete modulus. -/
theorem modulusPrimeTerm_eq_filtered_factors (N d : ℕ) (hd : d ≠ 0) :
    modulusPrimeTerm N d =
      (((d.primeFactors.filter (fun p => p ≤ N)).card : ℝ) * densityTest d) := by
  simp only [modulusPrimeTerm, chenPrimeDivisorCount,
    prefix_divisors_eq_filtered_factors N d hd, densityTest,
    div_eq_mul_inv, one_div]

/-- If the whole modulus lies below N, every one of its distinct prime
factors is already in the inclusive source prefix. The exceptional d=0
case is deliberately excluded. -/
theorem modulus_prime_population_eq_factor_card (N d : ℕ)
    (hd : d ≠ 0) (hdN : d ≤ N) :
    chenPrimeDivisorCount N d = (d.primeFactors.card : ℝ) := by
  have hf : d.primeFactors.filter (fun p => p ≤ N) = d.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact (Nat.le_of_mem_primeFactors hp).trans hdN
  unfold chenPrimeDivisorCount
  rw [prefix_divisors_eq_filtered_factors N d hd, hf]

/-- A bound in NATURAL-NUMBER cardinalities. The zero case must not use
Nat.primeFactors 0 (empty), because every prime divides 0. -/
def primeCountCap (N d : ℕ) : ℕ :=
  if d = 0 then (chenPrimePrefix N).card
  else min (chenPrimePrefix N).card d.primeFactors.card

theorem primeCountCap_zero (N : ℕ) :
    primeCountCap N 0 = (chenPrimePrefix N).card := by
  simp [primeCountCap]

theorem primeCountCap_le_prefix (N d : ℕ) :
    primeCountCap N d ≤ (chenPrimePrefix N).card := by
  by_cases hd : d = 0
  · simp [primeCountCap, hd]
  · simpa [primeCountCap, hd] using
      (min_le_left (chenPrimePrefix N).card d.primeFactors.card)

theorem primeCountCap_le_factor_card (N d : ℕ) (hd : d ≠ 0) :
    primeCountCap N d ≤ d.primeFactors.card := by
  simpa [primeCountCap, hd] using
    (min_le_right (chenPrimePrefix N).card d.primeFactors.card)

/-- A finite count that can be much smaller than the old pi_N charge;
it remains bounded by the old charge even for d > N and d = 0. -/
theorem prefix_prime_divisor_count_le_cap (N d : ℕ) :
    ((chenPrimePrefix N).filter (fun p => p ∣ d)).card ≤ primeCountCap N d := by
  by_cases hd : d = 0
  · subst d
    simp [primeCountCap]
  · simp only [primeCountCap, if_neg hd]
    apply le_min
    · exact Finset.card_le_card (Finset.filter_subset _ _)
    · rw [prefix_divisors_eq_filtered_factors N d hd]
      exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A pointwise nonnegative complete-modulus envelope. It keeps d=0
totalized rather than silently deducing nonzero support. -/
def factorModulusBudgetTest (N d : ℕ) : ℝ :=
  (primeCountCap N d : ℝ) * densityTest d

theorem modulusPrimeTerm_abs_le_factor_test (N d : ℕ) :
    |modulusPrimeTerm N d| ≤ factorModulusBudgetTest N d := by
  have hcount : chenPrimeDivisorCount N d ≤ (primeCountCap N d : ℝ) := by
    unfold chenPrimeDivisorCount
    exact_mod_cast prefix_prime_divisor_count_le_cap N d
  have hg : 0 ≤ densityTest d := by unfold densityTest; positivity
  calc
    |modulusPrimeTerm N d| = chenPrimeDivisorCount N d * densityTest d := by
      rw [abs_of_nonneg (modulusPrimeTerm_nonneg N d)]
      simp only [modulusPrimeTerm, densityTest, div_eq_mul_inv, one_div]
    _ ≤ factorModulusBudgetTest N d := by
      unfold factorModulusBudgetTest
      exact mul_le_mul_of_nonneg_right hcount hg

/-- The refined test itself is pointwise no larger than the previous
pi_N * 1/phi(d) test, with no positivity assumption on d. -/
theorem factor_test_le_coarse (N d : ℕ) :
    factorModulusBudgetTest N d ≤ primeMass N * densityTest d := by
  have hcap : (primeCountCap N d : ℝ) ≤ primeMass N := by
    unfold primeMass
    exact_mod_cast primeCountCap_le_prefix N d
  unfold factorModulusBudgetTest
  exact mul_le_mul_of_nonneg_right hcap (by unfold densityTest; positivity)

/-- Positive terminal absolute beta attachment is monotone in its
FULL physical-modulus test; the selected sign is held fixed. -/
theorem absoluteAttached_mono (N cap : ℕ) (w L : ℝ) (H K : ℕ → ℝ)
    (hHK : ∀ d, H d ≤ K d) (positive : Bool) (pre : List ℕ) :
    absoluteAttached N cap w L H positive pre ≤
      absoluteAttached N cap w L K positive pre := by
  unfold absoluteAttached
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (hHK (a * pre.prod)) (abs_nonneg _)

/-- The sign-sensitive retained recursion itself is monotone in a
nonnegative-terminal MAJORANT; this is not monotonicity in the sieve
level, and no signed saving is ordered. -/
theorem absoluteSignedTest_mono {α : Type*} (R : Bool → List α → Bool)
    (h : α → ℝ) (V W : Bool → List α → ℝ)
    (hVW : ∀ b hist, V b hist ≤ W b hist)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    absoluteSignedTest R h V pre positive mass remaining ≤
      absoluteSignedTest R h W pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp only [absoluteSignedTest]
      exact mul_le_mul_of_nonneg_left (hVW positive pre) (abs_nonneg _)
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [absoluteSignedTest, if_pos hr]
        exact add_le_add (ih pre positive mass)
          (ih (p :: pre) (!positive) (mass * h p))
      · simp only [absoluteSignedTest, if_neg hr, add_zero]
        exact ih pre positive mass

theorem continuationVariation_mono (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (H K : ℕ → ℝ)
    (hHK : ∀ d, H d ≤ K d) (s : FirstExitDepthState ℕ) :
    continuationVariation R N cap w L H s ≤
      continuationVariation R N cap w L K s := by
  unfold continuationVariation
  exact absoluteSignedTest_mono R (fun _ => 1)
    (absoluteAttached N cap w L H)
    (absoluteAttached N cap w L K)
    (fun b hist => absoluteAttached_mono N cap w L H K hHK b hist)
    s.selectedPrefix s.remaining s.positive s.mass

/-- Monotonicity holds through the ACTUAL changedStates occurrence lists,
retaining the two different ordinary policies and their common history.
It does not compare signed savings or change their parent levels. -/
theorem changedVariationBudget_mono
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (H K : ℕ → ℝ)
    (hHK : ∀ d, H d ≤ K d) :
    changedVariationBudget delta n e q om N cap w z L H ≤
      changedVariationBudget delta n e q om N cap w z L K := by
  unfold changedVariationBudget
  apply Finset.sum_le_sum
  intro c _
  let xs := changedStates delta n e q om N cap w z c
  change
    (xs.map (fun s =>
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap w L H s +
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap w L H s)).sum ≤
    (xs.map (fun s =>
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap w L K s +
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap w L K s)).sum
  induction xs with
  | nil => simp
  | cons s xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (add_le_add
          (continuationVariation_mono _ N cap w L H K hHK s)
          (continuationVariation_mono _ N cap w L H K hHK s)) ih

/-- The actual modulus-prime defect now uses at most the distinct full
modulus prime factors, and at most the old whole prime population. -/
theorem changed_modulus_factor_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    changedAbsBudget delta n e q om N cap w z L (modulusPrimeTerm N) ≤
      changedVariationBudget delta n e q om N cap w z L
        (factorModulusBudgetTest N) := by
  exact changedAbsBudget_le_variation delta n e q om N cap w z L
    (modulusPrimeTerm N) (factorModulusBudgetTest N)
    (modulusPrimeTerm_abs_le_factor_test N)

/-- The REFINED total changed budget is proved no worse than the old
pi_N-weighted budget, rather than merely claimed to be smaller. -/
theorem changed_factor_budget_le_population_budget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    changedVariationBudget delta n e q om N cap w z L
        (factorModulusBudgetTest N) ≤
      primeMass N * changedVariationBudget delta n e q om N cap w z L
        densityTest := by
  calc
    changedVariationBudget delta n e q om N cap w z L
        (factorModulusBudgetTest N) ≤
      changedVariationBudget delta n e q om N cap w z L
        (fun d => primeMass N * densityTest d) :=
      changedVariationBudget_mono delta n e q om N cap w z L
        (factorModulusBudgetTest N) (fun d => primeMass N * densityTest d)
        (factor_test_le_coarse N)
    _ = primeMass N * changedVariationBudget delta n e q om N cap w z L
        densityTest :=
      changedVariationBudget_scale delta n e q om N cap w z L densityTest
        (primeMass N)

/-- The EXACT same signed receiver and same old/new policy now satisfy
a strictly sharper eligible error ledger. Neither little-o nor reserve
payment follows without an additional bound on the displayed variation. -/
theorem receiver_density_changed_factor_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
      primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      changedAbsBudget delta n e q om N cap w z L (primitiveError N) +
      changedVariationBudget delta n e q om N cap w z L
        (factorModulusBudgetTest N) +
      chenPrimeDivisorCount N N *
        changedVariationBudget delta n e q om N cap w z L (fun _ => 1) := by
  have hraw := receiver_density_three_changed_error_bound
    delta n e q om N cap w z L
  have hmod := changed_modulus_factor_bound delta n e q om N cap w z L
  have hcenter := changed_centre_population_bound delta n e q om N cap w z L
  have hscale := changedVariationBudget_const delta n e q om N cap w z L
    (chenPrimeDivisorCount N N)
  rw [hscale] at hcenter
  linarith

end
end ImbalancedChen.P4AOriginalFull87FactorPopulation
