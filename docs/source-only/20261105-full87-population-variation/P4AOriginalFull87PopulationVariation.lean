import ImbalancedChen.P4AOriginalFull87ChangedFrontierBudget

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

An actual same-frontier absolute-variation carrier for the two exceptional
prime populations. It does not introduce a new sieve policy, an independent
prime source, an asymptotic assumption, or a new full-modulus coefficient.

The two ordinary continuations are evaluated at the previous actual
own-sixth level and the existing selected eighth cap respectively. The
bound is restricted to the PREVIOUS changed original87 occurrence lists.
Every leaf retains its own sign-dependent small Rosser beta factor and
the complete product modulus. This is a finite bound, not a little-o
estimate, a density theorem, or a reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87PopulationVariation
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87EighthPrimeMeanLedger
open P4AOriginalFull87ChangedFrontierBudget

/-- Absolute-value propagation through the SAME stopped signed recursion.
Unlike replacing the policy by a different upper sieve, all branching
decisions and the original remaining carrier are unchanged. -/
def absoluteSignedTest {α : Type*} (R : Bool → List α → Bool)
    (h : α → ℝ) (V : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => |signedTreeCoefficient positive mass| * V positive pre
  | p :: ps =>
      absoluteSignedTest R h V pre positive mass ps +
        if R (!positive) (p :: pre) = true then
          absoluteSignedTest R h V (p :: pre) (!positive) (mass * h p) ps
        else 0

theorem abs_signedTest_le_absoluteSignedTest {α : Type*}
    (R : Bool → List α → Bool) (h : α → ℝ)
    (T V : Bool → List α → ℝ)
    (hTV : ∀ b hist, |T b hist| ≤ V b hist)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    |signedTest R h T pre positive mass remaining| ≤
      absoluteSignedTest R h V pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp only [signedTest, absoluteSignedTest, abs_mul]
      exact mul_le_mul_of_nonneg_left (hTV positive pre)
        (abs_nonneg (signedTreeCoefficient positive mass))
  | cons p ps ih =>
      by_cases hp : R (!positive) (p :: pre) = true
      · simp only [signedTest, absoluteSignedTest, if_pos hp]
        exact (abs_add_le _ _).trans
          (add_le_add (ih pre positive mass)
            (ih (p :: pre) (!positive) (mass * h p)))
      · simp only [signedTest, absoluteSignedTest, if_neg hp, add_zero]
        exact ih pre positive mass

/-- Nonnegative carrier built from the ACTUAL small-Rosser support and
the actual plus/minus beta attachment, before any occurrence summation. -/
def absoluteAttached (N cap : ℕ) (w L : ℝ) (H : ℕ → ℝ)
    (positive : Bool) (pre : List ℕ) : ℝ :=
  ∑ a ∈ actualSmallRosserSupport N cap w,
    |if positive then actualSmallRosserPlus N cap w L a
     else actualSmallRosserMinus N cap w L a| * H (a * pre.prod)

/-- A pointwise bound for the FULL physical modulus, not only the rough
part: its product is a * pre.prod on each signed leaf. -/
theorem abs_attachedLeafTest_le_absoluteAttached
    (N cap : ℕ) (w L : ℝ) (G H : ℕ → ℝ)
    (hGH : ∀ d, |G d| ≤ H d) (positive : Bool) (pre : List ℕ) :
    |attachedLeafTest N cap 1 w L G positive pre| ≤
      absoluteAttached N cap w L H positive pre := by
  unfold attachedLeafTest absoluteAttached
  simp only [one_mul]
  calc
    |∑ a ∈ actualSmallRosserSupport N cap w,
      (if positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) * G (a * pre.prod)|
      ≤ ∑ a ∈ actualSmallRosserSupport N cap w,
          |(if positive then actualSmallRosserPlus N cap w L a
            else actualSmallRosserMinus N cap w L a) * G (a * pre.prod)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ actualSmallRosserSupport N cap w,
          |if positive then actualSmallRosserPlus N cap w L a
           else actualSmallRosserMinus N cap w L a| * |G (a * pre.prod)| := by
          simp only [abs_mul]
    _ ≤ ∑ a ∈ actualSmallRosserSupport N cap w,
          |if positive then actualSmallRosserPlus N cap w L a
           else actualSmallRosserMinus N cap w L a| * H (a * pre.prod) := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left (hGH (a * pre.prod)) (abs_nonneg _)

/-- This is a positive-variation envelope of the very same ordinary
continuation, with its original sign, incoming mass and carrier. -/
def continuationVariation (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (H : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) : ℝ :=
  absoluteSignedTest R (fun _ => 1)
    (absoluteAttached N cap w L H)
    s.selectedPrefix s.positive s.mass s.remaining

theorem abs_continuation_le_variation
    (R : Bool → List ℕ → Bool) (N cap : ℕ)
    (w L : ℝ) (G H : ℕ → ℝ)
    (hGH : ∀ d, |G d| ≤ H d) (s : FirstExitDepthState ℕ) :
    |signedTest R (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        s.selectedPrefix s.positive s.mass s.remaining| ≤
      continuationVariation R N cap w L H s := by
  exact abs_signedTest_le_absoluteSignedTest R (fun _ => 1)
    (attachedLeafTest N cap 1 w L G)
    (absoluteAttached N cap w L H)
    (abs_attachedLeafTest_le_absoluteAttached N cap w L G H hGH)
    s.selectedPrefix s.remaining s.positive s.mass

/-- Old and new are the two literal ordinary levels on ONE changed state.
No signed monotonicity is inferred from comparing those levels. -/
theorem ordinarySaving_abs_le_variations
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (G H : ℕ → ℝ)
    (hGH : ∀ d, |G d| ≤ H d) (c : Cell)
    (s : FirstExitDepthState ℕ) :
    |ordinarySaving n e q om N cap w L G c s| ≤
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap w L H s +
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap w L H s := by
  let Rold := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let Rnew := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  have ho := abs_continuation_le_variation Rold N cap w L G H hGH s
  have hn := abs_continuation_le_variation Rnew N cap w L G H hGH s
  change |signedTest Rold (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest Rnew (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      s.selectedPrefix s.positive s.mass s.remaining| ≤
    continuationVariation Rold N cap w L H s +
      continuationVariation Rnew N cap w L H s
  have ht : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    simpa only [sub_eq_add_neg, abs_neg] using abs_add a (-b)
  exact (ht _ _).trans (add_le_add ho hn)

/-- Exact owner- and changed-occurrence-dependent absolute carrier. This
is NOT a new source: it is the old changedStates list, and each term sums
the two ordinary branches' own signed leaf variations. -/
def changedVariationBudget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (H : ℕ → ℝ) : ℝ :=
  ∑ c : Cell, ((changedStates delta n e q om N cap w z c).map
    (fun s =>
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap w L H s +
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap w L H s)).sum

theorem changedAbsBudget_le_variation
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G H : ℕ → ℝ)
    (hGH : ∀ d, |G d| ≤ H d) :
    changedAbsBudget delta n e q om N cap w z L G ≤
      changedVariationBudget delta n e q om N cap w z L H := by
  unfold changedAbsBudget changedVariationBudget
  apply Finset.sum_le_sum
  intro c _
  let xs := changedStates delta n e q om N cap w z c
  change (xs.map (fun s => |ordinarySaving n e q om N cap w L G c s|)).sum ≤
    (xs.map (fun s =>
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap w L H s +
      continuationVariation
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap w L H s)).sum
  induction xs with
  | nil => simp
  | cons s xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (ordinarySaving_abs_le_variations n e q om N cap w L G H hGH c s) ih

/-- The centre-prime population is a subset of the actual primes
dividing N; no generic sieve distribution estimate enters. -/
theorem centrePrimeAPCount_le_primeDivisorCount (N d : ℕ) :
    chenCentrePrimeAPCount N N d ≤ chenPrimeDivisorCount N N := by
  have hs :
      ((chenPrimePrefix N).filter
        (fun p => Nat.ModEq d p N ∧ p ∣ N)) ⊆
      ((chenPrimePrefix N).filter (fun p => p ∣ N)) := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.2⟩
  unfold chenCentrePrimeAPCount chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card hs

/-- Every prime dividing the modulus belongs to the same inclusive
prefix, if counted there. The totalized d=0 boundary is included. -/
theorem modulusPrimeTerm_abs_le_primeMass_density (N d : ℕ) :
    |modulusPrimeTerm N d| ≤ primeMass N * densityTest d := by
  have hs :
      ((chenPrimePrefix N).filter (fun p => p ∣ d)) ⊆ chenPrimePrefix N :=
    Finset.filter_subset _ _
  have hle : chenPrimeDivisorCount N d ≤ primeMass N := by
    unfold chenPrimeDivisorCount primeMass
    exact_mod_cast Finset.card_le_card hs
  calc
    |modulusPrimeTerm N d| = modulusPrimeTerm N d :=
      abs_of_nonneg (modulusPrimeTerm_nonneg N d)
    _ = chenPrimeDivisorCount N d * ((Nat.totient d : ℝ)⁻¹) := by
      simp only [modulusPrimeTerm, div_eq_mul_inv]
    _ ≤ primeMass N * ((Nat.totient d : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    _ = primeMass N * densityTest d := by simp only [densityTest, one_div]

theorem centrePrimeTerm_abs_le_divisorPopulation (N d : ℕ) :
    |chenCentrePrimeAPCount N N d| ≤ chenPrimeDivisorCount N N := by
  rw [abs_of_nonneg (centrePrimeTerm_nonneg N d)]
  exact centrePrimeAPCount_le_primeDivisorCount N d

/-- Both exceptional populations are bounded on the SAME changed
occurrences, with the actual beta leaf factors and full modulus. -/
theorem changed_modulus_population_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    changedAbsBudget delta n e q om N cap w z L (modulusPrimeTerm N) ≤
      changedVariationBudget delta n e q om N cap w z L
        (fun d => primeMass N * densityTest d) := by
  exact changedAbsBudget_le_variation delta n e q om N cap w z L
    (modulusPrimeTerm N) (fun d => primeMass N * densityTest d)
    (modulusPrimeTerm_abs_le_primeMass_density N)

theorem changed_centre_population_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    changedAbsBudget delta n e q om N cap w z L
        (chenCentrePrimeAPCount N N) ≤
      changedVariationBudget delta n e q om N cap w z L
        (fun _ => chenPrimeDivisorCount N N) := by
  exact changedAbsBudget_le_variation delta n e q om N cap w z L
    (chenCentrePrimeAPCount N N) (fun _ => chenPrimeDivisorCount N N)
    (centrePrimeTerm_abs_le_divisorPopulation N)

/-- Finite error ledger with concrete positive population bounds for the
two exceptional parts. The primitive AP discrepancy remains explicitly
unpaid, as do uniformity, sixth loss and both manuscript reserves. -/
theorem receiver_density_changed_population_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
      primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      changedAbsBudget delta n e q om N cap w z L (primitiveError N) +
      changedVariationBudget delta n e q om N cap w z L
        (fun d => primeMass N * densityTest d) +
      changedVariationBudget delta n e q om N cap w z L
        (fun _ => chenPrimeDivisorCount N N) := by
  have hprior := receiver_density_three_changed_error_bound
    delta n e q om N cap w z L
  have hmod := changed_modulus_population_bound delta n e q om N cap w z L
  have hcentre := changed_centre_population_bound delta n e q om N cap w z L
  linarith

end
end ImbalancedChen.P4AOriginalFull87PopulationVariation
