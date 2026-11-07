import ImbalancedChen.FixedEvenRoughCoefficients

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-25.

A quantitative first-different-admission estimate BEFORE coefficients are
enumerated. This is a finite causal compiler component for the manuscript's
lower construction. The budget follows both policies through their common
actual retained history and stops each branch at its first different test.
The cost there is a proved unrestricted absolute continuation mass, not a
caller-supplied density bound. In particular, no positivity of a signed
lower polynomial is used.

The final theorem applies to the exact unrestricted reciprocal-totient
densities of fixedEvenRoughCoefficient on the actual target-deleted prime
carrier. It does not construct the missing original enhanced U6 policy,
evaluate its scalar density, identify an h248 bank entry, or assert the
original lower-amplitude+h248 target. Those remain separate OPEN suppliers.
-/

namespace ImbalancedChen.P5LowerPolicyDensityStability

noncomputable section

/-- Absolute mass of all unrestricted extensions of the actual incoming
history. This upper bound is valid for arbitrary real local weights. -/
def continuationVariation {α : Type*} (h : α → ℝ) (mass : ℝ)
    (remaining : List α) : ℝ :=
  |mass| * (remaining.map (fun p => 1 + |h p|)).prod

theorem continuationVariation_nonneg {α : Type*} (h : α → ℝ)
    (mass : ℝ) (remaining : List α) : 0 ≤ continuationVariation h mass remaining := by
  apply mul_nonneg (abs_nonneg _)
  induction remaining with
  | nil => simp
  | cons p ps ih =>
      simpa only [List.map_cons, List.prod_cons] using
        mul_nonneg (by positivity : 0 ≤ 1 + |h p|) ih

/-- Skip/select mass is counted once; the select continuation carries the
same multiplicative incoming mass used by the actual first-exit tree. -/
theorem continuationVariation_cons {α : Type*} (h : α → ℝ)
    (mass : ℝ) (p : α) (ps : List α) :
    continuationVariation h mass (p :: ps) =
      continuationVariation h mass ps + continuationVariation h (mass * h p) ps := by
  simp only [continuationVariation, List.map_cons, List.prod_cons, abs_mul]
  ring

theorem abs_firstExitRetainedPolynomial_le_variation {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    |firstExitRetainedPolynomial retained h pre positive mass remaining| ≤
      continuationVariation h mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      cases positive <;> simp [firstExitRetainedPolynomial,
        signedTreeCoefficient, continuationVariation]
  | cons p ps ih =>
      have hskip := ih pre positive mass
      have hselect := ih (p :: pre) (!positive) (mass * h p)
      rw [firstExitRetainedPolynomial, continuationVariation_cons]
      by_cases hr : retained (!positive) (p :: pre) = true
      · rw [if_pos hr]
        exact (abs_add _ _).trans (add_le_add hskip hselect)
      · rw [if_neg hr, add_zero]
        exact hskip.trans (le_add_of_nonneg_right
          (continuationVariation_nonneg h (mass * h p) ps))

/-- A DATA recursion for compiler disagreement. Common rejected branches
terminate at zero cost; common retained branches preserve their history;
a first different admission is charged once by its unrestricted mass. -/
def disagreementBudget {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => 0
  | p :: ps =>
      disagreementBudget oldPolicy newPolicy h pre positive mass ps +
        if oldPolicy (!positive) (p :: pre) = newPolicy (!positive) (p :: pre) then
          if newPolicy (!positive) (p :: pre) = true then
            disagreementBudget oldPolicy newPolicy h (p :: pre) (!positive)
              (mass * h p) ps
          else 0
        else continuationVariation h (mass * h p) ps

theorem disagreementBudget_nonneg {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    0 ≤ disagreementBudget oldPolicy newPolicy h pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp [disagreementBudget]
  | cons p ps ih =>
      have hskip := ih pre positive mass
      have hselect := ih (p :: pre) (!positive) (mass * h p)
      simp only [disagreementBudget]
      split_ifs
      · exact add_nonneg hskip hselect
      · exact add_nonneg hskip le_rfl
      · exact add_nonneg hskip (continuationVariation_nonneg h _ _)

theorem disagreementBudget_self {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    disagreementBudget policy policy h pre positive mass remaining = 0 := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih => simp [disagreementBudget, ih]

private theorem abs_add_sub_add_le (a b c d : ℝ) :
    |(a + b) - (c + d)| ≤ |a - c| + |b - d| := by
  calc
    |(a + b) - (c + d)| = |(a - c) + (b - d)| := by congr 1 <;> ring
    _ ≤ |a - c| + |b - d| := abs_add _ _

/-- Quantitative first-difference control. This proof follows the real
skip/select recursion; both policies' later continuations are retained
exactly until their first disagreement and bounded independently there. -/
theorem abs_policy_difference_le_disagreementBudget {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    |firstExitRetainedPolynomial newPolicy h pre positive mass remaining -
        firstExitRetainedPolynomial oldPolicy h pre positive mass remaining| ≤
      disagreementBudget oldPolicy newPolicy h pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp [firstExitRetainedPolynomial, disagreementBudget]
  | cons p ps ih =>
      have hskip := ih pre positive mass
      have hselect := ih (p :: pre) (!positive) (mass * h p)
      have hbranch :
          |(if newPolicy (!positive) (p :: pre) = true then
              firstExitRetainedPolynomial newPolicy h (p :: pre) (!positive)
                (mass * h p) ps else 0) -
            (if oldPolicy (!positive) (p :: pre) = true then
              firstExitRetainedPolynomial oldPolicy h (p :: pre) (!positive)
                (mass * h p) ps else 0)| ≤
          (if oldPolicy (!positive) (p :: pre) = newPolicy (!positive) (p :: pre) then
            if newPolicy (!positive) (p :: pre) = true then
              disagreementBudget oldPolicy newPolicy h (p :: pre) (!positive)
                (mass * h p) ps else 0
           else continuationVariation h (mass * h p) ps) := by
        cases ho : oldPolicy (!positive) (p :: pre) <;>
          cases hn : newPolicy (!positive) (p :: pre)
        · simp [ho, hn]
        · simpa [ho, hn] using
            abs_firstExitRetainedPolynomial_le_variation newPolicy h
              (p :: pre) ps (!positive) (mass * h p)
        · simpa [ho, hn] using
            abs_firstExitRetainedPolynomial_le_variation oldPolicy h
              (p :: pre) ps (!positive) (mass * h p)
        · simpa [ho, hn] using hselect
      exact (abs_add_sub_add_le _ _ _ _).trans (add_le_add hskip hbranch)

def fullDisagreementBudget (oldPolicy newPolicy : List ℕ → Bool)
    (N cap : ℕ) (z : ℝ) : ℝ :=
  disagreementBudget (evenFirstExitPolicy oldPolicy) (evenFirstExitPolicy newPolicy)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)

/-- The same unrestricted target-deleted full densities used by the U6
physical-rho projection obey this explicit finite compiler stability bound.
No enhanced-density scalar evaluation is an input to this result. -/
theorem abs_full_even_policy_density_difference_le
    (oldPolicy newPolicy : List ℕ → Bool) (N cap : ℕ) (z : ℝ) :
    |reciprocalTotientDensity (fixedEvenRoughSupport newPolicy N cap 0 z)
          (fixedEvenRoughCoefficient newPolicy N cap 0 z) -
        reciprocalTotientDensity (fixedEvenRoughSupport oldPolicy N cap 0 z)
          (fixedEvenRoughCoefficient oldPolicy N cap 0 z)| ≤
      fullDisagreementBudget oldPolicy newPolicy N cap z := by
  have h := abs_policy_difference_le_disagreementBudget
    (evenFirstExitPolicy oldPolicy) (evenFirstExitPolicy newPolicy)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
  change |evenFirstExitRetainedPolynomial newPolicy _ _ -
      evenFirstExitRetainedPolynomial oldPolicy _ _| ≤ _ at h
  simpa only [evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity] using h

/-- One-sided lower stability keeps the literal old and new full densities;
it does not assert that increasing even admissions increases the density. -/
theorem full_even_policy_density_sub_budget_le
    (oldPolicy newPolicy : List ℕ → Bool) (N cap : ℕ) (z : ℝ) :
    reciprocalTotientDensity (fixedEvenRoughSupport oldPolicy N cap 0 z)
        (fixedEvenRoughCoefficient oldPolicy N cap 0 z) -
      fullDisagreementBudget oldPolicy newPolicy N cap z ≤
    reciprocalTotientDensity (fixedEvenRoughSupport newPolicy N cap 0 z)
      (fixedEvenRoughCoefficient newPolicy N cap 0 z) := by
  have h := (abs_le.mp
    (abs_full_even_policy_density_difference_le oldPolicy newPolicy N cap z)).1
  linarith

end
end ImbalancedChen.P5LowerPolicyDensityStability

