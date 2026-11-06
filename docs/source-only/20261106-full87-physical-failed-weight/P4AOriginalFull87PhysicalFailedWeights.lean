import ImbalancedChen.P4AOriginalFull87FailedAttempts
import ImbalancedChen.P4AOriginalFull87ActualEighthCarrier
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT.

P1.4: the unit-weight failed attempts from the earlier finite source are
NOT by themselves physical g_N-weighted correction terms. Recover the
mass of every occurrence from the original successful select history,
then identify the same ordered occurrence keys for two local weights.
For the actual original87 eighth carrier, initialize with the literal
eight-prefix product and identify the reciprocal-totient prime weight
(halfProductDensity) with 1/(p-1) for the failed and later selected
rough primes. Root-to-eighth reweighting remains a separate obligation.
No target-deletion factor is multiplied into an event a second time.
-/

namespace ImbalancedChen.P4AOriginalFull87PhysicalFailedWeights
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts)
open P4AOriginalFull87Post8GuardExtraction
  (actualFrozenPost8Level)

/-- Every real failed-select occurrence has precisely the incoming
product of the weights of its actually selected intermediate primes.
Neither skipped primes nor the rejected prime enter `a.mass`.
The rejected prime enters `a.value` exactly once, separately. -/
theorem failed_attempt_exact_selected_mass {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (a : FirstExitRejectedAttempt α)
    (ha : a ∈ firstExitRejectedAttempts policy h pre positive mass remaining) :
    ∃ (before chosen : List α),
      remaining = before ++ a.rejected :: a.smaller ∧
      chosen <+ before ∧
      a.older = chosen.reverse ++ pre ∧
      a.mass = mass * (chosen.map h).prod := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [firstExitRejectedAttempts] at ha
  | cons p ps ih =>
      by_cases ht : policy (!positive) (p :: pre) = true
      · rw [firstExitRejectedAttempts, if_pos ht, List.mem_append] at ha
        rcases ha with hskip | hselect
        · obtain ⟨before, chosen, hrem, hsub, holder, hmass⟩ :=
            ih pre positive mass a hskip
          refine ⟨p :: before, chosen, ?_, hsub.cons p, holder, hmass⟩
          simp [hrem]
        · obtain ⟨before, chosen, hrem, hsub, holder, hmass⟩ :=
            ih (p :: pre) (!positive) (mass * h p) a hselect
          refine ⟨p :: before, p :: chosen, ?_, hsub.cons_cons p, ?_, ?_⟩
          · simp [hrem]
          · simpa only [List.reverse_cons, List.append_assoc,
                List.singleton_append] using holder
          · simp only [List.map_cons, List.prod_cons]
            rw [hmass]
            ring
      · rw [firstExitRejectedAttempts, if_neg ht,
          List.mem_append, List.mem_singleton] at ha
        rcases ha with hskip | hnow
        · obtain ⟨before, chosen, hrem, hsub, holder, hmass⟩ :=
            ih pre positive mass a hskip
          refine ⟨p :: before, chosen, ?_, hsub.cons p, holder, hmass⟩
          simp [hrem]
        · subst a
          exact ⟨[], [], rfl, List.Sublist.refl [], by simp, by simp⟩

/-- The physical weights change occurrence masses but cannot alter the
ordered traversal, rejection labels, signs or post-rejection suffixes.
The map intentionally discards ONLY mass and retains duplicates. -/
theorem failed_attempt_labels_independent_of_weights {α : Type*}
    (policy : Bool → List α → Bool) (h k : α → ℝ)
    (pre remaining : List α) (positive : Bool) (massH massK : ℝ) :
    (firstExitRejectedAttempts policy h pre positive massH remaining).map
        (fun a => (a.older, a.rejected, a.smaller, a.positive)) =
      (firstExitRejectedAttempts policy k pre positive massK remaining).map
        (fun a => (a.older, a.rejected, a.smaller, a.positive)) := by
  induction remaining generalizing pre positive massH massK with
  | nil => rfl
  | cons p ps ih =>
      by_cases ht : policy (!positive) (p :: pre) = true
      · simp only [firstExitRejectedAttempts, if_pos ht, List.map_append]
        rw [ih pre positive massH massK,
          ih (p :: pre) (!positive) (massH * h p) (massK * k p)]
      · simp only [firstExitRejectedAttempts, if_neg ht, List.map_append,
          List.map_singleton]
        rw [ih pre positive massH massK]
        rfl

/-- Genuine original87 rank-eight source: for an actual physically
weighted failed occurrence the whole success word, rejected prime,
and their exact densities come from ONE target-deleted carrier.
The same event occurs with the same ordered labels at unit weight.
`a.value` contains its rejected factor and Euler suffix ONCE.
This does not establish a signed-saving bound. -/
theorem owned87_actual_physical_failed_occurrence
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hEven : 2 ∣ N) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ : ℕ => 1) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ firstExitRejectedAttempts
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      halfProductDensity s.selectedPrefix s.positive
        (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
        s.remaining) :
    ∃ (before chosen : List ℕ),
      s.remaining = before ++ a.rejected :: a.smaller ∧
      chosen <+ before ∧
      a.older = chosen.reverse ++ s.selectedPrefix ∧
      a.mass = (s.mass * (s.selectedPrefix.map halfProductDensity).prod) *
        (chosen.map halfProductDensity).prod ∧
      2 < a.rejected ∧
      halfProductDensity a.rejected = 1 / ((a.rejected : ℝ) - 1) ∧
      (∀ p ∈ chosen,
        2 < p ∧
        halfProductDensity p = 1 / ((p : ℝ) - 1) ∧ ¬p ∣ N) ∧
      ¬a.rejected ∣ N ∧
      a.value halfProductDensity =
        -signedTreeCoefficient (!a.positive)
          ((s.mass * (s.selectedPrefix.map halfProductDensity).prod) *
            (chosen.map halfProductDensity).prod *
            halfProductDensity a.rejected) *
          (a.smaller.map (fun x => 1 - halfProductDensity x)).prod := by
  obtain ⟨before, chosen, hrem, hsub, holder, hmass⟩ :=
    failed_attempt_exact_selected_mass
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      halfProductDensity s.selectedPrefix s.remaining
      s.positive
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod) a ha
  obtain ⟨_, _, _, _, hcarrier⟩ :=
    owned87_eighth_state_exact_carrier delta n e q om
      N cap w z c s hs
  obtain ⟨last, tail, _, _, hremaining⟩ := hcarrier
  have hpMem : a.rejected ∈ roughPrimeUniverse N cap w (last : ℝ) := by
    rw [← hremaining, hrem]
    simp
  have hpPrime : Nat.Prime a.rejected :=
    mem_roughPrimeUniverse_prime hpMem
  have hpNotDiv : ¬a.rejected ∣ N :=
    mem_roughPrimeUniverse_not_dvd hpMem
  have hNEven : Even N := even_iff_two_dvd.mpr hEven
  have hpDensity : halfProductDensity a.rejected =
      1 / ((a.rejected : ℝ) - 1) := by
    simpa [chenInitialBoundingSieve] using
      chenInitialBoundingSieve_prime_density N w hNEven hpPrime
  have hpThree : 2 < a.rejected := by
    have hpTwo := hpPrime.two_le
    have hpNeTwo : a.rejected ≠ 2 := by
      intro he
      apply hpNotDiv
      simpa [he] using hEven
    omega
  have hchosen : ∀ p ∈ chosen,
      2 < p ∧
      halfProductDensity p = 1 / ((p : ℝ) - 1) ∧ ¬p ∣ N := by
    intro p hp
    have hpRemaining : p ∈ roughPrimeUniverse N cap w (last : ℝ) := by
      rw [← hremaining, hrem]
      exact List.mem_append.mpr (Or.inl (hsub.subset hp))
    have hprime : Nat.Prime p :=
      mem_roughPrimeUniverse_prime hpRemaining
    have hnot : ¬p ∣ N :=
      mem_roughPrimeUniverse_not_dvd hpRemaining
    have hgt : 2 < p := by
      have hpTwo := hprime.two_le
      have hpNeTwo : p ≠ 2 := by
        intro he
        apply hnot
        simpa [he] using hEven
      omega
    have hdens : halfProductDensity p = 1 / ((p : ℝ) - 1) := by
      simpa [chenInitialBoundingSieve] using
        chenInitialBoundingSieve_prime_density N w hNEven hprime
    exact ⟨hgt, hdens, hnot⟩
  refine ⟨before, chosen, hrem, hsub, holder, hmass,
    hpThree, hpDensity,
    hchosen, hpNotDiv, ?_⟩
  simp only [FirstExitRejectedAttempt.value, hmass]

end
end ImbalancedChen.P4AOriginalFull87PhysicalFailedWeights
