import ImbalancedChen.P4AOriginalFull87SixthOnlyEventInvoice
import ImbalancedChen.RoughPrimeUniverse
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.  No kernel credit.

At the ACTUAL even sixth gate there is no odd Rosser product test:
both original policies admit every positive-sign prefix.  Instead of
pretending that the sixth selected product is < N^(299/500), retain the
literal high-q support of the ORIGINAL plus Rosser beta.  The same
original ordered sixth-prime continuation is supported only at p with

  X < L * ((p :: fifthHistory).prod : ℝ).

Consequently an original carrier with p < z has zero sixth-positive
high-q contribution whenever L * fifthHistory.prod * z <= X.
This is a sufficient, explicitly quantitative *carrier-tail* cutoff,
NOT an unconditional level or density estimate.  No prime occurrence,
beta coefficient, signed mass or previous physical invoice is changed.
-/

namespace ImbalancedChen.P4AOriginalFull87SixthPositiveCarrierCut
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SixthOnlyEventInvoice (sixthPositiveContinuation)

/-- Sign-PLUS physical terminal: only actual NONZERO beta is used.
The literal strict high-q test is preserved, including the equality
endpoint X = a * selected.prod. -/
theorem plus_attached_highq_zero_of_level
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ)
    (hsmall : L * (pre.prod : ℝ) ≤ (X : ℝ)) :
    attachedLeafTest N cap 1 w L (highQTest X F) true pre = 0 := by
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  change actualSmallRosserPlus N cap w L a *
    highQTest X F (a * pre.prod) = 0
  by_cases hb : actualSmallRosserPlus N cap w L a = 0
  · simp [hb]
  · have hlt : (a : ℝ) < L :=
      (actualSmallRosserPlus_active hb).2.1
    have hmod : ((a * pre.prod : ℕ) : ℝ) ≤
        L * (pre.prod : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right hlt.le (Nat.cast_nonneg _)
    have hcut : ¬ X < a * pre.prod := by
      intro hx
      have hxreal : (X : ℝ) < ((a * pre.prod : ℕ) : ℝ) := by
        exact_mod_cast hx
      exact (not_lt_of_ge (hmod.trans hsmall)) hxreal
    simp [highQTest, hcut]

/-- Filter the EXISTING original post-fifth carrier, not the source list.
The condition is a necessary inequality for an active high-q term;
no density estimate or imaginary odd gate is inserted. -/
def largeSixthCarrier (L : ℝ) (X : ℕ)
    (pre remaining : List ℕ) : List ℕ :=
  remaining.filter (fun p => (X : ℝ) < L * ((p :: pre).prod : ℝ))

/-- Pure finite occurrence identity, with a zero term removed only
when it is known to be zero.  No deduplication or quotienting. -/
private theorem map_sum_filter_zero {α : Type*}
    (xs : List α) (f : α → ℝ) (Q : α → Prop)
    [DecidablePred Q]
    (hz : ∀ x, ¬ Q x → f x = 0) :
    (xs.map f).sum = ((xs.filter Q).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : Q x
      · simp [hx, ih]
      · simp [hx, hz x hx, ih]

/-- Every TRUE sixth child of the SAME original post-fifth suffix
has exactly the support cut required by the complete a*b high-q test.
It is NOT a cap monotonicity claim about the signed saving. -/
theorem sixthPositiveContinuation_eq_largeSixthCarrier
    (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (mass : ℝ) (remaining : List ℕ) :
    sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre mass remaining =
    ((largeSixthCarrier L X pre remaining).map (fun p =>
      if R true (p :: pre) = true then
        signedTreeCoefficient true mass *
          attachedLeafTest N cap 1 w L
            (highQTest X F) true (p :: pre)
      else 0)).sum := by
  unfold sixthPositiveContinuation largeSixthCarrier
  apply map_sum_filter_zero
  intro p hp
  have hz : attachedLeafTest N cap 1 w L
      (highQTest X F) true (p :: pre) = 0 :=
    plus_attached_highq_zero_of_level
      N cap w L X F (p :: pre) (le_of_not_gt hp)
  by_cases hr : R true (p :: pre) = true
  · simp [hr, hz]
  · simp [hr]

/-- Both ORIGINAL policies automatically admit every even sixth
prefix.  Thus the surviving list is determined by the physical
complete a*b test, not by a hypothetical sixth odd Rosser gate. -/
theorem actual_even_sixth_large_carrier_normal_form
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R : Bool → List ℕ → Bool)
    (hR :
      R = P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) ∨
      R = P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
    (pre : List ℕ) (mass : ℝ) (remaining : List ℕ) :
    sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre mass remaining =
    ((largeSixthCarrier L X pre remaining).map (fun p =>
      signedTreeCoefficient true mass *
        attachedLeafTest N cap 1 w L
          (highQTest X F) true (p :: pre))).sum := by
  have heven : ∀ p, R true (p :: pre) = true := by
    intro p
    rcases hR with hr | hs
    · rw [hr]
      exact P4AOriginalFull87CompleteSixthDispatch.policy_even
        e q om (N : ℝ) (p :: pre)
    · rw [hs]
      exact P4AOriginalFull87LicensedSixthPolicy.policy_even
        delta n e q om (N : ℝ) (p :: pre)
  simpa [heven] using
    (sixthPositiveContinuation_eq_largeSixthCarrier
      R N cap w L X F pre mass remaining)

/-- Finite-carrier quantitative cutoff.  If every actual candidate is
at most B, the original even-sixth high-q continuation vanishes
whenever L * b5 * B <= X.  This is a sufficient condition, not an
assumption equivalent to the desired global high-q theorem. -/
theorem sixthPositiveContinuation_zero_of_carrier_bound
    (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (mass : ℝ) (remaining : List ℕ)
    (B : ℝ) (hL : 0 ≤ L)
    (hB : ∀ p ∈ remaining, (p : ℝ) ≤ B)
    (hcut : (L * (pre.prod : ℝ)) * B ≤ (X : ℝ)) :
    sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre mass remaining = 0 := by
  revert hB
  induction remaining with
  | nil =>
      intro hB
      simp [sixthPositiveContinuation]
  | cons p ps ih =>
      intro hB
      have hpB : (p : ℝ) ≤ B := hB p (by simp)
      have hp : L * ((p :: pre).prod : ℝ) ≤ (X : ℝ) := by
        calc
          L * ((p :: pre).prod : ℝ) =
              (L * (pre.prod : ℝ)) * (p : ℝ) := by
                simp only [List.prod_cons, Nat.cast_mul]
                ring
          _ ≤ (L * (pre.prod : ℝ)) * B :=
            mul_le_mul_of_nonneg_left hpB
              (mul_nonneg hL (Nat.cast_nonneg _))
          _ ≤ (X : ℝ) := hcut
      have hz := plus_attached_highq_zero_of_level
        N cap w L X F (p :: pre) hp
      have htail : sixthPositiveContinuation R
          (attachedLeafTest N cap 1 w L (highQTest X F))
          pre mass ps = 0 :=
        ih (by
          intro t ht
          exact hB t (by simp [ht]))
      simp [sixthPositiveContinuation, hz, htail]

/-- The REAL rough-prime range supplies p < z with no synthetic
prime bound.  If the original post-fifth suffix is retained in this
range, the conditional cutoff uses its actual z, not enumeration cap. -/
theorem sixthPositiveContinuation_zero_of_original_rough_cutoff
    (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (mass : ℝ) (remaining : List ℕ)
    (hL : 0 ≤ L)
    (hrem : ∀ p ∈ remaining, p ∈ roughPrimeUniverse N cap w z)
    (hcut : (L * (pre.prod : ℝ)) * z ≤ (X : ℝ)) :
    sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre mass remaining = 0 := by
  exact sixthPositiveContinuation_zero_of_carrier_bound
    R N cap w L X F pre mass remaining z hL
    (fun p hp => le_of_lt (mem_roughPrimeUniverse_upper (hrem p hp)))
    hcut

end
end ImbalancedChen.P4AOriginalFull87SixthPositiveCarrierCut
