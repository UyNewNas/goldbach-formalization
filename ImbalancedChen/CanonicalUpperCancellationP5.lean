import ImbalancedChen.PositiveQuotientBuchstabP5
import ImbalancedChen.ActualThirdOriginalCoupledRecurrence
import MathlibNt.SieveTheory.JurkatRichert1965ChenDelayFunctions
import MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensitySource
import ImbalancedChen.Part5RenewalTablePrimitive

/-! SOURCE ONLY / UNCOMPILED. Genuine canonical upper cancellation.
The canonical delay functions are the actual method-of-steps functions.
The finite count identity is the actual additive-prime quotient identity.
Prior child LOWER estimates and their prime-test transport are explicit
inputs; no next-stage upper count estimate is assumed or asserted globally.
The cutoff interpretation and uniform analytic suppliers remain open. -/

namespace ImbalancedChen.P5CanonicalUpperCancellation

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open ImbalancedChen.P5PositiveQuotientBuchstab

def upperA (s : ℝ) : ℝ := s * jr1965F s / jr1965DelayConstant
def lowerBar (s : ℝ) : ℝ := s * jr1965f s / jr1965DelayConstant

theorem delayConstant_pos : 0 < jr1965DelayConstant := by
  unfold jr1965DelayConstant
  positivity

theorem lowerBar_div {s : ℝ} (hs : s ≠ 0) :
    lowerBar s / s = jr1965f s / jr1965DelayConstant := by
  unfold lowerBar
  field_simp [hs, ne_of_gt delayConstant_pos] <;> ring

theorem upperA_eq_one {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) :
    upperA s = 1 := by
  unfold upperA
  rw [jr1965F_eq_of_le_three hs3]
  unfold jr1965DelayConstant
  field_simp [ne_of_gt hs0, ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)] <;> ring

theorem lowerBar_eq_zero {s : ℝ} (hs : s ≤ 2) : lowerBar s = 0 := by
  simp only [lowerBar, jr1965f_initial hs, mul_zero, zero_div]

/-- The JR notation is the same canonical upper numerator used by the
actual Suzuki source, not a second synthetic delay system. -/
theorem upperA_eq_originalH {s : ℝ} (hs : 2 ≤ s) :
    upperA s = OriginalU2CoupledRecurrenceSourceOnly.H s := by
  have hp := (MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity.sourceParity_eq_jr1965 hs).1
  simp only [upperA, OriginalU2CoupledRecurrenceSourceOnly.H,
    OriginalU2CoupledRecurrenceSourceOnly.upper, suzukiContinuousUpperFactor,
    OriginalU2CoupledRecurrenceSourceOnly.A, jr1965DelayConstant, hp]
  ring

theorem lowerBar_eq_originalL {s : ℝ} (hs : 2 ≤ s) :
    lowerBar s = OriginalU2CoupledRecurrenceSourceOnly.L s := by
  have hm := (MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity.sourceParity_eq_jr1965 hs).2
  simp only [lowerBar, OriginalU2CoupledRecurrenceSourceOnly.L,
    OriginalU2CoupledRecurrenceSourceOnly.lower, thirdTailLowerFactor,
    suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    jr1965DelayConstant, hm]
  ring

/-- The actual integral recurrence, divided by its actual amplitude and
translated by one. The upper initial endpoint is 3, hence the lower 2. -/
theorem upperA_increment {r s : ℝ} (hr : 3 ≤ r) (hrs : r ≤ s) :
    upperA s - upperA r = ∫ w in (r - 1)..(s - 1), lowerBar w / w := by
  have hrec := jr1965F_integral_recurrence (v := r) (u := s) (by linarith) hrs
  calc
    upperA s - upperA r = (s * jr1965F s - r * jr1965F r) /
        jr1965DelayConstant := by unfold upperA; ring
    _ = (∫ t in r..s, jr1965f (t - 1)) / jr1965DelayConstant := by
      rw [hrec]
      ring
    _ = ∫ t in r..s, jr1965f (t - 1) / jr1965DelayConstant :=
      (intervalIntegral.integral_div _ _).symm
    _ = ∫ w in (r - 1)..(s - 1), jr1965f w / jr1965DelayConstant :=
      intervalIntegral.integral_comp_sub_right _ 1
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [uIcc_of_le (sub_le_sub_right hrs 1)] at hw
      exact (lowerBar_div (by linarith [hw.1] : w ≠ 0)).symm

theorem upperA_integral {s : ℝ} (hs : 3 ≤ s) :
    upperA s = 1 + ∫ w in (2 : ℝ)..(s - 1), lowerBar w / w := by
  have hi := upperA_increment (r := 3) le_rfl hs
  rw [upperA_eq_one (by norm_num) le_rfl] at hi
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num] at hi
  linarith only [hi]

theorem upperA_six_tail {s : ℝ} (hs3 : 3 ≤ s) (hs6 : s ≤ 6) :
    upperA 6 - upperA s = ∫ w in (s - 1)..5, lowerBar w / w := by
  simpa only [show (6 : ℝ) - 1 = 5 by norm_num] using
    upperA_increment hs3 hs6

/-- Exactly the clipped tail occurring in the original Hnew formula.
For 2≤s≤3, A(s)=A(3)=1 and the lower cutoff remains 2. -/
theorem upperA_six_clipped_tail {s : ℝ} (hs2 : 2 ≤ s) (hs6 : s ≤ 6) :
    upperA 6 - upperA s =
      ∫ w in (max 2 (s - 1))..5, lowerBar w / w := by
  by_cases hs3 : 3 ≤ s
  · rw [max_eq_right (by linarith : (2 : ℝ) ≤ s - 1)]
    exact upperA_six_tail hs3 hs6
  · have hsle : s ≤ 3 := (lt_of_not_ge hs3).le
    rw [max_eq_left (by linarith : s - 1 ≤ (2 : ℝ)),
      upperA_eq_one (by linarith) hsle]
    have h := upperA_six_tail (s := 3) le_rfl (by norm_num)
    simpa only [upperA_eq_one (by norm_num : (0 : ℝ) < 3) le_rfl,
      show (3 : ℝ) - 1 = 2 by norm_num] using h

theorem intervalIntegrable_lowerBar_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun w => lowerBar w / w) volume a b := by
  have hf : ContinuousOn jr1965f (uIcc a b) := by
    apply continuousOn_jr1965f.mono
    intro w hw
    rw [uIcc_of_le hab] at hw
    exact ha.trans_le hw.1
  unfold lowerBar
  apply ContinuousOn.intervalIntegrable
  apply ((continuousOn_id.mul hf).div_const jr1965DelayConstant).div continuousOn_id
  intro w hw
  rw [uIcc_of_le hab] at hw
  exact ne_of_gt (ha.trans_le hw.1)

/-- This is the canonical cancellation needed before any count soundness
argument: the source upper base plus the child lower base leaves A(s). -/
theorem upper_base_cancellation {s : ℝ} (hs2 : 2 ≤ s) (hs6 : s ≤ 6)
    (h : ℝ → ℝ)
    (hh : IntervalIntegrable (fun w => h w / w) volume (max 2 (s - 1)) 5) :
    upperA 6 - (∫ w in (max 2 (s - 1))..5, (lowerBar w + h w) / w) =
      upperA s - ∫ w in (max 2 (s - 1))..5, h w / w := by
  have ha : (0 : ℝ) < max 2 (s - 1) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hb : max 2 (s - 1) ≤ (5 : ℝ) := max_le (by norm_num) (by linarith)
  have hc := intervalIntegrable_lowerBar_div ha hb
  have hi : (∫ w in (max 2 (s - 1))..5, (lowerBar w + h w) / w) =
      (∫ w in (max 2 (s - 1))..5, lowerBar w / w) +
        ∫ w in (max 2 (s - 1))..5, h w / w := by
    simp only [add_div]
    exact intervalIntegral.integral_add hc hh
  rw [hi]
  have hbase := upperA_six_clipped_tail hs2 hs6
  linarith only [hbase]

/-- The actual stored lower table supplies precisely the defect tail in
adoptedHnew. This proves cancellation, not the table's count soundness. -/
theorem adoptedHnew_base_cancellation {s : ℝ} (hs2 : 2 ≤ s) (hs6 : s ≤ 6) :
    upperA 6 -
      (∫ w in (max 2 (s - 1))..5,
        (lowerBar w + Part5UpperTables.upperFloor
          Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators w) / w) =
      upperA s - Part5UpperTables.Renewal.adoptedHnew s := by
  rw [Part5UpperTables.Renewal.adoptedHnew,
    Part5UpperTables.Renewal.upperTransition_eq_interval_raw]
  exact upper_base_cancellation hs2 hs6 _
    (Part5UpperTables.Renewal.intervalIntegrable_upperFloor_div _ _ _)

/-- On the actual child strip the raw upper lookup of the lower array is
exactly the guarded lower lookup, including its scalar seam values. -/
theorem adopted_lower_lookup_eq_upper {w : ℝ} (hw : 2 ≤ w) :
    Part5OriginalUpsilon5CausalDictionary.adoptedH248Floor w =
      Part5UpperTables.upperFloor
        Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators w := by
  exact (Part5UpperTables.upperFloor_eq_lowerFloor_of_two_le _ hw).symm

theorem adoptedHnew_literal_base_cancellation {s : ℝ} (hs2 : 2 ≤ s) (hs6 : s ≤ 6) :
    upperA 6 -
      (∫ w in (max 2 (s - 1))..5,
        (lowerBar w + Part5OriginalUpsilon5CausalDictionary.adoptedH248Floor w) / w) =
      upperA s - Part5UpperTables.Renewal.adoptedHnew s := by
  have hstart : max 2 (s - 1) ≤ (5 : ℝ) := max_le (by norm_num) (by linarith)
  have heq :
      (∫ w in (max 2 (s - 1))..5,
        (lowerBar w + Part5OriginalUpsilon5CausalDictionary.adoptedH248Floor w) / w) =
      (∫ w in (max 2 (s - 1))..5,
        (lowerBar w + Part5UpperTables.upperFloor
          Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators w) / w) := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le hstart] at hw
    rw [adopted_lower_lookup_eq_upper ((le_max_left _ _).trans hw.1)]
  rw [heq]
  exact adoptedHnew_base_cancellation hs2 hs6

/-- A pointwise PRIOR child lower estimate yields a positive marked lower
average for the exact b*p children, including repeated prime factors. -/
theorem marked_child_lower_from_pointwise {ι : Type*} (T : Finset ι)
    (sigma : ι → ℝ) (B : ι → ℕ) (N : ℕ) (z0 z1 : ℝ)
    (hsigma : ∀ t ∈ T, 0 ≤ sigma t)
    (test childError : ι → ℕ → ℝ)
    (hchild : ∀ p ∈ transitionPrimes N z0 z1, ∀ t ∈ T,
      test t p - childError t p ≤
        ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ)) :
    (∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T, sigma t * test t p) -
        (∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T, sigma t * childError t p) ≤
      ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T,
        sigma t * ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ) := by
  have hsum : (∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T,
      sigma t * (test t p - childError t p)) ≤
      ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T,
        sigma t * ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_left (hchild p hp t ht) (hsigma t ht)
  simpa only [mul_sub, Finset.sum_sub_distrib] using hsum

/-- Actual finite receiver count consequence. The hypotheses expose (a)
the endpoint upper supplier at 6, (b) prior-child lower estimates and (c)
the prime-test transport. None is a next-stage parent upper estimate.
All marks and both cutoffs stay fixed across the exact Buchstab identity. -/
theorem marked_upper_from_prior_lower_and_transport {ι : Type*}
    (T : Finset ι) (sigma : ι → ℝ) (B : ι → ℕ) (N : ℕ)
    (z0 z1 : ℝ) (hzz : z0 ≤ z1) (hsigma : ∀ t ∈ T, 0 ≤ sigma t)
    {s : ℝ} (hs2 : 2 ≤ s) (hs6 : s ≤ 6)
    (Theta anchorError transportError : ℝ) (h : ℝ → ℝ)
    (hh : IntervalIntegrable (fun w => h w / w) volume (max 2 (s - 1)) 5)
    (childTheta childCoord childError : ι → ℕ → ℝ)
    (hanchor : (∑ t ∈ T, sigma t *
      ((chenSiftedQuotientPrimeSource N (B t) z0).card : ℝ)) ≤
        upperA 6 * Theta + anchorError)
    (hchild : ∀ p ∈ transitionPrimes N z0 z1, ∀ t ∈ T,
      (lowerBar (childCoord t p) + h (childCoord t p)) * childTheta t p -
        childError t p ≤
          ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ))
    (htransport :
      (∫ w in (max 2 (s - 1))..5, (lowerBar w + h w) / w) * Theta -
        transportError ≤
      ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T,
        sigma t * ((lowerBar (childCoord t p) + h (childCoord t p)) * childTheta t p)) :
    (∑ t ∈ T, sigma t *
      ((chenSiftedQuotientPrimeSource N (B t) z1).card : ℝ)) ≤
      (upperA s - ∫ w in (max 2 (s - 1))..5, h w / w) * Theta +
        anchorError + transportError +
          ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T, sigma t * childError t p := by
  have hid := marked_buchstab_identity T sigma B N z0 z1 hzz
  have hchildren := marked_child_lower_from_pointwise T sigma B N z0 z1 hsigma
    (fun t p => (lowerBar (childCoord t p) + h (childCoord t p)) * childTheta t p)
    childError hchild
  have hcancel := congrArg (fun x : ℝ => x * Theta)
    (upper_base_cancellation hs2 hs6 h hh)
  ring_nf at hcancel
  nlinarith only [hid, hanchor, hchildren, htransport, hcancel]

/-- Same count primitive, now with the literal original adopted lower
table and its actual Hnew integral. Its global prior-table soundness and
prime-test transport are still suppliers, not conclusions of this lemma. -/
theorem adoptedHnew_marked_upper {ι : Type*}
    (T : Finset ι) (sigma : ι → ℝ) (B : ι → ℕ) (N : ℕ)
    (z0 z1 : ℝ) (hzz : z0 ≤ z1) (hsigma : ∀ t ∈ T, 0 ≤ sigma t)
    {s : ℝ} (hs2 : 2 ≤ s) (hs6 : s ≤ 6)
    (Theta anchorError transportError : ℝ)
    (childTheta childCoord childError : ι → ℕ → ℝ)
    (hanchor : (∑ t ∈ T, sigma t *
      ((chenSiftedQuotientPrimeSource N (B t) z0).card : ℝ)) ≤
        upperA 6 * Theta + anchorError)
    (hchild : ∀ p ∈ transitionPrimes N z0 z1, ∀ t ∈ T,
      (lowerBar (childCoord t p) + Part5UpperTables.upperFloor
        Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators (childCoord t p)) *
          childTheta t p - childError t p ≤
            ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ))
    (htransport :
      (∫ w in (max 2 (s - 1))..5,
        (lowerBar w + Part5UpperTables.upperFloor
          Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators w) / w) * Theta -
        transportError ≤
      ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T, sigma t *
        ((lowerBar (childCoord t p) + Part5UpperTables.upperFloor
          Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators (childCoord t p)) *
            childTheta t p)) :
    (∑ t ∈ T, sigma t *
      ((chenSiftedQuotientPrimeSource N (B t) z1).card : ℝ)) ≤
        (upperA s - Part5UpperTables.Renewal.adoptedHnew s) * Theta +
          anchorError + transportError +
            ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T, sigma t * childError t p := by
  have hout := marked_upper_from_prior_lower_and_transport T sigma B N z0 z1 hzz hsigma
    hs2 hs6 Theta anchorError transportError
    (Part5UpperTables.upperFloor Part5OriginalUpsilon5CausalDictionary.adoptedH248Numerators)
    (Part5UpperTables.Renewal.intervalIntegrable_upperFloor_div _ _ _)
    childTheta childCoord childError hanchor hchild htransport
  simpa only [Part5UpperTables.Renewal.adoptedHnew,
    Part5UpperTables.Renewal.upperTransition_eq_interval_raw] using hout

end
end ImbalancedChen.P5CanonicalUpperCancellation
