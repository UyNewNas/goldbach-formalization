import ImbalancedChen.Part5OriginalH430TrueReceiverWeightedExit

/-!
P5.6 / h34 — EVEN-N SIGN AND SIZE OF THE ACTUAL RANK-TWO EXIT.

Unlike a bare positive (p,ell) receipt, the genuine selected rank-two
historical correction is NEGATIVE.  The original even-N hypothesis
excludes the prime 2 from its remaining rough-prime carrier.  Hence
every remaining Euler factor belongs to [0,1].  This packet proves
that the actual signed correction is between -W(p,ell) and zero.

Consequently the last packet's original q/tag-dependent unpaid receipt
gap is *at least* the literal receiver weight and at most that weight
plus one bare event mass per DISTINCT key.  This is a directional,
quantitative obstruction, NOT a payment or full count/owner closure.
The six non-event lanes remain unchanged.  Actual history occurrences,
original labels and the original sign are preserved.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED.  No new analytic input.
-/

namespace ImbalancedChen.Part5OriginalH430EvenSignedExitBounds

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430TrueReceiverWeightedExit

/-- The literal remaining list of any real rejected historical event
uses only entries of its starting carrier.  It is NOT a newly assumed
Euler-product bound or a replacement for the historical recursion. -/
private theorem historical_remaining_member {α : Type*}
    (retained : Bool → List α → Bool) (weight : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    ∀ e ∈ historicalRejectedEvents retained weight pre positive mass remaining,
      ∀ q ∈ e.remaining, q ∈ remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      intro e he
      simp [historicalRejectedEvents] at he
  | cons p ps ih =>
      intro e he q hq
      by_cases hpass : retained (!positive) (p :: pre) = true
      · simp [historicalRejectedEvents, hpass] at he
        rcases he with hskip | hdesc
        · exact List.mem_cons_of_mem _ (ih pre positive mass e hskip q hq)
        · exact List.mem_cons_of_mem _
            (ih (p :: pre) (!positive) (mass * weight p) e hdesc q hq)
      · have hfail : retained (!positive) (p :: pre) = false := by
          cases h : retained (!positive) (p :: pre) <;> simp_all
        simp [historicalRejectedEvents, hfail] at he
        rcases he with hskip | hsingle
        · exact List.mem_cons_of_mem _ (ih pre positive mass e hskip q hq)
        · subst e
          exact List.mem_cons_of_mem _ hq

/-- At even N, 2 is excluded by the *actual* p∤N rough-prime
carrier.  Thus every literal remaining Euler factor is in [0,1].
No positivity of an arbitrarily supplied suffix is assumed. -/
private theorem even_rough_euler_factor_bounds
    (N cap q : ℕ) (z : ℝ) (hEven : 2 ∣ N)
    (hq : q ∈ roughPrimeUniverse N cap 0 z) :
    0 ≤ (1 : ℝ) - 1 / ((q : ℝ) - 1) ∧
      (1 : ℝ) - 1 / ((q : ℝ) - 1) ≤ 1 := by
  have hprime : q.Prime := mem_roughPrimeUniverse_prime hq
  have hnot : ¬q ∣ N := mem_roughPrimeUniverse_not_dvd hq
  have hqne : q ≠ 2 := by
    intro heq
    subst q
    exact hnot hEven
  have hq3 : 3 ≤ q := by
    have hq2 := hprime.two_le
    omega
  have hq3r : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hden : 0 < (q : ℝ) - 1 := by linarith
  have hdiv_nonneg : 0 ≤ (1 : ℝ) / ((q : ℝ) - 1) :=
    div_nonneg (by norm_num) hden.le
  have hdiv_le : (1 : ℝ) / ((q : ℝ) - 1) ≤ 1 :=
    (div_le_iff₀ hden).2 (by linarith)
  constructor <;> linarith

/-- A suffix of the actual odd-prime carrier has an Euler product
between zero and one.  In particular its sign cannot be postulated
independently of the original even-N arithmetic source. -/
private theorem even_rough_euler_product_bounds
    (N cap : ℕ) (z : ℝ) (hEven : 2 ∣ N)
    (remaining : List ℕ) :
    (∀ q ∈ remaining, q ∈ roughPrimeUniverse N cap 0 z) →
      0 ≤ (remaining.map
          (fun q : ℕ => 1 - 1 / ((q : ℝ) - 1))).prod ∧
      (remaining.map
          (fun q : ℕ => 1 - 1 / ((q : ℝ) - 1))).prod ≤ 1 := by
  induction remaining with
  | nil =>
      intro _
      simp
  | cons p ps ih =>
      intro hsub
      have hp : p ∈ roughPrimeUniverse N cap 0 z :=
        hsub p (by simp)
      have htail : ∀ q ∈ ps, q ∈ roughPrimeUniverse N cap 0 z := by
        intro q hq
        exact hsub q (by simp [hq])
      obtain ⟨hfactor0, hfactor1⟩ :=
        even_rough_euler_factor_bounds N cap p z hEven hp
      obtain ⟨hprod0, hprod1⟩ := ih htail
      simp only [List.map_cons, List.prod_cons]
      constructor
      · exact mul_nonneg hfactor0 hprod0
      · calc
          (1 - 1 / ((p : ℝ) - 1)) *
              (ps.map (fun q : ℕ => 1 - 1 / ((q : ℝ) - 1))).prod
              ≤ 1 * (ps.map
                  (fun q : ℕ => 1 - 1 / ((q : ℝ) - 1))).prod :=
                mul_le_mul_of_nonneg_right hfactor1 hprod0
          _ = (ps.map
                  (fun q : ℕ => 1 - 1 / ((q : ℝ) - 1))).prod := by ring
          _ ≤ 1 := hprod1

/-- Every original key in the genuine fourth lanes contains two
actual primes: the original selected p and the true first bad ell.
The arithmetic quotient q itself is NOT asserted prime. -/
private theorem original_fourth_key_primes
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (key : EventKey)
    (hk : key ∈ fourthDistinctKeys N n tau z0 Q lower) :
    key.1.Prime ∧ key.2.Prime := by
  unfold fourthDistinctKeys at hk
  rcases Finset.mem_union.mp hk with hf | hr
  · change key ∈
        (fourthFrozenFail N n tau z0 Q lower).image
          (receiverEventKey (frozenOnlyBad N)) at hf
    rcases Finset.mem_image.mp hf with ⟨z, hz, hkey⟩
    have hzOwn : z ∈ ownPolicyFail (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 Q lower := by
      simpa [fourthFrozenFail] using hz
    have hzFrozen : z ∈ frozenOnly N n tau :=
      (Finset.mem_filter.mp hzOwn).1
    have hp : (arithmeticPrime z).Prime :=
      (original_band_prime
        (frozen_tagged_band (Finset.mem_sdiff.mp hzFrozen).1)).1
    have hell : (frozenOnlyBad N z).Prime :=
      (frozen_only_tagged_first_bad N n tau hzFrozen).1
    rw [← hkey]
    exact ⟨hp, hell⟩
  · change key ∈
        (fourthRejectedFail N n tau z0 Q lower).image
          (receiverEventKey (rejectedFrozenBad N n tau)) at hr
    rcases Finset.mem_image.mp hr with ⟨z, hz, hkey⟩
    have hzOwn : z ∈ ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower := by
      simpa [fourthRejectedFail] using hz
    have hzRej : z ∈ rejectedFrozen N n tau :=
      (Finset.mem_filter.mp hzOwn).1
    have hzRaw : z ∈ rawTagged N :=
      (Finset.mem_sdiff.mp hzRej).1
    have hp : (arithmeticPrime z).Prime := by
      cases z with
      | inl v =>
          have hv : v ∈ rawPairs N .U3 := by
            simpa [rawTagged] using hzRaw
          simpa [arithmeticPrime] using
            (original_band_prime (Finset.mem_sigma.mp hv).1).1
      | inr v =>
          have hv : v ∈ rawPairs N .U4 := by
            simpa [rawTagged] using hzRaw
          simpa [arithmeticPrime] using
            (original_band_prime (Finset.mem_sigma.mp hv).1).1
    have hell : (rejectedFrozenBad N n tau z).Prime :=
      (rejected_frozen_tagged_first_bad N n tau hzRej).1
    rw [← hkey]
    exact ⟨hp, hell⟩

private theorem original_fourth_key_mass_nonneg
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (key : EventKey)
    (hk : key ∈ fourthDistinctKeys N n tau z0 Q lower) :
    0 ≤ originalEventMass key := by
  obtain ⟨hp, hell⟩ :=
    original_fourth_key_primes N n tau z0 Q lower key hk
  have hpr : (2 : ℝ) ≤ (key.1 : ℝ) := by
    exact_mod_cast hp.two_le
  have hlr : (2 : ℝ) ≤ (key.2 : ℝ) := by
    exact_mod_cast hell.two_le
  have hdp : 0 < (key.1 : ℝ) - 1 := by linarith
  have hdl : 0 < (key.2 : ℝ) - 1 := by linarith
  unfold originalEventMass
  exact mul_nonneg (div_nonneg (by norm_num) hdp.le)
    (div_nonneg (by norm_num) hdl.le)

/-- Actual h34 rank-two correction: on the genuine ORIGINAL event
key and an even N, it lies in [-W,0].  The actual unique event and
its literal unprocessed suffix are used, with the original negative
historical sign.  There is no global owner/filter claim here. -/
theorem original_fourth_key_signed_exit_interval
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (key : EventKey)
    (hk : key ∈ fourthDistinctKeys N n tau z0 Q lower) :
    -originalEventMass key ≤
      actualRankTwoSignedExit N cap lower Q key ∧
      actualRankTwoSignedExit N cap lower Q key ≤ 0 := by
  obtain ⟨event, hsingle, _, hpositive, hmass⟩ :=
    original_fourth_lane_key_unique_signed_event
      N n cap tau z0 Q lower hzcap key (by simpa [fourthDistinctKeys] using hk)
  have hevent : event ∈ actualRankTwoHistory N cap lower Q key := by
    rw [hsingle]
    simp
  have hraw : event ∈ historicalRejectedEvents
      (ordinaryRosserRetainedPolicy lower Q)
      (fun q : ℕ => 1 / ((q : ℝ) - 1))
      [key.1] false (1 / ((key.1 : ℝ) - 1))
      (roughPrimeUniverse N cap 0 (key.1 : ℝ)) := by
    exact (List.mem_filter.mp
      (by simpa only [actualRankTwoHistory] using hevent)).1
  have hsuffix : ∀ q ∈ event.remaining,
      q ∈ roughPrimeUniverse N cap 0 (key.1 : ℝ) := by
    intro q hq
    exact historical_remaining_member
      (ordinaryRosserRetainedPolicy lower Q)
      (fun x : ℕ => 1 / ((x : ℝ) - 1))
      [key.1] false (1 / ((key.1 : ℝ) - 1))
      (roughPrimeUniverse N cap 0 (key.1 : ℝ))
      event hraw q hq
  obtain ⟨hprod0, hprod1⟩ :=
    even_rough_euler_product_bounds N cap
      (key.1 : ℝ) hEven event.remaining hsuffix
  have hm0 : 0 ≤ originalEventMass key :=
    original_fourth_key_mass_nonneg N n tau z0 Q lower key hk
  have hval : actualRankTwoSignedExit N cap lower Q key =
      -originalEventMass key *
        (event.remaining.map
          (fun q : ℕ => 1 - 1 / ((q : ℝ) - 1))).prod := by
    simp [actualRankTwoSignedExit, hsingle,
      historicalExitValue, hpositive, hmass]
  have hlow := mul_nonneg hm0 hprod0
  have hhigh := mul_le_mul_of_nonneg_left hprod1 hm0
  rw [hval]
  constructor <;> nlinarith

/-- The genuine tagged q-dependent key gap cannot be erased by the
negative signed exit.  It lies BETWEEN the literal receipt and that
receipt plus ONE bare key mass.  No positivity assumption on w is
needed for these inequalities: all signs are in the actual exit. -/
theorem original_fourth_key_receipt_gap_interval
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (w : TaggedReceiver → ℝ)
    (key : EventKey)
    (hk : key ∈ fourthDistinctKeys N n tau z0 Q lower) :
    fourthKeyReceipt N n tau z0 Q lower w key ≤
      fourthKeyReceipt N n tau z0 Q lower w key -
        actualRankTwoSignedExit N cap lower Q key ∧
    fourthKeyReceipt N n tau z0 Q lower w key -
        actualRankTwoSignedExit N cap lower Q key ≤
      fourthKeyReceipt N n tau z0 Q lower w key +
        originalEventMass key := by
  obtain ⟨hlow, hhigh⟩ :=
    original_fourth_key_signed_exit_interval
      N n cap tau z0 Q lower hEven hzcap key hk
  constructor <;> linarith

/-- Full DISTINCT-key quantitative interval.  Different q/tag
receipts are counted in the same key but the signed Euler event is
subtracted only once.  These are bounds on the UNPAID residual,
not a proof that the residual is funded by a selected history. -/
theorem original_fourth_total_receipt_gap_interval
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ))
    (w : TaggedReceiver → ℝ) :
    (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
      fourthKeyReceipt N n tau z0 Q lower w key) ≤
    (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
      fourthKeyReceipt N n tau z0 Q lower w key -
        actualRankTwoSignedExit N cap lower Q key) ∧
    (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
      fourthKeyReceipt N n tau z0 Q lower w key -
        actualRankTwoSignedExit N cap lower Q key) ≤
    (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
      fourthKeyReceipt N n tau z0 Q lower w key +
        originalEventMass key) := by
  constructor
  · apply Finset.sum_le_sum
    intro key hk
    exact (original_fourth_key_receipt_gap_interval
      N n cap tau z0 Q lower hEven hzcap w key hk).1
  · apply Finset.sum_le_sum
    intro key hk
    exact (original_fourth_key_receipt_gap_interval
      N n cap tau z0 Q lower hEven hzcap w key hk).2

/-- For the actual UNIT arithmetic count, the unpaid fourth-lane
gap is at least the total number of genuine fourth-lane receivers.
A negative Euler first-exit correction therefore cannot itself
pay a positive rejected receiver.  This is an explicit obstruction
to treating the previous exact identity as a completed payment. -/
theorem original_unit_fourth_receiver_gap_lower
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hEven : 2 ∣ N) (hzcap : z0 ≤ (cap : ℝ)) :
    ((fourthFrozenFail N n tau z0 Q lower).card : ℝ) +
      ((fourthRejectedFail N n tau z0 Q lower).card : ℝ) ≤
    ∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
      fourthKeyReceipt N n tau z0 Q lower (fun _ => 1) key -
        actualRankTwoSignedExit N cap lower Q key := by
  have hsum := (original_fourth_total_receipt_gap_interval
    N n cap tau z0 Q lower hEven hzcap (fun _ => 1)).1
  have hcount :=
    two_source_true_weight_sum_by_keys
      (fourthFrozenFail N n tau z0 Q lower)
      (fourthRejectedFail N n tau z0 Q lower)
      (frozenOnlyBad N) (rejectedFrozenBad N n tau)
      (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
  have hcard :
      (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
        fourthKeyReceipt N n tau z0 Q lower (fun _ => 1) key) =
      ((fourthFrozenFail N n tau z0 Q lower).card : ℝ) +
        ((fourthRejectedFail N n tau z0 Q lower).card : ℝ) := by
    simpa [fourthDistinctKeys, fourthKeyReceipt] using hcount
  rw [← hcard]
  exact hsum

end
end ImbalancedChen.Part5OriginalH430EvenSignedExitBounds
