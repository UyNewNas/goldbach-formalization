import ImbalancedChen.Part5OriginalH430HistoricalPolicyGates
import ImbalancedChen.FirstExitFrontierAdmission

/-!
P5.6 / h34: an occurrence-preserving ledger of ACTUAL first-excluded
historical selection events, not a least-prime-factor owner surrogate.

The existing firstExitCorrection already contains the signed first-exit
terms, but only recursively. This packet enumerates each rejected selection
as a distinct list occurrence with its selected prefix, sign, accumulated
mass and unprocessed suffix, and proves the exact correction sum.

At an actual retained ordinary-Rosser frontier, a failing next-prefix
test yields a first-excluded event in the genuine continuation ledger.
The two original U3/U4 arithmetic rejection lanes are instantiated only
when their quotient obstruction belongs to that carrier and fails that
retention test. No universal such admission/failure is claimed.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430HistoricalRejectedExitLedger

noncomputable section
open scoped Classical
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430PhysicalCutoffOwnerOrder
open Part5OriginalH430HistoricalCandidateOrder

/-- Enumerate each literal first rejection by the SAME recursion as the
original historical firstExitCorrection. A rejected selection stops
immediately; an admitted selection continues with the flipped sign and
its genuinely updated weight. Earlier skipped elements are kept in the
list index, so distinct events are not quotiented by a product or label. -/
def historicalRejectedEvents {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FirstExitDepthState α)
  | [] => []
  | p :: ps =>
      historicalRejectedEvents retained h pre positive mass ps ++
      if retained (!positive) (p :: pre) = true then
        historicalRejectedEvents retained h (p :: pre) (!positive)
          (mass * h p) ps
      else
        [{ selectedPrefix := p :: pre
           positive := !positive
           mass := mass * h p
           remaining := ps }]

/-- The literal first-exit contribution, including its historical sign
and the residual Euler product on exactly the remaining smaller labels. -/
def historicalExitValue {α : Type*} (h : α → ℝ)
    (event : FirstExitDepthState α) : ℝ :=
  -signedTreeCoefficient event.positive event.mass *
    (event.remaining.map (fun q => 1 - h q)).prod

/-- All first-exit correction terms, with their literal occurrence count,
are exactly the values of the enumerated rejected events. This uses the
ORIGINAL recursive correction and has no new analytic input or licence. -/
theorem historical_rejected_events_sum_eq_correction {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    ((historicalRejectedEvents retained h pre positive mass remaining).map
      (historicalExitValue h)).sum =
      firstExitCorrection retained h pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [historicalRejectedEvents, firstExitCorrection]
  | cons p ps ih =>
      by_cases hp : retained (!positive) (p :: pre) = true
      · simp [historicalRejectedEvents, firstExitCorrection, hp,
          ih pre positive mass, ih (p :: pre) (!positive) (mass * h p)]
      · simp [historicalRejectedEvents, firstExitCorrection, hp,
          historicalExitValue, ih pre positive mass]

/-- A real remaining-carrier occurrence with a FAILED selection test
produces its literal first-excluded event, with the exact residual suffix.
The condition is the actual local policy failure, not a hypothesis that
the global desired count identity is true. -/
theorem rejected_remaining_has_literal_event {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    {remaining : List α} {r : α}
    (hmem : r ∈ remaining)
    (hreject : retained (!positive) (r :: pre) = false) :
    ∃ before after, remaining = before ++ r :: after ∧
      ({ selectedPrefix := r :: pre
         positive := !positive
         mass := mass * h r
         remaining := after } : FirstExitDepthState α) ∈
        historicalRejectedEvents retained h pre positive mass remaining := by
  induction remaining with
  | nil => cases hmem
  | cons p ps ih =>
      rcases List.mem_cons.mp hmem with hpr | htail
      · subst p
        refine ⟨[], ps, rfl, ?_⟩
        simp [historicalRejectedEvents, hreject]
      · obtain ⟨before, after, hsplit, hexit⟩ := ih htail
        refine ⟨p :: before, after, ?_, ?_⟩
        · simp [hsplit]
        · exact List.mem_append_left _ hexit

/-- At a REAL full ordinary-Rosser frontier the incoming history is
already retained. Failure of the next selected prefix then yields a
literal first-excluded event of its actual unprocessed suffix; the parent
and failed child cannot be confused with the arithmetic least factor. -/
theorem ordinary_frontier_first_excluded_event
    (N cap k : ℕ) (hk : 0 < k) (lower : Bool) (Q z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z))
    {r : ℕ} (hremaining : r ∈ frontier.remaining)
    (hfailed : ¬ordinaryRosserPrefixAdmissible lower Q
      (r :: frontier.selectedPrefix)) :
    ordinaryRosserPrefixAdmissible lower Q frontier.selectedPrefix ∧
      ∃ before after, frontier.remaining = before ++ r :: after ∧
        ({ selectedPrefix := r :: frontier.selectedPrefix
           positive := !frontier.positive
           mass := frontier.mass * (1 / ((r : ℝ) - 1))
           remaining := after } : FirstExitDepthState ℕ) ∈
          historicalRejectedEvents (ordinaryRosserRetainedPolicy lower Q)
            (fun p : ℕ => 1 / ((p : ℝ) - 1))
            frontier.selectedPrefix frontier.positive frontier.mass
            frontier.remaining := by
  have hparent :=
    mem_firstExitDepthFrontier_ordinaryRosser_admissible_of_pos
      lower Q k hk (fun p : ℕ => 1 / ((p : ℝ) - 1))
      (roughPrimeUniverse N cap 0 z) frontier hfrontier
  have hfail : ordinaryRosserRetainedPolicy lower Q
      (!frontier.positive) (r :: frontier.selectedPrefix) = false := by
    simp [ordinaryRosserRetainedPolicy, hfailed]
  obtain ⟨before, after, hsplit, hexit⟩ :=
    rejected_remaining_has_literal_event
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass
      hremaining hfail
  exact ⟨hparent, before, after, hsplit, hexit⟩

/-- The ORIGINAL ordinary-Rosser root correction is an exact sum over
actual first-excluded history occurrences, with no unsigned replacement. -/
theorem ordinary_root_correction_eq_rejected_events
    (N cap : ℕ) (lower : Bool) (Q z : ℝ) :
    firstExitCorrection (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z) =
    ((historicalRejectedEvents (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z)).map
        (historicalExitValue (fun p : ℕ => 1 / ((p : ℝ) - 1)))).sum := by
  exact (historical_rejected_events_sum_eq_correction
    (ordinaryRosserRetainedPolicy lower Q)
    (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] (roughPrimeUniverse N cap 0 z) true 1).symm

/-- Conditional but literal frozenOnly owner: its FIRST BAD QUOTIENT
factor has to be present in the retained historical carrier and actually
fail the ordinary prefix test. These two conditions remain to be proved
for the complete original selected-count source. -/
theorem frozen_only_quotient_first_exit
    (N n cap k : ℕ) (hk : 0 < k) (tau z Q : ℝ)
    (lower : Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z))
    {receiver : TaggedReceiver} (hr : receiver ∈ frozenOnly N n tau)
    (hq : ¬ChenPrimeRough (arithmeticPrime receiver : ℝ)
      (arithmeticQuotientPrime receiver))
    (hremaining : firstBadPrime (arithmeticQuotientPrime receiver)
      ((N : ℝ)^a) ∈ frontier.remaining)
    (hfailed : ¬ordinaryRosserPrefixAdmissible lower Q
      (firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) ::
        frontier.selectedPrefix)) :
    ordinaryRosserPrefixAdmissible lower Q frontier.selectedPrefix ∧
      jointFirstPrime receiver ((N : ℝ)^a) =
        firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) ∧
      ∃ before after,
        frontier.remaining = before ++
          firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) :: after ∧
        ({ selectedPrefix :=
             firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) ::
               frontier.selectedPrefix
           positive := !frontier.positive
           mass := frontier.mass *
             (1 / ((firstBadPrime (arithmeticQuotientPrime receiver)
               ((N : ℝ)^a) : ℝ) - 1))
           remaining := after } : FirstExitDepthState ℕ) ∈
          historicalRejectedEvents (ordinaryRosserRetainedPolicy lower Q)
            (fun p : ℕ => 1 / ((p : ℝ) - 1))
            frontier.selectedPrefix frontier.positive frontier.mass
            frontier.remaining := by
  have hnot : ¬ ChenPrimeRough ((N : ℝ)^a)
      (arithmeticQuotientPrime receiver) :=
    bad_implies_not_rough (frozen_only_tagged_first_bad N n tau hr).1
  have hfirst := (joint_eq_bad_of_quotient_not_rough receiver hnot hq).1
  obtain ⟨hparent, before, after, hsplit, hexit⟩ :=
    ordinary_frontier_first_excluded_event N cap k hk lower Q z frontier
      hfrontier hremaining hfailed
  exact ⟨hparent, hfirst, before, after, hsplit, hexit⟩

/-- The distinct rejectedFrozen lane uses its own ACTUAL frozen cutoff.
It is not identified with frozenOnly or paid merely by an event witness. -/
theorem rejected_frozen_quotient_first_exit
    (N n cap k : ℕ) (hk : 0 < k) (tau z Q : ℝ)
    (lower : Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z))
    {receiver : TaggedReceiver} (hr : receiver ∈ rejectedFrozen N n tau)
    (hq : ¬ChenPrimeRough (arithmeticPrime receiver : ℝ)
      (arithmeticQuotientPrime receiver))
    (hremaining : firstBadPrime (arithmeticQuotientPrime receiver)
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver)) ∈ frontier.remaining)
    (hfailed : ¬ordinaryRosserPrefixAdmissible lower Q
      (firstBadPrime (arithmeticQuotientPrime receiver)
        (frozenPrimeCutoff N n tau (arithmeticBand receiver)
          (arithmeticPrime receiver)) :: frontier.selectedPrefix)) :
    ordinaryRosserPrefixAdmissible lower Q frontier.selectedPrefix ∧
      jointFirstPrime receiver
        (frozenPrimeCutoff N n tau (arithmeticBand receiver)
          (arithmeticPrime receiver)) =
        firstBadPrime (arithmeticQuotientPrime receiver)
          (frozenPrimeCutoff N n tau (arithmeticBand receiver)
            (arithmeticPrime receiver)) ∧
      ∃ before after,
        frontier.remaining = before ++
          firstBadPrime (arithmeticQuotientPrime receiver)
            (frozenPrimeCutoff N n tau (arithmeticBand receiver)
              (arithmeticPrime receiver)) :: after ∧
        ({ selectedPrefix :=
             firstBadPrime (arithmeticQuotientPrime receiver)
               (frozenPrimeCutoff N n tau (arithmeticBand receiver)
                 (arithmeticPrime receiver)) :: frontier.selectedPrefix
           positive := !frontier.positive
           mass := frontier.mass *
             (1 / ((firstBadPrime (arithmeticQuotientPrime receiver)
               (frozenPrimeCutoff N n tau (arithmeticBand receiver)
                 (arithmeticPrime receiver)) : ℝ) - 1))
           remaining := after } : FirstExitDepthState ℕ) ∈
          historicalRejectedEvents (ordinaryRosserRetainedPolicy lower Q)
            (fun p : ℕ => 1 / ((p : ℝ) - 1))
            frontier.selectedPrefix frontier.positive frontier.mass
            frontier.remaining := by
  have hnot : ¬ChenPrimeRough
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver))
      (arithmeticQuotientPrime receiver) :=
    bad_implies_not_rough (rejected_frozen_tagged_first_bad N n tau hr)
  have hfirst := (joint_eq_bad_of_quotient_not_rough receiver hnot hq).1
  obtain ⟨hparent, before, after, hsplit, hexit⟩ :=
    ordinary_frontier_first_excluded_event N cap k hk lower Q z frontier
      hfrontier hremaining hfailed
  exact ⟨hparent, hfirst, before, after, hsplit, hexit⟩

end
end ImbalancedChen.Part5OriginalH430HistoricalRejectedExitLedger
