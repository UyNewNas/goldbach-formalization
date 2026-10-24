import ImbalancedChen.P1SignedExitPartition

/-!
# First different admissions of two actual retained policies

The common tree follows a selection only when both policies retain it.
Its actual exits therefore contain the first different test of every
diverging branch, plus branches both policies reject. The latter have zero
difference. Filtering into new-only and old-only admissions preserves every
actual signed mass and remaining carrier, including restored old exits.

This draft depends on the sibling source-only P1SignedExitPartition module.
-/

namespace ImbalancedChen

noncomputable section

/-- Both policies retain every selection made in the common tree. -/
def p1CommonAdmissionPolicy {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool) : Bool → List α → Bool :=
  fun positive pre => oldPolicy positive pre && newPolicy positive pre

/-- Direction of a first different admission: admitted on `admitting`,
rejected on `rejecting`. It is a Boolean filter on the actual exit list. -/
def p1AdmissionOnly {α : Type*}
    (admitting rejecting : Bool → List α → Bool) (state : FirstExitDepthState α) : Bool :=
  admitting state.positive state.selectedPrefix &&
    !rejecting state.positive state.selectedPrefix

def p1CommonExitDifference {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (state : FirstExitDepthState α) : ℝ :=
  (if newPolicy state.positive state.selectedPrefix = true then
    firstExitRetainedPolynomial newPolicy h state.selectedPrefix
      state.positive state.mass state.remaining else 0) -
  (if oldPolicy state.positive state.selectedPrefix = true then
    firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
      state.positive state.mass state.remaining else 0)

/-- The common retained prefixes cancel recursively, and the first test
that either policy rejects contributes its policy-specific continuation.
The skip branch is included exactly once at every stage. -/
theorem p1_policy_sub_eq_common_exit_sum
    {α : Type*} (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial newPolicy h pre positive mass carrier -
      firstExitRetainedPolynomial oldPolicy h pre positive mass carrier =
        ((p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
          h pre positive mass carrier).map (p1CommonExitDifference oldPolicy newPolicy h)).sum := by
  induction carrier generalizing pre positive mass with
  | nil => simp [firstExitRetainedPolynomial, p1SignedExitStates]
  | cons p ps ih =>
      have hskip := ih pre positive mass
      have hselect := ih (p :: pre) (!positive) (mass * h p)
      cases ho : oldPolicy (!positive) (p :: pre) <;>
        cases hn : newPolicy (!positive) (p :: pre) <;>
        simp [firstExitRetainedPolynomial, p1SignedExitStates,
          p1CommonAdmissionPolicy, p1CommonExitDifference, ho, hn] <;>
        rw [← hskip] <;> (try rw [← hselect]) <;> ring

/-- The split is supported by mutually exclusive directions of admission.
It does not discard a branch because it failed the old test. -/
private theorem p1_common_exit_sum_eq_admission_only_sub
    {α : Type*} (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (states : List (FirstExitDepthState α)) :
    (∀ state ∈ states,
      p1CommonAdmissionPolicy oldPolicy newPolicy state.positive state.selectedPrefix ≠ true) →
    (states.map (p1CommonExitDifference oldPolicy newPolicy h)).sum =
      (((states.filter (p1AdmissionOnly newPolicy oldPolicy)).map
        (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) -
      (((states.filter (p1AdmissionOnly oldPolicy newPolicy)).map
        (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) := by
  induction states with
  | nil => intro _; simp
  | cons state states ih =>
      intro hstates
      have htail : ∀ s ∈ states,
          p1CommonAdmissionPolicy oldPolicy newPolicy s.positive s.selectedPrefix ≠ true :=
        fun s hs => hstates s (List.mem_cons_of_mem state hs)
      have hhead := hstates state (by simp)
      cases ho : oldPolicy state.positive state.selectedPrefix <;>
        cases hn : newPolicy state.positive state.selectedPrefix <;>
        simp [p1CommonAdmissionPolicy, ho, hn] at hhead <;>
        simp [p1CommonExitDifference, p1AdmissionOnly, ho, hn, ih htail] <;> ring

/-- Exact first-difference partition: new-only continuations minus old-only
continuations, taken on the shared retained history before divergence. -/
theorem p1_policy_sub_eq_first_different_admissions
    {α : Type*} (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial newPolicy h pre positive mass carrier -
      firstExitRetainedPolynomial oldPolicy h pre positive mass carrier =
      let states := p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h pre positive mass carrier
      (((states.filter (p1AdmissionOnly newPolicy oldPolicy)).map
        (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) -
      (((states.filter (p1AdmissionOnly oldPolicy newPolicy)).map
        (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) := by
  dsimp only
  rw [p1_policy_sub_eq_common_exit_sum]
  apply p1_common_exit_sum_eq_admission_only_sub
  intro state hstate
  exact p1_mem_exitStates_rejected _ h pre carrier positive mass state hstate

/-- Root Euler terms cancel for any policies. Thus the first-difference
partition is also the signed correction difference, with the same tails. -/
theorem p1_correction_sub_eq_first_different_admissions
    {α : Type*} (oldPolicy newPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitCorrection newPolicy h pre positive mass carrier -
      firstExitCorrection oldPolicy h pre positive mass carrier =
      let states := p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h pre positive mass carrier
      (((states.filter (p1AdmissionOnly newPolicy oldPolicy)).map
        (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) -
      (((states.filter (p1AdmissionOnly oldPolicy newPolicy)).map
        (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) := by
  have hpoly := p1_policy_sub_eq_first_different_admissions
    oldPolicy newPolicy h pre carrier positive mass
  rw [firstExitRetainedPolynomial_eq_product_add_correction,
    firstExitRetainedPolynomial_eq_product_add_correction] at hpoly
  simpa only [add_sub_add_left_eq_sub] using hpoly

/-- An admission-only state carries two actual opposite test values. -/
theorem p1_mem_admissionOnly_tests
    {α : Type*} (admitting rejecting : Bool → List α → Bool)
    (states : List (FirstExitDepthState α)) (state : FirstExitDepthState α)
    (hstate : state ∈ states.filter (p1AdmissionOnly admitting rejecting)) :
    state ∈ states ∧ admitting state.positive state.selectedPrefix = true ∧
      rejecting state.positive state.selectedPrefix = false := by
  have hmem := (List.mem_filter.mp hstate).1
  have htest := (List.mem_filter.mp hstate).2
  cases ha : admitting state.positive state.selectedPrefix <;>
    cases hr : rejecting state.positive state.selectedPrefix <;>
    simp [p1AdmissionOnly, ha, hr, hmem] at htest ⊢

/-- If two policies can disagree only at rank `k`, every supported first
different test is at exactly that rank. This is a genuine support theorem,
not an equality premise about already-summed corrections. -/
theorem p1_first_different_admissions_rank
    {α : Type*} (k : ℕ) (oldPolicy newPolicy : Bool → List α → Bool)
    (hdisagree : ∀ positive pre, oldPolicy positive pre ≠ newPolicy positive pre →
      pre.length = k) (states : List (FirstExitDepthState α))
    (state : FirstExitDepthState α)
    (hstate : state ∈ states.filter (p1AdmissionOnly newPolicy oldPolicy)) :
    state.selectedPrefix.length = k := by
  obtain ⟨_hmem, hn, ho⟩ := p1_mem_admissionOnly_tests newPolicy oldPolicy states state hstate
  apply hdisagree state.positive state.selectedPrefix
  rw [ho, hn]
  decide

/-- Agreement through a retained rank prevents any admission-only branch
from being charged at that rank or earlier. -/
theorem p1_first_different_admissions_after_agreement
    {α : Type*} (k : ℕ) (oldPolicy newPolicy : Bool → List α → Bool)
    (hsame : ∀ positive pre, pre.length ≤ k →
      oldPolicy positive pre = newPolicy positive pre)
    (states : List (FirstExitDepthState α)) (state : FirstExitDepthState α)
    (hstate : state ∈ states.filter (p1AdmissionOnly newPolicy oldPolicy)) :
    k < state.selectedPrefix.length := by
  obtain ⟨_hmem, hn, ho⟩ := p1_mem_admissionOnly_tests newPolicy oldPolicy states state hstate
  by_contra hnot
  have heq := hsame state.positive state.selectedPrefix (by omega)
  rw [ho, hn] at heq
  cases heq

/-- Every retained continuation charged at a first different admission is
its real incoming signed Euler product plus its own signed exit sum. -/
theorem p1_admission_continuation_eq_signed_product_add_exit_sum
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (state : FirstExitDepthState α) :
    firstExitRetainedPolynomial retained h state.selectedPrefix
        state.positive state.mass state.remaining =
      signedTreeCoefficient state.positive state.mass *
        (state.remaining.map (fun p => 1 - h p)).prod +
      ((p1SignedExitStates retained h state.selectedPrefix
          state.positive state.mass state.remaining).map (p1SignedExitValue h)).sum := by
  rw [firstExitRetainedPolynomial_eq_product_add_correction,
    p1_firstExitCorrection_eq_exitStates_sum]

/-- Different replacements under one depth splice cannot be charged in
the common retained part of that splice. No continuation equality is assumed. -/
theorem p1_depthSplice_admissionOnly_after_rank
    {α : Type*} (k : ℕ) (parent oldReplacement newReplacement : Bool → List α → Bool)
    (states : List (FirstExitDepthState α)) (state : FirstExitDepthState α)
    (hstate : state ∈ states.filter (p1AdmissionOnly
      (firstExitDepthSplicePolicy k parent newReplacement)
      (firstExitDepthSplicePolicy k parent oldReplacement))) :
    k < state.selectedPrefix.length := by
  apply p1_first_different_admissions_after_agreement k
    (firstExitDepthSplicePolicy k parent oldReplacement)
    (firstExitDepthSplicePolicy k parent newReplacement) _ states state hstate
  intro positive pre hpre
  simp [firstExitDepthSplicePolicy, hpre]

/-- Historical fourth and fifth policies share every test through rank
four, even though their later frozen levels and own admissions may differ. -/
theorem p1_historical_fourth_fifth_agree_through_four
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (positive : Bool) (pre : List ℕ) (hpre : pre.length ≤ 4) :
    fourthCappedUpperPolicy base Q3 Q4 positive pre =
      fifthCappedUpperPolicy base Q3 Q5 positive pre := by
  simp [fourthCappedUpperPolicy, fifthCappedUpperPolicy,
    firstExitDepthSplicePolicy, hpre]

/-- Both historical directions are supported strictly after the common
rank-four tree; neither side can charge an earlier retained prefix. -/
theorem p1_historical_fourth_fifth_first_admission_rank
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (states : List (FirstExitDepthState ℕ)) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ states.filter (p1AdmissionOnly
        (fifthCappedUpperPolicy base Q3 Q5) (fourthCappedUpperPolicy base Q3 Q4)) ∨
      state ∈ states.filter (p1AdmissionOnly
        (fourthCappedUpperPolicy base Q3 Q4) (fifthCappedUpperPolicy base Q3 Q5))) :
    4 < state.selectedPrefix.length := by
  rcases hstate with hnew | hold
  · exact p1_first_different_admissions_after_agreement 4
      (fourthCappedUpperPolicy base Q3 Q4) (fifthCappedUpperPolicy base Q3 Q5)
      (p1_historical_fourth_fifth_agree_through_four base Q3 Q4 Q5) states state hnew
  · exact p1_first_different_admissions_after_agreement 4
      (fifthCappedUpperPolicy base Q3 Q5) (fourthCappedUpperPolicy base Q3 Q4)
      (fun positive pre hpre =>
        (p1_historical_fourth_fifth_agree_through_four base Q3 Q4 Q5 positive pre hpre).symm)
      states state hold

/-- Exact signed correction dictionary for the actual historical fourth
to fifth comparison. The common tree is built on the actual target-deleted
rough-prime carrier. Both restored old exits and newly removed branches are
present, with each policy's full continuation and actual remaining carrier. -/
theorem p1_actualHistoricalFourthFifth_correction_sub_eq_first_admissions
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) :
    firstExitCorrection (fifthCappedUpperPolicy base Q3 Q5)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitCorrection (fourthCappedUpperPolicy base Q3 Q4)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      let oldPolicy := fourthCappedUpperPolicy base Q3 Q4
      let newPolicy := fifthCappedUpperPolicy base Q3 Q5
      let h := fun p : ℕ => 1 / ((p : ℝ) - 1)
      let states := p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h [] true 1 (roughPrimeUniverse N cap 0 z)
      (((states.filter (p1AdmissionOnly newPolicy oldPolicy)).map
        (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) -
      (((states.filter (p1AdmissionOnly oldPolicy newPolicy)).map
        (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) := by
  exact p1_correction_sub_eq_first_different_admissions
    (fourthCappedUpperPolicy base Q3 Q4) (fifthCappedUpperPolicy base Q3 Q5)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1

/-- The actual third-capped parent to fourth-capped replacement, resolved
into first restored and first removed admissions. No monotonicity premise
is needed for an exact signed finite equality. -/
theorem p1_actualHistoricalThirdFourth_correction_sub_eq_first_admissions
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) :
    firstExitCorrection (fourthCappedUpperPolicy base Q3 Q4)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitCorrection (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      let oldPolicy := thirdCappedUpperPolicy base Q3
      let newPolicy := fourthCappedUpperPolicy base Q3 Q4
      let h := fun p : ℕ => 1 / ((p : ℝ) - 1)
      let states := p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h [] true 1 (roughPrimeUniverse N cap 0 z)
      (((states.filter (p1AdmissionOnly newPolicy oldPolicy)).map
        (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) -
      (((states.filter (p1AdmissionOnly oldPolicy newPolicy)).map
        (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) := by
  exact p1_correction_sub_eq_first_different_admissions
    (thirdCappedUpperPolicy base Q3) (fourthCappedUpperPolicy base Q3 Q4)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1

/-- The actual third-capped parent to fifth-capped own-test replacement
uses both directions of admission and each side's genuine continuation. -/
theorem p1_actualHistoricalThirdFifth_correction_sub_eq_first_admissions
    (base : Bool → List ℕ → Bool) (Q3 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) :
    firstExitCorrection (fifthCappedUpperPolicy base Q3 Q5)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitCorrection (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      let oldPolicy := thirdCappedUpperPolicy base Q3
      let newPolicy := fifthCappedUpperPolicy base Q3 Q5
      let h := fun p : ℕ => 1 / ((p : ℝ) - 1)
      let states := p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h [] true 1 (roughPrimeUniverse N cap 0 z)
      (((states.filter (p1AdmissionOnly newPolicy oldPolicy)).map
        (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) -
      (((states.filter (p1AdmissionOnly oldPolicy newPolicy)).map
        (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) := by
  exact p1_correction_sub_eq_first_different_admissions
    (thirdCappedUpperPolicy base Q3) (fifthCappedUpperPolicy base Q3 Q5)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1

end

end ImbalancedChen
