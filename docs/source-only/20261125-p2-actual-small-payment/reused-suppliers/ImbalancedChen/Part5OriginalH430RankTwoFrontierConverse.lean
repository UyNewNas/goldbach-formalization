import ImbalancedChen.Part5OriginalH430ActualRankTwoFrontierSupport
import ImbalancedChen.FirstExitFrontierInvariants
import ImbalancedChen.FirstExitCandidateGeometry

/-!
P5.6 / h34: CONVERSE of actual rank-two frontier support, and
state-level uniqueness for a fixed ordered selected prefix.

This reverses the previous one-way rank-two support using the literal
skip/select recursion, NOT an assumed frontier-to-owner licence.
The ordinary policy is tested at both actual choices; Q is the
tag/root-specific originalPhysicalQ. A frontier state with prefix
[ell,p] is equivalent to two literal policy-retained selections
at p and ell, without claiming ell divides the original quotient q.

Uniqueness is ONLY of state values for a fixed physical Q and prefix.
It does NOT establish list-position uniqueness, a q/tag owner,
inherited/selected/full filtering, or historical mass payment.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430RankTwoFrontierConverse

noncomputable section
open scoped Classical
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430ActualRankTwoFrontierSupport

/-! One step short of the requested rank, every frontier member
arises from a real admitted next-choice, with skipped labels
accounted for by the literal recursion. -/
private theorem one_step_frontier_is_next
    {α : Type*} (k : ℕ) (policy : Bool → List α → Bool)
    (weight : α → ℝ) (pre : List α) (positive : Bool)
    (mass : ℝ) (remaining : List α) (state : FirstExitDepthState α)
    (hstep : pre.length + 1 = k)
    (hstate : state ∈ firstExitDepthFrontier k policy weight
      pre positive mass remaining) :
    ∃ c : FirstExitDepthState α,
      c ∈ firstExitNextSelectionCandidates weight pre positive mass remaining ∧
      policy c.positive c.selectedPrefix = true ∧ c = state := by
  induction remaining with
  | nil =>
      have hk : ¬ k ≤ pre.length := by omega
      simp [firstExitDepthFrontier, hk] at hstate
  | cons p ps ih =>
      have hk : ¬ k ≤ pre.length := by omega
      by_cases hpass : policy (!positive) (p :: pre) = true
      · rw [firstExitDepthFrontier, if_neg hk, if_pos hpass,
          List.mem_append] at hstate
        rcases hstate with hskip | hselect
        · obtain ⟨c, hc, hpol, heq⟩ := ih hskip
          refine ⟨c, ?_, hpol, heq⟩
          simp only [firstExitNextSelectionCandidates_cons, List.mem_cons]
          exact Or.inr hc
        · have hreach : k ≤ (p :: pre).length := by
            simp only [List.length_cons]
            omega
          rw [firstExitDepthFrontier_of_rank_le_length
            k policy weight (p :: pre) ps (!positive)
              (mass * weight p) hreach, List.mem_singleton] at hselect
          subst state
          refine ⟨{selectedPrefix := p :: pre, positive := !positive,
            mass := mass * weight p, remaining := ps}, ?_, hpass, rfl⟩
          simp [firstExitNextSelectionCandidates_cons]
      · rw [firstExitDepthFrontier, if_neg hk, if_neg hpass,
          List.append_nil] at hstate
        obtain ⟨c, hc, hpol, heq⟩ := ih hstate
        refine ⟨c, ?_, hpol, heq⟩
        simp only [firstExitNextSelectionCandidates_cons, List.mem_cons]
        exact Or.inr hc

/-- Reverse the original rank-two recursion into TWO admitted literal
next selections. The proof follows the skip arm and the first admitted
root arm; it does not synthesize a policy-test hypothesis. -/
private theorem two_step_frontier_is_two_nexts
    {α : Type*} (policy : Bool → List α → Bool)
    (weight : α → ℝ) (carrier : List α) (d : FirstExitDepthState α)
    (hd : d ∈ firstExitDepthFrontier 2 policy weight [] true 1 carrier) :
    ∃ c : FirstExitDepthState α,
      c ∈ firstExitNextSelectionCandidates weight [] true 1 carrier ∧
      policy c.positive c.selectedPrefix = true ∧
      d ∈ firstExitNextSelectionCandidates weight
        c.selectedPrefix c.positive c.mass c.remaining ∧
      policy d.positive d.selectedPrefix = true := by
  induction carrier with
  | nil =>
      simp [firstExitDepthFrontier] at hd
  | cons p ps ih =>
      have hk : ¬ 2 ≤ ([] : List α).length := by decide
      by_cases hpass : policy (!true) (p :: []) = true
      · rw [firstExitDepthFrontier, if_neg hk, if_pos hpass,
          List.mem_append] at hd
        rcases hd with hskip | hselect
        · obtain ⟨c, hc, hroot, hnext, hsecond⟩ := ih hskip
          refine ⟨c, ?_, hroot, hnext, hsecond⟩
          simp only [firstExitNextSelectionCandidates_cons, List.mem_cons]
          exact Or.inr hc
        · have hstep : ([p] : List α).length + 1 = 2 := by decide
          obtain ⟨next, hnext, hsecond, heq⟩ :=
            one_step_frontier_is_next 2 policy weight
              [p] (!true) (1 * weight p) ps d hstep hselect
          subst next
          refine ⟨{selectedPrefix := [p], positive := !true,
            mass := 1 * weight p, remaining := ps}, ?_,
              hpass, hnext, hsecond⟩
          simp [firstExitNextSelectionCandidates_cons]
      · rw [firstExitDepthFrontier, if_neg hk, if_neg hpass,
          List.append_nil] at hd
        obtain ⟨c, hc, hroot, hnext, hsecond⟩ := ih hd
        refine ⟨c, ?_, hroot, hnext, hsecond⟩
        simp only [firstExitNextSelectionCandidates_cons, List.mem_cons]
        exact Or.inr hc

/-- A genuine rank-two frontier state with EXACT prefix [ell,p]
must have passed the original first and second Rosser admission
tests at the SAME physical per-(tag,p) Q. This is a converse to
the earlier support theorem; ell | q is not manufactured here. -/
theorem actual_rank_two_frontier_implies_retained_original_second
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ) (d : FirstExitDepthState ℕ)
    (hd : d ∈ firstExitDepthFrontier 2
      (ordinaryRosserRetainedPolicy lower
        (originalPhysicalQ N precision tau z))
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hprefix : d.selectedPrefix = [ell, arithmeticPrime z]) :
    retainedOriginalSecond N cap precision tau z0 lower z ell := by
  let policy : Bool → List ℕ → Bool :=
    ordinaryRosserRetainedPolicy lower (originalPhysicalQ N precision tau z)
  let weight : ℕ → ℝ := fun r => 1 / ((r : ℝ) - 1)
  obtain ⟨c, hc, hroot, hnext, hsecond⟩ :=
    two_step_frontier_is_two_nexts policy weight
      (roughPrimeUniverse N cap 0 z0) d hd
  obtain ⟨before, q, after, hcarrier, hdstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      weight c.selectedPrefix c.remaining c.positive c.mass d).mp hnext
  have hcprefix : c.selectedPrefix = [arithmeticPrime z] := by
    rw [hdstate] at hprefix
    change q :: c.selectedPrefix = ell :: [arithmeticPrime z] at hprefix
    exact (List.cons.inj hprefix).2
  have hdpre : d.selectedPrefix = ell :: c.selectedPrefix := by
    simpa only [hcprefix] using hprefix
  exact ⟨c, d, hc, hcprefix, hroot, hnext, hdpre, hsecond⟩

/-- Exact two-way correspondence of *admission/existence*:
actual rank-two history membership, rather than merely two
unrelated enumeration candidates. This remains distinct from
a q-specific owner and from any count or mass payment. -/
theorem retained_original_second_iff_actual_rank_two
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ) :
    retainedOriginalSecond N cap precision tau z0 lower z ell ↔
      ∃ d : FirstExitDepthState ℕ,
        d ∈ firstExitDepthFrontier 2
          (ordinaryRosserRetainedPolicy lower
            (originalPhysicalQ N precision tau z))
          (fun r : ℕ => 1 / ((r : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
        d.selectedPrefix = [ell, arithmeticPrime z] := by
  constructor
  · intro hret
    obtain ⟨d, hd, hprefix, _hsign, _hmass⟩ :=
      retained_original_second_in_actual_rank_two_frontier
        N cap precision tau z0 lower z ell hret
    exact ⟨d, hd, hprefix⟩
  · rintro ⟨d, hd, hprefix⟩
    exact actual_rank_two_frontier_implies_retained_original_second
      N cap precision tau z0 lower z ell d hd hprefix

/-- For fixed genuine policy, root carrier and ordered prefix,
a positive-rank frontier determines the ENTIRE state value:
sign, historical product mass and exact remaining suffix.
No Nodup/list-position theorem is claimed. -/
theorem actual_frontier_state_determined_by_prefix
    (k : ℕ) (hk : 0 < k) (N cap : ℕ) (z0 Q : ℝ)
    (lower : Bool) (d e : FirstExitDepthState ℕ)
    (hd : d ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (he : e ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hp : d.selectedPrefix = e.selectedPrefix) : d = e := by
  let policy : Bool → List ℕ → Bool := ordinaryRosserRetainedPolicy lower Q
  let weight : ℕ → ℝ := fun r => 1 / ((r : ℝ) - 1)
  obtain ⟨p, tail, hdp, _hmem, hdr⟩ :=
    mem_firstExitDepthFrontier_roughPrime_remaining
      k hk policy weight N cap 0 z0 d hd
  obtain ⟨q, tail', hep, _hmem', her⟩ :=
    mem_firstExitDepthFrontier_roughPrime_remaining
      k hk policy weight N cap 0 z0 e he
  have hpq : p = q := by
    have h : p :: tail = q :: tail' := by
      calc
        p :: tail = d.selectedPrefix := hdp.symm
        _ = e.selectedPrefix := hp
        _ = q :: tail' := hep
    exact (List.cons.inj h).1
  have hrem : d.remaining = e.remaining := by
    calc
      d.remaining = roughPrimeUniverse N cap 0 (p : ℝ) := hdr
      _ = roughPrimeUniverse N cap 0 (q : ℝ) := by rw [hpq]
      _ = e.remaining := her.symm
  have hsign : d.positive = e.positive := by
    calc
      d.positive = evenListLength d.selectedPrefix :=
        mem_firstExitDepthFrontier_positive_eq_evenListLength
          k policy weight _ d hd
      _ = evenListLength e.selectedPrefix := by rw [hp]
      _ = e.positive :=
        (mem_firstExitDepthFrontier_positive_eq_evenListLength
          k policy weight _ e he).symm
  have hmass : d.mass = e.mass := by
    calc
      d.mass = (d.selectedPrefix.map weight).prod :=
        mem_firstExitDepthFrontier_mass_eq_selected_prod
          k policy weight _ d hd
      _ = (e.selectedPrefix.map weight).prod := by rw [hp]
      _ = e.mass :=
        (mem_firstExitDepthFrontier_mass_eq_selected_prod
          k policy weight _ e he).symm
  apply FirstExitDepthState.ext
  · exact hp
  · exact hsign
  · exact hmass
  · exact hrem

/-- A retained original second-prime selection has precisely ONE
rank-two STATE VALUE with ordered prefix [ell,p] under that root's
physical Q. Different original q receipts can witness this same state.
The list's occurrence multiplicity, owner and payment stay unproved. -/
theorem retained_original_second_unique_frontier_state
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ)
    (hret : retainedOriginalSecond N cap precision tau z0 lower z ell) :
    ∃! d : FirstExitDepthState ℕ,
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [ell, arithmeticPrime z] := by
  obtain ⟨d, hd, hp, _hsign, _hmass⟩ :=
    retained_original_second_in_actual_rank_two_frontier
      N cap precision tau z0 lower z ell hret
  refine ⟨d, ⟨hd, hp⟩, ?_⟩
  intro e he
  exact actual_frontier_state_determined_by_prefix
    2 (by decide) N cap z0 (originalPhysicalQ N precision tau z)
    lower e d he.1 hd (he.2.trans hp.symm)

end
end ImbalancedChen.Part5OriginalH430RankTwoFrontierConverse
