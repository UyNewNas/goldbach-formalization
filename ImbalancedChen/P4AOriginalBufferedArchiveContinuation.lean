import ImbalancedChen.P4AOriginalBufferedFallbackCaps
import ImbalancedChen.P4AOriginalCausalHistory
import ImbalancedChen.P5OriginalFourthFifthSourceInputs

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

Q22's concrete buffered second/third policy is continued through the
ORIGINAL fourth and fifth archives. The original licensed rows are below
mu, while both buffered changes are above mu. Their complete signed gains
are therefore preserved exactly, for every terminal test and every carrier.
The equality stratum belongs to the inherited original side.

The original fourth/fifth pointwise row formulas have NOT thereby become
finite scalar cap tables. The continuation below is a genuine intermediate
policy, not full87 and not O/P's compiledRho. No equality or density closeness
between those two physical coefficients is asserted. The missing complete
sixth/eighth parent and finite higher-cap realization remain explicit.
-/

namespace ImbalancedChen.P4AOriginalBufferedArchiveContinuation
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P1Pair12RetainedSignedSource
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonFourthSourceNavigation
open P5OriginalCommonFourthFallbackExcision
open P4AOriginalCausalHistory
open P4AOriginalBufferedFallbackCaps

/-- The actual original byte-backed fourth bank and original fifth owner
archive. No bank completeness or licence field is added to the input. -/
def originalSchedule (e : ℚ) (q : ℕ) (chi omega : ℝ) : ArchiveSchedule where
  rows4 := P5OriginalFourthFifthSourceInputs.originalRows4
  licensed4 := P5OriginalFourthFifthSourceInputs.originalAdmission4
  e := e
  q := q
  chi := chi
  omega := omega

theorem originalSchedule_data (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (originalSchedule e q chi omega).data =
      P5OriginalFourthFifthSourceInputs.heldData e q chi omega := rfl

theorem originalSchedule_geometry (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    FourthGeometry (originalSchedule e q chi omega).data := by
  intro r _hr hlicensed
  exact P5OriginalFourthFifthSourceInputs.originalAdmission4_geometry r hlicensed

theorem buffered_below_mu (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hmu : firstCoordinate N pre ≤ mu) :
    bufferedThirdPolicy d m buffer N positive pre = old3 d N positive pre := by
  by_cases h2 : pre.length ≤ 2
  · exact buffered_preserves_first_two d m buffer N positive pre h2
  · obtain ⟨hs, ht⟩ := guards_false_below_mu N pre (by omega) hmu
    simp [bufferedThirdPolicy, bufferedSecondPolicy, hs, ht]

/-- Both alternatives are actual Boolean prefix policies. The branch is
read at the first ancestor and is constant along every nonempty descendant. -/
private def aboveMuContinuation (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (P : Bool → List ℕ → Bool) (positive : Bool) (pre : List ℕ) : Bool :=
  if mu < firstCoordinate N pre then bufferedThirdPolicy d m buffer N positive pre
  else P positive pre

def fourthPolicy (d : OriginalData) (m : ℕ) (buffer N : ℝ) : Bool → List ℕ → Bool :=
  aboveMuContinuation d m buffer N (original4 d N)

def fifthPolicy (s : ArchiveSchedule) (m : ℕ) (buffer N : ℝ) : Bool → List ℕ → Bool :=
  aboveMuContinuation s.data m buffer N (original5 s.data N)

theorem fourthPolicy_through_four (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    fourthPolicy d m buffer N positive pre = bufferedThirdPolicy d m buffer N positive pre := by
  unfold fourthPolicy aboveMuContinuation
  split_ifs with hm
  · rfl
  · rw [original4_through_four d N positive pre hlen,
      buffered_below_mu d m buffer N positive pre (le_of_not_gt hm)]

theorem fifthPolicy_through_four (s : ArchiveSchedule) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    fifthPolicy s m buffer N positive pre = bufferedThirdPolicy s.data m buffer N positive pre := by
  unfold fifthPolicy aboveMuContinuation
  split_ifs with hm
  · rfl
  · rw [original5_through_four s.data N positive pre hlen,
      buffered_below_mu s.data m buffer N positive pre (le_of_not_gt hm)]

theorem fourthPolicy_below_mu (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hm : firstCoordinate N pre ≤ mu) :
    fourthPolicy d m buffer N positive pre = original4 d N positive pre := by
  simp only [fourthPolicy, aboveMuContinuation, if_neg (not_lt_of_ge hm)]

theorem fifthPolicy_below_mu (s : ArchiveSchedule) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hm : firstCoordinate N pre ≤ mu) :
    fifthPolicy s m buffer N positive pre = original5 s.data N positive pre := by
  simp only [fifthPolicy, aboveMuContinuation, if_neg (not_lt_of_ge hm)]

theorem fourthPolicy_above_mu (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hm : mu < firstCoordinate N pre) :
    fourthPolicy d m buffer N positive pre = bufferedThirdPolicy d m buffer N positive pre := by
  simp only [fourthPolicy, aboveMuContinuation, if_pos hm]

theorem fifthPolicy_above_mu (s : ArchiveSchedule) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hm : mu < firstCoordinate N pre) :
    fifthPolicy s m buffer N positive pre = bufferedThirdPolicy s.data m buffer N positive pre := by
  simp only [fifthPolicy, aboveMuContinuation, if_pos hm]

theorem buffered_archive_preserves_first_two (s : ArchiveSchedule) (m : ℕ) (buffer N : ℝ)
    (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 2) :
    fourthPolicy s.data m buffer N positive pre = old3 s.data N positive pre ∧
      fifthPolicy s m buffer N positive pre = old3 s.data N positive pre := by
  rw [fourthPolicy_through_four s.data m buffer N positive pre (by omega),
    fifthPolicy_through_four s m buffer N positive pre (by omega),
    buffered_preserves_first_two s.data m buffer N positive pre hlen]
  exact ⟨rfl, rfl⟩

/-- Retention is an actual Boolean assertion only. The signed gain theorem
below is proved separately and does not follow from this containment. -/
theorem fourth_original_decision_retained (d : OriginalData) (hg : FourthGeometry d)
    (m : ℕ) (buffer N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : original4 d N positive pre = true) : fourthPolicy d m buffer N positive pre = true := by
  by_cases hm : mu < firstCoordinate N pre
  · rw [fourthPolicy_above_mu d m buffer N positive pre hm]
    apply buffered_preserves_old_decision d m buffer N hN positive pre
    rwa [original4_eq_old3_above_mu d hg N positive pre hm] at hp
  · rwa [fourthPolicy_below_mu d m buffer N positive pre (le_of_not_gt hm)]

theorem fifth_original_decision_retained (s : ArchiveSchedule) (hg : FourthGeometry s.data)
    (m : ℕ) (buffer N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : original5 s.data N positive pre = true) : fifthPolicy s m buffer N positive pre = true := by
  by_cases hm : mu < firstCoordinate N pre
  · rw [fifthPolicy_above_mu s m buffer N positive pre hm]
    apply buffered_preserves_old_decision s.data m buffer N hN positive pre
    rwa [(archive_fifth_policies_inherit_above_mu s hg N hN positive pre hm).2] at hp
  · rwa [fifthPolicy_below_mu s m buffer N positive pre (le_of_not_gt hm)]

private theorem signed_eq_on_region (N : ℝ) (P Q : Bool → List ℕ → Bool)
    (region : ℝ → Prop)
    (hpolicy : ∀ positive pre, region (firstCoordinate N pre) → P positive pre = Q positive pre)
    (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (pre : List ℕ)
    (hlen : 1 ≤ pre.length) (hr : region (firstCoordinate N pre))
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest P weight T pre positive mass remaining =
      signedTest Q weight T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hr' : region (firstCoordinate N (p :: pre)) := by
        rwa [firstCoordinate_cons N p pre hlen]
      simp only [signedTest, hpolicy (!positive) (p :: pre) hr']
      rw [ih (pre := pre) (hlen := hlen) (hr := hr) (positive := positive) (mass := mass),
        ih (pre := p :: pre) (hlen := by simp; omega) (hr := hr')
          (positive := !positive) (mass := mass * weight p)]

private theorem patch_correction (d : OriginalData) (m : ℕ) (buffer N : ℝ)
    (P : Bool → List ℕ → Bool)
    (hearly : ∀ positive pre, pre.length ≤ 2 → P positive pre = old3 d N positive pre)
    (habove : ∀ positive pre, mu < firstCoordinate N pre → P positive pre = old3 d N positive pre)
    (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ)
    (hfront : firstExitDepthFrontier 2 P weight [] true 1 carrier =
      firstExitDepthFrontier 2 (old3 d N) weight [] true 1 carrier) :
    signedTest (aboveMuContinuation d m buffer N P) weight T [] true 1 carrier -
        signedTest P weight T [] true 1 carrier =
      signedTest (bufferedThirdPolicy d m buffer N) weight T [] true 1 carrier -
        signedTest (old3 d N) weight T [] true 1 carrier := by
  have hpatch : aboveMuContinuation d m buffer N P =
      firstExitDepthSplicePolicy 2 P (aboveMuContinuation d m buffer N P) := by
    funext positive pre
    by_cases h2 : pre.length ≤ 2
    · simp only [firstExitDepthSplicePolicy, if_pos h2, aboveMuContinuation]
      rw [buffered_preserves_first_two d m buffer N positive pre h2,
        hearly positive pre h2]
      simp
    · simp only [firstExitDepthSplicePolicy, if_neg h2]
  have hbuffer : bufferedThirdPolicy d m buffer N =
      firstExitDepthSplicePolicy 2 (old3 d N) (bufferedThirdPolicy d m buffer N) := by
    funext positive pre
    by_cases h2 : pre.length ≤ 2
    · simpa only [firstExitDepthSplicePolicy, if_pos h2] using
        buffered_preserves_first_two d m buffer N positive pre h2
    · simp only [firstExitDepthSplicePolicy, if_neg h2]
  have hp := signedTest_splice_sub_eq_frontier 2 P (aboveMuContinuation d m buffer N P)
    weight T [] carrier true 1
  rw [← hpatch, hfront] at hp
  have hb := signedTest_splice_sub_eq_frontier 2 (old3 d N) (bufferedThirdPolicy d m buffer N)
    weight T [] carrier true 1
  rw [← hbuffer] at hb
  rw [hp, hb]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  have hlen : 1 ≤ state.selectedPrefix.length := by
    have hl := firstExitDepthFrontier_selected_length 2 (old3 d N) weight [] carrier
      true 1 (by simp) state hstate
    omega
  by_cases hm : mu < firstCoordinate N state.selectedPrefix
  · have hnew := signed_eq_on_region N (aboveMuContinuation d m buffer N P)
      (bufferedThirdPolicy d m buffer N) (fun x => mu < x)
      (fun positive pre h => by simp only [aboveMuContinuation, if_pos h])
      weight T _ hlen hm state.positive state.mass state.remaining
    have hold := signed_eq_on_region N P (old3 d N) (fun x => mu < x) habove
      weight T _ hlen hm state.positive state.mass state.remaining
    rw [hnew, hold]
  · have hnew := signed_eq_on_region N (aboveMuContinuation d m buffer N P) P
      (fun x => x ≤ mu)
      (fun positive pre h => by simp only [aboveMuContinuation, if_neg (not_lt_of_ge h)])
      weight T _ hlen (le_of_not_gt hm) state.positive state.mass state.remaining
    have hold := signed_eq_on_region N (bufferedThirdPolicy d m buffer N) (old3 d N)
      (fun x => x ≤ mu) (buffered_below_mu d m buffer N)
      weight T _ hlen (le_of_not_gt hm) state.positive state.mass state.remaining
    rw [hnew, hold, sub_self, sub_self]

/-- The complete signed fourth saving survives Q22 buffering exactly.
This includes the original first-stop, restored third histories, occurrence
multiplicity, arbitrary incoming arithmetic weight and arbitrary terminal. -/
theorem fourth_signed_gain_preserved (d : OriginalData) (hg : FourthGeometry d)
    (m : ℕ) (buffer N : ℝ) (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (carrier : List ℕ) :
    signedTest (bufferedThirdPolicy d m buffer N) weight T [] true 1 carrier -
        signedTest (fourthPolicy d m buffer N) weight T [] true 1 carrier =
      signedTest (old3 d N) weight T [] true 1 carrier -
        signedTest (original4 d N) weight T [] true 1 carrier := by
  have h := patch_correction d m buffer N (original4 d N)
    (fun positive pre hlen => original4_through_four d N positive pre (by omega))
    (original4_eq_old3_above_mu d hg N) weight T carrier
    (original4_second_frontier d N weight [] carrier true 1)
  change signedTest (fourthPolicy d m buffer N) weight T [] true 1 carrier - _ = _ at h
  linarith only [h]

theorem fifth_signed_gain_preserved (s : ArchiveSchedule) (hg : FourthGeometry s.data)
    (m : ℕ) (buffer N : ℝ) (hN : 1 ≤ N) (weight : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (fourthPolicy s.data m buffer N) weight T [] true 1 carrier -
        signedTest (fifthPolicy s m buffer N) weight T [] true 1 carrier =
      signedTest (original4 s.data N) weight T [] true 1 carrier -
        signedTest (original5 s.data N) weight T [] true 1 carrier := by
  have hfront : firstExitDepthFrontier 2 (original5 s.data N) weight [] true 1 carrier =
      firstExitDepthFrontier 2 (old3 s.data N) weight [] true 1 carrier := by
    exact firstExitDepthFrontier_depthSplice_eq 2 4 (by omega) _ _ weight [] carrier true 1
  have h5 := patch_correction s.data m buffer N (original5 s.data N)
    (fun positive pre hlen => original5_through_four s.data N positive pre (by omega))
    (fun positive pre hm => (archive_fifth_policies_inherit_above_mu s hg N hN positive pre hm).2)
    weight T carrier hfront
  change signedTest (fifthPolicy s m buffer N) weight T [] true 1 carrier - _ = _ at h5
  have h4 := fourth_signed_gain_preserved s.data hg m buffer N weight T carrier
  linarith only [h4, h5]

/-- Concrete original-archive specialization: no FourthGeometry premise,
supplied gain equality, signed density bound or full87 licence is an input. -/
theorem original_archives_two_signed_gains (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (m : ℕ) (buffer N : ℝ) (hN : 1 ≤ N) (weight : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    let s := originalSchedule e q chi omega
    (signedTest (bufferedThirdPolicy s.data m buffer N) weight T [] true 1 carrier -
        signedTest (fourthPolicy s.data m buffer N) weight T [] true 1 carrier =
      signedTest (old3 s.data N) weight T [] true 1 carrier -
        signedTest (original4 s.data N) weight T [] true 1 carrier) ∧
    (signedTest (fourthPolicy s.data m buffer N) weight T [] true 1 carrier -
        signedTest (fifthPolicy s m buffer N) weight T [] true 1 carrier =
      signedTest (original4 s.data N) weight T [] true 1 carrier -
        signedTest (original5 s.data N) weight T [] true 1 carrier) := by
  dsimp only
  exact ⟨fourth_signed_gain_preserved _ (originalSchedule_geometry e q chi omega)
    m buffer N weight T carrier,
    fifth_signed_gain_preserved _ (originalSchedule_geometry e q chi omega)
      m buffer N hN weight T carrier⟩

end
end ImbalancedChen.P4AOriginalBufferedArchiveContinuation
