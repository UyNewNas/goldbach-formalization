import ImbalancedChen.P5OriginalCommonThirdActualLowerSource
import ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing common constructor is split into its actual second restoration
and its subsequent third action.  The latter uses the CURRENT rank-three
frontier, which can contain nodes excluded by the historical policy.
The disabled-small-third continuation is retained exactly.

The original fifth archive is then shown to preserve its complete signed
fourth-to-fifth change, for every terminal test, not only its limiting
kernel or its literal tuple charge.  This uses the actual archive separation
and the original fourth producer geometry, never signed monotonicity.

The final identity still names the held constructor's sixth/eighth changes.
Its policy8 has NOT been identified with the full original 87-domain policy.
No source identity, old-gain preservation, common-policy existence, density
estimate, or error estimate is an assumption of the public source identity.
-/

namespace ImbalancedChen.P4AOriginalCausalHistory
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P1Pair12RetainedSignedSource
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonRefinedAncestry P5OriginalCommonRefinedSource
open P5OriginalCommonRefinedSeedHull
open P5OriginalCommonFourthSourceNavigation P5OriginalCommonFourthFallbackExcision
open P5OriginalCommonThirdScreenedSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P5OriginalFifthArchiveFallbackSeparation P1HistoricalFifthCommonPolicyInputs
open P2OriginalFourthCapProducerInterface

/-- The second action is read at rank three, including its OWN cube.
Unsupported third histories keep the literal historical decision. -/
def secondStage (d : OriginalData) (N : ℝ) (positive : Bool) (pre : List ℕ) : Bool :=
  if pre.length ≤ 2 then old3 d N positive pre
  else if selectedThird d N pre ∧ secondGuard N pre then
    ordinaryParityRosserPolicy false (N ^ secondExponent N pre) positive pre
  else old3 d N positive pre

theorem secondStage_even (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    secondStage d N true pre = true := by
  simp [secondStage, old3, HistoricalThirdCoarse.policy_even]

theorem secondStage_splice_two (d : OriginalData) (N : ℝ) :
    secondStage d N = firstExitDepthSplicePolicy 2 (old3 d N) (secondStage d N) := by
  funext positive pre
  by_cases h2 : pre.length ≤ 2 <;> simp [secondStage, firstExitDepthSplicePolicy, h2]

/-- The third action starts AFTER the second stage's rank-three decision.
Its parent is not the historical rank-three frontier. -/
theorem common3_splice_current_three (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N : ℝ) (hN : 1 ≤ N) :
    common3 d N = firstExitDepthSplicePolicy 3 (secondStage d N) (common3 d N) := by
  funext positive pre
  by_cases h3 : pre.length ≤ 3
  · rw [firstExitDepthSplicePolicy, if_pos h3,
      common3_eq_screened3 d he hemax N hN]
    by_cases h2 : pre.length ≤ 2 <;> simp [screened3, secondStage, h2, h3]
  · simp only [firstExitDepthSplicePolicy, if_neg h3]

theorem secondGuard_append (N : ℝ) (later pre : List ℕ) (hlen : 2 ≤ pre.length) :
    secondGuard N (later ++ pre) ↔ secondGuard N pre := by
  simp only [secondGuard, rosserAncestor_append 2 later pre hlen]

theorem secondExponent_append (N : ℝ) (later pre : List ℕ) (hlen : 2 ≤ pre.length) :
    secondExponent N (later ++ pre) = secondExponent N pre := by
  simp only [secondExponent, rosserAncestor_append 2 later pre hlen]

/-- This is the actual rank-three restoration rule.  The historical
rank-three decision is absent from the right side, even when it was false. -/
theorem actual_rank_three_second_test (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N : ℝ) (hN : 1 ≤ N) (pre : List ℕ) (hlen : pre.length = 3)
    (hs : selectedThird d N pre) (hg : secondGuard N pre) :
    policy8 d N false pre =
      decide (ordinaryRosserPrefixAdmissible false (N ^ secondExponent N pre) pre) := by
  rw [policy8_through_six_eq_fifth d N false pre (by omega)]
  simp only [policy5, firstExitDepthSplicePolicy, if_pos (by omega : pre.length ≤ 4)]
  rw [common3_eq_screened3 d he hemax N hN]
  simp [screened3, hlen, hs, hg, ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem formerly_excluded_third_is_restored (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N : ℝ) (hN : 1 ≤ N) (pre : List ℕ) (hlen : pre.length = 3)
    (hs : selectedThird d N pre) (hg : secondGuard N pre)
    (hold : old3 d N false pre = false)
    (hnew : ordinaryRosserPrefixAdmissible false (N ^ secondExponent N pre) pre) :
    old3 d N false pre = false ∧ policy8 d N false pre = true := by
  refine ⟨hold, ?_⟩
  rw [actual_rank_three_second_test d he hemax N hN pre hlen hs hg]
  exact decide_eq_true hnew

theorem small_third_not_selected (d : OriginalData) (N : ℝ) (p1 p2 p3 : ℕ)
    (hp : (p3 : ℝ) < N ^ d.omega) : ¬selectedThird d N [p3,p2,p1] := by
  intro hs
  have hself : rosserAncestor 3 [p3,p2,p1] = [p3,p2,p1] := by
    exact rosserAncestor_self_of_length 3 _ (by simp)
  change P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
    (rosserAncestor 3 [p3,p2,p1]) at hs
  rw [hself, P1ThirdFallbackSupport.supported_triple] at hs
  exact (not_le_of_gt hp) hs.1

/-- No unsupported descendant is silently assigned the endpoint cap v(x).
The WHOLE signed continuation, including all terminal tests, is unchanged. -/
theorem disabled_small_third_continuation (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N : ℝ) (hN : 1 ≤ N) (p1 p2 p3 : ℕ) (hp : (p3 : ℝ) < N ^ d.omega)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    originalSeed d N [p3,p2,p1] = HistoricalThirdCoarse.initial (d.e : ℝ) ∧
      signedTest (common3 d N) h T [p3,p2,p1] positive mass remaining =
        signedTest (old3 d N) h T [p3,p2,p1] positive mass remaining := by
  have hs := small_third_not_selected d N p1 p2 p3 hp
  exact ⟨originalSeed_unsupported d N _ hs,
    unsupported_signed_continuation d he hemax N hN h T _ (by simp) hs
      positive mass remaining⟩

/-- Literal change at the actual current frontier. List multiplicities,
incoming sign, incoming mass and remaining carrier are not altered. -/
def frontierChange (k : ℕ) (parent fresh : Bool → List ℕ → Bool)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  ((firstExitDepthFrontier k parent h [] true 1 carrier).map (fun s =>
    signedTest fresh h T s.selectedPrefix s.positive s.mass s.remaining -
      signedTest parent h T s.selectedPrefix s.positive s.mass s.remaining)).sum

def secondChange (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  frontierChange 2 (old3 d N) (secondStage d N) h T carrier

def thirdChange (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  frontierChange 3 (secondStage d N) (common3 d N) h T carrier

theorem secondChange_eq (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    secondChange d N h T carrier = signedTest (secondStage d N) h T [] true 1 carrier -
      signedTest (old3 d N) h T [] true 1 carrier := by
  have hh := signedTest_splice_sub_eq_frontier 2 (old3 d N) (secondStage d N)
    h T [] carrier true 1
  rw [← secondStage_splice_two] at hh
  exact hh.symm

theorem thirdChange_eq (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N : ℝ) (hN : 1 ≤ N) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    thirdChange d N h T carrier = signedTest (common3 d N) h T [] true 1 carrier -
      signedTest (secondStage d N) h T [] true 1 carrier := by
  have hh := signedTest_splice_sub_eq_frontier 3 (secondStage d N) (common3 d N)
    h T [] carrier true 1
  rw [← common3_splice_current_three d he hemax N hN] at hh
  exact hh.symm

theorem original_second_third_telescope (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N : ℝ) (hN : 1 ≤ N) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (common3 d N) h T [] true 1 carrier =
      signedTest (old3 d N) h T [] true 1 carrier + secondChange d N h T carrier +
        thirdChange d N h T carrier := by
  rw [secondChange_eq, thirdChange_eq d he hemax N hN]
  ring

/-- The independently defined original fifth policy. -/
def original5 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega N
    d.rows4 d.licensed4 d.J5 d.rows5

theorem original5_through_four (d : OriginalData) (N : ℝ) (positive : Bool)
    (pre : List ℕ) (hlen : pre.length ≤ 4) :
    original5 d N positive pre = old3 d N positive pre :=
  P1OriginalVariableFifthContinuation.policy5_through_four d.e d.chi d.m d.omega N
    d.rows4 d.licensed4 d.J5 d.rows5 positive pre hlen

theorem common5_eq_original_below_mu (d : OriginalData) (N : ℝ)
    (positive : Bool) (pre : List ℕ) (hmu : firstCoordinate N pre ≤ mu) :
    policy5 d N positive pre = original5 d N positive pre := by
  by_cases h4 : pre.length ≤ 4
  · rw [original5_through_four d N positive pre h4]
    simpa only [policy5, firstExitDepthSplicePolicy, if_pos h4] using
      common3_eq_original_below_mu d N positive pre hmu
  · have hl : (rosserAncestor 5 pre).length = 5 := by
      rw [rosserAncestor_length, min_eq_left (by omega : 5 ≤ pre.length)]
    have hx : primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) 0 ≤ mu := by
      rwa [ancestor_first_coordinate N 5 (by omega) pre (by omega)]
    have hc := fifth_eq_old_below_mu d N (rosserAncestor 5 pre) hl hx
    simpa only [policy5, original5, P1OriginalVariableFifthContinuation.policy5,
      fifthCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg h4,
      frozenParityRosserPolicy, ancestorFrozenPolicy, level5,
      P1OriginalVariableFifthContinuation.level5, oldFifth] using
      congrArg (fun x : ℝ => ordinaryParityRosserPolicy false (N ^ x) positive pre) hc

/-- Finite schedule fields only. The fifth bank is the original loaded
archive; the fourth source records and licence are still explicit input data. -/
structure ArchiveSchedule where
  rows4 : Finset ProducerRow
  licensed4 : ProducerRow → Prop
  e : ℚ
  q : ℕ
  chi : ℝ
  omega : ℝ

def ArchiveSchedule.data (s : ArchiveSchedule) : OriginalData :=
  sourceData s.rows4 s.licensed4 s.e s.q s.chi s.omega

theorem archive_fifth_policies_inherit_above_mu (s : ArchiveSchedule)
    (hg : FourthGeometry s.data) (N : ℝ) (hN : 1 ≤ N)
    (positive : Bool) (pre : List ℕ) (hmu : mu < firstCoordinate N pre) :
    policy5 s.data N positive pre = common3 s.data N positive pre ∧
      original5 s.data N positive pre = old3 s.data N positive pre := by
  by_cases h4 : pre.length ≤ 4
  · exact ⟨by simp only [policy5, firstExitDepthSplicePolicy, if_pos h4],
      original5_through_four s.data N positive pre h4⟩
  have hl : (rosserAncestor 5 pre).length = 5 := by
    rw [rosserAncestor_length, min_eq_left (by omega : 5 ≤ pre.length)]
  have hx : mu ≤ primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) 0 := by
    rw [ancestor_first_coordinate N 5 (by omega) pre (by omega)]
    exact hmu.le
  have hcaps := actual_archive_fifth_outside_below_mu s.rows4 s.licensed4 s.e s.q
    s.chi s.omega N (rosserAncestor 5 pre) hl hx
  change oldFifth s.data N (rosserAncestor 5 pre) = oldInherited s.data N (rosserAncestor 5 pre) ∧
    exponent5 s.data N (rosserAncestor 5 pre) = commonInherited s.data N (rosserAncestor 5 pre) at hcaps
  have hm : mu < firstCoordinate N (rosserAncestor 4 (rosserAncestor 5 pre)) := by
    rwa [firstCoordinate_ancestor N 4 (by omega), firstCoordinate_ancestor N 5 (by omega)]
  have hc4 := common_exponent4_above_mu s.data hg N _ hm
  have ho4 := original_exponent4_above_mu s.data hg N _ hm
  have hc : exponent5 s.data N (rosserAncestor 5 pre) = lambda3 s.data N pre := by
    rw [hcaps.2, commonInherited, hc4, lambda3_ancestor s.data N 4 (by omega),
      lambda3_ancestor s.data N 5 (by omega)]
  have ho : oldFifth s.data N (rosserAncestor 5 pre) = originalSeed s.data N pre := by
    rw [hcaps.1, oldInherited, P1OriginalVariableFifthContinuation.inherited4, ho4]
    simp only [originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
      rosserAncestor_nested 3 4 (by omega), rosserAncestor_nested 3 5 (by omega)]
  constructor
  · rw [common3_after_three s.data N hN positive pre (by omega)]
    simp only [policy5, firstExitDepthSplicePolicy, if_neg h4,
      frozenParityRosserPolicy, ancestorFrozenPolicy, level5, hc]
  · rw [old3_after_two s.data N positive pre (by omega)]
    simpa only [original5, P1OriginalVariableFifthContinuation.policy5,
      fifthCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg h4,
      frozenParityRosserPolicy, ancestorFrozenPolicy,
      P1OriginalVariableFifthContinuation.level5, oldFifth] using
      congrArg (fun x : ℝ => ordinaryParityRosserPolicy false (N ^ x) positive pre) ho

private theorem signed_eq_first_region (N : ℝ) (P Q : Bool → List ℕ → Bool)
    (region : ℝ → Prop) (hpolicy : ∀ positive pre, region (firstCoordinate N pre) →
      P positive pre = Q positive pre) (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : 1 ≤ pre.length) (hr : region (firstCoordinate N pre))
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest P h T pre positive mass remaining = signedTest Q h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hr' : region (firstCoordinate N (p :: pre)) := by
      rwa [firstCoordinate_cons N p pre hlen]
    simp only [signedTest, hpolicy (!positive) (p :: pre) hr']
    rw [ih (pre := pre) (hlen := hlen) (hr := hr) (positive := positive) (mass := mass),
      ih (pre := p :: pre) (hlen := by simp; omega) (hr := hr')
        (positive := !positive) (mass := mass * h p)]

private theorem fifth_splice_two (d : OriginalData) (N : ℝ) :
    policy5 d N = firstExitDepthSplicePolicy 2 (original5 d N) (policy5 d N) := by
  funext positive pre
  by_cases h2 : pre.length ≤ 2
  · rw [firstExitDepthSplicePolicy, if_pos h2,
      original5_through_four d N positive pre (by omega)]
    simpa only [policy5, firstExitDepthSplicePolicy, if_pos (by omega : pre.length ≤ 4)] using
      common3_through_two d N positive pre h2
  · simp only [firstExitDepthSplicePolicy, if_neg h2]

private theorem original5_frontier_two (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (carrier : List ℕ) :
    firstExitDepthFrontier 2 (original5 d N) h [] true 1 carrier =
      firstExitDepthFrontier 2 (old3 d N) h [] true 1 carrier := by
  exact firstExitDepthFrontier_depthSplice_eq 2 4 (by omega) _ _ h [] carrier true 1

/-- Global signed source identity, including beta attachment or an
arbitrary AP-minus-mean test. The actual archive pays the separation. -/
theorem archive_fifth_correction_eq_third (s : ArchiveSchedule)
    (hg : FourthGeometry s.data) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (policy5 s.data N) h T [] true 1 carrier -
        signedTest (original5 s.data N) h T [] true 1 carrier =
      signedTest (common3 s.data N) h T [] true 1 carrier -
        signedTest (old3 s.data N) h T [] true 1 carrier := by
  have h5 := signedTest_splice_sub_eq_frontier 2 (original5 s.data N) (policy5 s.data N)
    h T [] carrier true 1
  rw [← fifth_splice_two, original5_frontier_two] at h5
  have h3 := signedTest_splice_sub_eq_frontier 2 (old3 s.data N) (common3 s.data N)
    h T [] carrier true 1
  rw [← common3_eq_splice_old3] at h3
  rw [h5, h3]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state hstate
  have hl : 1 ≤ state.selectedPrefix.length := by
    have hh := firstExitDepthFrontier_selected_length 2 (old3 s.data N) h [] carrier
      true 1 (by simp) state hstate
    omega
  by_cases hm : mu < firstCoordinate N state.selectedPrefix
  · have hc := signed_eq_first_region N (policy5 s.data N) (common3 s.data N)
      (fun x => mu < x) (fun b pre hp =>
        (archive_fifth_policies_inherit_above_mu s hg N hN b pre hp).1)
      h T _ hl hm state.positive state.mass state.remaining
    have ho := signed_eq_first_region N (original5 s.data N) (old3 s.data N)
      (fun x => mu < x) (fun b pre hp =>
        (archive_fifth_policies_inherit_above_mu s hg N hN b pre hp).2)
      h T _ hl hm state.positive state.mass state.remaining
    rw [hc, ho]
  · have hc := signed_eq_first_region N (policy5 s.data N) (original5 s.data N)
      (fun x => x ≤ mu) (common5_eq_original_below_mu s.data N)
      h T _ hl (le_of_not_gt hm) state.positive state.mass state.remaining
    have ho := signed_eq_first_region N (common3 s.data N) (old3 s.data N)
      (fun x => x ≤ mu) (common3_eq_original_below_mu s.data N)
      h T _ hl (le_of_not_gt hm) state.positive state.mass state.remaining
    rw [hc, ho, sub_self, sub_self]

theorem archive_fifth_signed_gain_preserved (s : ArchiveSchedule)
    (hg : FourthGeometry s.data) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (policy4 s.data N) h T [] true 1 carrier -
        signedTest (policy5 s.data N) h T [] true 1 carrier =
      signedTest (original4 s.data N) h T [] true 1 carrier -
        signedTest (original5 s.data N) h T [] true 1 carrier := by
  have h4 := fourth_signed_gain_preserved s.data hg N hN h T carrier
  have h5 := archive_fifth_correction_eq_third s hg N hN h T carrier
  linarith only [h4, h5]

/-- Complete current-parent telescope for the HELD concrete constructor.
The original fourth/fifth gains are subtracted once; the final two changes
remain actual source functions and are not identified with all22/87. -/
theorem held_final_source_with_original_gains (s : ArchiveSchedule)
    (hg : FourthGeometry s.data) (he : 0 ≤ (s.e : ℝ)) (hemax : (s.e : ℝ) ≤ 11 / 64000)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    let T := attachedLeafTest N cap 1 w L G
    let carrier := roughPrimeUniverse N cap w z
    (∑ q ∈ moduli s.data N cap w z,
      P5OriginalCommonRefinedConstructor.rho s.data N cap w z L q * G q) =
      signedTest (old3 s.data (N : ℝ)) (fun _ => 1) T [] true 1 carrier +
        secondChange s.data (N : ℝ) (fun _ => 1) T carrier +
        thirdChange s.data (N : ℝ) (fun _ => 1) T carrier -
        (signedTest (old3 s.data (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
          signedTest (original4 s.data (N : ℝ)) (fun _ => 1) T [] true 1 carrier) -
        (signedTest (original4 s.data (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
          signedTest (original5 s.data (N : ℝ)) (fun _ => 1) T [] true 1 carrier) +
        sourceChange s.data .sixth N cap w z L G + sourceChange s.data .eighth N cap w z L G := by
  dsimp only
  rw [actual_source_telescope]
  have h4 := source_next_sub_current s.data .fourth N cap w z L G
  have h5 := source_next_sub_current s.data .fifth N cap w z L G
  simp only [nextStage, parentStage, source_eq_actual_root, stagePolicy, terminal] at h4 h5
  have hpres4 := fourth_signed_gain_preserved s.data hg (N : ℝ) hN (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) (roughPrimeUniverse N cap w z)
  have hpres5 := archive_fifth_signed_gain_preserved s hg (N : ℝ) hN (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) (roughPrimeUniverse N cap w z)
  have h23 := original_second_third_telescope s.data he hemax (N : ℝ) hN (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) (roughPrimeUniverse N cap w z)
  rw [source_eq_actual_root]
  change signedTest (common3 s.data (N : ℝ)) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] true 1 (roughPrimeUniverse N cap w z) + _ + _ + _ + _ = _
  linarith only [h4, h5, hpres4, hpres5, h23]

/-- Stronger estimates replace the already counted source bound.  The
increment is algebraically new-minus-old, not a second cap action. -/
theorem same_source_bound_replacement (base other oldBound newBound : ℝ) :
    base - other - oldBound - (newBound - oldBound) = base - other - newBound := by
  ring

end
end ImbalancedChen.P4AOriginalCausalHistory
