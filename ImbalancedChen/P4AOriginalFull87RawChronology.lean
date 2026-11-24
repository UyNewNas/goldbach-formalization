import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import ImbalancedChen.P4AOriginalCatalogFiveArchiveSchedule
import ImbalancedChen.P5OriginalArchiveCommonRawMean

/-! Original upper density at w=0. The licensed fifth continuation and the
archive fifth continuation have the same rank-four predecessor. Their signed
change is taken on that predecessor's occurrence list. The sixth and eighth
changes are taken on the licensed predecessors. No stage gain is assumed. -/

namespace ImbalancedChen.P4AOriginalFull87RawChronology

noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P5OriginalCommonRefinedConstructor
open P4AOriginalCausalHistory
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize normalize_add normalize_sub)
open P5OriginalCommonFourthSourceLedger
  (signedTest_one_eq_polynomial originalFourthSaving)
open P5OriginalCommonFourthFallbackExcision (common_fourth_raw_ledger)
open P5OriginalArchiveCommonRawMean (normalizedRawDifference)
open P5OriginalFourthFifthSourceInputs (originalRows4 originalAdmission4)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier)
open P4ACatalogFiveGlobalLossReduction (normalizedActualSaving)

abbrev archiveData := P4AOriginalCompleteSixthChronology.data
abbrev licensed := P4AOriginalFull87LicensedSixthPolicy.policy
abbrev cutoff (N : ℕ) : ℝ := (N : ℝ) ^ (19 / 96 : ℝ)

/-- This carrier is the cap=N carrier of the original slot-five supplier. -/
def rawRoot (P : Bool → List ℕ → Bool) (N : ℕ) : ℝ :=
  raw P N N 0 (cutoff N)

private theorem signed_root_eq_raw (P : Bool → List ℕ → Bool)
    (hP : ∀ pre, P true pre = true) (N : ℕ) :
    signedTest P weight (fun _ _ => 1) [] true 1 (carrier N) = rawRoot P N := by
  rw [signedTest_one_eq_polynomial]
  exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    P hP N N 0 (cutoff N)

/-- Two continuations evaluated at the same actual predecessor state.
The sign and mass belong to the incoming state. -/
def rawChange (k : ℕ) (parent old fresh : Bool → List ℕ → Bool) (N : ℕ) : ℝ :=
  ((firstExitDepthFrontier k parent weight [] true 1 (carrier N)).map fun s =>
    signedTest fresh weight (fun _ _ => 1) s.selectedPrefix s.positive s.mass s.remaining -
      signedTest old weight (fun _ _ => 1) s.selectedPrefix s.positive s.mass s.remaining).sum

private theorem splice_pair_raw_sub (k : ℕ) (parent old fresh : Bool → List ℕ → Bool)
    (hP : ∀ pre, parent true pre = true)
    (hO : ∀ pre, old true pre = true) (hF : ∀ pre, fresh true pre = true) (N : ℕ) :
    rawRoot (firstExitDepthSplicePolicy k parent fresh) N -
      rawRoot (firstExitDepthSplicePolicy k parent old) N =
        rawChange k parent old fresh N := by
  rw [← signed_root_eq_raw _ (UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained
        k parent fresh hP hF),
      ← signed_root_eq_raw _ (UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained
        k parent old hP hO),
      signedTest_splice_eq_stopped_add_frontier, signedTest_splice_eq_stopped_add_frontier,
      add_sub_add_left_eq_sub]
  unfold rawChange
  generalize firstExitDepthFrontier k parent weight [] true 1 (carrier N) = states
  induction states with
  | nil => simp
  | cons s ss ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith only [ih]

private theorem splice_raw_sub (k : ℕ) (parent fresh : Bool → List ℕ → Bool)
    (hP : ∀ pre, parent true pre = true) (hF : ∀ pre, fresh true pre = true) (N : ℕ) :
    rawRoot (firstExitDepthSplicePolicy k parent fresh) N - rawRoot parent N =
        rawChange k parent parent fresh N := by
  simpa only [firstExitDepthSplicePolicy_self] using
    splice_pair_raw_sub k parent parent fresh hP hP hF N

/-- Original fifth archive compared with the licensed fifth cap on the
common fourth frontier. Both policies are spliced after rank four. -/
def fifthAdjustment (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let d := archiveData e q a
  rawChange 4 (common3 d (N : ℝ)) (frozenParityRosserPolicy false 5 (level5 d (N : ℝ)))
    (frozenParityRosserPolicy false 5 (fun h =>
      (N : ℝ) ^ P4AOriginalFull87FiniteParentPolicy.level5Exponent n e q a (N : ℝ) h)) N

def sixthIncrement (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let parent := P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q a (N : ℝ)
  rawChange 6 parent parent (frozenParityRosserPolicy false 6 (fun h =>
    (N : ℝ) ^ P4AOriginalFull87LicensedSixthPolicy.level6Exponent n e q a (N : ℝ) h)) N

def eighthIncrement (trim : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let parent := P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q a (N : ℝ)
  rawChange 8 parent parent
    (P4AOriginalFull87LicensedSixthPolicy.eighthContinuation trim n e q a (N : ℝ)) N

theorem licensed_raw_sub_sixth (trim : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) :
    rawRoot (licensed trim n e q a (N : ℝ)) N -
      rawRoot (P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q a (N : ℝ)) N =
        eighthIncrement trim n e q a N := by
  refine splice_raw_sub 8 _ _
    (P4AOriginalFull87LicensedSixthPolicy.sixth_even n e q a (N : ℝ)) ?_ N
  intro pre
  unfold P4AOriginalFull87LicensedSixthPolicy.eighthContinuation
  cases P4AOriginalFull87FiniteEighthPolicy.selectedCap trim n (N : ℝ) pre
  · exact P4AOriginalFull87LicensedSixthPolicy.sixth_even n e q a (N : ℝ) pre
  · simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem licensed_raw_sub_archive_fifth (trim : ℝ) (n : ℕ)
    (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) :
    rawRoot (licensed trim n e q a (N : ℝ)) N -
      rawRoot (policy5 (archiveData e q a) (N : ℝ)) N =
        fifthAdjustment n e q a N + sixthIncrement n e q a N +
          eighthIncrement trim n e q a N := by
  let d := archiveData e q a
  let p5 := P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q a (N : ℝ)
  let p6 := P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q a (N : ℝ)
  have h5 : rawRoot p5 N - rawRoot (policy5 d (N : ℝ)) N = fifthAdjustment n e q a N :=
    splice_pair_raw_sub 4 _ _ _ (common3_even d (N : ℝ))
      (fun pre => frozenParityRosserPolicy_upper_even 5 _ pre)
      (fun pre => frozenParityRosserPolicy_upper_even 5 _ pre) N
  have h6 : rawRoot p6 N - rawRoot p5 N = sixthIncrement n e q a N :=
    splice_raw_sub 6 _ _ (P4AOriginalFull87FiniteParentPolicy.fifth_even n e q a (N : ℝ))
      (fun pre => frozenParityRosserPolicy_upper_even 6 _ pre) N
  have h8 : rawRoot (licensed trim n e q a (N : ℝ)) N - rawRoot p6 N =
      eighthIncrement trim n e q a N :=
    licensed_raw_sub_sixth trim n e q a N
  change _ - rawRoot (policy5 d (N : ℝ)) N = _
  linarith only [h5, h6, h8]

/-- The common archive fifth raw difference, in the same normalized units
as the target and the two original finite approximation accounts. -/
abbrev fifthSaving (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  normalizedRawDifference originalRows4 originalAdmission4 e q ((e : ℝ) / 20) a N N

def thirdIncrement (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  thirdChange (archiveData e q a) (N : ℝ) weight (fun _ _ => 1) (carrier N)

/-- Exact raw history for the licensed producer. A positive saving appears
with a minus sign; the last three terms are signed new-minus-current
occurrence sums. The third above-mu adjustment starts on its second-stage
parent. No saved number or target inequality is used in this identity. -/
theorem normalized_licensed_raw_chronology (trim : ℝ) (n : ℕ) (e : ℚ)
    (q : ℕ) (a : ℝ) (N : ℕ) (he : 0 ≤ (e : ℝ)) (hemax : (e : ℝ) ≤ 11 / 64000)
    (hN : 1 ≤ (N : ℝ)) :
    let d := archiveData e q a
    normalize N (rawRoot (licensed trim n e q a (N : ℝ)) N) =
      normalize N (rawRoot (old3 d (N : ℝ)) N) + normalize N (thirdIncrement e q a N) -
        normalize N (originalFourthSaving d N N (cutoff N)) -
        fifthSaving e q a N - normalizedActualSaving d N +
        normalize N (fifthAdjustment n e q a N + sixthIncrement n e q a N +
          eighthIncrement trim n e q a N) := by
  dsimp only
  let d := archiveData e q a
  have h23 := original_second_third_telescope d he hemax (N : ℝ) hN
    weight (fun _ _ => 1) (carrier N)
  rw [signed_root_eq_raw _ (common3_even d (N : ℝ)),
    signed_root_eq_raw _ (HistoricalThirdCoarse.policy_even (d.e : ℝ) d.chi d.m d.omega (N : ℝ))] at h23
  have h23n := congrArg (normalize N) h23
  simp only [normalize_add] at h23n
  change normalize N (rawRoot (common3 d (N : ℝ)) N) =
    normalize N (rawRoot (old3 d (N : ℝ)) N) +
      normalize N (secondChange d (N : ℝ) weight (fun _ _ => 1) (carrier N)) +
      normalize N (thirdIncrement e q a N) at h23n
  have h2 : normalize N (secondChange d (N : ℝ) weight (fun _ _ => 1) (carrier N)) =
      -normalizedActualSaving d N := by
    unfold normalize normalizedActualSaving
    ring
  have h4 : rawRoot (policy4 d (N : ℝ)) N =
      rawRoot (common3 d (N : ℝ)) N - originalFourthSaving d N N (cutoff N) :=
    common_fourth_raw_ledger d (P4AOriginalArchiveFourteenPositivePresieve.actual_fourth_geometry e q a)
      N N hN (cutoff N)
  have h4n := congrArg (normalize N) h4
  rw [normalize_sub] at h4n
  have h5n : normalize N (rawRoot (policy4 d (N : ℝ)) N) -
      normalize N (rawRoot (policy5 d (N : ℝ)) N) = fifthSaving e q a N := by
    change normalize N (rawRoot (policy4 d (N : ℝ)) N) -
      normalize N (rawRoot (policy5 d (N : ℝ)) N) =
      normalize N (rawRoot (policy4 d (N : ℝ)) N - rawRoot (policy5 d (N : ℝ)) N)
    exact (normalize_sub N _ _).symm
  have hlast := congrArg (normalize N) (licensed_raw_sub_archive_fifth trim n e q a N)
  rw [normalize_sub] at hlast
  change normalize N (rawRoot (licensed trim n e q a (N : ℝ)) N) -
    normalize N (rawRoot (policy5 d (N : ℝ)) N) = _ at hlast
  change _ = normalize N (rawRoot (old3 d (N : ℝ)) N) + _ - _ - _ - _ + _
  linarith only [h23n, h2, h4n, h5n, hlast]

end
end ImbalancedChen.P4AOriginalFull87RawChronology
