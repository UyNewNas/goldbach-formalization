import ImbalancedChen.P5OriginalCommonRefinedConstructor
import ImbalancedChen.P5OriginalJoinedLateRange

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Range certificate for the independently frozen common-refined constructor.
The old third tree and corrected above-mu second/third tree are both kept;
original fourth/fifth row formulas use their actual common ancestor; the
sixth maximum is over the literal eleven PhysicalCell suppliers. Its local
ceiling is proved from BOTH selected branch licences, not assumed as h6.
The adopted eighth branch uses its original chosen PhysicalRows licence.
The resulting fixed rough support and nonzero SAME signed small/rough
coefficient give actualActiveUpperCap <= N^(599/1000).

This does not certify the numerical common compact partition, exhaustion,
archived gains, or that every provided row licence is nonempty. Those are
not needed for this upper range of the actual independently defined policy.
-/
namespace ImbalancedChen.P5Z.ActualCommonRefinedRange
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P1OriginalVariableFourthContinuation
open ImbalancedChen.P2OriginalFourthCapProducerInterface
open ImbalancedChen.P5Z.OriginalFifthPhysicalRange
open ImbalancedChen.P5Z.OriginalJoinedLateRange
open ImbalancedChen.P4BActualSmoothHyperbolaCorrection
open ImbalancedChen.P5OriginalAboveMuThirdLowerPhysicalCoefficient

/-- The two ACTUAL strict selected licences meet at 153/256. Neither
an auxiliary PP exponent nor a raw old-cap equality enters this bound. -/
theorem eleven_newCap_lt_envelope {c : Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical}
    (hc : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) : Certificates.P2OriginalSixthElevenLogSemantics.newCap c t < (153/256 : ℝ) := by
  have ha := hc.selectedAscending
  have hd := hc.selectedDescending
  linarith

theorem initial_le_theta (e : ℚ) (he : 0 ≤ e) :
    HistoricalThirdCoarse.initial (e : ℝ) ≤ (299/500 : ℝ) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  dsimp [HistoricalThirdCoarse.initial, extendedDistributionCap]
  linarith

theorem originalSeed_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) : P5OriginalCommonRefinedConstructor.originalSeed d N pre ≤ (299/500 : ℝ) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  exact (effectiveExponent_le_initial (d.e : ℝ) d.chi heR d.m d.omega N _).trans
    (initial_le_theta d.e he)

theorem fallbackSeed_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) : P5OriginalCommonRefinedConstructor.fallbackSeed d N pre ≤ (299/500 : ℝ) := by
  unfold P5OriginalCommonRefinedConstructor.fallbackSeed
  split_ifs
  · exact (VariableEnvelope.v_le_cap _).trans (by norm_num [VariableEnvelope.cap])
  · exact (VariableEnvelope.v_le_cap _).trans (by norm_num [VariableEnvelope.cap])
  · exact originalSeed_le_theta d he N pre

theorem lambda3_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) : P5OriginalCommonRefinedConstructor.lambda3 d N pre ≤ (299/500 : ℝ) :=
  max_le (originalSeed_le_theta d he N pre) (fallbackSeed_le_theta d he N pre)

/-- Actual fourth maximum, re-seeded at the common third parent. -/
theorem exponent4_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) : P5OriginalCommonRefinedConstructor.exponent4 d N pre ≤ (299/500 : ℝ) := by
  have hseed := lambda3_le_theta d he N pre
  unfold P5OriginalCommonRefinedConstructor.exponent4
  split_ifs
  · apply finiteMax_le _ _ _ _ _ hseed
    intro r hr heligible
    rw [r.bufferedCandidate_eq]
    have hv := VariableEnvelope.v_le_cap
      (∑ i ∈ r.selected, primeHistoryLogCoordinates N 4 pre i)
    have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
    dsimp [VariableEnvelope.cap] at hv
    linarith
  · exact hseed

/-- Actual fifth maximum, using its actual FOURTH ancestor rather than
an asserted equality with the old raw sixth comparison cap. -/
theorem exponent5_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) : P5OriginalCommonRefinedConstructor.exponent5 d N pre ≤ (299/500 : ℝ) := by
  have hseed := exponent4_le_theta d he N (rosserAncestor 4 pre)
  unfold P5OriginalCommonRefinedConstructor.exponent5
  dsimp only
  split_ifs
  · apply finiteMax_le _ _ _ _ _ hseed
    intro r hr heligible
    unfold P1OriginalVariableFifthContinuation.candidate
    rw [P1OriginalVariableFifthContinuation.envelope_eq_v]
    have hv := VariableEnvelope.v_le_cap
      (∑ i ∈ r.selected, primeHistoryLogCoordinates N 5 pre i)
    have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
    dsimp [VariableEnvelope.cap] at hv
    linarith
  · exact hseed

theorem actualParent5_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) : P5OriginalCommonRefinedConstructor.actualParent5 d N pre ≤ (299/500 : ℝ) :=
  exponent5_le_theta d he N (rosserAncestor 5 pre)

/-- ELIMINATES h6 for the concrete all-eleven finite supplier. All
candidates come from the actual PhysicalCell and old-parent re-test;
the finite maximum keeps its true fifth seed when no cell is eligible. -/
theorem actualEleven_lambda6_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) : P5OriginalCommonRefinedConstructor.lambda6 d N pre ≤ (299/500 : ℝ) := by
  unfold P5OriginalCommonRefinedConstructor.lambda6
  apply finiteMax_le _ _ _ _ _ (actualParent5_le_theta d he N pre)
  intro c hc heligible
  exact (eleven_newCap_lt_envelope heligible.2.1).le.trans (by norm_num)

theorem actualRaisedExponent_le_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (pre : List ℕ) :
    P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N
      (P5OriginalCommonRefinedConstructor.lambda3 d N) (P5OriginalCommonRefinedConstructor.lambda6 d N) pre ≤ (299/500 : ℝ) :=
  OriginalJoinedLateRange.actualRaisedExponent_le_theta N _ _
    (actualEleven_lambda6_le_theta d he N) pre

/-- The historical old T3 policy, with its original firstStop, has this
root range independently of later row selections. -/
theorem old3_implies_root (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : P5OriginalCommonRefinedConstructor.old3 d N positive pre = true) :
    ordinaryParityRosserPolicy false (N^(299/500 : ℝ)) positive pre = true := by
  cases positive with
  | true => exact ordinaryParityRosserPolicy_upper_even _ _
  | false =>
    have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
    have hi : ordinaryRosserPrefixAdmissible false
        (N^HistoricalThirdCoarse.initial (d.e : ℝ)) pre := by
      by_cases h2 : pre.length ≤ 2
      · rw [P5OriginalCommonRefinedConstructor.old3, HistoricalThirdCoarse.policy_through_two
          (d.e : ℝ) d.chi d.m d.omega N false pre h2] at hp
        have ha : ordinaryRosserPrefixAdmissible false
            (N^HistoricalThirdCoarse.initial (d.e : ℝ)) pre ∧
              (pre.length = 1 → HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m N pre) := by
          simpa [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy] using hp
        exact ha.1
      · have ha : ordinaryRosserPrefixAdmissible false
            (HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega N
              (rosserAncestor 3 pre)) pre := by
          simpa [P5OriginalCommonRefinedConstructor.old3, HistoricalThirdCoarse.policy, thirdCappedUpperPolicy,
            firstExitDepthSplicePolicy, h2, frozenParityRosserPolicy,
            ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
        exact ordinaryRosserPrefixAdmissible_mono false pre
          (rawLevel_le_initial (d.e : ℝ) d.chi heR d.m d.omega N hN _) ha
    have hroot := ordinaryRosserPrefixAdmissible_mono false pre
      (Real.rpow_le_rpow_of_exponent_le hN (initial_le_theta d.e he)) hi
    simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hroot

/-- Corrected rank-two replacement has the literal v(y) ceiling. -/
theorem secondPolicy_implies_root (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : secondPolicy (d.e : ℝ) d.chi d.m d.omega N positive pre = true) :
    ordinaryParityRosserPolicy false (N^(299/500 : ℝ)) positive pre = true := by
  by_cases h2 : pre.length ≤ 2
  · apply old3_implies_root d he N hN positive pre
    simpa [P5OriginalCommonRefinedConstructor.old3, secondPolicy, firstExitDepthSplicePolicy, h2, oldPolicy] using hp
  · by_cases hg : secondGuard N pre
    · have hi : ordinaryParityRosserPolicy false
          (N^VariableEnvelope.v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1))
          positive pre = true := by
        simpa [secondPolicy, firstExitDepthSplicePolicy, h2, secondReplacement, hg] using hp
      cases positive with
      | true => exact ordinaryParityRosserPolicy_upper_even _ _
      | false =>
        have ha : ordinaryRosserPrefixAdmissible false
            (N^VariableEnvelope.v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1))
            pre := by simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hi
        have hlevel : N^VariableEnvelope.v
            (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1) ≤ N^(299/500 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN
            ((VariableEnvelope.v_le_cap _).trans (by norm_num [VariableEnvelope.cap]))
        have ha' := ordinaryRosserPrefixAdmissible_mono false pre hlevel ha
        simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using ha'
    · apply old3_implies_root d he N hN positive pre
      simpa [P5OriginalCommonRefinedConstructor.old3, secondPolicy, firstExitDepthSplicePolicy, h2,
        secondReplacement, hg, oldPolicy] using hp

/-- Corrected rank-three selected pair has its literal v(y+z) ceiling;
the global ordinary UPPER parity is kept through this source dictionary. -/
theorem fallback23_implies_root (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : P5OriginalCommonRefinedConstructor.fallback23 d N positive pre = true) :
    ordinaryParityRosserPolicy false (N^(299/500 : ℝ)) positive pre = true := by
  by_cases h3 : pre.length ≤ 3
  · apply secondPolicy_implies_root d he N hN positive pre
    simpa [P5OriginalCommonRefinedConstructor.fallback23, finalPolicy, firstExitDepthSplicePolicy, h3] using hp
  · by_cases hg : thirdGuard N pre
    · have hi : ordinaryParityRosserPolicy false (thirdQ N (rosserAncestor 3 pre))
          positive pre = true := by
        simpa [P5OriginalCommonRefinedConstructor.fallback23, finalPolicy, firstExitDepthSplicePolicy, h3,
          thirdReplacement, hg] using hp
      cases positive with
      | true => exact ordinaryParityRosserPolicy_upper_even _ _
      | false =>
        have ha : ordinaryRosserPrefixAdmissible false
            (thirdQ N (rosserAncestor 3 pre)) pre := by
          simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hi
        have hlevel : thirdQ N (rosserAncestor 3 pre) ≤ N^(299/500 : ℝ) := by
          unfold thirdQ
          exact Real.rpow_le_rpow_of_exponent_le hN
            ((VariableEnvelope.v_le_cap _).trans (by norm_num [VariableEnvelope.cap]))
        have ha' := ordinaryRosserPrefixAdmissible_mono false pre hlevel ha
        simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using ha'
    · apply secondPolicy_implies_root d he N hN positive pre
      simpa [P5OriginalCommonRefinedConstructor.fallback23, finalPolicy, firstExitDepthSplicePolicy, h3,
        thirdReplacement, hg] using hp

theorem common3_implies_root (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : P5OriginalCommonRefinedConstructor.common3 d N positive pre = true) :
    ordinaryParityRosserPolicy false (N^(299/500 : ℝ)) positive pre = true := by
  rcases Bool.or_eq_true.mp hp with hold | hnew
  · exact old3_implies_root d he N hN positive pre hold
  · exact fallback23_implies_root d he N hN positive pre hnew

theorem actualPolicy5_implies_root (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : P5OriginalCommonRefinedConstructor.policy5 d N positive pre = true) :
    ordinaryParityRosserPolicy false (N^(299/500 : ℝ)) positive pre = true := by
  by_cases h4 : pre.length ≤ 4
  · apply common3_implies_root d he N hN positive pre
    simpa [P5OriginalCommonRefinedConstructor.policy5, firstExitDepthSplicePolicy, h4] using hp
  · cases positive with
    | true => exact ordinaryParityRosserPolicy_upper_even _ _
    | false =>
      have hi : ordinaryRosserPrefixAdmissible false
          (P5OriginalCommonRefinedConstructor.level5 d N (rosserAncestor 5 pre)) pre := by
        simpa [P5OriginalCommonRefinedConstructor.policy5, firstExitDepthSplicePolicy, h4, frozenParityRosserPolicy,
          ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
      have hlevel : P5OriginalCommonRefinedConstructor.level5 d N (rosserAncestor 5 pre) ≤ N^(299/500 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hN (exponent5_le_theta d he N _)
      have hi' := ordinaryRosserPrefixAdmissible_mono false pre hlevel hi
      simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hi'

/-- Full actual common-refined late policy; h6 has disappeared. Its
sixth and eighth ancestors are the original literal frozen ancestors. -/
theorem actualPolicy8_implies_root (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : P5OriginalCommonRefinedConstructor.policy8 d N positive pre = true) :
    ordinaryParityRosserPolicy false (N^(299/500 : ℝ)) positive pre = true := by
  cases positive with
  | true => exact ordinaryParityRosserPolicy_upper_even _ _
  | false =>
    have hadm : ordinaryRosserPrefixAdmissible false (N^(299/500 : ℝ)) pre := by
      by_cases h8 : pre.length ≤ 8
      · by_cases h6 : pre.length ≤ 6
        · have hbase : P5OriginalCommonRefinedConstructor.policy5 d N false pre = true := by
            simpa [P5OriginalCommonRefinedConstructor.policy8, P5OriginalAdoptedEighthPhysicalMasks.familyPolicy,
              P5OriginalAdoptedEighthPhysicalMasks.parentPolicy,
              P4AOriginalEighthParentPhysicalLedger.parentPolicy,
              P4AActualSixthFrozenEighthAdmission.sixthPolicy,
              firstExitDepthSplicePolicy, h8, h6] using hp
          have hi := actualPolicy5_implies_root d he N hN false pre hbase
          simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hi
        · have hi : ordinaryRosserPrefixAdmissible false
              (N^P5OriginalCommonRefinedConstructor.lambda6 d N (rosserAncestor 6 pre)) pre := by
            simpa [P5OriginalCommonRefinedConstructor.policy8, P5OriginalAdoptedEighthPhysicalMasks.familyPolicy,
              P5OriginalAdoptedEighthPhysicalMasks.parentPolicy,
              P4AOriginalEighthParentPhysicalLedger.parentPolicy,
              P4AActualSixthFrozenEighthAdmission.sixthPolicy,
              firstExitDepthSplicePolicy, h8, h6, frozenParityRosserPolicy,
              ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
          exact ordinaryRosserPrefixAdmissible_mono false pre
            (Real.rpow_le_rpow_of_exponent_le hN (actualEleven_lambda6_le_theta d he N _)) hi
      · have hi : ordinaryRosserPrefixAdmissible false
            (N^P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N
              (P5OriginalCommonRefinedConstructor.lambda3 d N) (P5OriginalCommonRefinedConstructor.lambda6 d N) (rosserAncestor 8 pre)) pre := by
          simpa [P5OriginalCommonRefinedConstructor.policy8, P5OriginalAdoptedEighthPhysicalMasks.familyPolicy,
            firstExitDepthSplicePolicy, h8, frozenParityRosserPolicy,
            ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
        exact ordinaryRosserPrefixAdmissible_mono false pre
          (Real.rpow_le_rpow_of_exponent_le hN (actualRaisedExponent_le_theta d he N _)) hi
    simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hadm

/-- Actual retained rough support, uniform before enumeration cutoff,
prime endpoints or overlaps among eligible original rows are chosen. -/
theorem actualRoughSupport_lt_theta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N enumerationCap : ℕ) (w z : ℝ) (hN : 2 ≤ N) {b : ℕ}
    (hb : b ∈ fixedRoughSupport (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ) false) N enumerationCap w z) :
    (b : ℝ) < (N : ℝ)^(299/500 : ℝ) := by
  let P := P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)
  let R := (N : ℝ)^(299/500 : ℝ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hR : 1 < R := Real.one_lt_rpow hNr (by norm_num)
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    P (P5OriginalCommonRefinedConstructor.policy8_even d (N : ℝ)) N enumerationCap w z] at hb
  obtain ⟨chosen, hsub, hvalid, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection P _ b).mp hb
  have hv := validSelection_mono P (ordinaryParityRosserPolicy false R)
    (actualPolicy8_implies_root d he (N : ℝ) hNr.le) [] chosen true hvalid
  have hroot : b ∈ firstExitRetainedModuli (ordinaryParityRosserPolicy false R)
      (roughPrimeUniverse N enumerationCap w z) :=
    (mem_firstExitRetainedModuli_iff_validSelection _ _ b).mpr ⟨chosen, hsub, hv, hprod⟩
  rw [ordinaryParityRosserRetainedModuli_eq false R hR _
    (roughPrimeUniverse_pairwise_gt N enumerationCap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (by simp)] at hroot
  exact ((mem_ordinaryRosserRetainedModuli_iff false R hR _
    (roughPrimeUniverse_pairwise_gt N enumerationCap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) b).mp hroot).2.1

/-- SAME actual signed rho: no absolute or unsigned replacement is made.
Nonzero coefficient supplies a genuine small factor <L and retained rough
factor; cancellation can only remove support from this upper range. -/
theorem actualRho_lt_inflatedTheta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N enumerationCap : ℕ) (w z epsilon L : ℝ) (hN : 2 ≤ N)
    (hepsilon : epsilon ≤ 1/1000) (hL : L ≤ (N : ℝ)^epsilon) {q : ℕ}
    (hq : P5OriginalCommonRefinedConstructor.rho d N enumerationCap w z L q ≠ 0) :
    (q : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNr
  obtain ⟨a, ha, b, hb, hprod, haL, hbne⟩ := actualSmallRoughRho_ne_zero_factors
    (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ) false) N enumerationCap w z L hq
  have hbR := actualRoughSupport_lt_theta d he N enumerationCap w z hN hb
  have hqR : (q : ℝ) < (N : ℝ)^((299/500 : ℝ)+epsilon) := by
    calc
      (q : ℝ) = (a : ℝ)*(b : ℝ) := by rw [hprod, Nat.cast_mul]
      _ ≤ (N : ℝ)^epsilon*(b : ℝ) :=
        mul_le_mul_of_nonneg_right (haL.le.trans hL) (Nat.cast_nonneg _)
      _ < (N : ℝ)^epsilon*(N : ℝ)^(299/500 : ℝ) :=
        mul_lt_mul_of_pos_left hbR (Real.rpow_pos_of_pos hN0 _)
      _ = _ := by rw [Real.rpow_add hN0]; ring
  exact hqR.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))

theorem actualAttachedCoefficient_lt_inflatedTheta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℕ) (r epsilon : ℝ) (cap : ℕ → ℕ) (hN : 2 ≤ N)
    (hepsilon : epsilon ≤ 1/1000) {q : ℕ}
    (hq : attachedUpperCoefficient 1 r epsilon
      (fun M => P5OriginalCommonRefinedConstructor.policy8 d (M : ℝ) false) cap N q ≠ 0) :
    (q : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
  apply actualRho_lt_inflatedTheta d he N (cap N)
    ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) epsilon ((N : ℝ)^epsilon)
    hN hepsilon le_rfl
  simpa only [P5OriginalCommonRefinedConstructor.rho, attachedUpperCoefficient, one_mul] using hq

/-- Concrete range certificate consumed by proper-power/complete-modulus
payment: target-dependent actual selectors are evaluated at the SAME N.
There is NO local h6, root-support or active-cap premise. -/
theorem actualActiveCap_le_inflatedTheta (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N : ℕ) (r epsilon : ℝ) (cap : ℕ → ℕ) (hN : 2 ≤ N)
    (hepsilon : epsilon ≤ 1/1000) :
    (actualActiveUpperCap 1 r epsilon
      (fun M => P5OriginalCommonRefinedConstructor.policy8 d (M : ℝ) false) cap N : ℝ) ≤ (N : ℝ)^(599/1000 : ℝ) := by
  have hpow : 0 ≤ (N : ℝ)^(599/1000 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hs : actualActiveUpperCap 1 r epsilon
      (fun M => P5OriginalCommonRefinedConstructor.policy8 d (M : ℝ) false) cap N ≤ Nat.floor ((N : ℝ)^(599/1000 : ℝ)) := by
    unfold actualActiveUpperCap
    apply Finset.sup_le
    intro q hq
    exact (Nat.le_floor_iff hpow).mpr
      (actualAttachedCoefficient_lt_inflatedTheta d he N r epsilon cap hN hepsilon
        (Finset.mem_filter.mp hq).2).le
  exact (Nat.cast_le.mpr hs).trans (Nat.floor_le hpow)

end
end ImbalancedChen.P5Z.ActualCommonRefinedRange
