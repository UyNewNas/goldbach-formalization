import ImbalancedChen.P5OriginalCommonRefinedAncestry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The common prefix rule is tied to its actual cap formulas, original first
stop and original fourth/fifth rows. Containment below is of actual retained
approvals, not coefficientwise monotonicity or preservation of a numerical
gain. All original and corrected policies keep their separate names. -/
namespace ImbalancedChen.P5OriginalCommonRefinedPreservation
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonRefinedAncestry
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

private theorem finiteMax_seed_mono {ι : Type*} (rows : Finset ι)
    (eligible : ι → Prop) (profile : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    P1OriginalVariableFourthContinuation.finiteMax rows eligible profile a ≤
      P1OriginalVariableFourthContinuation.finiteMax rows eligible profile b := by
  apply P1OriginalVariableFourthContinuation.finiteMax_le
  · exact hab.trans (P1OriginalVariableFourthContinuation.finiteMax_seed_le _ _ _ _)
  · intro r hr he
    exact P1OriginalVariableFourthContinuation.finiteMax_row_le _ _ _ _ r hr he

/-- Exact historical policy level after its retained third node. -/
theorem old3_after_two (d : OriginalData) (N : ℝ) (positive : Bool)
    (pre : List ℕ) (hlen : 2 < pre.length) :
    old3 d N positive pre = ordinaryParityRosserPolicy false
      (N ^ originalSeed d N pre) positive pre := by
  have hn : ¬pre.length ≤ 2 := by omega
  change thirdCappedUpperPolicy _ _ positive pre = _
  simp only [thirdCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg hn,
    frozenParityRosserPolicy, ancestorFrozenPolicy]
  change ordinaryParityRosserPolicy false
    (HistoricalThirdCoarse.frozenLevel (d.e : ℝ) d.chi d.m d.omega N pre) positive pre = _
  simpa only [originalSeed] using congrArg
    (fun Q : ℝ => ordinaryParityRosserPolicy false Q positive pre)
    (P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
      (d.e : ℝ) d.chi d.m d.omega N pre)

/-- Every actual corrected branch, including the ordinary inherited branch,
has the literal fallbackSeed value used by the constructor. -/
theorem fallback23_after_three (d : OriginalData) (N : ℝ) (positive : Bool)
    (pre : List ℕ) (hlen : 3 < pre.length) :
    fallback23 d N positive pre = ordinaryParityRosserPolicy false
      (N ^ fallbackSeed d N pre) positive pre := by
  have h3 : ¬pre.length ≤ 3 := by omega
  have h2 : ¬pre.length ≤ 2 := by omega
  by_cases ht : thirdGuard N pre
  · simp [fallback23, finalPolicy, firstExitDepthSplicePolicy, h3,
      thirdReplacement, ht, thirdQ, fallbackSeed]
  · by_cases hs : secondGuard N pre
    · simp [fallback23, finalPolicy, firstExitDepthSplicePolicy, h3,
        thirdReplacement, ht, secondPolicy, h2, secondReplacement, hs, fallbackSeed]
    · simpa [fallback23, finalPolicy, firstExitDepthSplicePolicy, h3,
        thirdReplacement, ht, secondPolicy, h2, secondReplacement, hs,
        fallbackSeed, oldPolicy, old3] using old3_after_two d N positive pre (by omega)

private theorem upper_or_eq_upper_of_le (Q R : ℝ) (hQR : Q ≤ R)
    (positive : Bool) (pre : List ℕ) :
    (ordinaryParityRosserPolicy false Q positive pre ||
      ordinaryParityRosserPolicy false R positive pre) =
      ordinaryParityRosserPolicy false R positive pre := by
  cases positive with
  | true => simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]
  | false =>
      by_cases hq : ordinaryRosserPrefixAdmissible false Q pre
      · have hr := ordinaryRosserPrefixAdmissible_mono false pre hQR hq
        simp [ordinaryParityRosserPolicy, oddFirstExitPolicy, hq, hr]
      · simp [ordinaryParityRosserPolicy, oddFirstExitPolicy, hq]

/-- The Boolean common refinement is the maximum of its two ACTUAL
third continuation levels, rather than a new assumed source identity. -/
theorem common3_after_three (d : OriginalData) (N : ℝ) (hN : 1 ≤ N)
    (positive : Bool) (pre : List ℕ) (hlen : 3 < pre.length) :
    common3 d N positive pre = ordinaryParityRosserPolicy false
      (N ^ lambda3 d N pre) positive pre := by
  unfold common3
  rw [old3_after_two d N positive pre (by omega), fallback23_after_three d N positive pre hlen]
  unfold lambda3
  by_cases h : originalSeed d N pre ≤ fallbackSeed d N pre
  · rw [max_eq_right h]
    exact upper_or_eq_upper_of_le _ _ (Real.rpow_le_rpow_of_exponent_le hN h) positive pre
  · rw [max_eq_left (le_of_not_ge h), Bool.or_comm]
    exact upper_or_eq_upper_of_le _ _
      (Real.rpow_le_rpow_of_exponent_le hN (le_of_not_ge h)) positive pre

/-- All future descendant queries read the same original third/second
ancestors. The common cap cannot depend on a later fourth/fifth child. -/
theorem lambda3_ancestor (d : OriginalData) (N : ℝ) (k : ℕ) (hk : 3 ≤ k)
    (pre : List ℕ) : lambda3 d N (rosserAncestor k pre) = lambda3 d N pre := by
  have h3 := rosserAncestor_nested 3 k hk pre
  have h2 := rosserAncestor_nested 2 k (by omega) pre
  simp [lambda3, fallbackSeed, originalSeed,
    P1OriginalVariableFourthContinuation.seedExponent, thirdGuard, secondGuard, h3, h2]

theorem common3_through_two (d : OriginalData) (N : ℝ) (positive : Bool)
    (pre : List ℕ) (hlen : pre.length ≤ 2) : common3 d N positive pre = old3 d N positive pre := by
  have h3 : pre.length ≤ 3 := hlen.trans (by decide)
  simp [common3, fallback23, finalPolicy, secondPolicy, firstExitDepthSplicePolicy,
    h3, hlen, oldPolicy, old3]

/-- Literal firstStop at the original initial cap is preserved by every
later common row maximum and the sixth/eighth selected family. -/
theorem final_firstStop_iff (d : OriginalData) (N : ℝ) (p : ℕ) :
    policy8 d N false [p] = true ↔
      ordinaryRosserPrefixAdmissible false (N ^ HistoricalThirdCoarse.initial (d.e : ℝ)) [p] ∧
      HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m N [p] := by
  rw [policy8_through_six_eq_fifth d N false [p] (by simp)]
  simp only [policy5, firstExitDepthSplicePolicy, List.length_singleton, if_pos (by decide : 1 ≤ 4)]
  rw [common3_through_two d N false [p] (by simp)]
  simp [old3, HistoricalThirdCoarse.policy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]

theorem lambda3_le_exponent4 (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    lambda3 d N pre ≤ exponent4 d N pre := by
  unfold exponent4
  split_ifs
  · exact P1OriginalVariableFourthContinuation.finiteMax_seed_le _ _ _ _
  · exact le_rfl

theorem inherited4_le_exponent5 (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    exponent4 d N (rosserAncestor 4 pre) ≤ exponent5 d N pre := by
  unfold exponent5
  split_ifs
  · exact P1OriginalVariableFourthContinuation.finiteMax_seed_le _ _ _ _
  · exact le_rfl

theorem lambda3_le_exponent5 (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    lambda3 d N pre ≤ exponent5 d N pre := by
  rw [← lambda3_ancestor d N 4 (by decide) pre]
  exact (lambda3_le_exponent4 d N _).trans (inherited4_le_exponent5 d N pre)

/-- Every original licensed fourth row and the original raw seed remain
inside the common actual fourth finite maximum. -/
theorem original_exponent4_le_common (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    P1OriginalVariableFourthContinuation.exponent4 (d.e : ℝ) d.chi d.m d.omega N d.rows4
      (P1OriginalVariableFourthContinuation.producerEligible d.licensed4)
      (fun r => r.bufferedCandidate (d.e : ℝ)) pre ≤ exponent4 d N pre := by
  unfold P1OriginalVariableFourthContinuation.exponent4 exponent4
  split_ifs
  · unfold P1OriginalVariableFourthContinuation.profile4
    exact finiteMax_seed_mono _ _ _ (le_max_left _ _)
  · exact le_max_left _ _

/-- All original fifth row occurrences/eligibility are unchanged; the
only changed seed is larger and read on the same fourth ancestor. -/
theorem original_exponent5_le_common (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    P1OriginalVariableFifthContinuation.exponent5 d.e d.chi d.m d.omega N
      d.rows4 d.licensed4 d.J5 d.rows5 pre ≤ exponent5 d N pre := by
  unfold P1OriginalVariableFifthContinuation.exponent5
    P1OriginalVariableFifthContinuation.inherited4 exponent5
  split_ifs
  · exact finiteMax_seed_mono _ _ _ (original_exponent4_le_common d N _)
  · exact original_exponent4_le_common d N _

/-- Actual approvals of the original variable-fifth policy remain actual
approvals of the common policy. This is not signed coefficient monotonicity. -/
theorem original_policy5_approval_preserved
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega N
      d.rows4 d.licensed4 d.J5 d.rows5 positive pre = true) :
    policy5 d N positive pre = true := by
  cases positive with
  | true => exact policy5_even d N pre
  | false =>
      by_cases h4 : pre.length ≤ 4
      · have ho : old3 d N false pre = true := by
          simpa [old3] using
            (P1OriginalVariableFifthContinuation.policy5_through_four
              d.e d.chi d.m d.omega N d.rows4 d.licensed4 d.J5 d.rows5 false pre h4).symm.trans hp
        simp [policy5, firstExitDepthSplicePolicy, h4, common3, ho]
      · have ho : ordinaryRosserPrefixAdmissible false
            (N ^ P1OriginalVariableFifthContinuation.exponent5 d.e d.chi d.m d.omega N
              d.rows4 d.licensed4 d.J5 d.rows5 (rosserAncestor 5 pre)) pre := by
          simpa [P1OriginalVariableFifthContinuation.policy5, fifthCappedUpperPolicy,
            firstExitDepthSplicePolicy, h4, frozenParityRosserPolicy, ancestorFrozenPolicy,
            ordinaryParityRosserPolicy, oddFirstExitPolicy, P1OriginalVariableFifthContinuation.level5] using hp
        have hn := ordinaryRosserPrefixAdmissible_mono false pre
          (Real.rpow_le_rpow_of_exponent_le hN (original_exponent5_le_common d N _)) ho
        simpa [policy5, firstExitDepthSplicePolicy, h4, frozenParityRosserPolicy,
          ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy, level5] using hn

/-- Corrected second/third actions are also retained on their actual
histories; their level is bounded by the SAME common fifth ancestor. -/
theorem fallback23_approval_preserved
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : fallback23 d N positive pre = true) : policy5 d N positive pre = true := by
  cases positive with
  | true => exact policy5_even d N pre
  | false =>
      by_cases h4 : pre.length ≤ 4
      · simp [policy5, firstExitDepthSplicePolicy, h4, common3, hp]
      · rw [fallback23_after_three d N false pre (by omega)] at hp
        have ho : ordinaryRosserPrefixAdmissible false (N ^ fallbackSeed d N pre) pre := by
          simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
        have he : fallbackSeed d N pre ≤ exponent5 d N (rosserAncestor 5 pre) := by
          have hs := lambda3_le_exponent5 d N (rosserAncestor 5 pre)
          rw [lambda3_ancestor d N 5 (by decide) pre] at hs
          exact (le_max_right _ _).trans hs
        have hn := ordinaryRosserPrefixAdmissible_mono false pre
          (Real.rpow_le_rpow_of_exponent_le hN he) ho
        simpa [policy5, firstExitDepthSplicePolicy, h4, frozenParityRosserPolicy,
          ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy, level5] using hn

/-- The actual eleven-family maximum inherits the TRUE fifth cap. -/
theorem fifth_approval_preserved_by_sixth
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : policy5 d N positive pre = true) : policy6 d N positive pre = true := by
  cases positive with
  | true => exact policy6_even d N pre
  | false =>
      by_cases h6 : pre.length ≤ 6
      · simpa [policy6, firstExitDepthSplicePolicy, h6] using hp
      · have h4 : ¬pre.length ≤ 4 := by omega
        have ho : ordinaryRosserPrefixAdmissible false
            (N ^ exponent5 d N (rosserAncestor 5 pre)) pre := by
          simpa [policy5, firstExitDepthSplicePolicy, h4, frozenParityRosserPolicy,
            ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy, level5] using hp
        have he := actualParent5_le_lambda6 d N (rosserAncestor 6 pre)
        rw [actualParent5_ancestor_six d N pre] at he
        have hn := ordinaryRosserPrefixAdmissible_mono false pre
          (Real.rpow_le_rpow_of_exponent_le hN he) ho
        simpa [policy6, firstExitDepthSplicePolicy, h6, frozenParityRosserPolicy,
          ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy, level6] using hn

/-- The adopted eighth guard either raises its current sixth cap or
inherits that exact cap. It cannot erase an earlier accepted history. -/
theorem sixth_approval_preserved_by_eighth
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : policy6 d N positive pre = true) : policy8 d N positive pre = true := by
  cases positive with
  | true => exact policy8_even d N pre
  | false =>
      by_cases h8 : pre.length ≤ 8
      · rwa [policy8_through_eight_eq_six d N false pre h8]
      · have h6 : ¬pre.length ≤ 6 := by omega
        have ho : ordinaryRosserPrefixAdmissible false
            (N ^ lambda6 d N (rosserAncestor 6 pre)) pre := by
          simpa [policy6, firstExitDepthSplicePolicy, h6, frozenParityRosserPolicy,
            ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy, level6] using hp
        have he := P5OriginalAdoptedEighthPhysicalMasks.actual_sixth_le_raised N
          (lambda3 d N) (lambda6 d N) (rosserAncestor 8 pre)
        rw [rosserAncestor_nested 6 8 (by decide)] at he
        have hn := ordinaryRosserPrefixAdmissible_mono false pre
          (Real.rpow_le_rpow_of_exponent_le hN he) ho
        simpa [policy8, P5OriginalAdoptedEighthPhysicalMasks.familyPolicy,
          firstExitDepthSplicePolicy, h8, frozenParityRosserPolicy, ancestorFrozenPolicy,
          ordinaryParityRosserPolicy, oddFirstExitPolicy] using hn

theorem original_policy5_approval_preserved_final
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega N
      d.rows4 d.licensed4 d.J5 d.rows5 positive pre = true) : policy8 d N positive pre = true :=
  sixth_approval_preserved_by_eighth d N hN positive pre
    (fifth_approval_preserved_by_sixth d N hN positive pre
      (original_policy5_approval_preserved d N hN positive pre hp))

theorem fallback23_approval_preserved_final
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hp : fallback23 d N positive pre = true) : policy8 d N positive pre = true :=
  sixth_approval_preserved_by_eighth d N hN positive pre
    (fifth_approval_preserved_by_sixth d N hN positive pre
      (fallback23_approval_preserved d N hN positive pre hp))

private theorem validSelection_mono
    (P R : Bool → List ℕ → Bool)
    (hPR : ∀ positive pre, P positive pre = true → R positive pre = true)
    (chosen pre : List ℕ) (positive : Bool)
    (h : FirstExitValidSelection P pre positive chosen) :
    FirstExitValidSelection R pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => trivial
  | cons p ps ih => exact ⟨hPR (!positive) (p :: pre) h.1, ih (p :: pre) (!positive) h.2⟩

/-- Every genuine original fifth prime word remains a genuine final
common-policy prime word; no leaf weight or arithmetic test is discarded. -/
theorem original_root_moduli_subset_final
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (carrier : List ℕ) :
    firstExitRetainedModuli
      (P1OriginalVariableFifthContinuation.policy5 d.e d.chi d.m d.omega N
        d.rows4 d.licensed4 d.J5 d.rows5) carrier ⊆
      firstExitRetainedModuli (policy8 d N) carrier := by
  intro q hq
  obtain ⟨chosen, hc, hv, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection _ carrier q).mp hq
  exact (mem_firstExitRetainedModuli_iff_validSelection _ carrier q).mpr
    ⟨chosen, hc, validSelection_mono _ _ (original_policy5_approval_preserved_final d N hN)
      chosen [] true hv, hprod⟩

theorem fallback_root_moduli_subset_final
    (d : OriginalData) (N : ℝ) (hN : 1 ≤ N) (carrier : List ℕ) :
    firstExitRetainedModuli (fallback23 d N) carrier ⊆ firstExitRetainedModuli (policy8 d N) carrier := by
  intro q hq
  obtain ⟨chosen, hc, hv, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection _ carrier q).mp hq
  exact (mem_firstExitRetainedModuli_iff_validSelection _ carrier q).mpr
    ⟨chosen, hc, validSelection_mono _ _ (fallback23_approval_preserved_final d N hN)
      chosen [] true hv, hprod⟩

end
end ImbalancedChen.P5OriginalCommonRefinedPreservation
