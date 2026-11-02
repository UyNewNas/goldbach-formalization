import ImbalancedChen.P5OriginalCommonFourthSourceLedger

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original fourth producer is confined to t1 <= 39/200 < mu.  Consequently
its complete signed gain survives the above-mu common refinement exactly.
This proves a source identity, not a monotonicity assertion about two signed
policies.  The above-mu correction is exactly the actual common-third change;
there is no additional fourth-bank interaction to estimate.
-/
namespace ImbalancedChen.P5OriginalCommonFourthFallbackExcision
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonRefinedSource P5OriginalCommonFourthSourceNavigation
open P5OriginalCommonFourthSourceLedger P1Pair12RetainedSignedSource
open P2OriginalFourthCapProducerInterface
open P4AOriginalVariableFifthPhysicalLedger
open P5OriginalCommonPositivePresieve P5OriginalArchivePositivePresieveGain
open P1HistoricalFifthCommonPolicyInputs P5OriginalFifthArchiveActualMean

/-- The existing producer geometry requirement, restricted to the actual
licensed rows.  It is not a source, density, or gain identity hypothesis. -/
def FourthGeometry (d : OriginalData) : Prop :=
  ∀ r ∈ d.rows4, d.licensed4 r → r.Geometry

/-- The actual closed producer boxes have no above-mu point.  This uses
Geometry's stored upper endpoint, through its already proved ordered lemma. -/
theorem no_fourth_row_above_mu (d : OriginalData) (hgeometry : FourthGeometry d)
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 4)
    (hmu : VariableEnvelope.mu < firstCoordinate N pre) :
    ∀ r ∈ d.rows4, ¬P1OriginalVariableFourthContinuation.producerEligible d.licensed4 r
      (primeHistoryLogCoordinates N 4 pre) := by
  intro r hr he
  have ht := (r.ordered (hgeometry r hr he.1) _ he.2).1.2.2.2
  have hfirst := ancestor_first_coordinate N 4 (by omega) pre (by omega)
  rw [rosserAncestor_self_of_length 4 pre hlen] at hfirst
  rw [hfirst] at ht
  exact (not_le_of_gt hmu) ht

/-- On the above-mu side the common fourth maximum has no eligible row;
its value is its actual common third seed, including all fallback maxima. -/
theorem common_exponent4_above_mu (d : OriginalData) (hgeometry : FourthGeometry d)
    (N : ℝ) (pre : List ℕ)
    (hmu : VariableEnvelope.mu < firstCoordinate N pre) :
    P5OriginalCommonRefinedConstructor.exponent4 d N pre = lambda3 d N pre := by
  unfold P5OriginalCommonRefinedConstructor.exponent4
  split_ifs with hlen
  · exact P1OriginalVariableFourthContinuation.finiteMax_eq_seed_of_outside _ _ _ _
      (no_fourth_row_above_mu d hgeometry N pre hlen hmu)
  · rfl

/-- The independently defined original fourth maximum also inherits,
so it continues to read the literal old third seed. -/
theorem original_exponent4_above_mu (d : OriginalData) (hgeometry : FourthGeometry d)
    (N : ℝ) (pre : List ℕ)
    (hmu : VariableEnvelope.mu < firstCoordinate N pre) :
    P1OriginalVariableFourthContinuation.exponent4 (d.e : ℝ) d.chi d.m d.omega N
      d.rows4 (P1OriginalVariableFourthContinuation.producerEligible d.licensed4) (fun r => r.bufferedCandidate (d.e : ℝ)) pre =
      originalSeed d N pre := by
  unfold P1OriginalVariableFourthContinuation.exponent4
  split_ifs with hlen
  · exact P1OriginalVariableFourthContinuation.profile4_eq_seed_of_outside _ _ _ _ _
      (no_fourth_row_above_mu d hgeometry N pre hlen hmu)
  · rfl

/-- A pointwise decision identity on all above-mu descendants, with the
actual common maximum retained rather than replaced by the fallback alone. -/
theorem common4_eq_common3_above_mu (d : OriginalData) (hgeometry : FourthGeometry d)
    (N : ℝ) (hN : 1 ≤ N) (positive : Bool) (pre : List ℕ)
    (hmu : VariableEnvelope.mu < firstCoordinate N pre) :
    policy4 d N positive pre = common3 d N positive pre := by
  by_cases h4 : pre.length ≤ 4
  · simp only [policy4, firstExitDepthSplicePolicy, if_pos h4]
  · have hm : VariableEnvelope.mu < firstCoordinate N (rosserAncestor 4 pre) := by
      rwa [firstCoordinate_ancestor N 4 (by omega)]
    rw [common3_after_three d N hN positive pre (by omega)]
    simp only [policy4, firstExitDepthSplicePolicy, if_neg h4,
      frozenParityRosserPolicy, ancestorFrozenPolicy, level4,
      common_exponent4_above_mu d hgeometry N _ hm,
      lambda3_ancestor d N 4 (by omega)]

theorem original4_eq_old3_above_mu (d : OriginalData) (hgeometry : FourthGeometry d)
    (N : ℝ) (positive : Bool) (pre : List ℕ)
    (hmu : VariableEnvelope.mu < firstCoordinate N pre) :
    original4 d N positive pre = old3 d N positive pre := by
  by_cases h4 : pre.length ≤ 4
  · exact original4_through_four d N positive pre h4
  · have hm : VariableEnvelope.mu < firstCoordinate N (rosserAncestor 4 pre) := by
      rwa [firstCoordinate_ancestor N 4 (by omega)]
    rw [old3_after_two d N positive pre (by omega)]
    simp only [original4, P1OriginalVariableFourthContinuation.producerPolicy4, P1OriginalVariableFourthContinuation.policy4,
      fourthCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg h4,
      frozenParityRosserPolicy, ancestorFrozenPolicy,
      P1OriginalVariableFourthContinuation.level4,
      original_exponent4_above_mu d hgeometry N _ hm, originalSeed,
      P1OriginalVariableFourthContinuation.seedExponent_ancestor_four]

/-- Policy agreement on one side of the first-coordinate cut propagates
through a complete signed continuation.  No prime word is deduplicated. -/
private theorem signedTest_eq_on_first_coordinate
    (N : ℝ) (P Q : Bool → List ℕ → Bool) (region : ℝ → Prop)
    (hpolicy : ∀ positive pre, region (firstCoordinate N pre) →
      P positive pre = Q positive pre)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (pre : List ℕ)
    (hlen : 1 ≤ pre.length) (hregion : region (firstCoordinate N pre))
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest P h T pre positive mass remaining =
      signedTest Q h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hr : region (firstCoordinate N (p :: pre)) := by
      rwa [firstCoordinate_cons N p pre hlen]
    simp only [signedTest, hpolicy (!positive) (p :: pre) hr]
    rw [ih (pre := pre) (positive := positive) (mass := mass)
        (hlen := hlen) (hregion := hregion),
      ih (pre := p :: pre) (positive := !positive) (mass := mass * h p)
        (hlen := by simp; omega) (hregion := hr)]

theorem common3_eq_splice_old3 (d : OriginalData) (N : ℝ) :
    common3 d N = firstExitDepthSplicePolicy 2 (old3 d N) (common3 d N) := by
  funext positive pre
  by_cases h2 : pre.length ≤ 2
  · simpa only [firstExitDepthSplicePolicy, if_pos h2] using
      common3_through_two d N positive pre h2
  · simp only [firstExitDepthSplicePolicy, if_neg h2]

/-- The I correction is precisely the independent common-third change.
The entire fourth-bank interaction disappears by genuine source geometry,
not by identifying old and common policies globally.  The test is arbitrary. -/
theorem correction_eq_common_third_change
    (d : OriginalData) (hgeometry : FourthGeometry d) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    correctionTest d N h T carrier =
      signedTest (common3 d N) h T [] true 1 carrier -
        signedTest (old3 d N) h T [] true 1 carrier := by
  have hthird := signedTest_splice_sub_eq_frontier 2 (old3 d N) (common3 d N)
    h T [] carrier true 1
  rw [← common3_eq_splice_old3] at hthird
  rw [hthird, correctionTest]
  generalize hs : firstExitDepthFrontier 2 (old3 d N) h [] true 1 carrier = states
  have hlen : ∀ s ∈ states, s.selectedPrefix.length = 2 := by
    intro s hmem
    rw [← hs] at hmem
    exact firstExitDepthFrontier_selected_length 2 _ h [] carrier true 1
      (by simp) s hmem
  clear hthird hs
  revert hlen
  induction states with
  | nil => intro hlen; simp
  | cons s states ih =>
    intro hlen
    have hl : 1 ≤ s.selectedPrefix.length := by
      have := hlen s (by simp)
      omega
    have htail : ∀ s' ∈ states, s'.selectedPrefix.length = 2 :=
      fun s' hs' => hlen s' (by simp [hs'])
    by_cases hm : VariableEnvelope.mu < firstCoordinate N s.selectedPrefix
    · have hc := signedTest_eq_on_first_coordinate N (policy4 d N) (common3 d N)
        (fun x => VariableEnvelope.mu < x)
        (common4_eq_common3_above_mu d hgeometry N hN) h T _ hl hm
        s.positive s.mass s.remaining
      have ho := signedTest_eq_on_first_coordinate N (original4 d N) (old3 d N)
        (fun x => VariableEnvelope.mu < x)
        (original4_eq_old3_above_mu d hgeometry N) h T _ hl hm
        s.positive s.mass s.remaining
      simp [hm, hc, ho, ih htail]
    · have ht := signedTest_eq_on_first_coordinate N (common3 d N) (old3 d N)
        (fun x => x ≤ VariableEnvelope.mu) (common3_eq_original_below_mu d N)
        h T _ hl (le_of_not_gt hm) s.positive s.mass s.remaining
      simp [hm, ht, ih htail]

/-- Every signed original fourth saving is unchanged on the common parent,
including AP counts and the actual sign-dependent small-beta terminal test. -/
theorem fourth_signed_gain_preserved
    (d : OriginalData) (hgeometry : FourthGeometry d) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (common3 d N) h T [] true 1 carrier -
        signedTest (policy4 d N) h T [] true 1 carrier =
      signedTest (old3 d N) h T [] true 1 carrier -
        signedTest (original4 d N) h T [] true 1 carrier := by
  have hc := common4_sub_original_eq_correction d N h T carrier
  rw [correction_eq_common_third_change d hgeometry N hN h T carrier] at hc
  linarith only [hc]

/-- The previously unpaid raw correction is independent of fourth/fifth
rows: only actual historical-third and fallback decisions occur on the RHS. -/
theorem rawCorrection_eq_common_third_change
    (d : OriginalData) (hgeometry : FourthGeometry d) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (w z : ℝ) :
    rawCorrection d N cap w z =
      raw (common3 d (N : ℝ)) N cap w z - raw (old3 d (N : ℝ)) N cap w z := by
  have hc := correction_eq_common_third_change d hgeometry (N : ℝ) hN
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun _ _ => 1)
    (roughPrimeUniverse N cap w z)
  rw [signedTest_one_eq_polynomial, signedTest_one_eq_polynomial,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (common3_even d (N : ℝ)) N cap w z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (HistoricalThirdCoarse.policy_even (d.e : ℝ) d.chi d.m d.omega (N : ℝ)) N cap w z] at hc
  exact hc

/-- The exact literal original fourth charge can be subtracted from THIS
common third raw source.  No fifth, sixth, or eighth gain is counted here. -/
theorem common_fourth_raw_ledger
    (d : OriginalData) (hgeometry : FourthGeometry d) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (z : ℝ) :
    raw (policy4 d (N : ℝ)) N cap 0 z =
      raw (common3 d (N : ℝ)) N cap 0 z - originalFourthSaving d N cap z := by
  rw [common4_raw_original_ledger d N cap hN z,
    rawCorrection_eq_common_third_change d hgeometry N cap hN 0 z]
  ring

/-- A complete-modulus physical source identity: the SAME attached signed
beta test occurs in both third sources, with no signed projection argument. -/
theorem physicalCorrection_eq_common_third_change
    (d : OriginalData) (hgeometry : FourthGeometry d) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    physicalCorrection d N cap w z L G = source d .third N cap w z L G -
      (∑ q ∈ actualSmallRoughModuli ((old3 d (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((old3 d (N : ℝ)) false) N cap w z L q * G q) := by
  have hc := correction_eq_common_third_change d hgeometry (N : ℝ) hN
    (fun _ => 1) (attachedLeafTest N cap 1 w L G) (roughPrimeUniverse N cap w z)
  have hs := source_eq_actual_root d .third N cap w z L G
  change source d .third N cap w z L G =
    signedTest (common3 d (N : ℝ)) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      [] true 1 (roughPrimeUniverse N cap w z) at hs
  have ho := physical_test_eq_signedTest (old3 d (N : ℝ))
    (HistoricalThirdCoarse.policy_even (d.e : ℝ) d.chi d.m d.omega (N : ℝ))
    N cap 1 w z L G
  simp only [one_mul] at ho
  rw [← hs, ← ho] at hc
  exact hc

/-- The fourth action in E's exact final-rho telescope is its ORIGINAL
physical signed saving, even though the common third parent is different. -/
theorem common_fourth_physical_change_original
    (d : OriginalData) (hgeometry : FourthGeometry d) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    sourceChange d .fourth N cap w z L G =
      (∑ q ∈ actualSmallRoughModuli ((original4 d (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((original4 d (N : ℝ)) false) N cap w z L q * G q) -
      (∑ q ∈ actualSmallRoughModuli ((old3 d (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((old3 d (N : ℝ)) false) N cap w z L q * G q) := by
  have hc := common4_physical_source_sub_original d N cap w z L G
  rw [physicalCorrection_eq_common_third_change d hgeometry N cap hN w z L G] at hc
  have hs := source_next_sub_current d .fourth N cap w z L G
  simp only [nextStage, parentStage] at hs
  linarith only [hc, hs]

/-- The literal final common rho now has the actual common-third source,
one original fourth charge and the unchanged later current-parent changes. -/
theorem final_rho_source_with_original_fourth_gain
    (d : OriginalData) (hgeometry : FourthGeometry d) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ moduli d N cap w z, rho d N cap w z L q * G q) =
      source d .third N cap w z L G +
      ((∑ q ∈ actualSmallRoughModuli ((original4 d (N : ℝ)) false) N cap w z,
          actualSmallRoughRho ((original4 d (N : ℝ)) false) N cap w z L q * G q) -
       (∑ q ∈ actualSmallRoughModuli ((old3 d (N : ℝ)) false) N cap w z,
          actualSmallRoughRho ((old3 d (N : ℝ)) false) N cap w z L q * G q)) +
      sourceChange d .fifth N cap w z L G + sourceChange d .sixth N cap w z L G +
        sourceChange d .eighth N cap w z L G := by
  rw [actual_source_telescope,
    common_fourth_physical_change_original d hgeometry N cap hN w z L G]

/-- One epsilon and one threshold give the unchanged final common rho a
baseline of common3 minus the two actual original integrals.  In particular
no fourth/fallback correction cost remains.  Common3 and laterRawLedger
still require their genuine original analytic/numerical suppliers. -/
theorem exists_common_third_original_fourth_fifth_ledger
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96)
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) ≤ omega / 2)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ))
    (nu eta epsilonMax : ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 ≤ (19 / 96 : ℝ) / nu ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let d := sourceData rows4 licensed4 e q chi omega
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (19 / 96 : ℝ)
        let L := (N : ℝ) ^ (nu * epsilon)
        let baseline := normalize N (raw (common3 d (N : ℝ)) N (cap N) 0 z) -
          originalFourthIntegral d - archiveFifthIntegral rows4 licensed4 e q chi omega
        1 < w ∧
          normalize N (physical (policy5 d (N : ℝ)) N (cap N) w z L) ≤ baseline + eta ∧
          normalize N (physicalDensitySum (moduli d N (cap N) w z)
            (rho d N (cap N) w z L)) ≤ baseline + laterRawLedger d N (cap N) z + eta := by
  obtain ⟨epsilon, heps, heps8, hepsMax, hepsr, N₀, hN₀, hbound⟩ :=
    exists_original_fourth_fifth_positive_ledger rows4 licensed4 e he q chi omega
      homega homegaRho hmesh cap hcap nu eta epsilonMax hnu heta hepsilonMax
  refine ⟨epsilon, heps, heps8, hepsMax, hepsr, N₀, hN₀, ?_⟩
  intro N hN hEven
  have hB := hbound N hN hEven
  let d := sourceData rows4 licensed4 e q chi omega
  have hg : FourthGeometry d := hgeometry
  have hN1 : 1 ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  dsimp only at hB ⊢
  have hc := congrArg (normalize N)
    (rawCorrection_eq_common_third_change d hg N (cap N) hN1 0
      ((N : ℝ) ^ (19 / 96 : ℝ)))
  rw [normalize_sub] at hc
  refine ⟨hB.1, ?_, ?_⟩
  · linarith only [hB.2.1, hc]
  · linarith only [hB.2.2, hc]

end
end ImbalancedChen.P5OriginalCommonFourthFallbackExcision
