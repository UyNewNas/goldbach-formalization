import ImbalancedChen.P5OriginalCommonThirdScreenedSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The real supported third-fallback cylinder has an exact old-minus-common
LOWER residual difference. Both inherited prefix licences are obtained from
the original old3 frontier and the proved stored-cap comparison. No caller
supplies either old/new prefix admission or a residual-density identity.
The whole final common rho continues to retain all later source ports.
-/
namespace ImbalancedChen.P5OriginalCommonThirdActualLowerSource
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonRefinedSource P5OriginalCommonFourthSourceNavigation
open P5OriginalCommonFourthSourceLedger P5OriginalCommonFourthFallbackExcision
open P5OriginalCommonThirdScreenedSource P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P1Pair12RetainedSignedSource P4AOriginalVariableFifthPhysicalLedger
open P5OriginalCommonPositivePresieve P5OriginalArchivePositivePresieveGain
open P1HistoricalFifthCommonPolicyInputs P5OriginalFifthArchiveActualMean
open P2OriginalFourthCapProducerInterface

theorem common_third_supported_continuation (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N : ℝ) (hN : 1 ≤ N) (base : List ℕ) (hlen : 3 ≤ base.length)
    (hs : selectedThird d N base) (hg : thirdGuard N base)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (common3 d N) h T base positive mass remaining =
      signedTest (frozenParityRosserPolicy false 3 (thirdQ N))
        h T base positive mass remaining := by
  have hrec (later : List ℕ) (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
      signedTest (common3 d N) h T (later ++ base) positive mass remaining =
        signedTest (frozenParityRosserPolicy false 3 (thirdQ N))
          h T (later ++ base) positive mass remaining := by
    induction remaining generalizing later positive mass with
    | nil => rfl
    | cons p ps ih =>
      have hl : 3 < ((p :: later) ++ base).length := by
        simp only [List.length_append, List.length_cons]
        omega
      have hsel : selectedThird d N ((p :: later) ++ base) :=
        (selectedThird_append d N (p :: later) base hlen).mpr hs
      have hguard : thirdGuard N ((p :: later) ++ base) :=
        (thirdGuard_later_history N (p :: later) base hlen).mpr hg
      have hpolicy : common3 d N (!positive) (p :: (later ++ base)) =
          frozenParityRosserPolicy false 3 (thirdQ N) (!positive) (p :: (later ++ base)) := by
        rw [common3_eq_screened3 d he hemax N hN]
        have hn2 : ¬((p :: later) ++ base).length ≤ 2 := by omega
        have hn3 : ¬((p :: later) ++ base).length ≤ 3 := by omega
        simpa only [List.cons_append] using
          (show screened3 d N (!positive) ((p :: later) ++ base) =
              frozenParityRosserPolicy false 3 (thirdQ N) (!positive) ((p :: later) ++ base) by
            simp only [screened3, if_neg hn2, if_neg hn3, if_pos ⟨hsel, hguard⟩,
              frozenParityRosserPolicy, ancestorFrozenPolicy, thirdExponent, thirdQ])
      simp only [signedTest, hpolicy]
      rw [ih later positive mass, ih (p :: later) (!positive) (mass * h p)]
  simpa only [List.nil_append] using hrec [] positive mass remaining

/-- The old third source is its own genuine frozen coarse continuation. -/
theorem old_third_continuation (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : 3 ≤ pre.length) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (old3 d N) h T pre positive mass remaining =
      signedTest (frozenParityRosserPolicy false 3
        (rawLevel (d.e : ℝ) d.chi d.m d.omega N)) h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hl : ¬(p :: pre).length ≤ 2 := by simp; omega
    have hp : old3 d N (!positive) (p :: pre) =
        frozenParityRosserPolicy false 3 (rawLevel (d.e : ℝ) d.chi d.m d.omega N)
          (!positive) (p :: pre) := by
      simp only [old3, HistoricalThirdCoarse.policy, thirdCappedUpperPolicy,
        firstExitDepthSplicePolicy, if_neg hl]
    simp only [signedTest, hp]
    rw [ih (pre := pre) (hlen := hlen) (positive := positive) (mass := mass),
      ih (pre := p :: pre) (hlen := by simp; omega)
        (positive := !positive) (mass := mass * h p)]

/-- Actual supported old third states pay BOTH old/new prefix licences;
the original prime carrier, incoming sign, mass and multiplicity are retained. -/
theorem actual_third_fallback_lower_difference (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) (s : FirstExitDepthState ℕ)
    (hstate : s ∈ firstExitDepthFrontier 3 (old3 d (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hs : selectedThird d (N : ℝ) s.selectedPrefix)
    (hg : thirdGuard (N : ℝ) s.selectedPrefix) :
    firstExitRetainedPolynomial (old3 d (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) s.selectedPrefix s.positive s.mass s.remaining -
      firstExitRetainedPolynomial (common3 d (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) s.selectedPrefix s.positive s.mass s.remaining =
      s.mass * (actualSmallRosserMinusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
        (thirdQ (N : ℝ) s.selectedPrefix / (s.selectedPrefix.prod : ℝ)) -
        actualSmallRosserMinusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
          (rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) s.selectedPrefix /
            (s.selectedPrefix.prod : ℝ))) := by
  obtain ⟨hlen, hsort, hprod, hcut, hrem, hsign, hmass⟩ :=
    actualPrimeFrontier_geometry 3 (by omega) (old3 d (N : ℝ)) N cap z s hstate
  have hself := rosserAncestor_self_of_length 3 s.selectedPrefix hlen
  have hold : ordinaryRosserPrefixAdmissible false
      (rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) s.selectedPrefix) s.selectedPrefix := by
    have ha := actualThirdCapped_frontier_admissible
      (initialPolicy (d.e : ℝ) d.m (N : ℝ))
      (rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ)) 3 (by omega)
      N cap z (fun p : ℕ => 1 / ((p : ℝ) - 1)) s hstate
    simpa only [hself] using ha
  have hlevel : rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) s.selectedPrefix ≤
      thirdQ (N : ℝ) s.selectedPrefix := by
    have hf := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
      (d.e : ℝ) d.chi d.m d.omega (N : ℝ) s.selectedPrefix
    change rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 s.selectedPrefix) = (N : ℝ) ^ originalSeed d (N : ℝ) s.selectedPrefix at hf
    rw [hself] at hf
    rw [hf]
    have hexp := (originalSeed_lt_third d he (N : ℝ) s.selectedPrefix (by omega) hs hg).le
    simpa only [thirdExponent, thirdQ, hself] using
      Real.rpow_le_rpow_of_exponent_le hN hexp
  have hnew := ordinaryRosserPrefixAdmissible_mono false s.selectedPrefix hlevel hold
  have ho := firstExitRetainedPolynomial_frozenParity_frontier_density false 3 (by omega)
    (old3 d (N : ℝ)) (rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ))
    N cap z s hstate hold
  have hn := firstExitRetainedPolynomial_frozenParity_frontier_density false 3 (by omega)
    (old3 d (N : ℝ)) (thirdQ (N : ℝ)) N cap z s hstate hnew
  have hc := common_third_supported_continuation d he hemax (N : ℝ) hN
    s.selectedPrefix (by omega) hs hg (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (fun _ _ => 1) s.positive s.mass s.remaining
  have hb := old_third_continuation d (N : ℝ) s.selectedPrefix (by omega)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun _ _ => 1) s.positive s.mass s.remaining
  simp only [signedTest_one_eq_polynomial] at hc hb
  rw [hc, hb, ho, hn]
  have hterm (Q : List ℕ → ℝ) :
      actualFrozenFrontierDensityTerm false N cap Q s.selectedPrefix =
        -s.mass * actualSmallRosserMinusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
          (Q s.selectedPrefix / (s.selectedPrefix.prod : ℝ)) := by
    simp only [actualFrozenFrontierDensityTerm, ← hmass,
      signedTreeCoefficient_evenListLength_eq_negOnePow, ordinaryRosserResidualLower, hlen]
    norm_num
  rw [hterm, hterm]
  ring

theorem common_fourth_raw_screened_ledger (d : OriginalData) (hg : FourthGeometry d)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) :
    raw (policy4 d (N : ℝ)) N cap 0 z =
      raw (screened3 d (N : ℝ)) N cap 0 z - originalFourthSaving d N cap z := by
  rw [common_fourth_raw_ledger d hg N cap hN z,
    common3_eq_screened3 d he hemax (N : ℝ) hN]

/-- The original rho is unchanged. Fifth, sixth and eighth remain their
literal current-parent source differences; no sign or endpoint is assigned. -/
theorem final_rho_screened_source (d : OriginalData) (hg : FourthGeometry d)
    (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ moduli d N cap w z, P5OriginalCommonRefinedConstructor.rho d N cap w z L q * G q) =
      signedTest (screened3 d (N : ℝ)) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        [] true 1 (roughPrimeUniverse N cap w z) +
      ((∑ q ∈ actualSmallRoughModuli ((original4 d (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((original4 d (N : ℝ)) false) N cap w z L q * G q) -
       (∑ q ∈ actualSmallRoughModuli ((old3 d (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((old3 d (N : ℝ)) false) N cap w z L q * G q)) +
      sourceChange d .fifth N cap w z L G + sourceChange d .sixth N cap w z L G +
        sourceChange d .eighth N cap w z L G := by
  rw [final_rho_source_with_original_fourth_gain d hg N cap hN w z L G,
    source_eq_actual_root]
  change signedTest (common3 d (N : ℝ)) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] true 1 (roughPrimeUniverse N cap w z) + _ + _ + _ + _ = _
  rw [common3_eq_screened3 d he hemax (N : ℝ) hN]

/-- The existing original-integral consumer keeps its one epsilon/threshold,
its entire laterRawLedger and the unchanged final physical rho. Screening
supplies only the newly proved source identity; no fallback bound is added. -/
theorem exists_screened_original_fourth_fifth_ledger
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (e : ℚ) (he : 0 ≤ e) (hemax : (e : ℝ) ≤ 11 / 64000)
    (q : ℕ) (chi omega : ℝ)
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
        let baseline := normalize N (raw (screened3 d (N : ℝ)) N (cap N) 0 z) -
          originalFourthIntegral d - archiveFifthIntegral rows4 licensed4 e q chi omega
        1 < w ∧
          normalize N (physical (policy5 d (N : ℝ)) N (cap N) w z L) ≤ baseline + eta ∧
          normalize N (physicalDensitySum (moduli d N (cap N) w z)
            (P5OriginalCommonRefinedConstructor.rho d N (cap N) w z L)) ≤
              baseline + laterRawLedger d N (cap N) z + eta := by
  obtain ⟨epsilon, heps, heps8, hepsMax, hepsr, N₀, hN₀, hbound⟩ :=
    exists_common_third_original_fourth_fifth_ledger rows4 licensed4 hgeometry
      e he q chi omega homega homegaRho hmesh cap hcap nu eta epsilonMax
      hnu heta hepsilonMax
  refine ⟨epsilon, heps, heps8, hepsMax, hepsr, N₀, hN₀, ?_⟩
  intro N hN hEven
  have hB := hbound N hN hEven
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have heR : 0 ≤ (e : ℝ) := by exact_mod_cast he
  dsimp only at hB ⊢
  rw [common3_eq_screened3 (sourceData rows4 licensed4 e q chi omega)
    heR hemax (N : ℝ) hN1] at hB
  exact hB

end
end ImbalancedChen.P5OriginalCommonThirdActualLowerSource
