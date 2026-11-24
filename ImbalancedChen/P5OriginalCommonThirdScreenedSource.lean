import ImbalancedChen.P5OriginalCommonFourthFallbackExcision

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Resolve the genuine historical/fallback maximum on its actual finite source.
An unsupported third ancestor inherits Theta-2e, which absorbs both fallback
caps.  A supported above-mu ancestor uses exactly the original qVLo baseline,
which lies strictly below the relevant new cap.  The resulting policy retains
the actual rough activation and simultaneous half-open coarse-cell ownership.
No endpoint integral, density sign, or smallness of omitted source is assumed.
-/
namespace ImbalancedChen.P5OriginalCommonThirdScreenedSource
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonFourthSourceNavigation P5OriginalCommonFourthSourceLedger
open P5OriginalCommonFourthFallbackExcision P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P1Pair12RetainedSignedSource
open P4AOriginalVariableFifthPhysicalLedger

/-- Exactly the old finite source support, not a geometric replacement. -/
def selectedThird (d : OriginalData) (N : ℝ) (pre : List ℕ) : Prop :=
  P1ThirdFallbackSupport.frozenSupported (d.e : ℝ) d.chi d.m d.omega N pre

def secondExponent (N : ℝ) (pre : List ℕ) : ℝ :=
  v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)

def thirdExponent (N : ℝ) (pre : List ℕ) : ℝ :=
  v (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1 +
    primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2)

/-- Explicit source dispatch. Rank two is untouched; the second action may
replace rank three itself, whereas the third action starts strictly later. -/
def screened3 (d : OriginalData) (N : ℝ) (positive : Bool) (pre : List ℕ) : Bool :=
  if pre.length ≤ 2 then old3 d N positive pre
  else if pre.length ≤ 3 then
    if selectedThird d N pre ∧ secondGuard N pre then
      ordinaryParityRosserPolicy false (N ^ secondExponent N pre) positive pre
    else old3 d N positive pre
  else if selectedThird d N pre ∧ thirdGuard N pre then
    ordinaryParityRosserPolicy false (N ^ thirdExponent N pre) positive pre
  else if selectedThird d N pre ∧ secondGuard N pre then
    ordinaryParityRosserPolicy false (N ^ secondExponent N pre) positive pre
  else old3 d N positive pre

theorem originalSeed_unsupported (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hs : ¬selectedThird d N pre) :
    originalSeed d N pre = initial (d.e : ℝ) := by
  change (if selectedThird d N pre then
    exponent (d.e : ℝ) d.chi d.m
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre))
    else initial (d.e : ℝ)) = _
  exact if_neg hs

/-- The manuscript's usual e<3/25600 already leaves the original positive
Theta-Lambda gap. This is arithmetic, not a cap or density premise. -/
theorem standard_buffer_below_initial_ceiling (e : ℝ)
    (he : e < (3 / 256 : ℝ) / 100) : e ≤ 11 / 64000 := by
  linarith

theorem fallback_cap_le_initial (d : OriginalData)
    (he : (d.e : ℝ) ≤ 11 / 64000) (t : ℝ) :
    v t ≤ initial (d.e : ℝ) := by
  have hv := v_le_cap t
  dsimp only [initial, extendedDistributionCap, cap] at *
  linarith

/-- Above mu, a supported cell cannot invoke the below-mu full Gamma.
The actual baseline is within 3chi/2+2e of v at its first coordinate. -/
theorem originalSeed_supported_interval (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hs : selectedThird d N pre) (hmu : mu < firstCoordinate N pre) :
    v (firstCoordinate N pre) - ((3 / 2 : ℝ) * d.chi + 2 * (d.e : ℝ)) ≤
        originalSeed d N pre ∧
      originalSeed d N pre ≤ v (firstCoordinate N pre) - 2 * (d.e : ℝ) := by
  obtain ⟨_ha, j, hj, ht⟩ := hs
  have hb := inBox_of_cell ht
  have hc := (mem_cells (d.e : ℝ) d.chi d.m j).mp hj
  have hx := ancestor_first_coordinate N 3 (by omega) pre hlen
  have hfull : ¬((box d.m j).ux : ℝ) ≤ mu - 4 * (d.e : ℝ) := by
    rw [hx] at hb
    linarith [hb.2.1]
  have hseed : originalSeed d N pre =
      (qVLo (box d.m j).lx (box d.m j).ux : ℝ) - 2 * (d.e : ℝ) := by
    change (if selectedThird d N pre then
      exponent (d.e : ℝ) d.chi d.m
        (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre))
      else initial (d.e : ℝ)) = _
    rw [if_pos hs, exponent_on_cell (d.e : ℝ) d.chi d.m _ j hj ht]
    simp only [levelExponent, gamma, if_neg hfull]
  have herr := rationalInterval_v_error hb.1 hb.2.1
  have hupper := qVLo_le_v hb.1 hb.2.1
  have hwidth : ((box d.m j).ux : ℝ) - (box d.m j).lx ≤ d.chi := by
    have hw : ((box d.m j).ux : ℝ) - (box d.m j).lx ≤ (box d.m j).width := by
      exact_mod_cast (box d.m j).coordinate_widths_le.1
    exact hw.trans hc.2.2.2.2.2
  rw [hx] at herr hupper
  rw [hseed]
  constructor <;> linarith

theorem originalSeed_lt_second (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hs : selectedThird d N pre) (hg : secondGuard N pre) :
    originalSeed d N pre < secondExponent N pre := by
  have hx := ancestor_first_coordinate N 2 (by omega) pre (by omega)
  have hmu : mu < firstCoordinate N pre := by simpa only [← hx] using hg.1
  have hseed := (originalSeed_supported_interval d he N pre hlen hs hmu).2
  have hnew := new_cap_gt_old hg.1 hg.2.2.1 hg.2.2.2
  change v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 0) <
    secondExponent N pre at hnew
  rw [hx] at hnew
  linarith

theorem originalSeed_lt_third (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hs : selectedThird d N pre) (hg : thirdGuard N pre) :
    originalSeed d N pre < thirdExponent N pre := by
  have hx := ancestor_first_coordinate N 3 (by omega) pre hlen
  have hmu : mu < firstCoordinate N pre := by simpa only [← hx] using hg.1
  have hseed := (originalSeed_supported_interval d he N pre hlen hs hmu).2
  have hnew := (third_initial_physical_gates hg).2.2.2.2.2
  change v (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0) <
    thirdExponent N pre at hnew
  rw [hx] at hnew
  linarith

/-- Both guards are false or exactly one can hold on a real three-ancestor.
This uses original coordinate restriction and the original 3/16 separation. -/
theorem second_third_disjoint (N : ℝ) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (h2 : secondGuard N pre) (h3 : thirdGuard N pre) : False := by
  have hl : (rosserAncestor 3 pre).length = 3 := by
    rw [rosserAncestor_length, min_eq_left hlen]
  have hc0 := primeHistoryLogCoordinates_ancestor N hl (by omega : 2 ≤ 3) (0 : Fin 2)
  have hc1 := primeHistoryLogCoordinates_ancestor N hl (by omega : 2 ≤ 3) (1 : Fin 2)
  simp only [rosserAncestor_nested 2 3 (by omega)] at hc0 hc1
  apply above_mu_regions_disjoint (x := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
    (y := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
    (z := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) _ h3
  simpa only [secondGuard, hc0, hc1] using h2

private theorem upper_union_right (Q R : ℝ) (hQR : Q ≤ R)
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

private theorem old_union_selected (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (N : ℝ) (hN : 1 ≤ N) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (positive : Bool) (a : ℝ) (hcap : originalSeed d N pre ≤ a) :
    (old3 d N positive pre || ordinaryParityRosserPolicy false (N ^ a) positive pre) =
      ordinaryParityRosserPolicy false (N ^ a) positive pre := by
  rw [old3_after_two d N positive pre (by omega)]
  exact upper_union_right _ _ (Real.rpow_le_rpow_of_exponent_le hN hcap) positive pre

private theorem old_union_unsupported (d : OriginalData)
    (he : (d.e : ℝ) ≤ 11 / 64000) (N : ℝ) (hN : 1 ≤ N)
    (pre : List ℕ) (hlen : 3 ≤ pre.length) (hs : ¬selectedThird d N pre)
    (positive : Bool) (t : ℝ) :
    (old3 d N positive pre || ordinaryParityRosserPolicy false (N ^ v t) positive pre) =
      old3 d N positive pre := by
  rw [old3_after_two d N positive pre (by omega), originalSeed_unsupported d N pre hs,
    Bool.or_comm]
  exact upper_union_right _ _
    (Real.rpow_le_rpow_of_exponent_le hN (fallback_cap_le_initial d he t)) positive pre

/-- Exact equality on ALL prime words: the old/common max has been resolved,
including inactive and active-but-unselected ancestors and rank-three itself. -/
theorem common3_eq_screened3 (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (hemax : (d.e : ℝ) ≤ 11 / 64000) (N : ℝ) (hN : 1 ≤ N) :
    common3 d N = screened3 d N := by
  funext positive pre
  by_cases h2 : pre.length ≤ 2
  · simpa only [screened3, if_pos h2] using common3_through_two d N positive pre h2
  have hl : 3 ≤ pre.length := by omega
  by_cases h3 : pre.length ≤ 3
  · by_cases hg : secondGuard N pre
    · have hf : fallback23 d N positive pre =
          ordinaryParityRosserPolicy false (N ^ secondExponent N pre) positive pre := by
        simp [fallback23, finalPolicy, secondPolicy, firstExitDepthSplicePolicy,
          h2, h3, secondReplacement, hg, secondExponent]
      by_cases hs : selectedThird d N pre
      · simpa only [common3, hf, screened3, if_neg h2, if_pos h3,
          if_pos (And.intro hs hg)] using
          old_union_selected d he N hN pre hl positive _
            (originalSeed_lt_second d he N pre hl hs hg).le
      · simpa [common3, hf, screened3, h2, h3, hs, secondExponent] using
          old_union_unsupported d hemax N hN pre hl hs positive
            (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)
    · simp [common3, fallback23, finalPolicy, secondPolicy, firstExitDepthSplicePolicy,
        h2, h3, secondReplacement, hg, oldPolicy, old3, screened3]
  · by_cases ht : thirdGuard N pre
    · have hf : fallback23 d N positive pre =
          ordinaryParityRosserPolicy false (N ^ thirdExponent N pre) positive pre := by
        simp [fallback23, finalPolicy, firstExitDepthSplicePolicy, h3,
          thirdReplacement, ht, thirdQ, thirdExponent]
      by_cases hs : selectedThird d N pre
      · simpa only [common3, hf, screened3, if_neg h2, if_neg h3,
          if_pos (And.intro hs ht)] using
          old_union_selected d he N hN pre hl positive _
            (originalSeed_lt_third d he N pre hl hs ht).le
      · simpa [common3, hf, screened3, h2, h3, hs, thirdExponent] using
          old_union_unsupported d hemax N hN pre hl hs positive
            (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1 +
              primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2)
    · by_cases hg : secondGuard N pre
      · have hf : fallback23 d N positive pre =
            ordinaryParityRosserPolicy false (N ^ secondExponent N pre) positive pre := by
          simp [fallback23, finalPolicy, firstExitDepthSplicePolicy, h2, h3,
            thirdReplacement, ht, secondPolicy, secondReplacement, hg, secondExponent]
        by_cases hs : selectedThird d N pre
        · simpa [common3, hf, screened3, h2, h3, hs, ht, hg] using
            old_union_selected d he N hN pre hl positive _
              (originalSeed_lt_second d he N pre hl hs hg).le
        · simpa [common3, hf, screened3, h2, h3, hs, secondExponent] using
            old_union_unsupported d hemax N hN pre hl hs positive
              (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)
      · simp [common3, fallback23, finalPolicy, secondPolicy, firstExitDepthSplicePolicy,
          h2, h3, secondReplacement, hg, thirdReplacement, ht, oldPolicy, old3, screened3]

theorem selectedThird_append (d : OriginalData) (N : ℝ) (later pre : List ℕ)
    (hlen : 3 ≤ pre.length) :
    selectedThird d N (later ++ pre) ↔ selectedThird d N pre := by
  simp only [selectedThird, P1ThirdFallbackSupport.frozenSupported,
    rosserAncestor_append 3 later pre hlen]

/-- The WHOLE unsupported continuation has zero signed common-old change,
with arbitrary terminal test and original multiplicities and incoming sign. -/
theorem unsupported_signed_continuation (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (hemax : (d.e : ℝ) ≤ 11 / 64000) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (pre : List ℕ)
    (hlen : 3 ≤ pre.length) (hs : ¬selectedThird d N pre)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (common3 d N) h T pre positive mass remaining =
      signedTest (old3 d N) h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hlen' : 3 ≤ (p :: pre).length := by simp; omega
    have hs' : ¬selectedThird d N (p :: pre) := by
      simpa only [List.singleton_append] using
        (not_congr (selectedThird_append d N [p] pre hlen)).mpr hs
    have hp : common3 d N (!positive) (p :: pre) = old3 d N (!positive) (p :: pre) := by
      rw [common3_eq_screened3 d he hemax N hN]
      simp [screened3, hs']
    simp only [signedTest, hp]
    rw [ih (pre := pre) (hlen := hlen) (hs := hs) (positive := positive) (mass := mass),
      ih (pre := p :: pre) (hlen := hlen') (hs := hs')
        (positive := !positive) (mass := mass * h p)]

/-- J's genuine raw correction now has an explicit support-screened source.
There is no residual max, fourth action, or unproved source identity premise. -/
theorem rawCorrection_eq_screened_change (d : OriginalData)
    (hg : FourthGeometry d) (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z : ℝ) :
    rawCorrection d N cap w z =
      raw (screened3 d (N : ℝ)) N cap w z - raw (old3 d (N : ℝ)) N cap w z := by
  rw [rawCorrection_eq_common_third_change d hg N cap hN w z,
    common3_eq_screened3 d he hemax (N : ℝ) hN]

/-- Same signed beta attachment and complete modulus as J's physical source. -/
theorem physicalCorrection_eq_screened_change (d : OriginalData)
    (hg : FourthGeometry d) (he : 0 ≤ (d.e : ℝ)) (hemax : (d.e : ℝ) ≤ 11 / 64000)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    physicalCorrection d N cap w z L G =
      signedTest (screened3 d (N : ℝ)) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        [] true 1 (roughPrimeUniverse N cap w z) -
      signedTest (old3 d (N : ℝ)) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        [] true 1 (roughPrimeUniverse N cap w z) := by
  change correctionTest d (N : ℝ) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
    (roughPrimeUniverse N cap w z) = _
  rw [correction_eq_common_third_change d hg (N : ℝ) hN,
    common3_eq_screened3 d he hemax (N : ℝ) hN]

end
end ImbalancedChen.P5OriginalCommonThirdScreenedSource
