import ImbalancedChen.P5ProperPowerPhysicalPolynomialPayment
import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P4ACompactCoefficientSupportExponent

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A concrete range certificate for the ACTUAL variable-fourth/fifth producer
policy, with its original coarse third parent, all simultaneous eligible
rows, inherited floors and firstStop.  The proof bounds the actual row
formulas, then the actual retained rough support, then the nonzero signed
small/rough attachment.  No active-range conclusion is assumed.

This is the original through-fifth policy, NOT the whole full22 strategy.
The literal sixth family and eighth updates must still be attached with
separately proved local level ceilings.  Whole full22/PP remains OPEN.
-/

namespace ImbalancedChen.P5Z.OriginalFifthPhysicalRange

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open ImbalancedChen.HistoricalThirdCoarse
open ImbalancedChen.P1ThirdFallbackSupport
open ImbalancedChen.P1CoarseFirstCubeFallbackMargin
open ImbalancedChen.P1OriginalVariableFourthContinuation
open ImbalancedChen.P1OriginalVariableFifthContinuation
open ImbalancedChen.P2OriginalFourthCapProducerInterface
open ImbalancedChen.P4BActualSmoothHyperbolaCorrection

/-- The actual selected Gamma is below its original initial exponent;
the fallback is exactly that initial exponent, rather than Lambda. -/
theorem coarseExponent_le_initial (e chi : ℝ) (he : 0 ≤ e) (m : ℕ)
    (t : Fin 3 → ℝ) : HistoricalThirdCoarse.exponent e chi m t ≤ initial e := by
  by_cases hs : ∃ j ∈ HistoricalThirdCoarse.cells e chi m,
      t ∈ logPrimeMeshCell 0 (19/96) m j
  · obtain ⟨j, hj, ht⟩ := hs
    rw [HistoricalThirdCoarse.exponent_on_cell e chi m t j hj ht]
    have hc := (HistoricalThirdCoarse.mem_cells e chi m j).mp hj
    exact (levelExponent_lt_initial e (box m j) he hc.1 hc.2.1).le
  · have hout : ∀ j ∈ HistoricalThirdCoarse.cells e chi m,
        t ∉ logPrimeMeshCell 0 (19/96) m j := by
      intro j hj ht
      exact hs ⟨j, hj, ht⟩
    rw [HistoricalThirdCoarse.exponent_outside e chi m t hout]

theorem effectiveExponent_le_initial (e chi : ℝ) (he : 0 ≤ e) (m : ℕ)
    (omega N : ℝ) (pre : List ℕ) :
    effectiveExponent e chi m omega N pre ≤ initial e := by
  unfold effectiveExponent
  split_ifs
  · exact coarseExponent_le_initial e chi he m _
  · exact le_rfl

theorem rawLevel_le_initial (e chi : ℝ) (he : 0 ≤ e) (m : ℕ)
    (omega N : ℝ) (hN : 1 ≤ N) (pre : List ℕ) :
    rawLevel e chi m omega N pre ≤ N^initial e := by
  rw [rawLevel_eq_rpow_effectiveExponent]
  exact Real.rpow_le_rpow_of_exponent_le hN (effectiveExponent_le_initial e chi he m omega N pre)

/-- Every actual fourth producer row uses v(sum I)-2e. The global
manuscript tent bound therefore controls the maximum without needing a
false improvement or whole-box geometry assumption for losing rows. -/
theorem producerFourthExponent_le_initial (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega N : ℝ) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (pre : List ℕ) :
    exponent4 e chi m omega N rows4 (producerEligible licensed4)
      (fun r => r.bufferedCandidate e) pre ≤ initial e := by
  have hseed : seedExponent e chi m omega N pre ≤ initial e :=
    effectiveExponent_le_initial e chi he m omega N _
  unfold exponent4
  split_ifs
  · unfold profile4
    apply finiteMax_le _ _ _ _ _ hseed
    intro r hr heligible
    rw [r.bufferedCandidate_eq]
    have hv := VariableEnvelope.v_le_cap
      (∑ i ∈ r.selected, primeHistoryLogCoordinates N 4 pre i)
    dsimp [initial, extendedDistributionCap, VariableEnvelope.cap] at *
    linarith
  · exact hseed

section Fifth
variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

theorem actualFifthExponent_le_initial (he : 0 ≤ e) (pre : List ℕ) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre ≤ initial (e : ℝ) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hseed : inherited4 e chi m omega N rows4 licensed4 pre ≤ initial (e : ℝ) := by
    exact producerFourthExponent_le_initial (e : ℝ) chi heR m omega N rows4 licensed4 _
  unfold exponent5
  split_ifs
  · apply finiteMax_le _ _ _ _ _ hseed
    intro row hrow heligible
    unfold candidate
    rw [envelope_eq_v]
    have hv := VariableEnvelope.v_le_cap
      (∑ i ∈ row.selected, primeHistoryLogCoordinates N 5 pre i)
    dsimp [initial, extendedDistributionCap, VariableEnvelope.cap] at *
    linarith
  · exact hseed

theorem actualFifthLevel_le_initial (he : 0 ≤ e) (hN : 1 ≤ N) (pre : List ℕ) :
    level5 e chi m omega N rows4 licensed4 J5 rows5 pre ≤ N^initial (e : ℝ) := by
  unfold level5
  exact Real.rpow_le_rpow_of_exponent_le hN
    (actualFifthExponent_le_initial e chi m omega N rows4 licensed4 J5 rows5 he pre)

theorem actualFifthPolicy_even (pre : List ℕ) :
    policy5 e chi m omega N rows4 licensed4 J5 rows5 true pre = true := by
  simp [policy5, fifthCappedUpperPolicy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, HistoricalThirdCoarse.initialPolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy]

/-- Concrete pointwise domination of every actual fifth-policy approval
by the original root-level parity Rosser policy. This precedes arithmetic
or reached-frontier selection and is not a supplied support estimate. -/
theorem actualFifthPolicy_implies_root (he : 0 ≤ e) (hN : 1 ≤ N)
    (positive : Bool) (pre : List ℕ)
    (hp : policy5 e chi m omega N rows4 licensed4 J5 rows5 positive pre = true) :
    ordinaryParityRosserPolicy false (N^initial (e : ℝ)) positive pre = true := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  cases positive with
  | true => exact ordinaryParityRosserPolicy_upper_even _ _
  | false =>
    have hadm : ordinaryRosserPrefixAdmissible false (N^initial (e : ℝ)) pre := by
      by_cases h4 : pre.length ≤ 4
      · rw [policy5_through_four e chi m omega N rows4 licensed4 J5 rows5 false pre h4] at hp
        by_cases h2 : pre.length ≤ 2
        · rw [HistoricalThirdCoarse.policy_through_two (e : ℝ) chi m omega N false pre h2] at hp
          have hi : ordinaryRosserPrefixAdmissible false (N^initial (e : ℝ)) pre ∧
              (pre.length = 1 → firstStop (e : ℝ) m N pre) := by
            simpa [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy] using hp
          exact hi.1
        · have hi : ordinaryRosserPrefixAdmissible false
              (rawLevel (e : ℝ) chi m omega N (rosserAncestor 3 pre)) pre := by
            simpa [HistoricalThirdCoarse.policy, thirdCappedUpperPolicy,
              firstExitDepthSplicePolicy, h2, frozenParityRosserPolicy,
              ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
          exact ordinaryRosserPrefixAdmissible_mono false pre
            (rawLevel_le_initial (e : ℝ) chi heR m omega N hN _) hi
      · have hi : ordinaryRosserPrefixAdmissible false
            (level5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 5 pre)) pre := by
          simpa [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy,
            h4, frozenParityRosserPolicy, ancestorFrozenPolicy,
            ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
        exact ordinaryRosserPrefixAdmissible_mono false pre
          (actualFifthLevel_le_initial e chi m omega N rows4 licensed4 J5 rows5 he hN _) hi
    simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hadm
end Fifth

-- These finite dictionary facts are private in the earlier compact-third
-- module. They are restated here for the NEW actual fourth/fifth policy;
-- no analytic estimate or original-policy conclusion is added as a premise.
theorem validSelection_mono (p q : Bool → List ℕ → Bool)
    (hdom : ∀ positive pre, p positive pre = true → q positive pre = true)
    (pre chosen : List ℕ) (positive : Bool)
    (hv : FirstExitValidSelection p pre positive chosen) :
    FirstExitValidSelection q pre positive chosen := by
  induction chosen generalizing pre positive with
  | nil => trivial
  | cons n ns ih => exact ⟨hdom _ _ hv.1, ih _ _ hv.2⟩

/-- The fixed rough carrier of the ACTUAL policy5 is below its original
initial level, regardless of enumeration cap or selected row overlap. -/
theorem actualFifthRoughSupport_lt_initial
    (e : ℚ) (he : 0 ≤ e) (heSmall : (e : ℝ) ≤ 1/384)
    (chi : ℝ) (m N enumerationCap : ℕ) (omega w z : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (hN : 2 ≤ N)
    {d : ℕ} (hd : d ∈ fixedRoughSupport
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
      N enumerationCap w z) : (d : ℝ) < (N : ℝ)^initial (e : ℝ) := by
  let P := policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5
  let R := (N : ℝ)^initial (e : ℝ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hinit : 0 < initial (e : ℝ) := by
    dsimp [initial, extendedDistributionCap]
    linarith
  have hR : 1 < R := Real.one_lt_rpow hNr hinit
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    P (actualFifthPolicy_even e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    N enumerationCap w z] at hd
  obtain ⟨chosen, hsub, hvalid, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection P _ d).mp hd
  have hv := validSelection_mono P (ordinaryParityRosserPolicy false R)
    (actualFifthPolicy_implies_root e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 he hNr.le)
    [] chosen true hvalid
  have hroot : d ∈ firstExitRetainedModuli (ordinaryParityRosserPolicy false R)
      (roughPrimeUniverse N enumerationCap w z) :=
    (mem_firstExitRetainedModuli_iff_validSelection _ _ d).mpr ⟨chosen, hsub, hv, hprod⟩
  rw [ordinaryParityRosserRetainedModuli_eq false R hR _
    (roughPrimeUniverse_pairwise_gt N enumerationCap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (by simp)] at hroot
  exact ((mem_ordinaryRosserRetainedModuli_iff false R hR _
    (roughPrimeUniverse_pairwise_gt N enumerationCap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) d).mp hroot).2.1

/-- Literal nonzero signed attachment factors into a SMALL Rosser factor
below N^epsilon and the actual policy5 retained rough factor above. The
real physical support is thereby proved, rather than postulated. -/
theorem actualFifthAttachedCoefficient_lt_theta
    (e : ℚ) (he : 0 ≤ e) (heSmall : (e : ℝ) ≤ 1/384)
    (chi : ℝ) (m N : ℕ) (omega r epsilon : ℝ) (cap : ℕ → ℕ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (hN : 2 ≤ N)
    (hepsilon : epsilon ≤ 2*(e : ℝ)) {q : ℕ}
    (hq : attachedUpperCoefficient 1 r epsilon
      (fun M => policy5 e chi m omega (M : ℝ) rows4 licensed4 J5 rows5 false) cap N q ≠ 0) :
    (q : ℝ) < (N : ℝ)^(299/500 : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNr
  obtain ⟨a, ha, b, hb, hprod, haL, hbne⟩ := actualSmallRoughRho_ne_zero_factors
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
    N (cap N) ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)
    (by simpa only [attachedUpperCoefficient, one_mul] using hq)
  have hbR := actualFifthRoughSupport_lt_initial e he heSmall chi m N (cap N) omega
    ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) rows4 licensed4 J5 rows5 hN hb
  have hqR : (q : ℝ) < (N : ℝ)^(initial (e : ℝ)+epsilon) := by
    calc
      (q : ℝ) = (a : ℝ)*(b : ℝ) := by rw [hprod, Nat.cast_mul]
      _ ≤ (N : ℝ)^epsilon*(b : ℝ) := mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg _)
      _ < (N : ℝ)^epsilon*(N : ℝ)^initial (e : ℝ) :=
        mul_lt_mul_of_pos_left hbR (Real.rpow_pos_of_pos hN0 _)
      _ = _ := by rw [Real.rpow_add hN0]; ring
  exact hqR.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le (by
    dsimp [initial, extendedDistributionCap]
    linarith))

/-- The exact active-cap supremum used by the three preceding transfer
batches now has a concrete polynomial certificate for this actual
through-fifth producer policy. No premise states the desired range. -/
theorem actualFifthActiveCap_le_theta
    (e : ℚ) (he : 0 ≤ e) (heSmall : (e : ℝ) ≤ 1/384)
    (chi : ℝ) (m N : ℕ) (omega r epsilon : ℝ) (cap : ℕ → ℕ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (hN : 2 ≤ N)
    (hepsilon : epsilon ≤ 2*(e : ℝ)) :
    (actualActiveUpperCap 1 r epsilon
      (fun M => policy5 e chi m omega (M : ℝ) rows4 licensed4 J5 rows5 false) cap N : ℝ) ≤
      (N : ℝ)^(299/500 : ℝ) := by
  have hpow : 0 ≤ (N : ℝ)^(299/500 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hsup : actualActiveUpperCap 1 r epsilon
      (fun M => policy5 e chi m omega (M : ℝ) rows4 licensed4 J5 rows5 false) cap N ≤
      Nat.floor ((N : ℝ)^(299/500 : ℝ)) := by
    unfold actualActiveUpperCap
    apply Finset.sup_le
    intro q hq
    exact (Nat.le_floor_iff hpow).mpr (actualFifthAttachedCoefficient_lt_theta
      e he heSmall chi m N omega r epsilon cap rows4 licensed4 J5 rows5 hN hepsilon
      (Finset.mem_filter.mp hq).2).le
  exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le hpow)

end
end ImbalancedChen.P5Z.OriginalFifthPhysicalRange
