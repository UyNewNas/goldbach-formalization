import ImbalancedChen.P5OriginalFifthPhysicalRange
import ImbalancedChen.P5OriginalAdoptedEighthPhysicalMasks

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Late-stage range bridge for the REAL original row5 + sixth + adopted87
constructor.  The actual 87 selected licences bound every selected new
cap by Lambda<Theta. Only the inherited literal sixth exponent ceiling
remains a local source obligation. This does NOT instantiate all eleven
sixth families or equate this joined policy with the older above-mu base.
-/

namespace ImbalancedChen.P5Z.OriginalJoinedLateRange

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.OriginalFifthPhysicalRange
open ImbalancedChen.P1OriginalVariableFifthContinuation
open ImbalancedChen.P2OriginalFourthCapProducerInterface
open ImbalancedChen.P5OriginalAdoptedEighthPhysicalMasks
open ImbalancedChen.P4BActualSmoothHyperbolaCorrection

/-- Literal adoptedGuard/choose uses its actual selected licence; no
all87 coverage or missing geometry is silently inferred from it. -/
theorem actualRaisedExponent_le_theta (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (h6 : ∀ pre, lambda6 pre ≤ (299/500 : ℝ)) (pre : List ℕ) :
    raisedExponent N lambda3 lambda6 pre ≤ (299/500 : ℝ) := by
  unfold raisedExponent
  split_ifs with h
  · exact (PhysicalRows.newCap_lt_physicalTheta (Classical.choose_spec h)).le
  · exact h6 _

/-- The exact familyPolicy applied to original policy5 preserves a root
ordinary approval on every history. Its new stages use their literal
sixth/raised exponent formulas, not an assumed active-support estimate. -/
theorem joinedPolicy_implies_root
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega N : ℝ) (hN : 1 ≤ N)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (lambda3 lambda6 : List ℕ → ℝ) (h6 : ∀ pre, lambda6 pre ≤ (299/500 : ℝ))
    (positive : Bool) (pre : List ℕ)
    (hp : familyPolicy N lambda3 lambda6
      (policy5 e chi m omega N rows4 licensed4 J5 rows5) positive pre = true) :
    ordinaryParityRosserPolicy false (N^(299/500 : ℝ)) positive pre = true := by
  cases positive with
  | true => exact ordinaryParityRosserPolicy_upper_even _ _
  | false =>
    have hadm : ordinaryRosserPrefixAdmissible false (N^(299/500 : ℝ)) pre := by
      by_cases h8 : pre.length ≤ 8
      · by_cases hlen6 : pre.length ≤ 6
        · have hbase : policy5 e chi m omega N rows4 licensed4 J5 rows5 false pre = true := by
            simpa [familyPolicy, parentPolicy,
              P4AOriginalEighthParentPhysicalLedger.parentPolicy,
              P4AActualSixthFrozenEighthAdmission.sixthPolicy,
              firstExitDepthSplicePolicy, h8, hlen6] using hp
          have hi : ordinaryRosserPrefixAdmissible false
              (N^HistoricalThirdCoarse.initial (e : ℝ)) pre := by
            have hroot := actualFifthPolicy_implies_root
              e chi m omega N rows4 licensed4 J5 rows5 he hN false pre hbase
            simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hroot
          exact ordinaryRosserPrefixAdmissible_mono false pre
            (Real.rpow_le_rpow_of_exponent_le hN (by
              have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
              dsimp [HistoricalThirdCoarse.initial, extendedDistributionCap]
              linarith)) hi
        · have hi : ordinaryRosserPrefixAdmissible false
              (N^lambda6 (rosserAncestor 6 pre)) pre := by
            simpa [familyPolicy, parentPolicy,
              P4AOriginalEighthParentPhysicalLedger.parentPolicy,
              P4AActualSixthFrozenEighthAdmission.sixthPolicy,
              firstExitDepthSplicePolicy, h8, hlen6,
              frozenParityRosserPolicy, ancestorFrozenPolicy,
              ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
          exact ordinaryRosserPrefixAdmissible_mono false pre
            (Real.rpow_le_rpow_of_exponent_le hN (h6 _)) hi
      · have hi : ordinaryRosserPrefixAdmissible false
            (N^raisedExponent N lambda3 lambda6 (rosserAncestor 8 pre)) pre := by
          simpa [familyPolicy, firstExitDepthSplicePolicy, h8,
            frozenParityRosserPolicy, ancestorFrozenPolicy,
            ordinaryParityRosserPolicy, oddFirstExitPolicy] using hp
        exact ordinaryRosserPrefixAdmissible_mono false pre
          (Real.rpow_le_rpow_of_exponent_le hN
            (actualRaisedExponent_le_theta N lambda3 lambda6 h6 _)) hi
    simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hadm

/-- This constructor is exactly the current original-row joined tree,
not the older corrected fallback-only physicalPolicy. -/
def joinedPolicy (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (lambda3 lambda6 : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  familyPolicy N lambda3 lambda6 (policy5 e chi m omega N rows4 licensed4 J5 rows5)

theorem joinedRoughSupport_lt_theta
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m N enumerationCap : ℕ) (omega w z : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (lambda3 lambda6 : List ℕ → ℝ) (h6 : ∀ pre, lambda6 pre ≤ (299/500 : ℝ))
    (hN : 2 ≤ N) {d : ℕ}
    (hd : d ∈ fixedRoughSupport
      (joinedPolicy e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 lambda3 lambda6 false)
      N enumerationCap w z) : (d : ℝ) < (N : ℝ)^(299/500 : ℝ) := by
  let P := joinedPolicy e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 lambda3 lambda6
  let R := (N : ℝ)^(299/500 : ℝ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hR : 1 < R := Real.one_lt_rpow hNr (by norm_num)
  have heven : ∀ pre, P true pre = true := family_even (N : ℝ) lambda3 lambda6
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    (actualFifthPolicy_even e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    P heven N enumerationCap w z] at hd
  obtain ⟨chosen, hsub, hvalid, hprod⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection P _ d).mp hd
  have hv := validSelection_mono P (ordinaryParityRosserPolicy false R)
    (joinedPolicy_implies_root e he chi m omega (N : ℝ) hNr.le rows4 licensed4 J5 rows5
      lambda3 lambda6 h6) [] chosen true hvalid
  have hroot : d ∈ firstExitRetainedModuli (ordinaryParityRosserPolicy false R)
      (roughPrimeUniverse N enumerationCap w z) :=
    (mem_firstExitRetainedModuli_iff_validSelection _ _ d).mpr ⟨chosen, hsub, hv, hprod⟩
  rw [ordinaryParityRosserRetainedModuli_eq false R hR _
    (roughPrimeUniverse_pairwise_gt N enumerationCap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) (by simp)] at hroot
  exact ((mem_ordinaryRosserRetainedModuli_iff false R hR _
    (roughPrimeUniverse_pairwise_gt N enumerationCap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) d).mp hroot).2.1

/-- Concrete small/rough multiplication gives the manuscript inflation
Theta+epsilon<=599/1000. The only missing selected-sixth input is the
local scalar ceiling h6, not the desired physical active-cap statement. -/
theorem joinedAttachedCoefficient_lt_inflatedTheta
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m N : ℕ) (omega r epsilon : ℝ)
    (cap : ℕ → ℕ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (lambda3 lambda6 : List ℕ → ℝ) (h6 : ∀ pre, lambda6 pre ≤ (299/500 : ℝ))
    (hN : 2 ≤ N) (hepsilon : epsilon ≤ 1/1000) {q : ℕ}
    (hq : attachedUpperCoefficient 1 r epsilon
      (fun M => joinedPolicy e chi m omega (M : ℝ) rows4 licensed4 J5 rows5
        lambda3 lambda6 false) cap N q ≠ 0) : (q : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNr
  obtain ⟨a, ha, b, hb, hprod, haL, hbne⟩ := actualSmallRoughRho_ne_zero_factors
    (joinedPolicy e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 lambda3 lambda6 false)
    N (cap N) ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)
    (by simpa only [attachedUpperCoefficient, one_mul] using hq)
  have hbR := joinedRoughSupport_lt_theta e he chi m N (cap N) omega
    ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) rows4 licensed4 J5 rows5 lambda3 lambda6 h6 hN hb
  have hqR : (q : ℝ) < (N : ℝ)^((299/500 : ℝ)+epsilon) := by
    calc
      (q : ℝ) = (a : ℝ)*(b : ℝ) := by rw [hprod, Nat.cast_mul]
      _ ≤ (N : ℝ)^epsilon*(b : ℝ) := mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg _)
      _ < (N : ℝ)^epsilon*(N : ℝ)^(299/500 : ℝ) :=
        mul_lt_mul_of_pos_left hbR (Real.rpow_pos_of_pos hN0 _)
      _ = _ := by rw [Real.rpow_add hN0]; ring
  exact hqR.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))

theorem joinedActiveCap_le_inflatedTheta
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m N : ℕ) (omega r epsilon : ℝ)
    (cap : ℕ → ℕ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (lambda3 lambda6 : List ℕ → ℝ) (h6 : ∀ pre, lambda6 pre ≤ (299/500 : ℝ))
    (hN : 2 ≤ N) (hepsilon : epsilon ≤ 1/1000) :
    (actualActiveUpperCap 1 r epsilon
      (fun M => joinedPolicy e chi m omega (M : ℝ) rows4 licensed4 J5 rows5
        lambda3 lambda6 false) cap N : ℝ) ≤ (N : ℝ)^(599/1000 : ℝ) := by
  have hpow : 0 ≤ (N : ℝ)^(599/1000 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hs : actualActiveUpperCap 1 r epsilon
      (fun M => joinedPolicy e chi m omega (M : ℝ) rows4 licensed4 J5 rows5
        lambda3 lambda6 false) cap N ≤ Nat.floor ((N : ℝ)^(599/1000 : ℝ)) := by
    unfold actualActiveUpperCap
    apply Finset.sup_le
    intro q hq
    exact (Nat.le_floor_iff hpow).mpr (joinedAttachedCoefficient_lt_inflatedTheta e he chi m N
      omega r epsilon cap rows4 licensed4 J5 rows5 lambda3 lambda6 h6 hN hepsilon
      (Finset.mem_filter.mp hq).2).le
  exact (Nat.cast_le.mpr hs).trans (Nat.floor_le hpow)

/-- Target-dependent actual sixth/third producers are allowed. Only the
chosen target's literal sixth ceiling is used; this is not a fixed-in-N
substitute for the source's logarithmic-history selector. -/
theorem joinedTargetDependentActiveCap_le_inflatedTheta
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m N : ℕ) (omega r epsilon : ℝ)
    (cap : ℕ → ℕ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (lambda3 lambda6 : ℕ → List ℕ → ℝ)
    (h6 : ∀ pre, lambda6 N pre ≤ (299/500 : ℝ))
    (hN : 2 ≤ N) (hepsilon : epsilon ≤ 1/1000) :
    (actualActiveUpperCap 1 r epsilon
      (fun M => joinedPolicy e chi m omega (M : ℝ) rows4 licensed4 J5 rows5
        (lambda3 M) (lambda6 M) false) cap N : ℝ) ≤ (N : ℝ)^(599/1000 : ℝ) := by
  have h := joinedActiveCap_le_inflatedTheta e he chi m N omega r epsilon cap
    rows4 licensed4 J5 rows5 (lambda3 N) (lambda6 N) h6 hN hepsilon
  simpa only [actualActiveUpperCap, attachedUpperModuli, attachedUpperCoefficient] using h

end
end ImbalancedChen.P5Z.OriginalJoinedLateRange
