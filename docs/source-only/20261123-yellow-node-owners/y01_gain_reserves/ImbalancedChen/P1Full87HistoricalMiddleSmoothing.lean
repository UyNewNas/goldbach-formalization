import ImbalancedChen.P1Full87SharpClassicalCut
import ImbalancedChen.P1OriginalSingletonMiddleWeight
import ImbalancedChen.P1Original87SharpMiddleReserve
import ImbalancedChen.P1Full87TrueDUnitBound

/-! The original two historical prime discrepancies and the compiled
singleton have distinct coefficient functions. Each keeps its own
integer carrier, including its squarefree and target-coprime tests.
Remove the full classical BV range and pay both independent smooth
endpoint reserves on the surviving signed physical sum. -/
namespace ImbalancedChen.P1Full87HistoricalMiddleSmoothing
noncomputable section
open Classical Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
open P1OriginalSharpFiniteReceiver (middle cut)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)
open P4AOriginalFull87EighthPrimeMeanLedger (primeMass densityTest)
open P5CanonicalTentNarrowSingletonTransfer
  (fullSmoothWeight lowerReserve upperReserve original_source_exact_reserves)
open P1Full87TrueDPolicyDelta
  (trueDDeltaRho trueDDeltaSupport trueDDeltaSupport_squarefree trueDDeltaSupport_coprime_target)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy policy)
open P1Original87SharpMiddleReserve (comparisonMiddle savingMiddle)
open P4AOriginalFull87PhysicalQAggregateInvoice (pairActualPhysicalModuli pairActualHighQModuli)
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)

def remainingModuli (B : ℝ) (N : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  Q.filter (fun d => panModulusCutoff N B < d ∧ (d : ℝ) < (N : ℝ)^(599/1000 : ℝ))

def smoothRemaining (B kappa : ℝ) (N : ℕ) (Q : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  Part3.primeProductSignedError 1 (2*N) N (remainingModuli B N Q) c
    (fullSmoothWeight kappa 6 N)

def policyRemaining (B kappa : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  smoothRemaining B kappa N (trueDDeltaSupport old fresh N cap w z)
    (trueDDeltaRho old fresh N cap w z L)

/-- The upper and lower smooth collars are paid individually. The
subcarrier and coefficient are selected after the common threshold. -/
theorem exists_middle_smoothing :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ kappa : ℝ, 0 < kappa → kappa < 1 →
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
    ∀ (Q : Finset ℕ) (c : ℕ → ℝ),
      (∀ d ∈ Q, Squarefree d ∧ d.Coprime N ∧ |c d| ≤ 1) →
      |middle N Q c - smoothRemaining B kappa N Q c| ≤ eta * singularNormalization N ∧
      |lowerReserve kappa 6 N (remainingModuli B N Q) c| ≤ eta/4 * singularNormalization N ∧
      |upperReserve kappa 6 N (remainingModuli B N Q) c| ≤ eta/4 * singularNormalization N := by
  obtain ⟨B, hB, C, _, hBV⟩ := P1Full87SharpClassicalCut.exists_pan_sharp_payment
  refine ⟨B, hB, ?_⟩
  intro kappa hk hk1 eta he
  have hfour : 0 < eta/4 := by positivity
  filter_upwards [hBV, p5z_eventually_logCube_le_singularNormalization C (eta/4) hfour,
    P5PrimeDivisorMean.eventually_log_square_cap_le_normalization (eta/4) hfour,
    P1OriginalSingletonMiddleWeight.lower_paid kappa (eta/4) hk hk1 hfour,
    P1OriginalSingletonMiddleWeight.upper_paid kappa (eta/4) hfour, eventually_ge_atTop (2 : ℕ)]
    with N hclass hlog hmean hlo hup hN
  intro hev Q c hQ
  let D := panModulusCutoff N B
  let S := Q.filter (fun d => cut N < d ∧ (d : ℝ) < (N : ℝ)^(599/1000 : ℝ))
  let low := S.filter (fun d => d ≤ D)
  let high := remainingModuli B N Q
  have hform : S.filter (fun d => D < d) = high := by
    ext d
    simp only [S, high, remainingModuli, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm, _, hupper⟩, hd⟩
      exact ⟨hm, hd, hupper⟩
    · rintro ⟨hm, hd, hupper⟩
      exact ⟨⟨hm, hclass.1.trans_lt hd, hupper⟩, hd⟩
  have hSN : S ⊆ Finset.Icc 1 N := by
    intro d hd
    obtain ⟨hm, _, hu⟩ := Finset.mem_filter.mp hd
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hupper : (N : ℝ)^(599/1000 : ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
        (show (599/1000 : ℝ) ≤ 1 by norm_num)
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hQ d hm).1.ne_zero,
      by exact_mod_cast (hu.trans_le hupper).le⟩
  have hlowS : low ⊆ S := Finset.filter_subset _ _
  have hhighS : high ⊆ S := hform ▸ Finset.filter_subset _ _
  have hSQ : S ⊆ Q := Finset.filter_subset _ _
  have hlow := (hclass.2 low (hlowS.trans hSN)
    (fun d hd => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hSN (hlowS hd))).1,
      (Finset.mem_filter.mp hd).2⟩)
    (fun d hd => (hQ d (hSQ (hlowS hd))).2.1) c
    (fun d hd => (hQ d (hSQ (hlowS hd))).2.2)).trans hlog
  have dataH (d : ℕ) (hd : d ∈ high) := hQ d (hSQ (hhighS hd))
  have hcap := hhighS.trans hSN
  have habs (d : ℕ) (hd : d ∈ high) := (dataH d hd).2.2
  have hp := (P5PrimeDivisorMean.abs_singleton_PP_sub_total_pi_error_le N N high c hcap
    (fun d hd => (dataH d hd).1) habs).trans (hmean N le_rfl)
  have hcenter :
      |Part3.primeProductSignedError 1 N N high c (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
        ∑ d ∈ high, c d * sharpPrimeError N d| ≤ eta/4 * singularNormalization N := by
    simpa only [sharpPrimeError, primeMass, densityTest, mul_one_div] using hp
  have hlower := hlo high c hcap habs
  have hupper := hup hev high c hcap habs
  have hsplit : (∑ d ∈ low, c d * sharpPrimeError N d) +
      (∑ d ∈ high, c d * sharpPrimeError N d) = middle N Q c := by
    simpa only [not_le, hform] using
      (Finset.sum_filter_add_sum_filter_not S (fun d => d ≤ D) (fun d => c d * sharpPrimeError N d))
  have hfull := original_source_exact_reserves kappa 6 N high c
  refine ⟨?_, hlower, hupper⟩
  change |middle N Q c - Part3.primeProductSignedError 1 (2*N) N high c _| ≤ _
  obtain ⟨l1, l2⟩ := abs_le.mp hlow
  obtain ⟨c1, c2⟩ := abs_le.mp hcenter
  obtain ⟨b1, b2⟩ := abs_le.mp hlower
  obtain ⟨t1, t2⟩ := abs_le.mp hupper
  exact abs_le.mpr ⟨by linarith only [l1, c2, b1, t1, hsplit, hfull],
    by linarith only [l2, c1, b2, t2, hsplit, hfull]⟩

/-- Equality at the original signs. The old/fresh order in trueDDeltaRho
is reversed for the raw-minus-licensed comparison and for sixth-minus-eighth. -/
theorem comparison_as_middle (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    let R := eventPolicy true (width r) n e q a N
    let S := eventPolicy false (width r) n e q a N
    comparisonMiddle r n e q a N cap w z L =
      middle N (trueDDeltaSupport (S false) (R false) N cap w z)
        (trueDDeltaRho (S false) (R false) N cap w z L) := by
  simp only [comparisonMiddle, middle, pairActualHighQModuli, pairActualPhysicalModuli,
    trueDDeltaSupport, trueDDeltaRho, supportedPhysicalRho, Finset.filter_filter]

theorem saving_as_middle (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    let six := sixthPolicy n e q a (N : ℝ)
    let eight := policy (width r) n e q a (N : ℝ)
    savingMiddle r n e q a N cap w z L =
      middle N (trueDDeltaSupport (eight false) (six false) N cap w z)
        (trueDDeltaRho (eight false) (six false) N cap w z L) := by
  rfl

/-- The analytic payment is uniform in both physical histories and the final
coefficient. Hence it does not exchange either historical parameter schedule
with the finite compiler's choices. -/
theorem exists_full87_simultaneous_smoothing :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ kappa : ℝ, 0 < kappa → kappa < 1 →
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
    ∀ (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (cap : ℕ) (w z L : ℝ),
      let R := eventPolicy true (width r) n e q a N
      let S := eventPolicy false (width r) n e q a N
      let six := sixthPolicy n e q a (N : ℝ)
      let eight := policy (width r) n e q a (N : ℝ)
      |comparisonMiddle r n e q a N cap w z L -
        policyRemaining B kappa (S false) (R false) N cap w z L| ≤ eta * singularNormalization N ∧
      |savingMiddle r n e q a N cap w z L -
        policyRemaining B kappa (eight false) (six false) N cap w z L| ≤ eta * singularNormalization N ∧
      ∀ (f : List ℕ → Bool) (tag : ℕ → List Bool) (tau : ℝ),
        let Q := P4AUpperTaggedBetaAttachment.support N cap w z
        let c := P4AUpperTaggedBetaAttachment.rho f tag N cap w z tau L
        |middle N Q c - smoothRemaining B kappa N Q c| ≤ eta * singularNormalization N := by
  obtain ⟨B, hB, h⟩ := exists_middle_smoothing
  refine ⟨B, hB, ?_⟩
  intro kappa hk hk1 eta he
  filter_upwards [h kappa hk hk1 eta he] with N hN
  intro hev r n e q a cap w z L
  have hd (old fresh : List ℕ → Bool) :
      |middle N (trueDDeltaSupport old fresh N cap w z) (trueDDeltaRho old fresh N cap w z L) -
        policyRemaining B kappa old fresh N cap w z L| ≤ eta * singularNormalization N :=
    (hN hev _ _ (fun d hm => ⟨trueDDeltaSupport_squarefree old fresh N cap w z hm,
      trueDDeltaSupport_coprime_target old fresh N cap w z hm,
      P1Full87TrueDUnitBound.trueDDeltaRho_abs_le_one old fresh N cap d w z L⟩)).1
  dsimp only
  rw [comparison_as_middle, saving_as_middle]
  refine ⟨hd _ _, hd _ _, ?_⟩
  intro f tag tau
  exact (hN hev _ _ (fun d hm => ⟨P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hm,
    P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hm,
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d⟩)).1

end
end ImbalancedChen.P1Full87HistoricalMiddleSmoothing
