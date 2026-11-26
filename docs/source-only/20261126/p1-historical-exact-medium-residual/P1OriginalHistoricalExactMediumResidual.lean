import ImbalancedChen.P1OriginalHistoricalRemainingTypeIPaid
import ImbalancedChen.P1OriginalHistoricalAtlasCorrectionReduction
import ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original literal mediumAtlas remains explicit. The complement of
that sum is paid, with the same physical N, original kap, historical
Q/rho and old/fresh policy order. No estimate for mediumAtlas or smooth
signed PP is assumed or asserted.

The historical retainedAtlas uses kap BOTH in actualLicence and in the
complete-product eta. Thus the new remaining theorem is instantiated
with kap0=kap, and its genuine gate kap<kappa/(4*(1+kappa)) is EXPLICIT.
The older count interfaces allow any 0<kap<1; they do not imply this
extra gate for an already fixed kap. A small-parameter existence lemma
shows how their free smoothing choice can satisfy it before histories
and N are chosen, without changing kap partway through a source identity.

HistoryRemainder and policyRemaining minus the exact medium sum receive
arbitrary logarithmic accuracy. The original physical count interfaces
retain their actual u*singularNormalization rate and selection schedule.
They are not upgraded to an arbitrary-log physical-count theorem here.

Proper-power payment calls the existing P3-dependent Atlas theorem.
Its P3 compilation/owner hold remains a dependency boundary of this file.
-/

namespace ImbalancedChen.P1OriginalHistoricalExactMediumResidual
noncomputable section
open Classical Filter VariableEnvelope
open scoped BigOperators
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve properPowerReserve)
open P5Z.OriginalPrimeAtlasReserveBranches (mediumAtlas originalMediumLow originalMediumHigh)
open P1Full87TrueDPolicyDelta (trueDDeltaRho)
open P1Full87HistoricalMiddleSmoothing (policyRemaining)
open P1Full87HistoricalOneLongRemainder
  (retainedAtlas historyRemainder eventually_history_remainder)
open P1OriginalHistoricalAtlasCorrectionReduction
  (distributionAtlas historyDistribution exists_original_count_distributions)
open P1OriginalHistoricalTwoLongP2
  (historicalModuli historicalRho historical_modulus_class)
open P1OriginalHistoricalRemainingTypeIPaid
  (sourceChannel eventually_historical_remainingTypeI_paid)
open P1OriginalSingletonAtlasTrimLogAccuracy
  (eventually_original_singleton_atlas_trim_logAccuracy)
open P1OriginalSingletonAtlasProperPower
  (eventually_original_singleton_atlas_properPower_logAccuracy)
open P4BOriginalSharpEndpointPrices (eventually_inverse_log)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy policy)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest densityTest gain primeMass)
open P1Original87SharpMiddleReserve (comparisonReceiver)

/-- The exact original medium summand, without a bound or surrogate. -/
def mediumAtlasSum (kap zeta : ℝ) (K N : ℕ) (Q : Finset ℕ) (c : ℕ → ℝ) : ℂ :=
  ∑ js ∈ chartBank (2*N) 1,
    mediumAtlas (actualLicence kap 6 N) K (2*N) N kap
      (originalMediumLow zeta js) (originalMediumHigh zeta js)
      Q (fun q => (c q : ℂ)) js

def historyMedium (B kap zeta : ℝ) (K : ℕ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℂ :=
  mediumAtlasSum kap zeta K N (historicalModuli B old fresh N cap w z)
    (trueDDeltaRho old fresh N cap w z L)

/-- The old top-level count interfaces quantify over every 0<kap<1.
They therefore permit this choice BEFORE histories and N. The lemma
does not assert the remaining-geometry gate for arbitrary fixed kap. -/
theorem exists_small_original_smoothing (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ kappa kap : ℝ, 0 < kappa ∧ kappa ≤ zeta/10000 ∧
      0 < kap ∧ kap < 1 ∧ kap < kappa/(4*(1+kappa)) := by
  let kappa := zeta/20000
  let kap := kappa/(8*(1+kappa))
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  have hsmall : kappa ≤ zeta/10000 := by dsimp only [kappa]; linarith
  have hkap : 0 < kap := by dsimp only [kap]; positivity
  have hk : kap < 1 := by
    dsimp only [kap]
    apply (div_lt_one (by positivity : (0 : ℝ) < 8*(1+kappa))).mpr
    linarith
  have htrim : kap < kappa/(4*(1+kappa)) := by
    dsimp only [kap]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    have hpos := mul_pos hkappa (show 0 < 1+kappa by linarith)
    nlinarith
  exact ⟨kappa, kap, hkappa, hsmall, hkap, hk, htrim⟩

/-- Exact subtraction at the original signs and unchanged coefficient. -/
theorem historyDistribution_sub_medium_eq_remaining
    (B kap zeta : ℝ) (K : ℕ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) :
    historyDistribution B kap zeta K old fresh N cap w z L -
      historyMedium B kap zeta K old fresh N cap w z L =
        sourceChannel kap N K kap zeta B old fresh cap w z L := by
  unfold historyDistribution distributionAtlas historyMedium mediumAtlasSum sourceChannel
  dsimp only [historicalModuli, historicalRho]
  rw [Finset.sum_add_distrib]
  ring

private theorem historyRemainder_sub_medium_eq
    (B kap zeta : ℝ) (K : ℕ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) :
    historyRemainder B kap zeta K old fresh N cap w z L -
      historyMedium B kap zeta K old fresh N cap w z L =
      trimReserve (actualLicence kap 6 N) (2*N) N kap
        (historicalModuli B old fresh N cap w z) (historicalRho old fresh N cap w z L) +
      sourceChannel kap N K kap zeta B old fresh cap w z L -
      ∑ js ∈ chartBank (2*N) 1,
        properPowerReserve (actualLicence kap 6 N) K (2*N) N kap
          (historicalModuli B old fresh N cap w z) (historicalRho old fresh N cap w z L) js := by
  unfold historyRemainder retainedAtlas historyMedium mediumAtlasSum sourceChannel
  dsimp only [historicalModuli, historicalRho]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private theorem eventually_constant_log_budget (C : ℝ) (hC : 0 ≤ C) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, C*((N : ℝ)/(Real.log (N : ℝ))^(A+1)) ≤
      (N : ℝ)/(Real.log (N : ℝ))^A := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_inverse_log C hC 0 A (A+1) (by omega))
  filter_upwards [h] with N hN
  have hm := mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg N)
  simpa only [pow_zero, mul_one, div_eq_mul_inv, one_mul,
    mul_assoc, mul_comm, mul_left_comm] using hm

/-- The explicit distribution sum has exactly one unpaid summand:
the unchanged mediumAtlas. The extra scalar gate is retained visibly. -/
theorem eventually_historyDistribution_sub_medium_logAccuracy
    (kap zeta : ℝ) (K A : ℕ) (hk : kap < 1)
    {kappa : ℝ} (hkappa : 0 < kappa) (hsmall : kappa ≤ zeta/10000)
    (hzeta : zeta ≤ 1/20000) (htrim : kap < kappa/(4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℝ) (old fresh : List ℕ → Bool)
      (cap : ℕ) (w z L : ℝ),
      ‖historyDistribution B kap zeta K old fresh N cap w z L -
        historyMedium B kap zeta K old fresh N cap w z L‖ ≤
          (N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_historical_remainingTypeI_paid A K
    (kap0 := kap) hkappa hsmall hzeta htrim] with N hN
  intro B old fresh cap w z L
  rw [historyDistribution_sub_medium_eq_remaining]
  exact hN kap hk B old fresh cap w z L

/-- Trim, remaining Type I and the signed proper-power sum are all paid.
The original medium is retained literally. Proper-power payment inherits
its P3 hold; no replacement estimate is a hypothesis of this theorem. -/
theorem eventually_historyRemainder_sub_medium_logAccuracy
    (kap zeta : ℝ) (K A : ℕ) (hkap : 0 < kap) (hk : kap < 1)
    {kappa : ℝ} (hkappa : 0 < kappa) (hsmall : kappa ≤ zeta/10000)
    (hzeta : zeta ≤ 1/20000) (htrim : kap < kappa/(4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℝ) (old fresh : List ℕ → Bool)
      (cap : ℕ) (w z L : ℝ),
      ‖historyRemainder B kap zeta K old fresh N cap w z L -
        historyMedium B kap zeta K old fresh N cap w z L‖ ≤
          (N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_original_singleton_atlas_trim_logAccuracy
      kap hkap hk (A+1) 1 (by norm_num),
    eventually_original_singleton_atlas_properPower_logAccuracy
      kap hk ((A+1 : ℕ) : ℝ) 1 (by norm_num),
    eventually_historical_remainingTypeI_paid (A+1) K
      (kap0 := kap) hkappa hsmall hzeta htrim,
    eventually_constant_log_budget 3 (by norm_num) A,
    eventually_ge_atTop (2 : ℕ)] with N hT hP hR hsum hN
  intro B old fresh cap w z L
  let Q := historicalModuli B old fresh N cap w z
  let c := trueDDeltaRho old fresh N cap w z L
  let T := trimReserve (actualLicence kap 6 N) (2*N) N kap Q (fun q => (c q : ℂ))
  let P := ∑ js ∈ chartBank (2*N) 1,
    properPowerReserve (actualLicence kap 6 N) K (2*N) N kap Q (fun q => (c q : ℂ)) js
  let R := sourceChannel kap N K kap zeta B old fresh cap w z L
  let E := (N : ℝ)/(Real.log (N : ℝ))^(A+1)
  have hrange : ∀ q ∈ Q, 0 < q ∧ (q : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
    intro q hq
    exact ⟨(historical_modulus_class B old fresh N cap w z L hq).1,
      (Finset.mem_filter.mp hq).2.2⟩
  have hQ : Q ⊆ Finset.Icc 1 N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hscale : (N : ℝ)^(599/1000 : ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
        (show (599/1000 : ℝ) ≤ 1 by norm_num)
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(hrange q hq).1,
      by exact_mod_cast (hrange q hq).2.le.trans hscale⟩
  have hunit : ∀ q ∈ Q, |c q| ≤ 1 := fun q _ =>
    P1Full87TrueDUnitBound.trueDDeltaRho_abs_le_one old fresh N cap q w z L
  have hTb : ‖T‖ ≤ E := by
    simpa only [one_mul] using hT kap 6 Q c hQ hunit
  have hPb : ‖P‖ ≤ E := by
    simpa only [Real.rpow_natCast, one_mul] using hP 6 K kap Q c hrange hunit
  have hRb : ‖R‖ ≤ E := hR kap hk B old fresh cap w z L
  rw [historyRemainder_sub_medium_eq]
  change ‖T+R-P‖ ≤ _
  calc
    _ ≤ ‖T+R‖+‖P‖ := norm_sub_le _ _
    _ ≤ (‖T‖+‖R‖)+‖P‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ (E+E)+E := add_le_add (add_le_add hTb hRb) hPb
    _ = 3*E := by ring
    _ ≤ _ := hsum

/-- The original smoothed signed prime error differs from its original
medium sum by arbitrary log accuracy, after also paying the old one-long
extraction. This is policyRemaining, not an upgraded physical-count rate. -/
theorem eventually_policyRemaining_sub_medium_logAccuracy
    (kap zeta : ℝ) (K A : ℕ) (hK : 1 ≤ K) (hkap : 0 < kap) (hk : kap < 1)
    {kappa : ℝ} (hkappa : 0 < kappa) (hsmall : kappa ≤ zeta/10000)
    (hzeta : zeta ≤ 1/20000) (htrim : kap < kappa/(4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℝ) (old fresh : List ℕ → Bool)
      (cap : ℕ) (w z L : ℝ),
      ‖(policyRemaining B kap old fresh N cap w z L : ℂ) -
        historyMedium B kap zeta K old fresh N cap w z L‖ ≤
          (N : ℝ)/(Real.log (N : ℝ))^A := by
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  filter_upwards [eventually_history_remainder kap zeta hk hzeta0 hzeta K hK (A+1),
    eventually_historyRemainder_sub_medium_logAccuracy kap zeta K (A+1)
      hkap hk hkappa hsmall hzeta htrim,
    eventually_constant_log_budget 2 (by norm_num) A] with N hlong hrest hsum
  intro B old fresh cap w z L
  calc
    _ ≤ ‖(policyRemaining B kap old fresh N cap w z L : ℂ) -
          historyRemainder B kap zeta K old fresh N cap w z L‖ +
        ‖historyRemainder B kap zeta K old fresh N cap w z L -
          historyMedium B kap zeta K old fresh N cap w z L‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (policyRemaining B kap old fresh N cap w z L : ℂ)
        (historyRemainder B kap zeta K old fresh N cap w z L)
        (historyMedium B kap zeta K old fresh N cap w z L)
    _ ≤ (N : ℝ)/(Real.log (N : ℝ))^(A+1) +
        (N : ℝ)/(Real.log (N : ℝ))^(A+1) :=
      add_le_add (hlong B old fresh cap w z L) (hrest B old fresh cap w z L)
    _ = 2*((N : ℝ)/(Real.log (N : ℝ))^(A+1)) := by ring
    _ ≤ _ := hsum

private theorem halves {x y z : ℂ} {u H : ℝ}
    (hxy : ‖x-y‖ ≤ u/2*H) (hyz : ‖y-z‖ ≤ u/2*H) : ‖x-z‖ ≤ u*H := by
  calc
    _ ≤ ‖x-y‖+‖y-z‖ := by simpa only [dist_eq_norm] using dist_triangle x y z
    _ ≤ u/2*H+u/2*H := add_le_add hxy hyz
    _ = _ := by ring

/-- Both original physical receivers retain their own literal medium
sum and old/fresh order. The actual u*singularNormalization rate, all
omission budgets and the original history-selection schedule are kept.
The small smoothing gate remains explicit; there is no medium estimate. -/
theorem exists_original_count_medium_residuals :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (kap zeta : ℝ) (K : ℕ) {kappa : ℝ},
      0 < kap → kap < 1 → 0 < kappa → kappa ≤ zeta/10000 → zeta ≤ 1/20000 →
      kap < kappa/(4*(1+kappa)) → 1 ≤ K →
      ∀ u epsSource epsBox epsSixth : ℝ, 0 < u → 0 < epsSource → 0 < epsBox → 0 < epsSixth →
      ∃ s r : ℕ, ∃ E : ℝ, 0 < E ∧ E ≤ 11/64000 ∧
        P4AOriginalFull87SixthMarginIntegration.totalSixthOmitted s (fun _ _ => (1 : ℝ)) < epsSixth ∧
        P4AOriginalFull87TrimOmission.totalOmitted r (fun _ _ => (1 : ℝ)) < epsSource ∧
        ∀ e : ℚ, 0 < e → (e : ℝ) < E → ∃ q0 : ℕ, 0 < q0 ∧ ∀ q ≥ q0,
        ∀ a : ℝ, a ≤ 1/100 → ∃ n0 : ℕ, ∀ n ≥ n0, ∃ m0 : ℕ, ∀ m ≥ m0,
        P4AOriginalFull87AllRankBoxedProvenance.allOmitted n e q a m (fun _ _ => (1 : ℝ)) < epsBox ∧
        FilteredSourceSupply s r n e q a ∧
        ∀ᶠ N : ℕ in atTop, Even N → ∀ (cap : ℕ) (w z ell : ℝ),
          w ≤ (N : ℝ)^(53/13824 : ℝ) → (N : ℝ)^mu ≤ z → z ≤ cap → 0 < ell → ell ≤ 1/1000 →
          let L := (N : ℝ)^ell
          let R := eventPolicy true (width r) n e q a N
          let S := eventPolicy false (width r) n e q a N
          let six := sixthPolicy n e q a (N : ℝ)
          let eight := policy (width r) n e q a (N : ℝ)
          ‖((comparisonReceiver r n e q a N cap w z L (receiverTest N) -
              primeMass N * comparisonReceiver r n e q a N cap w z L densityTest : ℝ) : ℂ) -
              historyMedium B kap zeta K (S false) (R false) N cap w z L‖
              ≤ u*singularNormalization N ∧
          ‖((gain (width r) n e q a N cap w z L (receiverTest N) -
              primeMass N * gain (width r) n e q a N cap w z L densityTest : ℝ) : ℂ) -
              historyMedium B kap zeta K (eight false) (six false) N cap w z L‖
              ≤ u*singularNormalization N := by
  obtain ⟨B, hB, hcounts⟩ := exists_original_count_distributions
  refine ⟨B, hB, ?_⟩
  intro kap zeta K kappa hkap hk hkappa hsmall hzeta htrim hK
    u epsSource epsBox epsSixth hu hs hb h6
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  obtain ⟨s, r, E, hE, hE1, hSix, hSource, hChoose⟩ :=
    hcounts kap zeta K hkap hk hzeta0 hzeta hK (u/2) epsSource epsBox epsSixth
      (half_pos hu) hs hb h6
  refine ⟨s, r, E, hE, hE1, hSix, hSource, ?_⟩
  intro e he he1
  obtain ⟨q0, hq0, hq⟩ := hChoose e he he1
  refine ⟨q0, hq0, ?_⟩
  intro q hqq a ha
  obtain ⟨n0, hn⟩ := hq q hqq a ha
  refine ⟨n0, ?_⟩
  intro n hnn
  obtain ⟨m0, hm⟩ := hn n hnn
  refine ⟨m0, ?_⟩
  intro m hmm
  obtain ⟨hBox, hHist, hPhysical⟩ := hm m hmm
  refine ⟨hBox, hHist, ?_⟩
  filter_upwards [hPhysical,
    eventually_historyDistribution_sub_medium_logAccuracy kap zeta K 3
      hk hkappa hsmall hzeta htrim,
    p5z_eventually_logCube_le_singularNormalization 1 (u/2) (half_pos hu)]
      with N hP hResidual hScale
  intro hev cap w z ell hw hzcut hcap hell hell1
  obtain ⟨hComp, hSave⟩ := hP hev cap w z ell hw hzcut hcap hell hell1
  have hbudget : (N : ℝ)/(Real.log (N : ℝ))^3 ≤ u/2*singularNormalization N := by
    simpa only [one_mul] using hScale
  let L := (N : ℝ)^ell
  let R := eventPolicy true (width r) n e q a N
  let S := eventPolicy false (width r) n e q a N
  let six := sixthPolicy n e q a (N : ℝ)
  let eight := policy (width r) n e q a (N : ℝ)
  exact ⟨halves hComp ((hResidual B (S false) (R false) cap w z L).trans hbudget),
    halves hSave ((hResidual B (eight false) (six false) cap w z L).trans hbudget)⟩

end
end ImbalancedChen.P1OriginalHistoricalExactMediumResidual
