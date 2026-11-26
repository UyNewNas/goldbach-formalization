import ImbalancedChen.P1Full87HistoricalOneLongRemainder
import ImbalancedChen.P1OriginalSingletonAtlasProperPower
import ImbalancedChen.P1OriginalSingletonAtlasTrim

/-! Trim and signed proper-power payment on the original historical modulus
families after the one-long extraction. The medium and remaining Type I
terms keep the moving residue and exact coprime mean of each historical
coefficient. This file does not give a bound on their sum. -/
namespace ImbalancedChen.P1OriginalHistoricalAtlasCorrectionReduction
noncomputable section

open Classical Filter VariableEnvelope
open scoped BigOperators
open P1Full87HistoricalOneLongRemainder
  (retainedAtlas historyRemainder exists_original_count_remainders)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open P1Full87TrueDPolicyDelta (trueDDeltaRho trueDDeltaSupport trueDDeltaSupport_squarefree)
open P1OriginalSingletonOneLongRectangle (remainingTypeIAtlas)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve properPowerReserve)
open P5Z.OriginalPrimeAtlasReserveBranches (mediumAtlas originalMediumLow originalMediumHigh)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy policy)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest densityTest gain primeMass)
open P1Original87SharpMiddleReserve (comparisonReceiver)

/-- The two signed contributions still requiring distribution estimates. -/
def distributionAtlas (kap zeta : ℝ) (K N : ℕ) (Q : Finset ℕ) (c : ℕ → ℝ) : ℂ :=
  let lic := actualLicence kap 6 N
  let rho := fun d => (c d : ℂ)
  ∑ js ∈ chartBank (2*N) 1,
    (mediumAtlas lic K (2*N) N kap (originalMediumLow zeta js) (originalMediumHigh zeta js)
        Q rho js +
     remainingTypeIAtlas lic K (2*N) N kap (originalMediumLow zeta js) (originalMediumHigh zeta js)
        Q rho js)

def historyDistribution (B kap zeta : ℝ) (K : ℕ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℂ :=
  distributionAtlas kap zeta K N (remainingModuli B N (trueDDeltaSupport old fresh N cap w z))
    (trueDDeltaRho old fresh N cap w z L)

/-- In the raw source the trim enters positively and the sum of proper
powers negatively. Both use the coefficient of the two surviving charts. -/
private theorem retained_sub_distribution (kap zeta : ℝ) (K N : ℕ) (Q : Finset ℕ)
    (c : ℕ → ℝ) :
    retainedAtlas kap zeta K N Q c - distributionAtlas kap zeta K N Q c =
      trimReserve (actualLicence kap 6 N) (2*N) N kap Q (fun q => (c q : ℂ)) -
        ∑ js ∈ chartBank (2*N) 1,
          properPowerReserve (actualLicence kap 6 N) K (2*N) N kap Q (fun q => (c q : ℂ)) js := by
  unfold retainedAtlas distributionAtlas
  dsimp only
  rw [Finset.sum_sub_distrib]
  ring

/-- One threshold precedes both histories and every selected modulus
carrier. This comparison only removes the two displayed corrections and
therefore is uniform in the chart order; the count below retains 1 ≤ K. -/
theorem eventually_history_corrections (kap tol : ℝ) (hkap : 0 < kap)
    (hk : kap < 1) (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ (B zeta : ℝ) (K : ℕ) (old fresh : List ℕ → Bool)
      (cap : ℕ) (w z L : ℝ),
      ‖historyRemainder B kap zeta K old fresh N cap w z L -
        historyDistribution B kap zeta K old fresh N cap w z L‖ ≤ tol * singularNormalization N := by
  filter_upwards [
    P1OriginalSingletonAtlasTrim.eventually_original_singleton_atlas_trim_singularNormalization
      kap (tol/2) hkap hk (half_pos htol),
    P1OriginalSingletonAtlasProperPower.eventually_original_singleton_atlas_properPower_singularNormalization
      kap hk (tol/2) (half_pos htol),
    eventually_ge_atTop (2 : ℕ)] with N htrim hpower hN
  intro B zeta K old fresh cap w z L
  let Q := remainingModuli B N (trueDDeltaSupport old fresh N cap w z)
  let c := trueDDeltaRho old fresh N cap w z L
  have hrange : ∀ d ∈ Q, 0 < d ∧ (d : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
    intro d hd
    obtain ⟨hmem, _, hupper⟩ := Finset.mem_filter.mp hd
    exact ⟨Nat.pos_of_ne_zero
      (trueDDeltaSupport_squarefree old fresh N cap w z hmem).ne_zero, hupper⟩
  have hQ : Q ⊆ Finset.Icc 1 N := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hscale : (N : ℝ)^(599/1000 : ℝ) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
        (show (599/1000 : ℝ) ≤ 1 by norm_num)
    intro d hd
    obtain ⟨hpos, hdN⟩ := hrange d hd
    exact Finset.mem_Icc.mpr ⟨hpos, by exact_mod_cast hdN.le.trans hscale⟩
  have hunit : ∀ d ∈ Q, |c d| ≤ 1 := fun d _ =>
    P1Full87TrueDUnitBound.trueDDeltaRho_abs_le_one old fresh N cap d w z L
  have hT := htrim kap 6 Q c hQ hunit
  have hP := hpower 6 K kap Q c hrange hunit
  change ‖retainedAtlas kap zeta K N Q c - distributionAtlas kap zeta K N Q c‖ ≤ _
  rw [retained_sub_distribution]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ tol/2 * singularNormalization N + tol/2 * singularNormalization N := add_le_add hT hP
    _ = _ := by ring

private theorem halves {x y z : ℂ} {u H : ℝ}
    (hxy : ‖x-y‖ ≤ u/2*H) (hyz : ‖y-z‖ ≤ u/2*H) : ‖x-z‖ ≤ u*H := by
  calc
    _ ≤ ‖x-y‖ + ‖y-z‖ := by simpa only [dist_eq_norm] using dist_triangle x y z
    _ ≤ u/2*H + u/2*H := add_le_add hxy hyz
    _ = _ := by ring

/-- Shared history choices and a common physical threshold for both original
counts after paying the two corrections. Each explicit distribution sum
uses its own historical difference in the original order. -/
theorem exists_original_count_distributions :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (kap zeta : ℝ) (K : ℕ),
      0 < kap → kap < 1 → 0 < zeta → zeta ≤ 1/20000 → 1 ≤ K →
      ∀ u epsSource epsBox epsSixth : ℝ, 0 < u → 0 < epsSource → 0 < epsBox → 0 < epsSixth →
      ∃ s r : ℕ, ∃ E : ℝ, 0 < E ∧ E ≤ 11/64000 ∧
        P4AOriginalFull87SixthMarginIntegration.totalSixthOmitted s (fun _ _ => (1:ℝ)) < epsSixth ∧
        P4AOriginalFull87TrimOmission.totalOmitted r (fun _ _ => (1:ℝ)) < epsSource ∧
        ∀ e : ℚ, 0 < e → (e:ℝ) < E → ∃ q0 : ℕ, 0 < q0 ∧ ∀ q ≥ q0,
        ∀ a : ℝ, a ≤ 1/100 → ∃ n0 : ℕ, ∀ n ≥ n0, ∃ m0 : ℕ, ∀ m ≥ m0,
        P4AOriginalFull87AllRankBoxedProvenance.allOmitted n e q a m (fun _ _ => (1:ℝ)) < epsBox ∧
        FilteredSourceSupply s r n e q a ∧
        ∀ᶠ N : ℕ in atTop, Even N → ∀ (cap : ℕ) (w z ell : ℝ),
          w ≤ (N:ℝ)^(53/13824 : ℝ) → (N:ℝ)^mu ≤ z → z ≤ cap → 0 < ell → ell ≤ 1/1000 →
          let L := (N:ℝ)^ell
          let R := eventPolicy true (width r) n e q a N
          let S := eventPolicy false (width r) n e q a N
          let six := sixthPolicy n e q a (N : ℝ)
          let eight := policy (width r) n e q a (N : ℝ)
          ‖((comparisonReceiver r n e q a N cap w z L (receiverTest N) -
              primeMass N * comparisonReceiver r n e q a N cap w z L densityTest : ℝ) : ℂ) -
              historyDistribution B kap zeta K (S false) (R false) N cap w z L‖
              ≤ u * singularNormalization N ∧
          ‖((gain (width r) n e q a N cap w z L (receiverTest N) -
              primeMass N * gain (width r) n e q a N cap w z L densityTest : ℝ) : ℂ) -
              historyDistribution B kap zeta K (eight false) (six false) N cap w z L‖
              ≤ u * singularNormalization N := by
  obtain ⟨B, hB, hcounts⟩ := exists_original_count_remainders
  refine ⟨B, hB, ?_⟩
  intro kap zeta K hkap hk hz hz1 hK u epsSource epsBox epsSixth hu hs hb h6
  obtain ⟨s, r, E, hE, hE1, hSix, hSource, hChoose⟩ :=
    hcounts kap zeta K hkap hk hz hz1 hK (u/2) epsSource epsBox epsSixth
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
  filter_upwards [hPhysical, eventually_history_corrections kap (u/2) hkap hk (half_pos hu)]
    with N hP hCorrection
  intro hev cap w z ell hw hzcut hcap hell hell1
  obtain ⟨hComp, hSave⟩ := hP hev cap w z ell hw hzcut hcap hell hell1
  let L := (N : ℝ)^ell
  let R := eventPolicy true (width r) n e q a N
  let S := eventPolicy false (width r) n e q a N
  let six := sixthPolicy n e q a (N : ℝ)
  let eight := policy (width r) n e q a (N : ℝ)
  exact ⟨halves hComp (hCorrection B zeta K (S false) (R false) cap w z L),
    halves hSave (hCorrection B zeta K (eight false) (six false) cap w z L)⟩

end
end ImbalancedChen.P1OriginalHistoricalAtlasCorrectionReduction
