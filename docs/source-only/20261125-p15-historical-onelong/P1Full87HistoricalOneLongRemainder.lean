import ImbalancedChen.P1Full87PhysicalKernelSmoothing
import ImbalancedChen.P1OriginalSingletonOneLongConsumer
import ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero

/-! Remove the original one-long sum from two historical physical prime counts.
The retained complex sum contains the trim, medium and remaining Type I charts,
and the signed proper-power correction for each history's own coefficient. -/
namespace ImbalancedChen.P1Full87HistoricalOneLongRemainder
noncomputable section

open Classical Filter VariableEnvelope
open scoped BigOperators
open P1Full87HistoricalMiddleSmoothing (remainingModuli smoothRemaining policyRemaining)
open P1Full87TrueDPolicyDelta
  (trueDDeltaRho trueDDeltaSupport trueDDeltaSupport_squarefree trueDDeltaSupport_coprime_target)
open P1OriginalSingletonOneLongCoefficients (modulusCap)
open P1OriginalSingletonOneLongConsumer (sourceChannel eventually_actual_sourceChannel)
open P1OriginalSingletonOneLongRectangle (remainingTypeIAtlas noMedium_exact_partition)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence fullSmoothWeight)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (trimReserve properPowerReserve)
open P5Z.OriginalPrimeAtlasReserveBranches
  (mediumAtlas originalMediumLow originalMediumHigh original_prime_discrepancy_mode_carriers)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy policy)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest densityTest gain primeMass)
open P1Original87SharpMiddleReserve (comparisonReceiver)

/-- The surviving original singleton chart terms at prime cap 2*N and residue N. -/
def retainedAtlas (kap zeta : ℝ) (K N : ℕ) (Q : Finset ℕ) (c : ℕ → ℝ) : ℂ :=
  let lic := actualLicence kap 6 N
  let rho := fun d => (c d : ℂ)
  trimReserve lic (2*N) N kap Q rho +
    ∑ js ∈ chartBank (2*N) 1,
      (mediumAtlas lic K (2*N) N kap (originalMediumLow zeta js) (originalMediumHigh zeta js)
          Q rho js +
       remainingTypeIAtlas lic K (2*N) N kap (originalMediumLow zeta js) (originalMediumHigh zeta js)
          Q rho js -
       properPowerReserve lic K (2*N) N kap Q rho js)

def historyRemainder (B kap zeta : ℝ) (K : ℕ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℂ :=
  retainedAtlas kap zeta K N (remainingModuli B N (trueDDeltaSupport old fresh N cap w z))
    (trueDDeltaRho old fresh N cap w z L)

/-- A common threshold gives the exact chart identity before either history is chosen. -/
private theorem eventually_split (kap zeta : ℝ) (hk : kap < 1) (K : ℕ) (hK : 1 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ (Q : Finset ℕ) (c : ℕ → ℝ),
      (Part3.primeProductSignedError 1 (2*N) N Q c (fullSmoothWeight kap 6 N) : ℂ) =
        retainedAtlas kap zeta K N Q c + sourceChannel kap N K zeta Q (fun d => (c d : ℂ)) := by
  filter_upwards [
    P1OriginalSingletonRoughPrimeReserveZero.eventually_original_singleton_roughPrimeReserve_sum_zero
      K hK kap hk] with N hzero
  intro Q c
  rw [show (Part3.primeProductSignedError 1 (2*N) N Q c (fullSmoothWeight kap 6 N) : ℂ) = _
      from original_prime_discrepancy_mode_carriers (actualLicence kap 6 N) K (2*N) N kap zeta Q c]
  unfold retainedAtlas sourceChannel
  dsimp only
  simp_rw [noMedium_exact_partition]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hzero 6 kap Q (fun d => (c d : ℂ))]
  ring

/-- The physical signed difference is uniformly one-bounded. Cut the same
modulus set that occurs in policyRemaining, including its strict upper end. -/
theorem eventually_history_remainder (kap zeta : ℝ) (hk : kap < 1) (hz : 0 < zeta)
    (hz1 : zeta ≤ 1/20000) (K : ℕ) (hK : 1 ≤ K) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℝ) (old fresh : List ℕ → Bool)
      (cap : ℕ) (w z L : ℝ),
      ‖(policyRemaining B kap old fresh N cap w z L : ℂ) -
        historyRemainder B kap zeta K old fresh N cap w z L‖ ≤
          (N : ℝ) / Real.log (N : ℝ)^A := by
  filter_upwards [eventually_split kap zeta hk K hK,
    eventually_actual_sourceChannel kap zeta hk hz hz1 K 1 (by norm_num) A 1 (by norm_num)]
    with N hsplit hlong
  intro B old fresh cap w z L
  let Q := remainingModuli B N (trueDDeltaSupport old fresh N cap w z)
  let c := trueDDeltaRho old fresh N cap w z L
  have hmem {d : ℕ} (hd : d ∈ Q) : d ∈ trueDDeltaSupport old fresh N cap w z :=
    (Finset.mem_filter.mp hd).1
  have hcut : Q ⊆ Finset.Ioc 0 (modulusCap N) := by
    intro d hd
    have hupper : (d : ℝ) < (N : ℝ)^(599/1000 : ℝ) := (Finset.mem_filter.mp hd).2.2
    exact Finset.mem_Ioc.mpr
      ⟨Nat.pos_of_ne_zero (trueDDeltaSupport_squarefree old fresh N cap w z (hmem hd)).ne_zero,
       Nat.le_floor hupper.le⟩
  have hcop : ∀ d ∈ Q, N.Coprime d := fun d hd =>
    (trueDDeltaSupport_coprime_target old fresh N cap w z (hmem hd)).symm
  have hunit : ∀ d ∈ Q, ‖(c d : ℂ)‖ ≤ 1 := by
    intro d _
    simpa only [c, Complex.norm_real, Real.norm_eq_abs] using
      P1Full87TrueDUnitBound.trueDDeltaRho_abs_le_one old fresh N cap d w z L
  change ‖(Part3.primeProductSignedError 1 (2*N) N Q c (fullSmoothWeight kap 6 N) : ℂ) -
    retainedAtlas kap zeta K N Q c‖ ≤ _
  rw [hsplit Q c, add_sub_cancel_left]
  simpa only [one_mul] using hlong Q (fun d => (c d : ℂ)) hcut hcop hunit

private theorem combine {x p H u : ℝ} {r : ℂ}
    (hx : |x-p| ≤ u/2*H) (hr : ‖(p : ℂ)-r‖ ≤ u/2*H) :
    ‖(x : ℂ)-r‖ ≤ u*H := by
  have hxp : ‖(x : ℂ)-(p : ℂ)‖ ≤ u/2*H := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hx
  calc
    _ ≤ ‖(x : ℂ)-(p : ℂ)‖ + ‖(p : ℂ)-r‖ := by
      simpa only [dist_eq_norm] using dist_triangle (x : ℂ) (p : ℂ) r
    _ ≤ u/2*H + u/2*H := add_le_add hxp hr
    _ = _ := by ring

/-- The raw-minus-licensed and sixth-minus-eighth physical receivers keep
their own signed coefficient and exact mean. The same cutoff, choices and
target threshold serve both. Each retained atlas is an explicit remainder. -/
theorem exists_original_count_remainders :
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
              historyRemainder B kap zeta K (S false) (R false) N cap w z L‖
              ≤ u * singularNormalization N ∧
          ‖((gain (width r) n e q a N cap w z L (receiverTest N) -
              primeMass N * gain (width r) n e q a N cap w z L densityTest : ℝ) : ℂ) -
              historyRemainder B kap zeta K (eight false) (six false) N cap w z L‖
              ≤ u * singularNormalization N := by
  obtain ⟨B, hB, hreceivers⟩ := P1Full87PhysicalKernelSmoothing.exists_original_kernel_receivers
  refine ⟨B, hB, ?_⟩
  intro kap zeta K hkap hk hz hz1 hK u epsSource epsBox epsSixth hu hs hb h6
  obtain ⟨s, r, E, hE, hE1, hSix, hSrc, hChoose⟩ :=
    (hreceivers kap hkap hk).1 (u/2) epsSource epsBox epsSixth (half_pos hu) hs hb h6
  refine ⟨s, r, E, hE, hE1, hSix, hSrc, ?_⟩
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
  filter_upwards [hPhysical, eventually_history_remainder kap zeta hk hz hz1 K hK 3,
    p5z_eventually_logCube_le_singularNormalization 1 (u/2) (half_pos hu)] with N hP hR hScale
  intro hev cap w z ell hw hzcut hcap hell hell1
  obtain ⟨hComp, hSave⟩ := hP hev cap w z ell hw hzcut hcap hell hell1
  have hbudget : (N : ℝ) / Real.log (N : ℝ)^3 ≤ u/2*singularNormalization N := by
    simpa only [one_mul] using hScale
  exact ⟨combine hComp ((hR B _ _ cap w z ((N : ℝ)^ell)).trans hbudget),
    combine hSave ((hR B _ _ cap w z ((N : ℝ)^ell)).trans hbudget)⟩

end
end ImbalancedChen.P1Full87HistoricalOneLongRemainder
