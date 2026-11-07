import ImbalancedChen.P5AllGroupHBLogNormalization
import ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
import ImbalancedChen.P5ActualAllRankOccurrenceFourierBridge

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual narrow singleton lower caller reaches the log-normalized
ALL-group HB atlas with its ORIGINAL lower small/rough rho. Its two
external smoothing reserves and three internal HB reserves are explicit.
The normalized smooth occurrence chart has a proved uniform derivative
and Fourier integral budget without an abstract Family-cover premise.
This is one genuine independent rank; it does not supply absent callers.
-/
namespace ImbalancedChen.P5Z.ActualLowerNormalizedHBSource
noncomputable section
open Classical MeasureTheory Set Filter Topology
open scoped BigOperators
open AllGroupHBLogNormalization OriginalPrimeAllGroupHBDiscrepancy
open LicensedOriginalIntegerProfile ExactOriginalSmoothDyadicPartition
open ActualIndependentGroupLogNormalization ExistingIndependentFamilyLogNormalization
open P5CanonicalTentNarrowSingletonTransfer
open AdmissibleAllRankIntegerGeometricFamily GroupedOccurrenceLogShift
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open ActualEtaPsiOccurrenceBudget ActualOccurrencePlateauWordBudget
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open OccurrenceEuclideanMixedIntegral ActualEuclideanPhysicalFourier

/-- This is the normalized ambient of the EXISTING source licence;
the prime test itself stays the original unnormalized narrow caller. -/
def ambient (kappa : ℝ) (B N : ℕ) : (Fin 1 → ℝ) → ℝ :=
  normalize (actualLicence kappa B N).ambient

theorem ambient_smooth (kappa : ℝ) (B N : ℕ) :
    ContDiff ℝ ∞ (ambient kappa B N) :=
  normalize_smooth _ (actualLicence kappa B N).smooth

theorem ambient_integer (kappa : ℝ) (B N : ℕ) (u : Fin 1 → ℕ) :
    ambient kappa B N (fun i => (u i : ℝ)) =
      ActualSingletonLogCollarFamily.integerWeight (1-kappa)
        (ActualSingletonLogCollarFamily.logWidth B N) N u /
          ∏ i, Real.log (u i : ℝ) :=
  normalize_nat (actualLicence kappa B N).ambient u

theorem ambient_support (kappa : ℝ) (hkappa : kappa < 1) (B N : ℕ)
    (u : Fin 1 → ℝ) (hu : ambient kappa B N u ≠ 0) :
    (∀ i, (N : ℝ) ^ (1-kappa) ≤ u i) ∧ (∏ i, u i) ≤ 2 * (N : ℝ) := by
  exact ActualSingletonLogCollarFamily.logWidth_family_support
    (by linarith : 0 < 1-kappa) B (normalize_nonzero hu)

/-- One constant precedes N, the lower-policy parameters, every real
point, every occurrence count and every repeated ordered owner word. -/
theorem normalized_occurrence_budget (B q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (kappa : ℝ) N m (owner : Fin m → Fin 1)
      (U : Fin m → ℝ) (w : List (Fin m)) z, w.length ≤ q →
      |occWord w (fun y => ambient kappa B N
        (fun i => groupProduct owner U i y)) z| ≤
          (C : ℝ) * Real.log ((N : ℝ) + 2) ^ (B*q) := by
  obtain ⟨K, hK, hb⟩ := normalize_occurrence_bound 1 q
  obtain ⟨C0, hC0, hraw⟩ := ActualSingletonLogCollarFamily.logWidth_mixedEuler B q
  refine ⟨K*C0, Nat.mul_pos hK hC0, ?_⟩
  intro kappa N m owner U w z hw
  have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by positivity)
  have h := hb 1 le_rfl m owner U (actualLicence kappa B N).ambient
    (actualLicence kappa B N).smooth
    ((C0 : ℝ) * Real.log ((N : ℝ) + 2) ^ (B*q)) (by positivity)
    (fun v p hv => hraw (1-kappa) N v p hv) w z hw
  simpa only [ambient, Nat.cast_mul, mul_assoc] using h

def chart {m : ℕ} (kappa : ℝ) (B N : ℕ) (owner : Fin m → Fin 1)
    (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ) (z : Fin m → ℝ) : ℝ :=
  ambient kappa B N (fun i => groupProduct owner U i z) *
    actualEta N owner U kappa0 z * actualPsi owner U R z * plateau m z

theorem chart_smooth {m : ℕ} (kappa : ℝ) (B N : ℕ) (owner : Fin m → Fin 1)
    (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ) :
    ContDiff ℝ ∞ (chart kappa B N owner U R kappa0) := by
  have hp : ContDiff ℝ ∞ (fun z => fun i => groupProduct owner U i z) :=
    contDiff_pi.mpr (fun i => groupProduct_smooth owner U i)
  exact ((((ambient_smooth kappa B N).comp hp).mul
    (actualEta_smooth N owner U kappa0)).mul (actualPsi_smooth owner U R)).mul
      (plateau_smooth m)

theorem chart_compact {m : ℕ} (kappa : ℝ) (B N : ℕ) (owner : Fin m → Fin 1)
    (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ) :
    HasCompactSupport (chart kappa B N owner U R kappa0) := by
  apply (plateau_compact m).mono'
  intro z hz
  apply subset_tsupport (plateau m)
  intro hzero
  exact hz (by simp [chart, hzero])

/-- All factors of the genuine normalized smooth chart are paid,
including the original eta, every group psi and the occurrence plateau.
For order-three HB at the genuine rank one, m<=6 and orders<=12 suffice. -/
theorem complete_chart_word_budget (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N m (owner : Fin m → Fin 1)
      (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ)
      (w : List (Fin m)) z,
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) →
      m ≤ 6 → w.length ≤ 12 →
      |occWord w (chart kappa B N owner U R kappa0) z| ≤
        C * Real.log ((N : ℝ) + 2) ^ (B*12) := by
  obtain ⟨CN, hCN, bn⟩ := normalized_occurrence_budget B 12
  obtain ⟨ME, hME, be⟩ := finite_order_constants etaLog exists_etaLog_order_bound 12
  obtain ⟨MP, hMP, bp⟩ := finite_order_constants psiLog exists_psiLog_order_bound 12
  obtain ⟨MC, hMC, bc⟩ := exists_uniform_plateau_word_budget 1
  let C : ℝ := (4 : ℝ)^12 * (CN : ℝ) * ME * MP * MC
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro kappa N m owner U R kappa0 w z hN hU hR hm hw
  have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by positivity)
  have hf : ContDiff ℝ ∞ (fun z => ambient kappa B N
      (fun i => groupProduct owner U i z)) :=
    (ambient_smooth kappa B N).comp
      (contDiff_pi.mpr (fun i => groupProduct_smooth owner U i))
  have bE (v : List (Fin m)) (hv : v.length ≤ w.length) :
      |occWord v (actualEta N owner U kappa0) z| ≤ ME := by
    rw [actualEta_eq_scalarLift N owner U kappa0 hN hU, occWord_scalarLift]
    exact be v.length (hv.trans hw) _
  have bP (v : List (Fin m)) (hv : v.length ≤ w.length) :
      |occWord v (actualPsi owner U R) z| ≤ MP := by
    rw [actualPsi_eq_groupTensor owner U R hU hR]
    simpa only [pow_one] using groupTensor_word_bound owner _ psiLog v z MP
      (zero_le_one.trans hMP) (fun n hn x => bp n (hn.trans (hv.trans hw)) x)
  have h := occWord_four_bound
    (fun z => ambient kappa B N (fun i => groupProduct owner U i z))
    (actualEta N owner U kappa0) (actualPsi owner U R) (plateau m)
    hf (actualEta_smooth N owner U kappa0) (actualPsi_smooth owner U R)
    (plateau_smooth m) w z
    ((CN : ℝ) * Real.log ((N : ℝ) + 2) ^ (B*12)) ME MP MC
    (by positivity) (zero_le_one.trans hME) (zero_le_one.trans hMP)
    (zero_le_one.trans hMC)
    (fun v hv => bn kappa N m owner U v z (hv.trans hw)) bE bP
    (fun v hv => bc m (by omega) v (by omega) z)
  change |occWord w (chart kappa B N owner U R kappa0) z| ≤ _ at h
  calc
    _ ≤ (4 : ℝ)^w.length *
        (((CN : ℝ) * Real.log ((N : ℝ) + 2) ^ (B*12)) * ME * MP * MC) := h
    _ ≤ (4 : ℝ)^12 *
        (((CN : ℝ) * Real.log ((N : ℝ) + 2) ^ (B*12)) * ME * MP * MC) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw) (by positivity)
    _ = C * Real.log ((N : ℝ) + 2) ^ (B*12) := by dsimp [C]; ring

def euclideanChart {m : ℕ} (kappa : ℝ) (B N : ℕ) (owner : Fin m → Fin 1)
    (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ) : V m → ℂ :=
  euclideanLift m (chart kappa B N owner U R kappa0)

/-- This is the actual Euclidean derivative integral required by Fourier
separation, obtained from the concrete chart rather than a Family premise. -/
theorem actual_mixedD_budget (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N m (owner : Fin m → Fin 1)
      (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ),
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 6 →
      mixedD m (euclideanChart kappa B N owner U R kappa0) ≤
        C * Real.log ((N : ℝ) + 2) ^ (B*12) := by
  obtain ⟨C0, hC0, hb⟩ := complete_chart_word_budget B
  refine ⟨dimensionBudget 1 * C0, mul_nonneg (dimensionBudget_nonneg 1) hC0, ?_⟩
  intro kappa N m owner U R kappa0 hN hU hR hm
  have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by positivity)
  have hs : tsupport (chart kappa B N owner U R kappa0) ⊆ plateauBox m :=
    window_tsupport m (fun z => ambient kappa B N (fun i => groupProduct owner U i z) *
      actualEta N owner U kappa0 z * actualPsi owner U R z)
  have h := mixedD_euclideanLift_le m (chart kappa B N owner U R kappa0)
    (chart_smooth kappa B N owner U R kappa0)
    (chart_compact kappa B N owner U R kappa0) hs
    (C0 * Real.log ((N : ℝ) + 2) ^ (B*12)) (by positivity)
    (fun v hv z => hb kappa N m owner U R kappa0 v z hN hU hR hm (by omega))
  exact h.trans (by
    calc
      _ ≤ dimensionBudget 1 * (C0 * Real.log ((N : ℝ) + 2) ^ (B*12)) :=
        mul_le_mul_of_nonneg_right (dimension_factor_le (by omega : m ≤ 6*1)) (by positivity)
      _ = _ := by ring)

/-- A direct same-extension Fourier norm bound. There is no replacement
of this reciprocal-log chart by the earlier unnormalized chart. -/
theorem actual_fourier_l1_budget (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N m (owner : Fin m → Fin 1)
      (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ),
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 6 →
      (∫ ξ : Fin m → ℝ, ‖physicalFourier m
        (euclideanChart kappa B N owner U R kappa0) ξ‖) / frequencyScale^m ≤
          C * Real.log ((N : ℝ) + 2) ^ (B*12) / 2^m := by
  obtain ⟨C, hC, hb⟩ := actual_mixedD_budget B
  refine ⟨C, hC, ?_⟩
  intro kappa N m owner U R kappa0 hN hU hR hm
  exact (physicalFourier_normalized_l1_le m _
    (euclideanLift_smooth m _ (chart_smooth kappa B N owner U R kappa0))
    (euclideanLift_compact m _ (chart_compact kappa B N owner U R kappa0))).trans
      (div_le_div_of_nonneg_right (hb kappa N m owner U R kappa0 hN hU hR hm) (by positivity))

/-- The pointwise cube tail uses the SAME normalized extension. This is
not yet its payment after the full arithmetic modulus sum. -/
theorem actual_normalized_cube_tail (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (kappa : ℝ) N m (owner : Fin m → Fin 1)
      (U : Fin m → ℝ) (R : Fin 1 → ℝ) (kappa0 : ℝ),
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 6 →
      ∀ (H : ℝ), 0 < H → ∀ z : V m,
      ‖euclideanChart kappa B N owner U R kappa0 z -
        truncatedPhysical m (euclideanChart kappa B N owner U R kappa0) H z‖ ≤
          (m : ℝ) * (C * Real.log ((N : ℝ) + 2) ^ (B*12)) / H := by
  obtain ⟨C, hC, hb⟩ := actual_mixedD_budget B
  refine ⟨C, hC, ?_⟩
  intro kappa N m owner U R kappa0 hN hU hR hm H hH z
  exact (actual_uniform_truncation_error m _
    (euclideanLift_smooth m _ (chart_smooth kappa B N owner U R kappa0))
    (euclideanLift_compact m _ (chart_compact kappa B N owner U R kappa0)) H hH z).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb kappa N m owner U R kappa0 hN hU hR hm)
          (Nat.cast_nonneg m)) hH.le)

def lowerAtlas (kappa : ℝ) (B N : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  trimReserve (actualLicence kappa B N) (2*N) N kappa0
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) +
    ∑ js ∈ chartBank (2*N) 1,
      (normalizedAllGroupAtlas (actualLicence kappa B N) 1 (2*N) N kappa0
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js -
        properPowerReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js +
        roughPrimeReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (actualLowerSmallRoughModuli retainEven N cap w z)
          (fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)) js)

theorem actual_lower_smooth_normalized (kappa : ℝ) (B N : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    (Part3.primeProductSignedError 1 (2*N) N
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualLowerSmallRoughRho retainEven N cap w z L)
      (fullSmoothWeight kappa B N) : ℂ) =
        lowerAtlas kappa B N kappa0 retainEven cap w z L :=
  original_prime_normalized_allGroup (actualLicence kappa B N) 1 (2*N) N kappa0
    (actualLowerSmallRoughModuli retainEven N cap w z)
    (actualLowerSmallRoughRho retainEven N cap w z L)

/-- This starts at the actual independently defined sharp lower receiver.
The normalization does not change its physical rho or its exact coprime
mean, and does not silently delete either of its external reserves. -/
theorem original_lower_source_normalized (kappa : ℝ) (B N : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    (Part3.primeProductSignedError 1 N N
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualLowerSmallRoughRho retainEven N cap w z L)
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) : ℂ) =
      lowerAtlas kappa B N kappa0 retainEven cap w z L +
        (lowerReserve kappa B N (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) : ℂ) +
        (upperReserve kappa B N (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) : ℂ) := by
  rw [original_source_exact_reserves]
  push_cast
  rw [actual_lower_smooth_normalized]

/-- Consume the independently proved genuine narrow source-restoration
payment at this SAME normalized atlas. The full physical Q support gate
is explicit; no unsupported claim about the adopted lower level is made.
Internal HB reserves are still inside lowerAtlas and are not paid here. -/
theorem eventually_original_lower_hb_smoothing_paid (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool)
      (cap M : ℕ) (w z L kappa0 : ℝ),
      Even N → M ≤ N →
      actualLowerSmallRoughModuli retainEven N cap w z ⊆ Finset.Icc 1 M →
      ‖(Part3.primeProductSignedError 1 N N
        (actualLowerSmallRoughModuli retainEven N cap w z)
        (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight N (fun _ => 1)) : ℂ) -
          lowerAtlas kappa (A+3) N kappa0 retainEven cap w z L‖ ≤
        41 * (N : ℝ) / Real.log (N : ℝ)^A := by
  filter_upwards [eventually_original_source_smoothing_paid kappa hkappa hkappa1 A]
    with N hN
  intro retainEven cap M w z L kappa0 hEven hMN hQ
  rw [← actual_lower_smooth_normalized]
  have h := hN retainEven cap M w z L
    (actualLowerSmallRoughModuli retainEven N cap w z) hEven hMN hQ
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

end
end ImbalancedChen.P5Z.ActualLowerNormalizedHBSource
