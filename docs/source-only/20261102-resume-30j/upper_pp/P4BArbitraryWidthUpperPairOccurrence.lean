import ImbalancedChen.P4BArbitraryWidthUpperPairHBNormalization
import ImbalancedChen.P5ActualUpperPairNormalizedOccurrence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The full original rank-two HB occurrence chart at every legal physical
width: actual normalized independent pair, complete-product eta, both
original-group psi factors, and the existing individual plateau. One
constant precedes width, with the proved width^(-24) dependence retained.
-/
namespace ImbalancedChen.P4BArbitraryWidthUpperPairOccurrence
noncomputable section
open Classical Set Filter
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P4BArbitraryWidthUpperPairHBNormalization
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget
open P5Z.AdmissibleAllRankIntegerGeometricFamily P5Z.GroupedOccurrenceLogShift
open P5Z.AllWordAmbientOccurrenceBound P5Z.OccurrenceWordFourFactorLeibniz
open P5Z.ActualOccurrencePlateauWordBudget P5Z.ActualEtaPsiOccurrenceBudget
open P5Z.ActualEuclideanPhysicalFourier P5Z.OccurrenceEuclideanMixedIntegral
open P5Z.ActualAllRankOccurrenceFourierBridge P5Z.LicensedOriginalIntegerProfile

def groupChart (b kappa width : ℝ) (N : ℕ) (kappa0 : ℝ)
    (R : Fin 2 → ℝ) (p : Fin 2 → ℝ) : ℝ :=
  normalizedProfile b kappa width N p *
    eta ((∏ i, p i) / (N : ℝ) ^ (1 - kappa0)) * ∏ i, psi (p i / R i)

def occurrenceChart {m : ℕ} (b kappa width : ℝ) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ)
    (kappa0 : ℝ) (z : Fin m → ℝ) : ℝ :=
  normalizedProfile b kappa width N (fun i => groupProduct owner U i z) *
    actualEta N owner U kappa0 z * actualPsi owner U R z * plateau m z

theorem occurrenceChart_eq_groupChart {m : ℕ} (b kappa width : ℝ)
    (N : ℕ) (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ)
    (kappa0 : ℝ) (z : Fin m → ℝ) :
    occurrenceChart b kappa width N owner U R kappa0 z =
      groupChart b kappa width N kappa0 R (fun i => groupProduct owner U i z) *
        plateau m z := rfl

section Fields
variable {b kappa nu r width : ℝ}
variable (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hwidth : 0 < width)
variable (hgap : 2 * width ≤ baseline b kappa - nu * r)

theorem groupChart_nat (N : ℕ) (kappa0 : ℝ) (R : Fin 2 → ℝ) (u : Fin 2 → ℕ) :
    groupChart b kappa width N kappa0 R (fun i => (u i : ℝ)) =
      chartAmbient (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N)
        chi eta (N : ℝ) kappa0 R (fun i => (u i : ℝ)) /
          ∏ i, Real.log (u i : ℝ) := by
  rw [groupChart, exact_integer_normalization]
  unfold normalizedIntegerWeight chartAmbient P4BArbitraryWidthUpperPairProfile.licence integerWeight
  simp only [psi]
  ring

include hb hnu hr hwidth hgap in
theorem grouped_profile_smooth {m : ℕ} (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun z => normalizedProfile b kappa width N
      (fun i => groupProduct owner U i z)) := by
  apply (normalized_smooth hb hnu hr hwidth hgap N).comp
  exact contDiff_pi.mpr (fun i => groupProduct_smooth owner U i)

include hb hnu hr hwidth hgap in
theorem occurrenceChart_smooth {m : ℕ} (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (kappa0 : ℝ) :
    ContDiff ℝ ∞ (occurrenceChart b kappa width N owner U R kappa0) :=
  (((grouped_profile_smooth hb hnu hr hwidth hgap N owner U).mul
    (actualEta_smooth N owner U kappa0)).mul (actualPsi_smooth owner U R)).mul
      (plateau_smooth m)

/-- The atom equals the RAW original Licence chart divided by the two
original group logs; units and repeated owners stay in the same carrier. -/
theorem occurrenceChart_integer_atom {m : ℕ} (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (kappa0 : ℝ)
    (n : Fin m → ℕ) (hU : ∀ a, 0 < U a) (hlo : ∀ a, U a < (n a : ℝ))
    (hhi : ∀ a, (n a : ℝ) ≤ 2 * U a) :
    occurrenceChart b kappa width N owner U R kappa0 (logOccurrence U n) =
      chartAmbient (P4BArbitraryWidthUpperPairProfile.licence hb hnu hr hwidth hgap N)
        chi eta (N : ℝ) kappa0 R (fun i => (integerGroupProduct owner n i : ℝ)) /
          ∏ i, Real.log (integerGroupProduct owner n i : ℝ) := by
  have hn : ∀ a, 0 < n a := fun a => by exact_mod_cast (hU a).trans (hlo a)
  rw [occurrenceChart_eq_groupChart,
    show plateau m (logOccurrence U n) = 1 from plateau_rightClosed_atom U n hU hlo hhi,
    mul_one]
  simp_rw [groupProduct_logOccurrence owner U n hU hn]
  exact groupChart_nat hb hnu hr hwidth hgap N kappa0 R (integerGroupProduct owner n)

end Fields

theorem occurrenceChart_tsupport_box {m : ℕ} (b kappa width : ℝ) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (kappa0 : ℝ) :
    tsupport (occurrenceChart b kappa width N owner U R kappa0) ⊆ plateauBox m :=
  window_tsupport m (fun z => normalizedProfile b kappa width N
    (fun i => groupProduct owner U i z) * actualEta N owner U kappa0 z * actualPsi owner U R z)

theorem occurrenceChart_compact {m : ℕ} (b kappa width : ℝ) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (kappa0 : ℝ) :
    HasCompactSupport (occurrenceChart b kappa width N owner U R kappa0) := by
  apply HasCompactSupport.of_support_subset_isCompact (plateauBox_compact m)
  exact (subset_tsupport _).trans (occurrenceChart_tsupport_box b kappa width N owner U R kappa0)

/-- Full geometric derivative envelope for the current hUniformPP source.
The one constant is independent of width; its actual inverse-width cost
is displayed. All q arithmetic and exact means are untouched. -/
theorem exists_occurrenceChart_width_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ (N m : ℕ) (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ)
        (kappa0 : ℝ) (w : List (Fin m)) z,
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) →
      m ≤ 12 → w.length ≤ 24 →
        |occWord w (occurrenceChart b kappa width N owner U R kappa0) z| ≤ C / width ^ 24 := by
  obtain ⟨CA, hCA, bA⟩ := normalized_occurrence_width_budget 24
  obtain ⟨ME, hME, bE⟩ := finite_order_constants etaLog exists_etaLog_order_bound 24
  obtain ⟨MP, hMP, bP⟩ := finite_order_constants psiLog exists_psiLog_order_bound 24
  obtain ⟨MC, hMC, bCut⟩ := exists_uniform_plateau_word_budget 2
  let C : ℝ := (4 : ℝ) ^ 24 * CA * ME * MP ^ 2 * MC
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
    N m owner U R kappa0 w z hN hU hR hm hw
  have he (v : List (Fin m)) (hv : v.length ≤ w.length) :
      |occWord v (actualEta N owner U kappa0) z| ≤ ME := by
    rw [actualEta_eq_scalarLift N owner U kappa0 hN hU, occWord_scalarLift]
    exact bE v.length (hv.trans hw) _
  have hp (v : List (Fin m)) (hv : v.length ≤ w.length) :
      |occWord v (actualPsi owner U R) z| ≤ MP ^ 2 := by
    rw [actualPsi_eq_groupTensor owner U R hU hR]
    exact groupTensor_word_bound owner _ psiLog v z MP (zero_le_one.trans hMP)
      (fun n hn x => bP n (hn.trans (hv.trans hw)) x)
  have hraw := occWord_four_bound
    (fun z => normalizedProfile b kappa width N (fun i => groupProduct owner U i z))
    (actualEta N owner U kappa0) (actualPsi owner U R) (plateau m)
    (grouped_profile_smooth hb hnu hr hwidth hgap N owner U)
    (actualEta_smooth N owner U kappa0) (actualPsi_smooth owner U R) (plateau_smooth m) w z
    (CA / width ^ 24) ME (MP ^ 2) MC (div_nonneg hCA (pow_nonneg hwidth.le _))
    (zero_le_one.trans hME) (by positivity) (zero_le_one.trans hMC)
    (fun v hv => bA b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
      N m owner U v z (hv.trans hw)) he hp
    (fun v hv => bCut m (by omega) v (by omega) z)
  calc
    _ ≤ (4 : ℝ) ^ w.length * ((CA / width ^ 24) * ME * MP ^ 2 * MC) := hraw
    _ ≤ (4 : ℝ) ^ 24 * ((CA / width ^ 24) * ME * MP ^ 2 * MC) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw) (by positivity)
    _ = C / width ^ 24 := by dsimp [C]; ring

def euclideanChart {m : ℕ} (b kappa width : ℝ) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (kappa0 : ℝ) : V m → ℂ :=
  euclideanLift m (occurrenceChart b kappa width N owner U R kappa0)

/-- The actual Fourier API's mixedD is bounded with the same width
cost. No Family, chart-derivative, Fourier-norm or PP bound is an input. -/
theorem exists_actual_mixedD_width_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa nu r width : ℝ,
      0 < b → b ≤ 1 → 0 < kappa → 0 < nu → 0 < r → 0 < width →
      2 * width ≤ baseline b kappa - nu * r →
      ∀ (N m : ℕ) (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (kappa0 : ℝ),
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 12 →
        mixedD m (euclideanChart b kappa width N owner U R kappa0) ≤ C / width ^ 24 := by
  obtain ⟨C0, hC0, hbound⟩ := exists_occurrenceChart_width_budget
  refine ⟨dimensionBudget 2 * C0, mul_nonneg (dimensionBudget_nonneg 2) hC0, ?_⟩
  intro b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap N m owner U R kappa0 hN hU hR hm
  have hnonneg : 0 ≤ C0 / width ^ 24 := div_nonneg hC0 (pow_nonneg hwidth.le _)
  have hlocal := mixedD_euclideanLift_le m
    (occurrenceChart b kappa width N owner U R kappa0)
    (occurrenceChart_smooth hb hnu hr hwidth hgap N owner U R kappa0)
    (occurrenceChart_compact b kappa width N owner U R kappa0)
    (occurrenceChart_tsupport_box b kappa width N owner U R kappa0)
    (C0 / width ^ 24) hnonneg
    (fun v hv z => hbound b kappa nu r width hb hbOne hkappa hnu hr hwidth hgap
      N m owner U R kappa0 v z hN hU hR hm (by omega))
  calc
    _ ≤ _ := hlocal
    _ ≤ dimensionBudget 2 * (C0 / width ^ 24) :=
      mul_le_mul_of_nonneg_right (dimension_factor_le (by omega : m ≤ 6 * 2)) hnonneg
    _ = (dimensionBudget 2 * C0) / width ^ 24 := by ring

end
end ImbalancedChen.P4BArbitraryWidthUpperPairOccurrence
