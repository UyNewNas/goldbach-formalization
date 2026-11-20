import ImbalancedChen.P1ActualVariableFifthPositiveCellLimit
import ImbalancedChen.P1ActualVariableFifthGlobalPositiveLimit
import ImbalancedChen.P1OriginalFifthUntruncatedIntegral
import ImbalancedChen.P1ActualCoarseLevelCeiling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Continuous domination only: the actual variable5/actual old4 kernel is
bounded by the integrable ORIGINAL rawQ3-to-initial kernel on the same
selected fifth domain. The coarse cap4 and cap5 tables and their checks are
constructed below. No arithmetic-source, stored-parent or policy identity
is inferred from this continuous majorization.
-/

namespace ImbalancedChen.P1ActualVariableFifthUntruncatedDomination
noncomputable section
open MeasureTheory Filter Topology Set
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseFifthContinuation
open P1CorrectedFifthDensityDictionary
open P1ActualVariableFifthProfiles
open P1OriginalFifthIntegral

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

/-- The fourth table is EXACTLY the raw selected third-cell exponent. -/
def coarseCap4 (e : ℚ) (m : ℕ) : P1OriginalCoarseContinuation.FourthCell m → ℚ :=
  P1OriginalCoarseContinuation.thirdCellExponent e m

def coarseCap5 (e : ℚ) {m : ℕ} (_j : Label5 m) : ℚ := (299 / 500 : ℚ) - 2 * e

def coarseSeed (e : ℚ) (m : ℕ) (j : Label5 m) : ℚ :=
  P1OriginalCoarseContinuation.thirdCellExponent e m
    (historicalPrefixProject (by omega : 4 ≤ 5) j)

theorem coarse_old5_eq_seed (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m) :
    old5 e chi m omega Finset.univ (coarseCap4 e m) j = coarseSeed e m j := by
  simp [old5, coarseCap4, coarseSeed]

theorem coarseSeed_cast (e : ℚ) (m : ℕ) (j : Label5 m) :
    (coarseSeed e m j : ℝ) = P1ActualVariableFourthFifthCellTestLimit.selectedSeed e m j := by
  simp only [coarseSeed, P1OriginalCoarseContinuation.cast_thirdCellExponent,
    historicalPrefixProject_comp, P1ActualVariableFourthFifthCellTestLimit.selectedSeed,
    HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner]

theorem coarseCap5_cast (e : ℚ) {m : ℕ} (j : Label5 m) :
    (coarseCap5 e j : ℝ) = initial (e : ℝ) := by
  simp [coarseCap5, initial, extendedDistributionCap]

/-- h34 is reflexivity on every actual selected fourth owner, not a
requested comparison with the variable fourth producer. -/
theorem coarse_h34 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) :
    P1OriginalCoarseContinuation.h34Check e chi m omega Finset.univ (coarseCap4 e m) = true := by
  simp [P1OriginalCoarseContinuation.h34Check, coarseCap4, decide_eq_true_eq]

/-- h45 follows from the actual selected original Gamma bound. No cap
check or pointwise majorant is assumed as a supplier. -/
theorem coarse_h45 (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) :
    h45Check e chi m omega Finset.univ (coarseCap4 e m) J5 (coarseCap5 e) = true := by
  simp only [h45Check, decide_eq_true_eq]
  intro j hj
  rw [coarse_old5_eq_seed]
  apply (Rat.cast_le (K := ℝ)).mp
  rw [coarseSeed_cast, coarseCap5_cast]
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hs := ((mem_selectedFifthCells e chi m omega J5 j).mp hj).2.1
  exact (P1ActualCoarseLevelCeiling.selected_levelExponent_lt_initial
    (e : ℝ) chi heR m _ hs).le

def coarseMajorant (e : ℚ) (m : ℕ) (j : Label5 m) (t : Point5) : ℝ :=
  cellKernel (coarseSeed e m j : ℝ) (initial (e : ℝ)) t

/-- Reuse the canonical actual positive-cell kernel; no second profile is defined. -/
abbrev actualKernel (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) : Point5 → ℝ :=
  P1ActualVariableFifthPositiveCellLimit.variableCellKernel e chi m omega j rows4 licensed4 rows5

/-- A genuine integrable continuous majorant from the constructed tables.
Only this integrability theorem is consumed; its arithmetic equalities are
not used to identify an actual variable-old source. -/
theorem integrableOn_coarseMajorant (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) :
    IntegrableOn (coarseMajorant e m j)
      (P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j) := by
  have h := P1OriginalFifthUntruncatedIntegral.integrableOn_kernel_fullCell
    e chi m omega homega homegaRho Finset.univ (coarseCap4 e m) J5 (coarseCap5 e)
    (coarse_h34 e chi m omega) (coarse_h45 e he chi m omega J5) j hj
  simpa only [coarse_old5_eq_seed, coarseCap5_cast, coarseMajorant] using h

/-- All selected raw seeds and actual fifth candidates are below initial.
The actual old4 floor and every eligible fifth row remain present. -/
theorem actualNext5_le_initial_on_owner (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) (t : Point5) :
    actualNext5 e chi m omega j rows4 licensed4 rows5 t ≤ initial (e : ℝ) := by
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hs := ((mem_selectedFifthCells e chi m omega J5 j).mp hj).2.1
  have hseed := (P1ActualCoarseLevelCeiling.selected_levelExponent_lt_initial
    (e : ℝ) chi heR m _ hs).le
  have hcap : VariableEnvelope.cap - 2 * (e : ℝ) ≤ initial (e : ℝ) := by
    dsimp [VariableEnvelope.cap, initial, extendedDistributionCap]
    linarith
  have hthird : HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdCellExponent
      (e : ℝ) chi m j = P1ActualVariableFourthFifthCellTestLimit.selectedSeed e m j := by
    simp only [HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdCellExponent, if_pos hs,
      P1ActualVariableFourthFifthCellTestLimit.selectedSeed]
  have hh := (actualNext5_mem_interval e chi m omega j rows4 licensed4 rows5 t).2
  simpa only [upperLevel, hthird, max_eq_left hseed, max_eq_left hcap] using hh

/-- Pointwise 0<=actual<=coarse, derived from canonical lower profile
monotonicity. Finite signed density monotonicity is never invoked. -/
theorem actualKernel_domination (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (t : Point5) (ht : t ∈ P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j) :
    0 ≤ actualKernel e chi m omega j rows4 licensed4 rows5 t ∧
      actualKernel e chi m omega j rows4 licensed4 rows5 t ≤ coarseMajorant e m j t := by
  have hW : 0 ≤ (∏ i : Fin 5, 1 / t i) :=
    Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht.1 i).le)
  have holdnew := old4_le_actualNext5 e chi m omega j rows4 licensed4 rows5 t
  have hnew := actualNext5_le_initial_on_owner e he chi m omega J5 j hj rows4 licensed4 rows5 t
  have hseed := originalVariableFourthProfile_inherits_rawQ3 e chi omega m j rows4 licensed4 t
  have hselected := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 j hj ht.2.2.1
  rw [hselected] at hseed
  have hseed' : (coarseSeed e m j : ℝ) ≤
      originalVariableFourthProfile e chi omega m j rows4 licensed4 t := by
    simpa only [coarseSeed_cast, P1ActualVariableFourthFifthCellTestLimit.selectedSeed] using hseed
  have hmono := p1PrimeOwnCubeGatedProfile_mono t (ht.1 (Fin.last 4)) holdnew
  have hnewmono := p1PrimeOwnCubeGatedProfile_mono t (ht.1 (Fin.last 4)) hnew
  have holdmono := p1PrimeOwnCubeGatedProfile_mono t (ht.1 (Fin.last 4)) hseed'
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hmono) hW
  · change (_ - _) * (∏ i : Fin 5, 1 / t i) ≤ (_ - _) * (∏ i : Fin 5, 1 / t i)
    exact mul_le_mul_of_nonneg_right (by linarith) hW

/-- The constructed majorant and actual local atom integrability imply
full integrability by the same exact exhaustion. No full integral is an
input. The concrete local atom supplier is composed below. -/
theorem integrableOn_actualKernel_of_local
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (hlocal : ∀ a : ℝ, 0 < a → IntegrableOn
      (actualKernel e chi m omega j rows4 licensed4 rows5)
      (truncatedCell e chi m omega a j)) :
    IntegrableOn (actualKernel e chi m omega j rows4 licensed4 rows5)
      (P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j) := by
  let F := actualKernel e chi m omega j rows4 licensed4 rows5
  let G := coarseMajorant e m j
  let K := P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j
  have hG : IntegrableOn G K := integrableOn_coarseMajorant e he chi m omega homega homegaRho J5 j hj
  have hK : MeasurableSet K := P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j
  have hT (n : ℕ) : truncatedCell e chi m omega (P1OriginalFifthUntruncatedIntegral.cutoff n) j ⊆ K :=
    P1OriginalFifthUntruncatedIntegral.truncatedCell_subset_fullCell e chi m omega
      (P1OriginalFifthUntruncatedIntegral.cutoff_pos n) j
  have hfi : ∀ n : ℕ, IntegrableOn F
      (truncatedCell e chi m omega (P1OriginalFifthUntruncatedIntegral.cutoff n) j)
      (volume.restrict K) := by
    intro n
    change Integrable _ ((volume.restrict _).restrict _)
    rw [Measure.restrict_restrict_of_subset (hT n)]
    exact hlocal _ (P1OriginalFifthUntruncatedIntegral.cutoff_pos n)
  have hnn : ∀ᵐ t ∂volume.restrict K, 0 ≤ F t := by
    filter_upwards [ae_restrict_mem hK] with t ht
    exact (actualKernel_domination e he chi m omega J5 j hj rows4 licensed4 rows5 t ht).1
  have hGnn : ∀ᵐ t ∂volume.restrict K, 0 ≤ G t := by
    filter_upwards [ae_restrict_mem hK] with t ht
    have hd := actualKernel_domination e he chi m omega J5 j hj rows4 licensed4 rows5 t ht
    exact hd.1.trans hd.2
  apply (P1OriginalFifthUntruncatedIntegral.truncatedCell_aecover e chi m omega j).integrable_of_integral_bounded_of_nonneg_ae (∫ t in K, G t) hfi hnn
  apply Eventually.of_forall
  intro n
  rw [Measure.restrict_restrict_of_subset (hT n)]
  calc
    (∫ t in truncatedCell e chi m omega (P1OriginalFifthUntruncatedIntegral.cutoff n) j, F t) ≤
        ∫ t in truncatedCell e chi m omega (P1OriginalFifthUntruncatedIntegral.cutoff n) j, G t :=
      setIntegral_mono_on (hlocal _ (P1OriginalFifthUntruncatedIntegral.cutoff_pos n))
        (hG.mono_set (hT n)) (truncatedCell_measurable e chi m omega _ j)
        (fun t ht => (actualKernel_domination e he chi m omega J5 j hj
          rows4 licensed4 rows5 t (hT n ht)).2)
    _ ≤ ∫ t in K, G t := setIntegral_mono_set hG hGnn (Eventually.of_forall (fun t ht => hT n ht))

/-- General positive-cut exhaustion for an integrable function on this
exact original domain. Its concrete use below supplies integrability from
actual row atoms and the constructed coarse majorant. -/
theorem tendsto_positive_cut_integral_of_integrable
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (f : Point5 → ℝ)
    (hf : IntegrableOn f (P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j)) :
    Tendsto (fun a : ℝ => ∫ t in truncatedCell e chi m omega a j, f t)
      (𝓝[Ioi 0] (0 : ℝ))
      (𝓝 (∫ t in P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j, f t)) := by
  let K := P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j
  have hK : MeasurableSet K := P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j
  have hmeas : ∀ᶠ a : ℝ in 𝓝[Ioi 0] (0 : ℝ), AEStronglyMeasurable
      ((truncatedCell e chi m omega a j).indicator f) (volume.restrict K) :=
    Eventually.of_forall fun a => hf.aestronglyMeasurable.indicator (truncatedCell_measurable e chi m omega a j)
  have hbound : ∀ᶠ a : ℝ in 𝓝[Ioi 0] (0 : ℝ), ∀ᵐ t ∂volume.restrict K,
      ‖(truncatedCell e chi m omega a j).indicator f t‖ ≤ ‖f t‖ := by
    apply Eventually.of_forall
    intro a
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ truncatedCell e chi m omega a j
    · rw [indicator_of_mem ht]
    · rw [indicator_of_not_mem ht]
      simp
  have hpoint : ∀ᵐ t ∂volume.restrict K,
      Tendsto (fun a : ℝ => (truncatedCell e chi m omega a j).indicator f t)
        (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (f t)) := by
    filter_upwards [ae_restrict_mem hK] with t ht
    have hcoords : ∀ᶠ a : ℝ in 𝓝[Ioi 0] (0 : ℝ), ∀ i : Fin 5, a < t i :=
      eventually_all.2 (fun i => (gt_mem_nhds (ht.1 i)).filter_mono nhdsWithin_le_nhds)
    apply tendsto_const_nhds.congr'
    filter_upwards [hcoords] with a ha
    have hmem : t ∈ truncatedCell e chi m omega a j :=
      ⟨mem_logPrimeBox.mpr (fun i => ⟨(ha i).le, (mem_logPrimeBox.mp ht.2.1 i).2⟩), ht.2.2⟩
    rw [indicator_of_mem hmem]
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖f t‖) hmeas hbound hf.norm hpoint
  apply hlim.congr'
  have hpos : ∀ᶠ a : ℝ in 𝓝[Ioi 0] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  filter_upwards [hpos] with a ha
  change (∫ t in K, (truncatedCell e chi m omega a j).indicator f t) = _
  rw [setIntegral_indicator (truncatedCell_measurable e chi m omega a j),
    inter_eq_right.mpr (P1OriginalFifthUntruncatedIntegral.truncatedCell_subset_fullCell e chi m omega ha j)]
/-- The true local measurability/integrability supplier uses shared fourth
face atoms and fixed selected fifth eligibility. Full integrability is now
concluded with no local or full desired-integral premise. -/
theorem integrableOn_actualKernel_fullCell
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) :
    IntegrableOn (actualKernel e chi m omega j rows4 licensed4 rows5)
      (P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j) := by
  apply integrableOn_actualKernel_of_local e he chi m omega homega homegaRho J5 j hj rows4 licensed4 rows5
  intro a ha
  exact P1ActualVariableFifthPositiveCellLimit.integrableOn_actualVariable5_kernel
    e chi m omega a ha J5 j hj rows4 licensed4 rows5

def fullCellIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) (j : Label5 m) : ℝ :=
  ∫ t in P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j,
    actualKernel e chi m omega j rows4 licensed4 rows5 t

def fullSelectedIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    fullCellIntegral e chi m omega rows4 licensed4 rows5 j

/-- Reuses the exact canonical per-owner variableCellIntegral. -/
abbrev selectedCellIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) : ℝ → ℝ :=
  P1ActualVariableFifthGlobalSourceAssembly.selectedIntegral e chi m omega rows4 licensed4 J5 rows5

theorem fullCellIntegral_nonneg_le_coarse
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) :
    0 ≤ fullCellIntegral e chi m omega rows4 licensed4 rows5 j ∧
      fullCellIntegral e chi m omega rows4 licensed4 rows5 j ≤
        ∫ t in P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j, coarseMajorant e m j t := by
  have hK := P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j
  constructor
  · exact setIntegral_nonneg hK (fun t ht =>
      (actualKernel_domination e he chi m omega J5 j hj rows4 licensed4 rows5 t ht).1)
  · exact setIntegral_mono_on
      (integrableOn_actualKernel_fullCell e he chi m omega homega homegaRho J5 j hj rows4 licensed4 rows5)
      (integrableOn_coarseMajorant e he chi m omega homega homegaRho J5 j hj) hK
      (fun t ht => (actualKernel_domination e he chi m omega J5 j hj rows4 licensed4 rows5 t ht).2)

/-- Genuine a↓0 convergence to a specified FULL actual-variable integral,
not an unnamed limit or a coarse-source identification. -/
theorem tendsto_variableCellIntegral_fullCellIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) :
    Tendsto (fun a : ℝ => P1ActualVariableFifthPositiveCellLimit.variableCellIntegral
      e chi m omega a j rows4 licensed4 rows5) (𝓝[Ioi 0] (0 : ℝ))
      (𝓝 (fullCellIntegral e chi m omega rows4 licensed4 rows5 j)) := by
  exact tendsto_positive_cut_integral_of_integrable e chi m omega j
    (actualKernel e chi m omega j rows4 licensed4 rows5)
    (integrableOn_actualKernel_fullCell e he chi m omega homega homegaRho J5 j hj rows4 licensed4 rows5)

/-- The finite exact selected sum has its real full-integral limit. -/
theorem tendsto_selectedCellIntegral_fullSelectedIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)) :
    Tendsto (P1ActualVariableFifthGlobalSourceAssembly.selectedIntegral e chi m omega rows4 licensed4 J5 rows5)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (fullSelectedIntegral e chi m omega rows4 licensed4 J5 rows5)) := by
  exact tendsto_finsetSum (selectedFifthCells e chi m omega J5) (fun j hj =>
    tendsto_variableCellIntegral_fullCellIntegral e he chi m omega homega homegaRho J5 j hj rows4 licensed4 rows5)
end
end ImbalancedChen.P1ActualVariableFifthUntruncatedDomination