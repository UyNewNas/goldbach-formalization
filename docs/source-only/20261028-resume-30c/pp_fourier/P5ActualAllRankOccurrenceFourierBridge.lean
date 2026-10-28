import ImbalancedChen.P5OccurrenceEuclideanMixedIntegral
import ImbalancedChen.P5ActualEtaPsiOccurrenceBudget
import ImbalancedChen.PrimeProductsMellinExactMeanInsertion

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
This applies the occurrence/Fourier connection to the actual all-rank
original test family, complete-product eta, grouped psi and fixed plateau.
The independent test word is recovered from HB occurrence products. It is
never identified with a marked prime word inside the physical modulus rho.
The final finite count/mean identity uses exactly the same rho and complete
integer on both sides. No Fourier representation, mixedD bound or final
prime-product estimate is supplied as a premise.
-/
namespace ImbalancedChen.P5Z.ActualAllRankOccurrenceFourierBridge
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open AdmissibleAllRankIntegerGeometricFamily GroupedOccurrenceLogShift
open AllWordAmbientOccurrenceBound ActualOccurrencePlateauWordBudget
open ActualEtaPsiOccurrenceBudget ActualEuclideanPhysicalFourier
open OccurrenceEuclideanMixedIntegral
open ImbalancedChen.PrimeProducts

variable {kStar m : ℕ}

def actualEuclideanChart (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) : V m → ℂ :=
  euclideanLift m (actualChart A T k owner U R κ₀)

theorem actualEuclideanChart_smooth (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) :
    ContDiff ℝ ∞ (actualEuclideanChart A T k owner U R κ₀) :=
  euclideanLift_smooth m _ (actualChart_smooth A T k owner U R κ₀)

theorem actualEuclideanChart_compact (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) :
    HasCompactSupport (actualEuclideanChart A T k owner U R κ₀) :=
  euclideanLift_compact m _ (actualChart_compact A T k owner U R κ₀)

theorem actualChart_tsupport_box (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) :
    tsupport (actualChart A T k owner U R κ₀) ⊆ plateauBox m :=
  window_tsupport m (fun z => A.ambient T k (fun i => groupProduct owner U i z) *
    actualEta T owner U κ₀ z * actualPsi owner U R z)

/-- This is the genuine D_T integral budget for the actual independent
occurrence chart. The constant is chosen once for the original all-rank
Family, before T, k, owner maps, U/R scales and κ₀. The occurrence cutoff
budgets, derivative transport and L1 integration are all proved upstream. -/
theorem exists_actual_mixedD_budget (A : Family kStar) :
    ∃ C : ℝ, ∃ B : ℕ, 0 ≤ C ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ),
        0 < (T : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 6 * kStar →
        mixedD m (actualEuclideanChart A T k owner U R κ₀) ≤
          C * Real.log ((T : ℝ) + 2) ^ B := by
  obtain ⟨C₀, B, hC₀, hword⟩ := exists_actualChart_word_budget A
  refine ⟨dimensionBudget kStar * C₀, B,
    mul_nonneg (dimensionBudget_nonneg kStar) hC₀, ?_⟩
  intro T k m owner U R κ₀ hT hU hR hm
  have hlog : 0 ≤ Real.log ((T : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hbound : 0 ≤ C₀ * Real.log ((T : ℝ) + 2) ^ B := by positivity
  have hlocal := mixedD_euclideanLift_le m (actualChart A T k owner U R κ₀)
    (actualChart_smooth A T k owner U R κ₀) (actualChart_compact A T k owner U R κ₀)
    (actualChart_tsupport_box A T k owner U R κ₀)
    (C₀ * Real.log ((T : ℝ) + 2) ^ B) hbound
    (fun v hv z => hword T k m owner U R κ₀ v z hT hU hR hm (by omega))
  calc
    mixedD m (actualEuclideanChart A T k owner U R κ₀) ≤
        (2 : ℝ) ^ m * boxMass ^ m * (C₀ * Real.log ((T : ℝ) + 2) ^ B) := hlocal
    _ ≤ dimensionBudget kStar * (C₀ * Real.log ((T : ℝ) + 2) ^ B) :=
      mul_le_mul_of_nonneg_right (dimension_factor_le hm) hbound
    _ = (dimensionBudget kStar * C₀) * Real.log ((T : ℝ) + 2) ^ B := by ring

/-- The physical Fourier amplitude contains exactly the inversion
normalization. It is the same scalar coefficient for count and exact mean. -/
def actualAmplitude (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (ξ : Fin m → ℝ) : ℂ :=
  (frequencyScale ^ m)⁻¹ • physicalFourier m (actualEuclideanChart A T k owner U R κ₀) ξ

theorem actualAmplitude_integrable (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) :
    Integrable (actualAmplitude A T k owner U R κ₀) :=
  (physicalFourier_integrable m (actualEuclideanChart A T k owner U R κ₀)
    (actualEuclideanChart_smooth A T k owner U R κ₀)
    (actualEuclideanChart_compact A T k owner U R κ₀)).const_smul _

theorem actualAmplitude_l1_le (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) :
    (∫ ξ : Fin m → ℝ, ‖actualAmplitude A T k owner U R κ₀ ξ‖) ≤
      mixedD m (actualEuclideanChart A T k owner U R κ₀) / 2 ^ m := by
  have heq :
      (∫ ξ : Fin m → ℝ, ‖actualAmplitude A T k owner U R κ₀ ξ‖) =
      (∫ ξ : Fin m → ℝ,
        ‖physicalFourier m (actualEuclideanChart A T k owner U R κ₀) ξ‖) /
        frequencyScale ^ m := by
    simp only [actualAmplitude, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg frequencyScale_pos.le m))]
    rw [integral_const_mul]
    ring
  rw [heq]
  exact physicalFourier_normalized_l1_le m _
    (actualEuclideanChart_smooth A T k owner U R κ₀)
    (actualEuclideanChart_compact A T k owner U R κ₀)


/-- One preselected logarithmic budget supplies the actual derivative
integral, actual Fourier L1 mass and actual retained-cube error together.
The exponent/constant are uniform before all arithmetic parameters. -/
theorem exists_actual_fourier_budgets (A : Family kStar) :
    ∃ C : ℝ, ∃ B : ℕ, 0 ≤ C ∧
      ∀ (T : ℕ) (k : Fin (kStar + 1)) (m : ℕ)
        (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ),
        0 < (T : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 6 * kStar →
        mixedD m (actualEuclideanChart A T k owner U R κ₀) ≤
          C * Real.log ((T : ℝ) + 2) ^ B ∧
        (∫ ξ : Fin m → ℝ, ‖actualAmplitude A T k owner U R κ₀ ξ‖) ≤
          (C * Real.log ((T : ℝ) + 2) ^ B) / 2 ^ m ∧
        ∀ (H : ℝ), 0 < H → ∀ z : V m,
          ‖actualEuclideanChart A T k owner U R κ₀ z -
            truncatedPhysical m (actualEuclideanChart A T k owner U R κ₀) H z‖ ≤
          (m : ℝ) * (C * Real.log ((T : ℝ) + 2) ^ B) / H := by
  obtain ⟨C, B, hC, hb⟩ := exists_actual_mixedD_budget A
  refine ⟨C, B, hC, ?_⟩
  intro T k m owner U R κ₀ hT hU hR hm
  have hd := hb T k m owner U R κ₀ hT hU hR hm
  refine ⟨hd, (actualAmplitude_l1_le A T k owner U R κ₀).trans
    (div_le_div_of_nonneg_right hd (by positivity)), ?_⟩
  intro H hH z
  exact (actual_uniform_truncation_error m (actualEuclideanChart A T k owner U R κ₀)
    (actualEuclideanChart_smooth A T k owner U R κ₀)
    (actualEuclideanChart_compact A T k owner U R κ₀) H hH z).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg m)) hH.le)

/-- Recover the original independent integer word from occurrence roles.
The same original owner may repeat, with its full product multiplicity. -/
def integerGroupProduct {k m : ℕ} (owner : Fin m → Fin k)
    (n : Fin m → ℕ) (i : Fin k) : ℕ :=
  ∏ a : Fin m, if owner a = i then n a else 1

def logOccurrence (U : Fin m → ℝ) (n : Fin m → ℕ) : Fin m → ℝ :=
  fun a => Real.log ((n a : ℝ) / U a)


/-- The physical phase is a genuine tensor of individual occurrence
modes. All factors are attached to independent test coordinates; rho and
its marked modulus primes never enter these coordinates. -/
def occurrenceMode (U : Fin m → ℝ) (n : Fin m → ℕ) (ξ : Fin m → ℝ) : ℂ :=
  ∏ a, Complex.exp ((((ξ a * logOccurrence U n a : ℝ) : ℂ)) * Complex.I)

theorem physicalPhase_occurrenceMode (U : Fin m → ℝ) (n : Fin m → ℕ)
    (ξ : Fin m → ℝ) :
    physicalPhase m (WithLp.toLp 2 (logOccurrence U n)) ξ = occurrenceMode U n ξ := by
  unfold physicalPhase dotPhysical occurrenceMode
  simp only [PiLp.toLp_apply, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

/-- The logarithmic coordinate is evaluated on the actual individual
integer atom, and is not a mark inside the modulus coefficient. -/
theorem groupProduct_logOccurrence {k m : ℕ} (owner : Fin m → Fin k)
    (U : Fin m → ℝ) (n : Fin m → ℕ)
    (hU : ∀ a, 0 < U a) (hn : ∀ a, 0 < n a) (i : Fin k) :
    groupProduct owner U i (logOccurrence U n) = (integerGroupProduct owner n i : ℝ) := by
  classical
  unfold groupProduct groupBase groupLog integerGroupProduct
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  push_cast
  apply Finset.prod_congr rfl
  intro a ha
  by_cases hoa : owner a = i
  · simp only [hoa, if_true, logOccurrence]
    rw [Real.exp_log (div_pos (by exact_mod_cast hn a) (hU a))]
    field_simp [(hU a).ne']
  · simp [hoa]

/-- All occurrences appear in one and only one original owner product.
This complete integer is used by both congruence and coprimality tests. -/
theorem complete_product_grouped {k m : ℕ} (owner : Fin m → Fin k) (n : Fin m → ℕ) :
    (∏ i : Fin k, integerGroupProduct owner n i) = ∏ a : Fin m, n a := by
  classical
  unfold integerGroupProduct
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro a ha
  have hprod := Finset.prod_eq_single (s := (Finset.univ : Finset (Fin k)))
    (f := fun i => if owner a = i then n a else 1) (owner a)
    (fun i hi hne => by simp [Ne.symm hne]) (by simp)
  simpa using hprod

/-- Literal original ambient integer extension, smooth complete-product
trim and original grouped psi, without a spurious sharp group indicator. -/
def integerChartWeight (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (R : Fin k.val → ℝ) (κ₀ : ℝ) (n : Fin m → ℕ) : ℝ :=
  A.ambient T k (fun i => (integerGroupProduct owner n i : ℝ)) *
    eta (((∏ i, integerGroupProduct owner n i : ℕ) : ℝ) / (T : ℝ) ^ (1 - κ₀)) *
    ∏ i, psi ((integerGroupProduct owner n i : ℝ) / R i)

/-- At every actual right-closed (U,2U] integer atom the fixed occurrence
plateau equals one, and the Euclidean chart is exactly the original
integer extension with its complete trim and grouped profile factors. -/
theorem actualEuclideanChart_integer_atom (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (n : Fin m → ℕ)
    (hU : ∀ a, 0 < U a) (hlo : ∀ a, U a < (n a : ℝ))
    (hhi : ∀ a, (n a : ℝ) ≤ 2 * U a) :
    actualEuclideanChart A T k owner U R κ₀ (WithLp.toLp 2 (logOccurrence U n)) =
      (integerChartWeight A T k owner R κ₀ n : ℂ) := by
  have hn : ∀ a, 0 < n a := fun a => by exact_mod_cast (hU a).trans (hlo a)
  rw [actualEuclideanChart, euclideanLift_toLp]
  unfold actualChart actualEta actualPsi integerChartWeight
  simp_rw [groupProduct_logOccurrence owner U n hU hn]
  rw [show plateau m (logOccurrence U n) = 1 from plateau_rightClosed_atom U n hU hlo hhi]
  simp only [mul_one, Nat.cast_prod]

/-- Fourier inversion for each actual HB integer tuple. This eliminates
the representation hypothesis formerly required by the finite same-rho
Mellin functional, and retains the independent original group word. -/
theorem integerChartWeight_fourier (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (n : Fin m → ℕ)
    (hU : ∀ a, 0 < U a) (hlo : ∀ a, U a < (n a : ℝ))
    (hhi : ∀ a, (n a : ℝ) ≤ 2 * U a) :
    (integerChartWeight A T k owner R κ₀ n : ℂ) =
      ∫ ξ : Fin m → ℝ, actualAmplitude A T k owner U R κ₀ ξ *
        physicalPhase m (WithLp.toLp 2 (logOccurrence U n)) ξ := by
  have hprod :
      (fun ξ => actualAmplitude A T k owner U R κ₀ ξ *
        physicalPhase m (WithLp.toLp 2 (logOccurrence U n)) ξ) =
      fun ξ => (frequencyScale ^ m)⁻¹ •
        (physicalFourier m (actualEuclideanChart A T k owner U R κ₀) ξ *
          physicalPhase m (WithLp.toLp 2 (logOccurrence U n)) ξ) := by
    funext ξ
    simp only [actualAmplitude, smul_mul_assoc]
  rw [hprod, integral_smul, physical_inverse m _
    (actualEuclideanChart_smooth A T k owner U R κ₀)
    (actualEuclideanChart_compact A T k owner U R κ₀),
    actualEuclideanChart_integer_atom A T k owner U R κ₀ n hU hlo hhi]

/-- Absolute integrability of every real integer tuple's separated mode
is proved from the actual amplitude and unit complex phase. -/
theorem actual_integer_mode_integrable (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (owner : Fin m → Fin k.val)
    (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ) (n : Fin m → ℕ) :
    Integrable (fun ξ : Fin m → ℝ => actualAmplitude A T k owner U R κ₀ ξ *
      physicalPhase m (WithLp.toLp 2 (logOccurrence U n)) ξ) := by
  have hA := actualAmplitude_integrable A T k owner U R κ₀
  apply hA.norm.mono'
    (hA.aestronglyMeasurable.mul (physicalPhase_continuous m _).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ξ => by rw [norm_mul, physicalPhase_norm, mul_one])

/-- The finite same-rho count/mean functional commutes with the actual
all-rank Fourier modes. The representation and integrability inputs are
proved above for this chart and the retained integer atoms. -/
theorem same_rho_actual_fourier_integral {ι : Type*}
    (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (s : Finset ι) (n : ι → Fin m → ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) (a : ℕ)
    (hU : ∀ j, 0 < U j)
    (hlo : ∀ i ∈ s, ∀ j, U j < (n i j : ℝ))
    (hhi : ∀ i ∈ s, ∀ j, (n i j : ℝ) ≤ 2 * U j) :
    MellinInsertion20261028.exactDiscrepancy s Q rho (fun i => ∏ j, n i j) a
      (fun i => (integerChartWeight A T k owner R κ₀ (n i) : ℂ)) =
    ∫ ξ : Fin m → ℝ, actualAmplitude A T k owner U R κ₀ ξ *
      MellinInsertion20261028.exactDiscrepancy s Q rho (fun i => ∏ j, n i j) a
        (fun i => physicalPhase m (WithLp.toLp 2 (logOccurrence U (n i))) ξ) := by
  classical
  let c : ι → ℂ := fun i => ∑ q ∈ Q,
    rho q * MellinInsertion20261028.residueKernel q a (∏ j, n i j)
  have hrep (i : ι) (hi : i ∈ s) := integerChartWeight_fourier A T k owner U R κ₀
    (n i) hU (hlo i hi) (hhi i hi)
  change MellinInsertion20261028.functional s c
    (fun i => (integerChartWeight A T k owner R κ₀ (n i) : ℂ)) = _
  calc
    MellinInsertion20261028.functional s c
        (fun i => (integerChartWeight A T k owner R κ₀ (n i) : ℂ)) =
      MellinInsertion20261028.functional s c (fun i =>
        ∫ ξ : Fin m → ℝ, actualAmplitude A T k owner U R κ₀ ξ *
          physicalPhase m (WithLp.toLp 2 (logOccurrence U (n i))) ξ) := by
      unfold MellinInsertion20261028.functional
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrep i hi]
    _ = ∫ ξ : Fin m → ℝ, MellinInsertion20261028.functional s c
        (fun i => actualAmplitude A T k owner U R κ₀ ξ *
          physicalPhase m (WithLp.toLp 2 (logOccurrence U (n i))) ξ) :=
      MellinInsertion20261028.functional_integral s c _
        (fun i hi => actual_integer_mode_integrable A T k owner U R κ₀ (n i))
    _ = _ := by
      simp_rw [MellinInsertion20261028.functional_mul]
      rfl

/-- Expanded count and exact coprime mean: no projector, complete integer
or physical signed coefficient is changed by the Fourier separation. -/
theorem same_rho_count_mean_fourier {ι : Type*}
    (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (s : Finset ι) (n : ι → Fin m → ℕ) (Q : Finset ℕ) (rho : ℕ → ℂ) (a : ℕ)
    (hU : ∀ j, 0 < U j)
    (hlo : ∀ i ∈ s, ∀ j, U j < (n i j : ℝ))
    (hhi : ∀ i ∈ s, ∀ j, (n i j : ℝ) ≤ 2 * U j) :
    (∑ q ∈ Q, rho q *
      (MellinInsertion20261028.residueCount s (fun i => ∏ j, n i j) a q
        (fun i => (integerChartWeight A T k owner R κ₀ (n i) : ℂ)) -
       MellinInsertion20261028.exactCoprimeMean s (fun i => ∏ j, n i j) q
        (fun i => (integerChartWeight A T k owner R κ₀ (n i) : ℂ)))) =
    ∫ ξ : Fin m → ℝ, actualAmplitude A T k owner U R κ₀ ξ *
      (∑ q ∈ Q, rho q *
        (MellinInsertion20261028.residueCount s (fun i => ∏ j, n i j) a q
          (fun i => physicalPhase m (WithLp.toLp 2 (logOccurrence U (n i))) ξ) -
         MellinInsertion20261028.exactCoprimeMean s (fun i => ∏ j, n i j) q
          (fun i => physicalPhase m (WithLp.toLp 2 (logOccurrence U (n i))) ξ))) := by
  rw [← MellinInsertion20261028.exactDiscrepancy_eq_count_sub_mean,
    same_rho_actual_fourier_integral A T k owner U R κ₀ s n Q rho a hU hlo hhi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    rw [MellinInsertion20261028.exactDiscrepancy_eq_count_sub_mean])

/-- Actual finite HB slot weights (truncated Moebius, logs, rough
projectors, finite signs and multiplicities) stay outside the smooth
geometric differentiation. The same fixed slot weight occurs in count
and exact coprime mean and is restored on every independent tensor mode. -/
theorem same_rho_hb_weighted_tensor_integral {ι : Type*}
    (A : Family kStar) (T : ℕ) (k : Fin (kStar + 1))
    (owner : Fin m → Fin k.val) (U : Fin m → ℝ) (R : Fin k.val → ℝ) (κ₀ : ℝ)
    (s : Finset ι) (n : ι → Fin m → ℕ) (β : ι → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (a : ℕ)
    (hU : ∀ j, 0 < U j)
    (hlo : ∀ i ∈ s, ∀ j, U j < (n i j : ℝ))
    (hhi : ∀ i ∈ s, ∀ j, (n i j : ℝ) ≤ 2 * U j) :
    MellinInsertion20261028.exactDiscrepancy s Q rho (fun i => ∏ j, n i j) a
      (fun i => β i * (integerChartWeight A T k owner R κ₀ (n i) : ℂ)) =
    ∫ ξ : Fin m → ℝ, actualAmplitude A T k owner U R κ₀ ξ *
      MellinInsertion20261028.exactDiscrepancy s Q rho (fun i => ∏ j, n i j) a
        (fun i => β i * occurrenceMode U (n i) ξ) := by
  classical
  let c : ι → ℂ := fun i => ∑ q ∈ Q,
    rho q * MellinInsertion20261028.residueKernel q a (∏ j, n i j)
  have hrep (i : ι) (hi : i ∈ s) :
      β i * (integerChartWeight A T k owner R κ₀ (n i) : ℂ) =
      ∫ ξ : Fin m → ℝ, actualAmplitude A T k owner U R κ₀ ξ *
        (β i * occurrenceMode U (n i) ξ) := by
    rw [integerChartWeight_fourier A T k owner U R κ₀ (n i) hU (hlo i hi) (hhi i hi),
      ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [physicalPhase_occurrenceMode]
      ring)
  have hint (i : ι) : Integrable (fun ξ : Fin m → ℝ =>
      actualAmplitude A T k owner U R κ₀ ξ * (β i * occurrenceMode U (n i) ξ)) := by
    have hi := (actual_integer_mode_integrable A T k owner U R κ₀ (n i)).const_mul (β i)
    apply hi.congr
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [physicalPhase_occurrenceMode]
      ring)
  change MellinInsertion20261028.functional s c
    (fun i => β i * (integerChartWeight A T k owner R κ₀ (n i) : ℂ)) = _
  calc
    MellinInsertion20261028.functional s c
        (fun i => β i * (integerChartWeight A T k owner R κ₀ (n i) : ℂ)) =
      MellinInsertion20261028.functional s c (fun i =>
        ∫ ξ : Fin m → ℝ, actualAmplitude A T k owner U R κ₀ ξ *
          (β i * occurrenceMode U (n i) ξ)) := by
      unfold MellinInsertion20261028.functional
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrep i hi]
    _ = ∫ ξ : Fin m → ℝ, MellinInsertion20261028.functional s c
        (fun i => actualAmplitude A T k owner U R κ₀ ξ *
          (β i * occurrenceMode U (n i) ξ)) :=
      MellinInsertion20261028.functional_integral s c _ (fun i hi => hint i)
    _ = _ := by
      simp_rw [MellinInsertion20261028.functional_mul]
      rfl

end
end ImbalancedChen.P5Z.ActualAllRankOccurrenceFourierBridge
