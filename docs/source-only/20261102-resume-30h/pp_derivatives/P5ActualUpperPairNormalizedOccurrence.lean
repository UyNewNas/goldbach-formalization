import ImbalancedChen.P5ActualIndependentUpperPairLogFields
import ImbalancedChen.P5ActualAllRankOccurrenceFourierBridge
import ImbalancedChen.ActualUpperCountingInputs

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original caller is the production smoothPhysicalPairOuterRamp on TWO
independent prime coordinates. Its prime-product target remains RAW.
Only the HB group chart below is divided by the two original group logs.
The G extension is exact on ALL natural group products, including 0 and 1.

This constructs the complete rank-two occurrence chart and its actual
ordered-word / mixedD budgets without assuming an all-rank Family. No
rank-zero/rank-one profiles are padded into Family 2. The exact integer
atom identity fixes the original Licence, complete-product trim, every
original group bump and both original logarithmic denominators.
-/
namespace ImbalancedChen.P5Z.ActualUpperPairNormalizedOccurrence
noncomputable section
open Classical Set Filter
open scoped BigOperators
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open AdmissibleAllRankIntegerGeometricFamily GroupedOccurrenceLogShift
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open ActualOccurrencePlateauWordBudget ActualEtaPsiOccurrenceBudget
open ActualEuclideanPhysicalFourier OccurrenceEuclideanMixedIntegral
open ActualAllRankOccurrenceFourierBridge
open LicensedOriginalIntegerProfile
open P5ActualIndependentUpperPairProfile

/-- This is the original raw upper source's HB group chart. The normalizer
belongs here, rather than in the original prime-product discrepancy. -/
def groupChart (D : Parameters) (b : Band D) (N : ℕ) (κ₀ : ℝ)
    (R : Fin 2 → ℝ) (p : Fin 2 → ℝ) : ℝ :=
  ActualIndependentUpperPairLogFields.profile D b N p *
    eta ((∏ i, p i) / (N : ℝ) ^ (1 - κ₀)) * ∏ i, psi (p i / R i)

/-- Same original owner map, complete product and all grouped psi factors.
The plateau is the existing fixed occurrence plateau. -/
def occurrenceChart {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ)
    (κ₀ : ℝ) (z : Fin m → ℝ) : ℝ :=
  ActualIndependentUpperPairLogFields.profile D b N
      (fun i => groupProduct owner U i z) *
    actualEta N owner U κ₀ z * actualPsi owner U R z * plateau m z

theorem occurrenceChart_eq_groupChart {m : ℕ} (D : Parameters) (b : Band D)
    (N : ℕ) (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ)
    (κ₀ : ℝ) (z : Fin m → ℝ) :
    occurrenceChart D b N owner U R κ₀ z =
      groupChart D b N κ₀ R (fun i => groupProduct owner U i z) * plateau m z := rfl

/-- Exact original-group logarithms, on all HB integer replacements.
No prime, roughness or congruence indicator is introduced by normalization. -/
theorem groupChart_nat (D : Parameters) (b : Band D) (N : ℕ) (κ₀ : ℝ)
    (R : Fin 2 → ℝ) (u : Fin 2 → ℕ) :
    groupChart D b N κ₀ R (fun i => (u i : ℝ)) =
      chartAmbient (P5ActualIndependentUpperPairProfile.licence D b N)
        chi eta (N : ℝ) κ₀ R (fun i => (u i : ℝ)) /
          ∏ i, Real.log (u i : ℝ) := by
  rw [groupChart, ActualIndependentUpperPairLogFields.exact_integer_normalization]
  unfold ActualIndependentUpperPairLogFields.integerWeight chartAmbient
    P5ActualIndependentUpperPairProfile.licence
    P5ActualIndependentUpperPairProfile.integerWeight
  simp only [psi]
  ring

/-- On the actual production prime carrier this is the raw original caller
times the exact HB log normalizer. It is not a PP theorem for the divided test. -/
theorem original_prime_caller_groupChart (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N) (κ₀ : ℝ) (R : Fin 2 → ℝ)
    (u : Fin 2 → Fin (N + 1)) (hu : u ∈ Part3.labelledPrimeTuples 2 N) :
    groupChart D b N κ₀ R (P4B.primeTuplePoint N u) =
      (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
          (selected D).width u / ∏ i, Real.log ((u i).val : ℝ)) *
        eta ((∏ i, ((u i).val : ℝ)) / (N : ℝ) ^ (1 - κ₀)) *
          ∏ i, psi (((u i).val : ℝ) / R i) := by
  unfold groupChart
  rw [← ActualIndependentUpperPairLogFields.exact_original_pair_caller D b hN u hu]
  rfl

/-- The actual chart inherits the original complete-product endpoints;
neither the cutoff nor reciprocal logs weaken the original lower floor. -/
theorem groupChart_endpoint_product_fields (D : Parameters) (b : Band D)
    {N : ℕ} {κ₀ : ℝ} {R : Fin 2 → ℝ} {p : Fin 2 → ℝ}
    (hp : groupChart D b N κ₀ R p ≠ 0) :
    2 ≤ N ∧ (∀ i, (N : ℝ)^D.theta < p i) ∧
      (N : ℝ)^(1-D.kappaZero) < ∏ i, p i ∧
        (∏ i, p i) < Real.exp (selected D).width * (N : ℝ) := by
  apply ActualIndependentUpperPairLogFields.actual_endpoint_product_fields D b
  intro hz
  exact hp (by simp only [groupChart, hz, zero_mul])

theorem finite_groupChart_integer_support (D : Parameters) (b : Band D)
    (N : ℕ) (κ₀ : ℝ) (R : Fin 2 → ℝ) :
    Set.Finite {u : Fin 2 → ℕ | groupChart D b N κ₀ R (fun i => (u i : ℝ)) ≠ 0} := by
  apply (ActualIndependentUpperPairLogFields.finite_integer_support D b N).subset
  intro u hu
  rw [← ActualIndependentUpperPairLogFields.exact_integer_normalization]
  intro hz
  exact hu (by simp only [groupChart, hz, zero_mul])

/-- These are endpoints of the original independent group products of
the actual HB chart, including arbitrary repeated occurrence owners. -/
theorem occurrenceChart_original_endpoints {m : ℕ} (D : Parameters) (b : Band D)
    {N : ℕ} {owner : Fin m → Fin 2} {U : Fin m → ℝ} {R : Fin 2 → ℝ}
    {κ₀ : ℝ} {z : Fin m → ℝ} (hz : occurrenceChart D b N owner U R κ₀ z ≠ 0) :
    2 ≤ N ∧ (∀ i, (N : ℝ)^D.theta < groupProduct owner U i z) ∧
      (N : ℝ)^(1-D.kappaZero) < ∏ i, groupProduct owner U i z ∧
        (∏ i, groupProduct owner U i z) < Real.exp (selected D).width * (N : ℝ) := by
  apply ActualIndependentUpperPairLogFields.actual_endpoint_product_fields D b
  intro hp
  exact hz (by simp only [occurrenceChart, hp, zero_mul])

/-- The normalized extension has no hidden collar above the original N cap,
eventually and uniformly in b. This uses the second genuine prime coordinate. -/
theorem eventually_full_normalized_support_inside_original_cap (D : Parameters) :
    ∀ᶠ N : ℕ in atTop, ∀ (b : Band D) (p : Fin 2 → ℝ),
      ActualIndependentUpperPairLogFields.profile D b N p ≠ 0 →
        ∀ i, p i < (N : ℝ) := by
  filter_upwards [eventually_full_support_inside_original_cap D] with N hN
  intro b p hp
  exact hN b p (ActualIndependentGroupLogNormalization.normalize_nonzero hp)

/-- Exact raw signed source, with both count and coprime mean unchanged.
This connects the actual production caller to its G raw Licence; the
reciprocal-log profile does not replace W in this functional. -/
theorem original_signed_source (D : Parameters) (b : Band D) {N : ℕ}
    (hN : 2 ≤ N) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 2 N N Q rho
      (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
        (selected D).width) =
      Part3.primeProductSignedError 2 N N Q rho
        (fun u => P5ActualIndependentUpperPairProfile.integerWeight D b N
          (fun i => (u i).val)) := by
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [actual_original_caller D b hN u hu]
  rfl

/-- Literal same-rho specialization at the current production upper
consumer. No coefficient support, density or distribution premise is used. -/
theorem original_attachedUpper_signed_source (D : Parameters) (b : Band D)
    {N : ℕ} (hN : 2 ≤ N) (nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    Part3.primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (P4B.smoothPhysicalPairOuterRamp b.val N (manuscriptHalfProductCutoff D.kappa N)
        (selected D).width) =
      Part3.primeProductSignedError 2 N N
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)
        (fun u => P5ActualIndependentUpperPairProfile.integerWeight D b N
          (fun i => (u i).val)) :=
  original_signed_source D b hN _ _

theorem grouped_profile_smooth {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun z => ActualIndependentUpperPairLogFields.profile D b N
      (fun i => groupProduct owner U i z)) := by
  apply (ActualIndependentUpperPairLogFields.profile_smooth D b N).comp
  exact contDiff_pi.mpr (fun i => groupProduct_smooth owner U i)

theorem occurrenceChart_smooth {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ) :
    ContDiff ℝ ∞ (occurrenceChart D b N owner U R κ₀) :=
  (((grouped_profile_smooth D b N owner U).mul
    (actualEta_smooth N owner U κ₀)).mul (actualPsi_smooth owner U R)).mul
      (plateau_smooth m)

theorem occurrenceChart_tsupport_box {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ) :
    tsupport (occurrenceChart D b N owner U R κ₀) ⊆ plateauBox m :=
  window_tsupport m (fun z => ActualIndependentUpperPairLogFields.profile D b N
    (fun i => groupProduct owner U i z) * actualEta N owner U κ₀ z * actualPsi owner U R z)

theorem occurrenceChart_compact {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ) :
    HasCompactSupport (occurrenceChart D b N owner U R κ₀) := by
  apply HasCompactSupport.of_support_subset_isCompact (plateauBox_compact m)
  exact (subset_tsupport _).trans (occurrenceChart_tsupport_box D b N owner U R κ₀)

/-- The full rank-two chart bound, with no abstract Family or derivative
envelope premise. The constant precedes b,N,all owner maps, positive block
scales, complete-product trim exponents, and every repeated ordered word.
The genuine HB occurrence limits are 6*2 and 12*2. Here the log cost is B=0. -/
theorem exists_occurrenceChart_word_budget (D : Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Band D) (N m : ℕ) (owner : Fin m → Fin 2)
      (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ) (w : List (Fin m)) z,
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) →
      m ≤ 12 → w.length ≤ 24 → |occWord w (occurrenceChart D b N owner U R κ₀) z| ≤ C := by
  obtain ⟨CA, hCA, bA⟩ :=
    ActualIndependentUpperPairLogFields.actual_normalized_occurrence_budget D 24
  obtain ⟨ME, hME, bE⟩ := finite_order_constants etaLog exists_etaLog_order_bound 24
  obtain ⟨MP, hMP, bP⟩ := finite_order_constants psiLog exists_psiLog_order_bound 24
  obtain ⟨MC, hMC, bCut⟩ := exists_uniform_plateau_word_budget 2
  let C : ℝ := (4 : ℝ)^24 * (CA : ℝ) * ME * MP^2 * MC
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro b N m owner U R κ₀ w z hN hU hR hm hw
  have he (v : List (Fin m)) (hv : v.length ≤ w.length) :
      |occWord v (actualEta N owner U κ₀) z| ≤ ME := by
    rw [actualEta_eq_scalarLift N owner U κ₀ hN hU, occWord_scalarLift]
    exact bE v.length (hv.trans hw) _
  have hp (v : List (Fin m)) (hv : v.length ≤ w.length) :
      |occWord v (actualPsi owner U R) z| ≤ MP^2 := by
    rw [actualPsi_eq_groupTensor owner U R hU hR]
    exact groupTensor_word_bound owner _ psiLog v z MP (zero_le_one.trans hMP)
      (fun n hn x => bP n (hn.trans (hv.trans hw)) x)
  have hraw := occWord_four_bound
    (fun z => ActualIndependentUpperPairLogFields.profile D b N
      (fun i => groupProduct owner U i z))
    (actualEta N owner U κ₀) (actualPsi owner U R) (plateau m)
    (grouped_profile_smooth D b N owner U) (actualEta_smooth N owner U κ₀)
    (actualPsi_smooth owner U R) (plateau_smooth m) w z
    (CA : ℝ) ME (MP^2) MC (Nat.cast_nonneg _) (zero_le_one.trans hME)
    (by positivity) (zero_le_one.trans hMC)
    (fun v hv => bA b N m owner U v z (hv.trans hw)) he hp
    (fun v hv => bCut m (by omega) v (by omega) z)
  calc
    |occWord w (occurrenceChart D b N owner U R κ₀) z| ≤
        (4 : ℝ)^w.length * ((CA : ℝ)*ME*MP^2*MC) := hraw
    _ ≤ (4 : ℝ)^24 * ((CA : ℝ)*ME*MP^2*MC) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hw) (by positivity)
    _ = C := by dsimp [C]; ring

/-- Exact HB integer atom, including unit occurrences and every repeated
original owner. The right-closed atom removes the existing plateau by proof. -/
theorem occurrenceChart_integer_atom {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ)
    (n : Fin m → ℕ) (hU : ∀ a, 0 < U a) (hlo : ∀ a, U a < (n a : ℝ))
    (hhi : ∀ a, (n a : ℝ) ≤ 2 * U a) :
    occurrenceChart D b N owner U R κ₀ (logOccurrence U n) =
      chartAmbient (P5ActualIndependentUpperPairProfile.licence D b N)
        chi eta (N : ℝ) κ₀ R (fun i => (integerGroupProduct owner n i : ℝ)) /
          ∏ i, Real.log (integerGroupProduct owner n i : ℝ) := by
  have hn : ∀ a, 0 < n a := fun a => by exact_mod_cast (hU a).trans (hlo a)
  rw [occurrenceChart_eq_groupChart,
    show plateau m (logOccurrence U n) = 1 from plateau_rightClosed_atom U n hU hlo hhi,
    mul_one]
  simp_rw [groupProduct_logOccurrence owner U n hU hn]
  exact groupChart_nat D b N κ₀ R (integerGroupProduct owner n)

def euclideanChart {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ) : V m → ℂ :=
  euclideanLift m (occurrenceChart D b N owner U R κ₀)

theorem euclideanChart_smooth {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ) :
    ContDiff ℝ ∞ (euclideanChart D b N owner U R κ₀) :=
  euclideanLift_smooth m _ (occurrenceChart_smooth D b N owner U R κ₀)

theorem euclideanChart_compact {m : ℕ} (D : Parameters) (b : Band D) (N : ℕ)
    (owner : Fin m → Fin 2) (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ) :
    HasCompactSupport (euclideanChart D b N owner U R κ₀) :=
  euclideanLift_compact m _ (occurrenceChart_compact D b N owner U R κ₀)

/-- The actual mixedD supplier needed by the existing Fourier API is
constructed for the real rank-two caller. No Family at absent ranks and
no mixedD/PP conclusion are inputs. All constants precede the original b. -/
theorem exists_actual_mixedD_budget (D : Parameters) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Band D) (N m : ℕ) (owner : Fin m → Fin 2)
      (U : Fin m → ℝ) (R : Fin 2 → ℝ) (κ₀ : ℝ),
      0 < (N : ℝ) → (∀ a, 0 < U a) → (∀ i, 0 < R i) → m ≤ 12 →
      mixedD m (euclideanChart D b N owner U R κ₀) ≤ C := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_occurrenceChart_word_budget D
  refine ⟨dimensionBudget 2 * C₀, mul_nonneg (dimensionBudget_nonneg 2) hC₀, ?_⟩
  intro b N m owner U R κ₀ hN hU hR hm
  have hlocal := mixedD_euclideanLift_le m (occurrenceChart D b N owner U R κ₀)
    (occurrenceChart_smooth D b N owner U R κ₀)
    (occurrenceChart_compact D b N owner U R κ₀)
    (occurrenceChart_tsupport_box D b N owner U R κ₀) C₀ hC₀
    (fun v hv z => hb b N m owner U R κ₀ v z hN hU hR hm (by omega))
  exact hlocal.trans (mul_le_mul_of_nonneg_right (dimension_factor_le (by omega : m ≤ 6*2)) hC₀)

end
end ImbalancedChen.P5Z.ActualUpperPairNormalizedOccurrence
